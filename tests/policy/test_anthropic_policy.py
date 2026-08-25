"""
Tests for policy/anthropic.py

Unit tests mock the AsyncAnthropic client — no real API calls, no cost.
The integration test at the bottom is skipped unless ANTHROPIC_API_KEY is set.

Run all (unit only):
    pytest tests/policy/test_anthropic_policy.py -v

Run including integration:
    ANTHROPIC_API_KEY=sk-... pytest tests/policy/test_anthropic_policy.py -v

"""

from __future__ import annotations

import json
import os
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from core.ledger import Ledger
from core.proof_state import make_proof_state
from policy.anthropic import AnthropicPolicy
from policy.base import DIRECTOR_SYSTEM_PROMPT, DirectorResponse


# ---------------------------------------------------------------------------
# AnthropicPolicy (mocked client)
# ---------------------------------------------------------------------------

def _make_api_response(text: str) -> MagicMock:
    """Build a fake Anthropic API message response."""
    content_block = MagicMock()
    content_block.type = "text"
    content_block.text = text
    response = MagicMock()
    response.content = [content_block]
    return response


class _FakeStreamManager:
    """
    Fake for the object returned by client.messages.stream(...) -- an async
    context manager whose get_final_message() yields the complete Message,
    mirroring how AnthropicPolicy._call_api actually consumes it (see
    policy/anthropic.py: streaming, not a single buffered create() call, so
    a stalled response fails on the read timeout instead of hanging).
    """

    def __init__(self, final_message):
        self._final_message = final_message

    async def __aenter__(self):
        return self

    async def __aexit__(self, *exc_info):
        return False

    async def get_final_message(self):
        return self._final_message


def _make_thinking_then_text_response(thinking: str, text: str) -> MagicMock:
    """
    Build a fake response shaped like the newest Claude generation, which
    thinks by default regardless of the `thinking` param — content[0] is a
    ThinkingBlock (no .text attribute at all in the real SDK), with the
    actual answer in a later text block.
    """
    thinking_block = MagicMock(spec=["type", "thinking"])
    thinking_block.type = "thinking"
    thinking_block.thinking = thinking

    text_block = MagicMock()
    text_block.type = "text"
    text_block.text = text

    response = MagicMock()
    response.content = [thinking_block, text_block]
    return response


def _director_json(tactic: str = "simp", chosen: str = "x") -> str:
    return json.dumps({"chosen_state": chosen, "tactic": tactic, "reasoning": "because"})


def _ledger_with_one_state() -> tuple[Ledger, str]:
    ledger = Ledger()
    state_id = ledger.add_state(make_proof_state(["n + 0 = n"]))
    return ledger, state_id


@pytest.fixture
def mock_policy():
    """AnthropicPolicy with the AsyncAnthropic client replaced by a mock."""
    with patch("policy.anthropic.AsyncAnthropic") as MockClient:
        # messages.stream(...) itself is a plain (sync) call that returns an
        # async context manager -- MagicMock, not AsyncMock. The awaiting
        # happens inside the `async with` / get_final_message(), which
        # _FakeStreamManager provides.
        mock_instance = MagicMock()
        mock_instance.messages.stream = MagicMock()
        mock_instance.close = AsyncMock()
        MockClient.return_value = mock_instance

        policy = AnthropicPolicy(api_key="test-key")
        yield policy, mock_instance


class TestAnthropicPolicyGetNextAction:

    async def test_returns_parsed_director_response(self, mock_policy):
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_api_response(_director_json(tactic="intro n"))
        )
        ledger, _ = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert isinstance(resp, DirectorResponse)
        assert resp.tactic == "intro n"
        assert resp.reasoning == "because"

    async def test_thinking_block_before_text_is_skipped_not_crashed_on(self, mock_policy):
        """Regression test: the newest Claude generation thinks by default
        regardless of the `thinking` param, so content[0] can be a
        ThinkingBlock with no .text attribute at all — content[0].text
        raises AttributeError. The real answer must still be found in a
        later text block instead of crashing."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_thinking_then_text_response(
                thinking="Let me work through this proof step by step...",
                text=_director_json(tactic="omega"),
            )
        )
        ledger, _ = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])
        assert resp.tactic == "omega"

    async def test_premises_passed_to_api(self, mock_policy):
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_api_response(_director_json())
        )
        ledger, _ = _ledger_with_one_state()

        await policy.get_next_action(
            "theorem foo := by", ledger, ["Nat.add_zero", "Nat.add_comm"]
        )

        _, kwargs = client.messages.stream.call_args
        user_content = kwargs["messages"][0]["content"]
        assert "Nat.add_zero" in user_content
        assert "Nat.add_comm" in user_content

    async def test_system_prompt_is_marked_cacheable(self, mock_policy):
        """The system prompt is identical on every director call — every
        turn, every trial, every problem — so it should be sent as a
        cache_control-tagged block, not a plain string, letting every call
        after the first pay the cheaper cache-read rate for it instead of
        full input price."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_api_response(_director_json())
        )
        ledger, _ = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [])

        _, kwargs = client.messages.stream.call_args
        system = kwargs["system"]
        assert isinstance(system, list)
        assert system[0]["cache_control"] == {"type": "ephemeral"}
        assert system[0]["text"] == DIRECTOR_SYSTEM_PROMPT

    async def test_thinking_is_explicitly_disabled_by_default(self, mock_policy):
        """Omitting the `thinking` param is NOT the same as disabling it on
        the newest Claude models — they think by default, and a modest
        max_tokens can then be consumed entirely by hidden reasoning,
        returning empty text (confirmed live). So it must be passed
        explicitly."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_api_response(_director_json())
        )
        ledger, _ = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [])

        _, kwargs = client.messages.stream.call_args
        assert kwargs["thinking"] == {"type": "disabled"}

    async def test_thinking_enabled_uses_adaptive(self, mock_policy):
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_api_response(_director_json())
        )
        await policy._call_api("prompt", enable_thinking=True)

        _, kwargs = client.messages.stream.call_args
        assert kwargs["thinking"] == {"type": "adaptive"}

    async def test_api_failure_falls_back_instead_of_raising(self, mock_policy):
        """A single bad turn must not end the search."""
        policy, client = mock_policy
        client.messages.stream.side_effect = Exception("network error")
        ledger, state_id = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert resp.chosen_state_id == state_id
        assert resp.tactic == "simp"
        assert resp.abandoned_state_ids == []

    async def test_empty_response_falls_back_to_simp(self, mock_policy):
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response(""))
        ledger, state_id = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert resp.chosen_state_id == state_id
        assert resp.tactic == "simp"

    async def test_close_delegates_to_client(self, mock_policy):
        policy, client = mock_policy
        await policy.close()
        client.close.assert_called_once()

    async def test_satisfies_policy_model_protocol(self, mock_policy):
        """isinstance check via @runtime_checkable should pass."""
        from core.policy import PolicyModel
        policy, _ = mock_policy
        assert isinstance(policy, PolicyModel)


# ---------------------------------------------------------------------------
# Integration test (skipped without API key)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY"),
    reason="ANTHROPIC_API_KEY not set",
)
class TestAnthropicPolicyIntegration:

    async def test_real_api_call_returns_a_usable_decision(self):
        """Makes a real API call and verifies the response is parseable."""
        # claude haiku is one of the cheaper models - we dont need a powerful model for these
        # integration tests.
        policy = AnthropicPolicy(model="claude-haiku-4-5-20251001")
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n + 0 = n"], [[("n", "ℕ")]]))

        resp = await policy.get_next_action(
            "theorem foo (n : ℕ) : n + 0 = n := by", ledger, ["Nat.add_zero"]
        )

        assert isinstance(resp, DirectorResponse)
        assert isinstance(resp.tactic, str) and resp.tactic
        await policy.close()
