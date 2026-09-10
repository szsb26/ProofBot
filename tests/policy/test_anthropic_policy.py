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


def _make_budget_exhausted_response(
    output_tokens: int = 16000, thinking_tokens: int = 15980,
    stop_reason: str = "max_tokens",
) -> MagicMock:
    """A well-formed response that contains no answer.

    Thinking tokens and output tokens share one max_tokens budget, so a model
    that thinks deeply enough hits the ceiling before writing any text: a
    `thinking` block, no `text` block, stop_reason="max_tokens". Documented
    live for the one-shot prover on imo1968_tetrahedron (search/one_shot.py).
    Real ints, not MagicMocks, because the diagnosis message quotes them.
    """
    thinking_block = MagicMock()
    thinking_block.type = "thinking"
    response = MagicMock()
    response.content = [thinking_block]
    response.stop_reason = stop_reason
    response.usage.output_tokens = output_tokens
    response.usage.output_tokens_details.thinking_tokens = thinking_tokens
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

    async def test_response_with_no_text_is_reported_not_disguised_as_simp(
        self, mock_policy
    ):
        """A response carrying no answer must not arrive as a deliberate simp.

        Thinking tokens and output tokens share one max_tokens budget, so a
        model that thinks deeply enough stops at the ceiling before writing
        anything: a thinking block, no text block, stop_reason="max_tokens"
        (documented live for the one-shot prover on imo1968_tetrahedron).
        _call_api used to return "" for this, and parse_director_response
        turned "" into its blind "simp" default — indistinguishable in the
        ledger and the trace from the model proposing simp on purpose, and
        raising nothing, so it never counted toward the consecutive-failure
        guard either. A run could spend turns on invisible simps and finish
        looking like an ordinary failure.
        """
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_budget_exhausted_response()
        )
        ledger, state_id = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert resp.tactic == "", "must not invent a tactic the model never sent"
        assert resp.no_tactic_reason, "the turn must carry its own explanation"
        # the diagnosis has to name the cause, not just say "empty"
        assert "max_tokens" in resp.no_tactic_reason
        assert "16000" in resp.no_tactic_reason
        assert "15980" in resp.no_tactic_reason
        assert resp.chosen_state_id == state_id

    async def test_text_block_of_only_whitespace_counts_as_no_text(
        self, mock_policy
    ):
        """The same condition can present as a present-but-empty text block."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_api_response("   \n  ")
        )
        ledger, _ = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])
        assert resp.tactic == ""
        assert resp.no_tactic_reason

    async def test_a_no_text_turn_does_not_trip_the_failure_guard(
        self, mock_policy
    ):
        """It is not a transport failure — the request succeeded and the model
        ran. The consecutive-failure guard exists for conditions that fail
        every call (spent credits, bad key); this one is budget-dependent and
        can resolve next turn against a different state, so aborting the run
        after three would be wrong."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(
            _make_budget_exhausted_response()
        )
        ledger, _ = _ledger_with_one_state()

        for _ in range(5):
            resp = await policy.get_next_action("theorem foo := by", ledger, [])
            assert resp.no_tactic_reason
        assert policy._consecutive_api_failures == 0

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


class TestStopReasonIsLoggedEveryCall:
    """stop_reason is recorded on every call, not only the failing ones.

    It is a typed enum from the API (end_turn / max_tokens / stop_sequence /
    tool_use / pause_turn / refusal), not prose we classify, and NOTHING
    branches on it — the no-text raise triggers on the absence of text, which
    is ground truth. It is logged so its distribution can be checked against
    reality instead of inferred from a small sample. This repo has been burned
    once by heuristics over provider text: an error categoriser audited across
    2847 real Lean errors had two of nine branches that never fired and a
    catch-all holding a third of everything, and a wrong label was worse than
    none. Pass the value through; classify nothing.
    """

    async def test_ordinary_call_logs_stop_reason_at_debug(self, mock_policy, caplog):
        import logging
        policy, client = mock_policy
        msg = _make_api_response(_director_json())
        msg.stop_reason = "end_turn"
        msg.usage.output_tokens = 812
        msg.usage.output_tokens_details.thinking_tokens = None
        client.messages.stream.return_value = _FakeStreamManager(msg)
        ledger, _ = _ledger_with_one_state()

        with caplog.at_level(logging.DEBUG, logger="policy.anthropic"):
            await policy.get_next_action("theorem foo := by", ledger, [])

        ours = [r for r in caplog.records if r.name == "policy.anthropic"]
        assert any("stop_reason='end_turn'" in r.getMessage()
                   for r in ours if r.levelno == logging.DEBUG)
        # a normal turn must not raise a warning, or warnings become noise
        assert not [r for r in ours if r.levelno >= logging.WARNING]

    async def test_unexpected_stop_reason_is_warned_even_with_text(
        self, mock_policy, caplog
    ):
        """A truncated-but-parseable response is the dangerous case: the turn
        looks fine, so nothing else flags it."""
        import logging
        policy, client = mock_policy
        msg = _make_api_response(_director_json())
        msg.stop_reason = "max_tokens"
        msg.usage.output_tokens = 16000
        msg.usage.output_tokens_details.thinking_tokens = 15000
        client.messages.stream.return_value = _FakeStreamManager(msg)
        ledger, _ = _ledger_with_one_state()

        with caplog.at_level(logging.DEBUG, logger="policy.anthropic"):
            resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert resp.tactic == "simp"  # text was present and parsed
        warned = [r for r in caplog.records
                  if r.name == "policy.anthropic" and r.levelno >= logging.WARNING]
        assert warned, "a non-end_turn stop must not pass unnoticed"
        assert "max_tokens" in warned[0].getMessage()
