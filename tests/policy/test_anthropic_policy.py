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

import os
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from core.policy import TacticCandidate
from core.proof_state import make_proof_state, ProofState
from policy.anthropic import AnthropicPolicy
from policy.base import parse_tactics as _parse_tactics, build_user_prompt as _build_user_prompt


# ---------------------------------------------------------------------------
# _parse_tactics (pure function, no mocking needed)
# ---------------------------------------------------------------------------

class TestParseTactics:

    def test_plain_lines_returned_as_is(self):
        """Clean tactic lines should come back unchanged."""
        text = "simp\nring\nomega"
        assert _parse_tactics(text, 3) == ["simp", "ring", "omega"]

    def test_numbered_prefix_stripped(self):
        """'1. tactic' and '2) tactic' prefixes should be removed."""
        text = "1. simp\n2) ring\n3. omega"
        result = _parse_tactics(text, 3)
        assert result == ["simp", "ring", "omega"]

    def test_bullet_prefix_stripped(self):
        """'- tactic' bullet prefix should be removed."""
        text = "- simp\n- ring"
        assert _parse_tactics(text, 2) == ["simp", "ring"]

    def test_backtick_stripped(self):
        """`simp` with surrounding backticks should be cleaned."""
        text = "`simp`\n`ring`"
        assert _parse_tactics(text, 2) == ["simp", "ring"]

    def test_blank_lines_skipped(self):
        text = "simp\n\n\nring"
        assert _parse_tactics(text, 2) == ["simp", "ring"]

    def test_duplicates_removed_preserving_order(self):
        """If Claude repeats a tactic, keep only the first occurrence."""
        text = "simp\nring\nsimp\nomega"
        result = _parse_tactics(text, 4)
        assert result == ["simp", "ring", "omega"]

    def test_truncated_to_k(self):
        text = "simp\nring\nomega\nlinarith\ndecide"
        result = _parse_tactics(text, 3)
        assert len(result) == 3
        assert result == ["simp", "ring", "omega"]

    def test_empty_text_falls_back_to_simp(self):
        assert _parse_tactics("", 4) == ["simp"]

    def test_whitespace_only_falls_back_to_simp(self):
        assert _parse_tactics("   \n   ", 4) == ["simp"]

    def test_intro_with_variable_name(self):
        text = "intro n\nsimp"
        assert _parse_tactics(text, 2) == ["intro n", "simp"]


# ---------------------------------------------------------------------------
# _build_user_prompt (pure function)
# ---------------------------------------------------------------------------

class TestBuildUserPrompt:

    def test_contains_serialized_state(self):
        state = make_proof_state(["n + 0 = n"])
        prompt = _build_user_prompt(state, [], k=4)
        assert "n + 0 = n" in prompt

    def test_contains_premises_when_provided(self):
        state = make_proof_state(["n + 0 = n"])
        prompt = _build_user_prompt(state, ["Nat.add_zero", "Nat.add_comm"], k=4)
        assert "Nat.add_zero" in prompt
        assert "Nat.add_comm" in prompt

    def test_no_premises_section_when_empty(self):
        state = make_proof_state(["n + 0 = n"])
        prompt = _build_user_prompt(state, [], k=4)
        assert "Relevant Lemmas" not in prompt

    def test_k_mentioned_in_prompt(self):
        state = make_proof_state(["P"])
        prompt = _build_user_prompt(state, [], k=6)
        assert "6" in prompt


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


class TestAnthropicPolicyGetTactics:

    async def test_returns_tactic_candidates(self, mock_policy):
        """Normal response should be parsed into TacticCandidate objects."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response("simp\nring\nomega"))

        state = make_proof_state(["n + 0 = n"])
        results = await policy.get_tactics(state, [], k=3)

        assert len(results) == 3
        assert all(isinstance(r, TacticCandidate) for r in results)
        assert results[0].tactic == "simp"
        assert results[1].tactic == "ring"
        assert results[2].tactic == "omega"

    async def test_thinking_block_before_text_is_skipped_not_crashed_on(self, mock_policy):
        """Regression test: the newest Claude generation thinks by default
        regardless of the `thinking` param, so content[0] can be a
        ThinkingBlock with no .text attribute at all — content[0].text
        raises AttributeError. The real answer must still be found in a
        later text block instead of crashing."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_thinking_then_text_response(
            thinking="Let me work through this proof step by step...",
            text="simp\nring\nomega",
        ))

        state = make_proof_state(["n + 0 = n"])
        results = await policy.get_tactics(state, [], k=3)

        assert len(results) == 3
        assert results[0].tactic == "simp"

    async def test_log_probs_are_descending(self, mock_policy):
        """First candidate should have the highest log_prob (closest to 0)."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response("simp\nring\nomega"))

        state = make_proof_state(["n + 0 = n"])
        results = await policy.get_tactics(state, [], k=3)

        log_probs = [r.log_prob for r in results]
        assert log_probs == sorted(log_probs, reverse=True)

    async def test_respects_k_limit(self, mock_policy):
        """Should return at most k candidates even if Claude outputs more."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response(
            "simp\nring\nomega\nlinarith\ndecide\nrfl\nnorm_num\ntauto"
        ))
        state = make_proof_state(["P"])
        results = await policy.get_tactics(state, [], k=4)
        assert len(results) == 4

    async def test_premises_passed_to_api(self, mock_policy):
        """Premises should appear in the message sent to the API."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response("simp"))

        state = make_proof_state(["n + 0 = n"])
        await policy.get_tactics(state, ["Nat.add_zero", "Nat.add_comm"], k=1)

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
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response("simp"))

        state = make_proof_state(["n + 0 = n"])
        await policy.get_tactics(state, [], k=1)

        _, kwargs = client.messages.stream.call_args
        system = kwargs["system"]
        assert isinstance(system, list)
        assert system[0]["cache_control"] == {"type": "ephemeral"}
        assert system[0]["text"]  # the actual prompt text is still present

    async def test_api_failure_returns_simp_fallback(self, mock_policy):
        """If the API raises, the policy should return [simp] rather than crashing."""
        policy, client = mock_policy
        client.messages.stream.side_effect = Exception("network error")

        state = make_proof_state(["n + 0 = n"])
        results = await policy.get_tactics(state, [], k=4)

        assert len(results) == 1
        assert results[0].tactic == "simp"

    async def test_empty_response_falls_back_to_simp(self, mock_policy):
        """An empty API response should not crash — fall back to simp."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response(""))

        state = make_proof_state(["P"])
        results = await policy.get_tactics(state, [], k=4)

        assert results[0].tactic == "simp"

    async def test_numbered_response_parsed_correctly(self, mock_policy):
        """Claude sometimes numbers its output — numbering should be stripped."""
        policy, client = mock_policy
        client.messages.stream.return_value = _FakeStreamManager(_make_api_response(
            "1. intro n\n2. simp\n3. omega"
        ))
        state = make_proof_state(["∀ n : ℕ, n + 0 = n"])
        results = await policy.get_tactics(state, [], k=3)

        assert results[0].tactic == "intro n"
        assert results[1].tactic == "simp"
        assert results[2].tactic == "omega"

    async def test_close_delegates_to_client(self, mock_policy):
        """close() should call the underlying client's close method."""
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

    async def test_real_api_call_returns_tactics(self):
        """Makes a real API call and verifies the response is parseable."""

        # claude haiku is one of the cheaper models - we dont need a powerful model for these
        # integration tests.
        policy = AnthropicPolicy(model="claude-haiku-4-5-20251001")
        state = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])

        results = await policy.get_tactics(state, premises=["Nat.add_zero"], k=4)

        assert len(results) >= 1
        assert all(isinstance(r, TacticCandidate) for r in results)
        assert all(isinstance(r.tactic, str) and r.tactic for r in results)
        await policy.close()
