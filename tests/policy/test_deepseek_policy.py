"""
Tests for policy/deepseek.py

Unit tests mock the AsyncOpenAI client — no real API calls, no cost.
The integration test at the bottom is skipped unless DEEPSEEK_API_KEY is set.

Run all (unit only):
    pytest tests/policy/test_deepseek_policy.py -v

Run including integration:
    DEEPSEEK_API_KEY=sk-... pytest tests/policy/test_deepseek_policy.py -v
"""

from __future__ import annotations

import os
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from core.policy import PolicyModel, TacticCandidate
from core.proof_state import make_proof_state
from policy.deepseek import DeepSeekPolicy


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_api_response(text: str) -> MagicMock:
    """Build a fake OpenAI-compatible chat completion response."""
    message = MagicMock()
    message.content = text
    choice = MagicMock()
    choice.message = message
    response = MagicMock()
    response.choices = [choice]
    return response


@pytest.fixture
def mock_policy():
    """DeepSeekPolicy with the AsyncOpenAI client replaced by a mock."""
    with patch("policy.deepseek.AsyncOpenAI") as MockClient:
        mock_instance = MagicMock()
        mock_instance.chat.completions.create = AsyncMock()
        mock_instance.close = AsyncMock()
        MockClient.return_value = mock_instance

        policy = DeepSeekPolicy(api_key="test-key")
        yield policy, mock_instance


# ---------------------------------------------------------------------------
# Unit tests (mocked client)
# ---------------------------------------------------------------------------

class TestDeepSeekPolicyGetTactics:

    async def test_returns_tactic_candidates(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response("simp\nring\nomega")

        state = make_proof_state(["n + 0 = n"])
        results = await policy.get_tactics(state, [], k=3)

        assert len(results) == 3
        assert all(isinstance(r, TacticCandidate) for r in results)
        assert results[0].tactic == "simp"
        assert results[1].tactic == "ring"
        assert results[2].tactic == "omega"

    async def test_log_probs_are_descending(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response("simp\nring\nomega")

        state = make_proof_state(["n + 0 = n"])
        results = await policy.get_tactics(state, [], k=3)

        log_probs = [r.log_prob for r in results]
        assert log_probs == sorted(log_probs, reverse=True)

    async def test_respects_k_limit(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response(
            "simp\nring\nomega\nlinarith\ndecide\nrfl\nnorm_num\ntauto"
        )
        state = make_proof_state(["P"])
        results = await policy.get_tactics(state, [], k=4)
        assert len(results) == 4

    async def test_premises_in_api_call(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response("simp")

        state = make_proof_state(["n + 0 = n"])
        await policy.get_tactics(state, ["Nat.add_zero", "Nat.add_comm"], k=1)

        _, kwargs = client.chat.completions.create.call_args
        user_msg = next(m["content"] for m in kwargs["messages"] if m["role"] == "user")
        assert "Nat.add_zero" in user_msg
        assert "Nat.add_comm" in user_msg

    async def test_system_prompt_sent(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response("simp")

        state = make_proof_state(["n + 0 = n"])
        await policy.get_tactics(state, [], k=1)

        _, kwargs = client.chat.completions.create.call_args
        system_msg = next(m["content"] for m in kwargs["messages"] if m["role"] == "system")
        assert "Lean 4" in system_msg

    async def test_api_failure_returns_simp_fallback(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.side_effect = Exception("network error")

        state = make_proof_state(["n + 0 = n"])
        results = await policy.get_tactics(state, [], k=4)

        assert len(results) == 1
        assert results[0].tactic == "simp"

    async def test_empty_response_falls_back_to_simp(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response("")

        state = make_proof_state(["P"])
        results = await policy.get_tactics(state, [], k=4)

        assert results[0].tactic == "simp"

    async def test_numbered_response_parsed_correctly(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response(
            "1. intro n\n2. simp\n3. omega"
        )
        state = make_proof_state(["∀ n : ℕ, n + 0 = n"])
        results = await policy.get_tactics(state, [], k=3)

        assert results[0].tactic == "intro n"
        assert results[1].tactic == "simp"
        assert results[2].tactic == "omega"

    async def test_close_delegates_to_client(self, mock_policy):
        policy, client = mock_policy
        await policy.close()
        client.close.assert_called_once()

    async def test_satisfies_policy_model_protocol(self, mock_policy):
        policy, _ = mock_policy
        assert isinstance(policy, PolicyModel)

    async def test_default_model_is_deepseek_v4_flash(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response("simp")

        state = make_proof_state(["P"])
        await policy.get_tactics(state, [], k=1)

        _, kwargs = client.chat.completions.create.call_args
        assert kwargs["model"] == "deepseek-v4-flash"

    async def test_custom_model_passed_through(self):
        with patch("policy.deepseek.AsyncOpenAI") as MockClient:
            mock_instance = MagicMock()
            mock_instance.chat.completions.create = AsyncMock(
                return_value=_make_api_response("simp")
            )
            mock_instance.close = AsyncMock()
            MockClient.return_value = mock_instance

            policy = DeepSeekPolicy(model="deepseek-v4-pro", api_key="test-key")
            state = make_proof_state(["P"])
            await policy.get_tactics(state, [], k=1)

            _, kwargs = mock_instance.chat.completions.create.call_args
            assert kwargs["model"] == "deepseek-v4-pro"

    def test_base_url_points_to_deepseek(self):
        with patch("policy.deepseek.AsyncOpenAI") as MockClient:
            MockClient.return_value = MagicMock()
            DeepSeekPolicy(api_key="test-key")
            _, kwargs = MockClient.call_args
            assert kwargs["base_url"] == "https://api.deepseek.com"


# ---------------------------------------------------------------------------
# Integration test (skipped without API key)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not os.environ.get("DEEPSEEK_API_KEY"),
    reason="DEEPSEEK_API_KEY not set",
)
class TestDeepSeekPolicyIntegration:

    async def test_real_api_call_returns_tactics(self):
        """Makes a real DeepSeek API call and verifies the response is parseable."""
        policy = DeepSeekPolicy(model="deepseek-v4-flash")
        state = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])

        results = await policy.get_tactics(state, premises=["Nat.add_zero"], k=4)

        assert len(results) >= 1
        assert all(isinstance(r, TacticCandidate) for r in results)
        assert all(isinstance(r.tactic, str) and r.tactic for r in results)
        await policy.close()
