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

import json
import os
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from core.ledger import Ledger
from core.policy import PolicyModel
from core.proof_state import make_proof_state
from policy.base import DIRECTOR_SYSTEM_PROMPT, DirectorResponse
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


def _director_json(tactic: str = "simp", chosen: str = "x") -> str:
    return json.dumps({"chosen_state": chosen, "tactic": tactic, "reasoning": "because"})


def _ledger_with_one_state() -> tuple[Ledger, str]:
    ledger = Ledger()
    state_id = ledger.add_state(make_proof_state(["n + 0 = n"]))
    return ledger, state_id


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

class TestDeepSeekPolicyGetNextAction:

    async def test_returns_parsed_director_response(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response(
            _director_json(tactic="intro n")
        )
        ledger, _ = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert isinstance(resp, DirectorResponse)
        assert resp.tactic == "intro n"

    async def test_premises_in_api_call(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response(_director_json())
        ledger, _ = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, ["Nat.add_zero"])

        _, kwargs = client.chat.completions.create.call_args
        assert "Nat.add_zero" in kwargs["messages"][1]["content"]

    async def test_director_system_prompt_sent(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response(_director_json())
        ledger, _ = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [])

        _, kwargs = client.chat.completions.create.call_args
        assert kwargs["messages"][0]["content"] == DIRECTOR_SYSTEM_PROMPT

    async def test_api_failure_falls_back_instead_of_raising(self, mock_policy):
        """A single bad turn must not end the search."""
        policy, client = mock_policy
        client.chat.completions.create.side_effect = Exception("network error")
        ledger, state_id = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert resp.chosen_state_id == state_id
        assert resp.tactic == "simp"

    async def test_empty_response_falls_back_to_simp(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response("")
        ledger, state_id = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [])

        assert resp.chosen_state_id == state_id
        assert resp.tactic == "simp"

    async def test_close_delegates_to_client(self, mock_policy):
        policy, client = mock_policy
        await policy.close()
        client.close.assert_called_once()

    async def test_satisfies_policy_model_protocol(self, mock_policy):
        policy, _ = mock_policy
        assert isinstance(policy, PolicyModel)

    async def test_default_model_is_deepseek_v4_flash(self, mock_policy):
        policy, client = mock_policy
        client.chat.completions.create.return_value = _make_api_response(_director_json())
        ledger, _ = _ledger_with_one_state()
        await policy.get_next_action("theorem foo := by", ledger, [])

        _, kwargs = client.chat.completions.create.call_args
        assert kwargs["model"] == "deepseek-v4-flash"

    async def test_custom_model_passed_through(self):
        with patch("policy.deepseek.AsyncOpenAI") as MockClient:
            mock_instance = MagicMock()
            mock_instance.chat.completions.create = AsyncMock(
                return_value=_make_api_response(_director_json())
            )
            mock_instance.close = AsyncMock()
            MockClient.return_value = mock_instance

            policy = DeepSeekPolicy(model="deepseek-v4-pro", api_key="test-key")
            ledger, _ = _ledger_with_one_state()
            await policy.get_next_action("theorem foo := by", ledger, [])

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

    async def test_real_api_call_returns_a_usable_decision(self):
        """Makes a real DeepSeek API call and verifies the response is parseable."""
        policy = DeepSeekPolicy(model="deepseek-v4-flash")
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n + 0 = n"], [[("n", "ℕ")]]))

        resp = await policy.get_next_action(
            "theorem foo (n : ℕ) : n + 0 = n := by", ledger, ["Nat.add_zero"]
        )

        assert isinstance(resp, DirectorResponse)
        assert isinstance(resp.tactic, str) and resp.tactic
        await policy.close()
