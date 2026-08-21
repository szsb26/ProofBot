"""
Unit tests for core/trace.py — TracingPolicy, the wrapper that captures
every director call's exact prompt and raw response verbatim.
"""

from __future__ import annotations

import json

from core.ledger import Ledger
from core.proof_state import make_proof_state
from core.trace import TracingPolicy


class FakeBaseLLMPolicy:
    """
    Minimal BaseLLMPolicy-compatible test double: has the internals
    TracingPolicy reaches into (_call_api, _director_max_tokens,
    _director_thinking) without needing a real DeepSeekPolicy/AnthropicPolicy.
    """

    def __init__(self, responses: list[str]):
        self._responses = responses
        self._call_count = 0
        self._director_max_tokens = 1024
        self._director_thinking = False
        self.closed = False

    async def _call_api(self, user_prompt, system_prompt="", max_tokens=None, enable_thinking=False):
        resp = self._responses[min(self._call_count, len(self._responses) - 1)]
        self._call_count += 1
        return resp

    async def close(self) -> None:
        self.closed = True


def _ledger_with_one_state() -> tuple[Ledger, str]:
    ledger = Ledger()
    state_id = ledger.add_state(make_proof_state(["n = n"]))
    return ledger, state_id


class TestTracingPolicy:

    async def test_returns_parsed_director_response_unchanged(self):
        raw = json.dumps({"chosen_state": "x", "tactics": ["simp"], "reasoning": "close it"})
        inner = FakeBaseLLMPolicy([raw])
        policy = TracingPolicy(inner)
        ledger, state_id = _ledger_with_one_state()

        resp = await policy.get_next_action("theorem foo := by", ledger, [], k=4)

        assert [c.tactic for c in resp.tactics] == ["simp"]
        assert resp.reasoning == "close it"

    async def test_render_includes_prompt_and_raw_response(self):
        raw = json.dumps({"chosen_state": "x", "tactics": ["omega"]})
        inner = FakeBaseLLMPolicy([raw])
        policy = TracingPolicy(inner)
        ledger, state_id = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [], k=4)
        text = policy.render()

        assert "PROMPT SENT TO LLM" in text
        assert "theorem foo := by" in text
        assert "RAW RESPONSE FROM LLM" in text
        assert raw in text
        assert "PARSED DECISION" in text
        assert "omega" in text

    async def test_turn_counter_increments_across_calls(self):
        raw = json.dumps({"chosen_state": "x", "tactics": ["simp"]})
        inner = FakeBaseLLMPolicy([raw, raw])
        policy = TracingPolicy(inner)
        ledger, state_id = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [], k=4)
        await policy.get_next_action("theorem foo := by", ledger, [], k=4)

        assert policy.turn == 2
        assert "TURN 1" in policy.render()
        assert "TURN 2" in policy.render()

    async def test_close_delegates_to_inner_policy(self):
        inner = FakeBaseLLMPolicy([json.dumps({"chosen_state": "x", "tactics": ["simp"]})])
        policy = TracingPolicy(inner)
        await policy.close()
        assert inner.closed

    async def test_verbose_mode_prints_live(self, capsys):
        raw = json.dumps({"chosen_state": "x", "tactics": ["simp"]})
        inner = FakeBaseLLMPolicy([raw])
        policy = TracingPolicy(inner, verbose=True)
        ledger, state_id = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [], k=4)

        captured = capsys.readouterr()
        assert "PROMPT SENT TO LLM" in captured.out

    async def test_non_verbose_mode_does_not_print(self, capsys):
        raw = json.dumps({"chosen_state": "x", "tactics": ["simp"]})
        inner = FakeBaseLLMPolicy([raw])
        policy = TracingPolicy(inner, verbose=False)
        ledger, state_id = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [], k=4)

        captured = capsys.readouterr()
        assert captured.out == ""

    def test_render_empty_before_any_calls(self):
        inner = FakeBaseLLMPolicy([])
        policy = TracingPolicy(inner)
        assert policy.render() == ""


class TestTracingPolicyRecordsSystemPrompt:
    """
    Regression coverage for a real diagnostic failure: a trace recorded only
    the user prompt, so when a DIRECTOR_SYSTEM_PROMPT change appeared to have
    no effect there was no way to tell from the trace whether the model
    ignored the new instruction or the edit never reached it. A trace must
    state which instructions were in force for that run.
    """

    async def test_system_prompt_appears_in_the_trace(self):
        from policy.base import DIRECTOR_SYSTEM_PROMPT

        raw = json.dumps({"chosen_state": "x", "tactics": ["simp"]})
        policy = TracingPolicy(FakeBaseLLMPolicy([raw]))
        ledger, _ = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [], k=4)

        assert DIRECTOR_SYSTEM_PROMPT in policy.render()

    async def test_system_prompt_emitted_once_not_per_turn(self):
        """It is identical every turn; emitting it 150 times would bloat the
        trace for no information gain."""
        raw = json.dumps({"chosen_state": "x", "tactics": ["simp"]})
        policy = TracingPolicy(FakeBaseLLMPolicy([raw, raw, raw]))
        ledger, _ = _ledger_with_one_state()

        for _ in range(3):
            await policy.get_next_action("theorem foo := by", ledger, [], k=4)

        assert policy.render().count("SYSTEM PROMPT (identical for every turn below)") == 1
        assert policy.turn == 3

    async def test_system_prompt_precedes_the_first_turn(self):
        raw = json.dumps({"chosen_state": "x", "tactics": ["simp"]})
        policy = TracingPolicy(FakeBaseLLMPolicy([raw]))
        ledger, _ = _ledger_with_one_state()

        await policy.get_next_action("theorem foo := by", ledger, [], k=4)

        text = policy.render()
        assert text.index("SYSTEM PROMPT") < text.index("TURN 1 — PROMPT SENT TO LLM")
