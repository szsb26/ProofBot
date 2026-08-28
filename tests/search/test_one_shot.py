"""
Unit tests for search/one_shot.py — the north-star baseline: one Lean proof
generated in a single call, plus a bounded number of error-feedback fixes,
no search tree at all.
"""

from __future__ import annotations

import asyncio

from core.proof_state import ProofState, make_proof_state
from search.one_shot import OneShotProve, _extract_proof_code


# ---------------------------------------------------------------------------
# _extract_proof_code
# ---------------------------------------------------------------------------

class TestExtractProofCode:

    def test_plain_code_passed_through(self):
        assert _extract_proof_code("intro n\nsimp") == "intro n\nsimp"

    def test_strips_surrounding_whitespace(self):
        assert _extract_proof_code("  \n simp \n ") == "simp"

    def test_strips_markdown_fence_with_lean_tag(self):
        text = "```lean\nintro n\nsimp\n```"
        assert _extract_proof_code(text) == "intro n\nsimp"

    def test_strips_plain_markdown_fence(self):
        text = "```\nsimp\n```"
        assert _extract_proof_code(text) == "simp"

    def test_strips_leading_theorem_header_if_model_includes_it(self):
        text = "theorem foo : n + 0 = n := by\n  simp"
        assert _extract_proof_code(text) == "simp"

    def test_strips_fence_and_header_together(self):
        text = "```lean\ntheorem foo : n + 0 = n := by\n  simp\n```"
        assert _extract_proof_code(text) == "simp"


# ---------------------------------------------------------------------------
# Test doubles
# ---------------------------------------------------------------------------

class ErroringExecutor:
    capacity = 1

    async def reset(self, theorem: str, preamble: str = "") -> ProofState:
        return ProofState(goals=(), error="Lean parse error: unexpected token")

    async def step(self, state, tactic):
        raise AssertionError("step() should never be called after a parse error")

    async def close(self) -> None:
        pass


class AlreadyClosedExecutor:
    capacity = 1

    async def reset(self, theorem: str, preamble: str = "") -> ProofState:
        return ProofState(goals=())

    async def step(self, state, tactic):
        raise AssertionError("step() should never be called when already closed")

    async def close(self) -> None:
        pass


class ScriptedExecutor:
    """Fake executor whose step() outcome for a given tactic string is
    pre-scripted by exact match, so fix-retry sequences can be tested
    without depending on MockExecutor's single-atomic-tactic simulation."""

    capacity = 1

    def __init__(self, outcomes: dict[str, str | None], initial_goal: str = "n + 0 = n"):
        # outcomes: tactic -> None (closes) or an error string (fails)
        self._outcomes = outcomes
        self._initial_goal = initial_goal
        self.received: list[str] = []

    async def reset(self, theorem: str, preamble: str = "") -> ProofState:
        return make_proof_state([self._initial_goal])

    async def step(self, state: ProofState, tactic: str):
        from core.executor import StepResult

        self.received.append(tactic)
        outcome = self._outcomes.get(tactic, "unknown tactic")
        if outcome is None:
            next_state = ProofState(goals=(), tactic_trace=state.tactic_trace + (tactic,))
        else:
            next_state = ProofState(
                goals=state.goals, error=outcome,
                depth=state.depth, tactic_trace=state.tactic_trace,
            )
        return StepResult(next_state=next_state, tactic=tactic)

    async def close(self) -> None:
        pass


class FakeOneShotPolicy:
    """Returns one scripted response per call, in order (repeats the last
    one if exhausted)."""

    def __init__(self, responses: list[str], raise_on_call: bool = False):
        self.responses = responses
        self.raise_on_call = raise_on_call
        self.call_count = 0
        self.prompts: list[str] = []
        self.system_prompts: list[str] = []

    async def _call_api(self, user_prompt, system_prompt="", max_tokens=None, enable_thinking=False):
        if self.raise_on_call:
            raise RuntimeError("simulated API failure")
        self.prompts.append(user_prompt)
        self.system_prompts.append(system_prompt)
        idx = min(self.call_count, len(self.responses) - 1)
        self.call_count += 1
        return self.responses[idx]

    async def close(self) -> None:
        pass


# ---------------------------------------------------------------------------
# OneShotProve.prove
# ---------------------------------------------------------------------------

class TestOneShotProve:

    def test_parse_error_short_circuits_before_any_llm_call(self):
        policy = FakeOneShotPolicy(["simp"])
        prover = OneShotProve(policy=policy, executor=ErroringExecutor())

        result = asyncio.run(prover.prove("not valid lean at all"))

        assert not result.result.success
        assert result.result.failure_reason == "parse_error"
        assert result.attempts_used == 0
        assert policy.call_count == 0

    def test_already_closed_theorem_short_circuits(self):
        policy = FakeOneShotPolicy(["simp"])
        prover = OneShotProve(policy=policy, executor=AlreadyClosedExecutor())

        result = asyncio.run(prover.prove("theorem foo : True := by trivial"))

        assert result.result.success
        assert result.attempts_used == 0
        assert policy.call_count == 0

    def test_succeeds_on_first_attempt(self):
        executor = ScriptedExecutor(outcomes={"simp": None})
        policy = FakeOneShotPolicy(["simp"])
        prover = OneShotProve(policy=policy, executor=executor)

        result = asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert result.result.success
        assert result.attempts_used == 1
        assert policy.call_count == 1

    def test_strips_markdown_fence_before_sending_to_lean(self):
        executor = ScriptedExecutor(outcomes={"simp": None})
        policy = FakeOneShotPolicy(["```lean\nsimp\n```"])
        prover = OneShotProve(policy=policy, executor=executor)

        asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert executor.received == ["simp"]

    def test_recovers_after_a_fix(self):
        executor = ScriptedExecutor(outcomes={"bad_tactic": "unknown identifier", "simp": None})
        policy = FakeOneShotPolicy(["bad_tactic", "simp"])
        prover = OneShotProve(policy=policy, executor=executor)

        result = asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert result.result.success
        assert result.attempts_used == 2
        assert policy.call_count == 2
        # The second prompt must include the first attempt and its error,
        # so the model can actually see what went wrong.
        assert "bad_tactic" in policy.prompts[1]
        assert "unknown identifier" in policy.prompts[1]

    def test_fails_after_exhausting_max_fixes(self):
        executor = ScriptedExecutor(outcomes={"bad_tactic": "still broken"})
        policy = FakeOneShotPolicy(["bad_tactic"])
        prover = OneShotProve(policy=policy, executor=executor, max_fixes=2)

        result = asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert not result.result.success
        assert result.result.failure_reason == "fixes_exhausted"
        # 1 initial attempt + 2 fixes = 3 total calls.
        assert result.attempts_used == 3
        assert policy.call_count == 3

    def test_sorry_is_never_accepted_as_a_proof(self):
        """Even if Lean would trivially accept it (ScriptedExecutor closes
        on any tactic mapped to None), the banned-tactic filter must reject
        sorry before it ever reaches the executor."""
        executor = ScriptedExecutor(outcomes={"sorry": None, "simp": None})
        policy = FakeOneShotPolicy(["sorry", "simp"])
        prover = OneShotProve(policy=policy, executor=executor)

        result = asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert result.result.success
        assert executor.received == ["simp"]
        assert "sorry" not in executor.received

    def test_api_failure_is_reported_not_raised(self):
        policy = FakeOneShotPolicy(["simp"], raise_on_call=True)
        prover = OneShotProve(policy=policy, executor=ScriptedExecutor(outcomes={"simp": None}))

        result = asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert not result.result.success
        assert result.result.failure_reason == "draft_failed"

    def test_every_attempt_is_used_before_giving_up(self):
        """Replaces an old test that counted error CATEGORIES; the
        categoriser was removed as unreliable, so assert on the observable
        behaviour instead — both attempts run, then it reports exhaustion."""
        executor = ScriptedExecutor(outcomes={"bad1": "type mismatch", "bad2": "unknown identifier"})
        policy = FakeOneShotPolicy(["bad1", "bad2"])
        prover = OneShotProve(policy=policy, executor=executor, max_fixes=1)

        result = asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert not result.result.success
        assert result.attempts_used == 2
        assert result.result.failure_reason == "fixes_exhausted"

    def test_uses_one_shot_system_prompt(self):
        from search.one_shot import ONE_SHOT_SYSTEM_PROMPT

        executor = ScriptedExecutor(outcomes={"simp": None})
        policy = FakeOneShotPolicy(["simp"])
        prover = OneShotProve(policy=policy, executor=executor)

        asyncio.run(prover.prove("theorem foo : n + 0 = n := by"))

        assert policy.system_prompts[0] == ONE_SHOT_SYSTEM_PROMPT
