"""
Unit and integration tests for lean/repl.py.

TestParseGoalString          — fast, no Lean needed; tests the goal string parser
TestSubprocessExecutor       — slow, real Lean; tests a single executor end-to-end
TestProveParallelIntegration — slow, real Lean; tests k (LedgerSearch,
                               SubprocessExecutor) pairs running concurrently
                               via prove_parallel on the same theorem
TestEndToEnd                 — slow, real Lean + real Anthropic API; tests the
                               full stack: AnthropicPolicy → LedgerSearch →
                               SubprocessExecutor → lake exe repl
TestDeepSeekEndToEnd         — slow, real Lean + real DeepSeek API; same stack
                               with DeepSeekPolicy instead of AnthropicPolicy
"""

import os
import pytest
import pytest_asyncio
import asyncio
from unittest.mock import AsyncMock
from lean.repl import (
    LeanWorker,
    SubprocessExecutor,
    _parse_goal_string,
    _split_top_level_tactics,
    _annotate_chain_error,
    LEAN_PROJECT_DIR,
)
from core.proof_state import ProofState, make_proof_state
from policy.mock import MockPolicy
from policy.anthropic import AnthropicPolicy
from policy.deepseek import DeepSeekPolicy
from search.ledger_search import LedgerSearch, _classify_tactic_error, prove_parallel


# ---------------------------------------------------------------------------
# Parser tests (fast, no Lean needed)
# ---------------------------------------------------------------------------

class TestParseGoalString:

    def test_simple_goal(self):
        # _parse_goal_string() returns a ProofState with a single Goal.
        # No hypotheses because the string has no " : " lines.
        result = _parse_goal_string("⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 0

    def test_goal_with_hypotheses(self):
        # Lines before ⊢ are parsed as hypotheses in "name : type" format.
        result = _parse_goal_string("n : Nat\nh : n > 0\n⊢ n + 0 = n")
        assert result.num_goals == 1
        assert result.goals[0].target == "n + 0 = n"
        assert len(result.goals[0].hypotheses) == 2
        assert result.goals[0].hypotheses[0].name == "n"
        assert result.goals[0].hypotheses[0].type_ == "Nat"
        assert result.goals[0].hypotheses[1].name == "h"
        assert result.goals[0].hypotheses[1].type_ == "n > 0"

    def test_empty_goal(self):
        # Empty string means the REPL returned no goals → proof is closed.
        result = _parse_goal_string("")
        assert result.is_closed

    def test_universal_goal(self):
        # ∀ in the target must not be mistaken for a hypothesis even though
        # the string contains " : ".
        result = _parse_goal_string("⊢ ∀ (n : Nat), n + 0 = n")
        assert result.goals[0].target == "∀ (n : Nat), n + 0 = n"


# ---------------------------------------------------------------------------
# _split_top_level_tactics / _annotate_chain_error (fast, pure functions)
# ---------------------------------------------------------------------------

class TestSplitTopLevelTactics:
    """
    The REPL's tactic-stepping endpoint only parses one atomic Lean 4
    `tactic` per call, not a `tacticSeq` — confirmed empirically: even
    "constructor; simp" is rejected outright with "expected end of input"
    right after "constructor". This splitter lets a chained candidate like
    the model naturally writes actually run, by sending each step as its
    own sequential REPL call.
    """

    def test_single_tactic_is_not_split(self):
        assert _split_top_level_tactics("simp") == ["simp"]

    def test_simple_top_level_chain_is_split(self):
        assert _split_top_level_tactics("intro n; simp") == ["intro n", "simp"]

    def test_three_step_top_level_chain_is_split(self):
        assert _split_top_level_tactics("by_contra h; push_neg at h; omega") == [
            "by_contra h", "push_neg at h", "omega",
        ]

    def test_semicolon_inside_brackets_is_not_split(self):
        assert _split_top_level_tactics("simp [foo, bar]; omega") == [
            "simp [foo, bar]", "omega",
        ]

    def test_nested_by_block_is_not_split_for_non_have_constructs(self):
        """'by' is a reserved keyword — an unbracketed top-level occurrence
        unambiguously opens a nested tacticSeq that (in a flat, unindented
        string) absorbs everything to its right. This still holds for any
        construct other than "have NAME : STMT := by ..." (see
        TestSplitHaveWithInlineProof for that specific, deliberate
        exception)."""
        tactic = "suffices h : P by intro y hy; simp at hy; exact hy"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_top_level_chain_before_nested_by_block_splits_correctly(self):
        tactic = "by_contra h; push_neg at h; suffices hsub : P by intro y; simp"
        assert _split_top_level_tactics(tactic) == [
            "by_contra h",
            "push_neg at h",
            "suffices hsub : P by intro y; simp",
        ]

    def test_whitespace_only_tactic_splits_to_empty_list(self):
        assert _split_top_level_tactics("   ") == []

    def test_parts_are_stripped_of_surrounding_whitespace(self):
        assert _split_top_level_tactics(" intro n ; simp ") == ["intro n", "simp"]


class TestSplitProtectsSemicolonCombinator:
    """
    Lean's '<;>' combinator ("run this tactic on every goal produced by the
    previous one") contains a ';' that must NOT be treated as a step
    separator — splitting there corrupts it into two dangling, syntactically
    invalid fragments. A real eval trace caught this live: every candidate
    using '<;>' failed with a syntax error at exactly that point (e.g.
    "cases h1 <;> cases h2" became "cases h1 <" then "> cases h2"), for
    every model tried, until one model diagnosed the harness bug itself and
    worked around it with 'all_goals' instead.
    """

    def test_simple_semicolon_combinator_is_not_split(self):
        tactic = "cases h1 <;> cases h2 <;> linarith"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_semicolon_combinator_after_rcases_pattern_is_not_split(self):
        tactic = "rcases h1 with h1 | h1 | h1 <;> linarith"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_semicolon_combinator_mixed_with_real_top_level_chain(self):
        tactic = "intro n; rcases h with h | h <;> nlinarith; simp"
        assert _split_top_level_tactics(tactic) == [
            "intro n",
            "rcases h with h | h <;> nlinarith",
            "simp",
        ]

    def test_semicolon_combinator_inside_brackets_still_not_split_either_way(self):
        tactic = "simp [foo <;> bar]; omega"
        assert _split_top_level_tactics(tactic) == ["simp [foo <;> bar]", "omega"]


class TestSplitHaveWithInlineProof:
    """
    "have NAME : STMT := by REST" is deliberately split into the bare
    "have NAME : STMT" plus REST (recursively split), instead of being kept
    atomic like every other "... := by ..." construct. Measured motivation:
    347 inlined sub-lemmas of exactly this shape were proposed against
    tournament_champion, and every sampled failure was a mechanical error
    *inside* REST — discarding a correct decomposition on every one, since
    the whole block previously passed or failed as a single unit.

    Confirmed against a real Lean REPL: sending the bare "have NAME : STMT"
    alone opens STMT as a new first goal and keeps the original goal
    available with NAME as a hypothesis, and Lean's default "operate on the
    first goal" behavior then routes REST's own steps onto that new
    sub-goal automatically — no separate goal-targeting logic needed.
    """

    def test_have_with_type_and_inline_proof_is_split(self):
        tactic = "have hsub : ∀ y, beats c y → beats p y := by intro y hy; simp; exact h"
        assert _split_top_level_tactics(tactic) == [
            "have hsub : ∀ y, beats c y → beats p y",
            "intro y hy",
            "simp",
            "exact h",
        ]

    def test_top_level_chain_before_a_have_still_splits_the_have_too(self):
        tactic = "by_contra h; push_neg at h; have hcardp : X := by exact hmax p"
        assert _split_top_level_tactics(tactic) == [
            "by_contra h",
            "push_neg at h",
            "have hcardp : X",
            "exact hmax p",
        ]

    def test_nested_have_inside_the_proof_is_also_unrolled(self):
        """A have-with-inline-proof inside REST is itself split the same
        way, recursively — fully flattening any depth of nesting."""
        tactic = "have h1 : P := by have h2 : Q := by tac_a; tac_b; tac_c"
        assert _split_top_level_tactics(tactic) == [
            "have h1 : P", "have h2 : Q", "tac_a", "tac_b", "tac_c",
        ]

    def test_anonymous_have_with_inline_proof_is_split(self):
        tactic = "have : p ≠ c := by intro h; exact hp h"
        assert _split_top_level_tactics(tactic) == [
            "have : p ≠ c", "intro h", "exact hp h",
        ]

    def test_have_with_no_type_annotation_is_not_split(self):
        """"have h := by simp" states no separate type — h's type is only
        inferred once the proof exists, so there is nothing valid to open
        as a bare sub-goal. Confirmed against a real Lean REPL: bare
        "have h" with no type at all is rejected outright."""
        tactic = "have h := by simp"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_have_used_as_a_plain_rewrite_target_is_unaffected(self):
        """"have" appearing without ":=" at all (e.g. referencing an
        existing hypothesis) must not trip the have-split path."""
        tactic = "have hp; simp"
        assert _split_top_level_tactics(tactic) == ["have hp", "simp"]

    def test_single_have_with_inline_proof_and_no_chain_before_it(self):
        tactic = "have h : True := by trivial"
        assert _split_top_level_tactics(tactic) == ["have h : True", "trivial"]


class TestAnnotateChainError:

    def test_single_step_returns_error_unchanged(self):
        assert _annotate_chain_error("Lean error:\nboom", ["simp"], 0) == "Lean error:\nboom"

    def test_multi_step_error_names_the_failing_step(self):
        result = _annotate_chain_error(
            "Lean error:\nunknown identifier `y`",
            ["by_contra h", "push_neg at h", "exact y"],
            2,
        )
        assert "step 3 of 3" in result
        assert '"exact y"' in result
        assert "unknown identifier `y`" in result

    def test_multi_step_error_mentions_preceding_successful_steps(self):
        result = _annotate_chain_error(
            "boom",
            ["intro n", "simp"],
            1,
        )
        assert 'after "intro n" succeeded' in result

    def test_first_step_failure_has_no_preceding_steps_mentioned(self):
        result = _annotate_chain_error("boom", ["intro n", "simp"], 0)
        assert "succeeded" not in result


# ---------------------------------------------------------------------------
# LeanWorker.step() closure detection (fast, no real Lean — mocks _send)
# ---------------------------------------------------------------------------

class TestLeanWorkerStepClosureDetection:
    """
    Regression coverage for a real bug: apply?/exact? can report empty
    goals while proofStatus says "Incomplete: contains sorry" — no full
    match was found, so Lean fell back to a placeholder. The old condition
    `if not goals_raw or proof_status == "Completed":` treated empty goals
    ALONE as a genuine close, silently accepting these as full proofs. Only
    proofStatus == "Completed" may signal a genuine close now.

    No real Lean process needed — _send() is mocked with the exact raw
    response shapes captured from a live REPL session.
    """

    def _make_worker_with_cached_state(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        state = make_proof_state(["some goal"])
        worker._proof_state_cache[state.stable_hash()] = 0
        return worker, state

    async def test_completed_status_is_a_genuine_close(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Completed", "proofState": 1, "goals": [],
        })
        result = await worker.step(state, "simp")
        assert result.success
        assert result.proof_closed

    async def test_empty_goals_without_completed_status_is_not_a_close(self):
        """The apply?/exact? bug, reproduced from a real captured response."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Incomplete: contains sorry",
            "proofState": 1,
            "goals": [],
            "messages": [
                {"severity": "info", "data": "Try this:\n  refine ?_"},
            ],
        })
        result = await worker.step(state, "apply?")
        assert not result.success
        assert not result.proof_closed
        assert "hidden sorry" in result.next_state.error.lower()

    async def test_empty_goals_without_completed_status_classified_as_hidden_sorry(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Incomplete: contains sorry",
            "proofState": 1,
            "goals": [],
        })
        result = await worker.step(state, "apply?")
        assert _classify_tactic_error(result.next_state.error) == "hidden_sorry"

    async def test_nonempty_goals_still_parsed_normally(self):
        """Sanity check: the fix must not disturb the ordinary
        'tactic succeeded, goals remain' path."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "",
            "proofState": 1,
            "goals": ["n : Nat\n⊢ n = n"],
        })
        result = await worker.step(state, "intro n")
        assert result.success
        assert not result.proof_closed
        assert result.next_state.goals[0].target == "n = n"


# ---------------------------------------------------------------------------
# LeanWorker.step() chained-tactic execution (fast, no real Lean — mocks _send)
# ---------------------------------------------------------------------------

class TestLeanWorkerStepChaining:
    """
    The REPL only parses one atomic tactic per call, so a top-level ';'
    chain like "intro n; simp" is split and each step sent as its own
    sequential call, chaining proofState ids forward. Regression coverage
    for that behavior — no real Lean process needed, _send is mocked.
    """

    def _make_worker_with_cached_state(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        state = make_proof_state(["some goal"])
        worker._proof_state_cache[state.stable_hash()] = 0
        return worker, state

    async def test_unchained_tactic_sends_exactly_one_request(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "", "proofState": 1, "goals": ["⊢ True"],
        })
        await worker.step(state, "simp")
        assert worker._send.await_count == 1

    async def test_two_step_chain_sends_each_step_against_prior_proofstate(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n"]},
            {"proofStatus": "Completed", "proofState": 2, "goals": []},
        ])
        result = await worker.step(state, "intro n; rfl")

        assert worker._send.await_count == 2
        first_call, second_call = worker._send.await_args_list
        assert first_call.args[0] == {"tactic": "intro n", "proofState": 0}
        assert second_call.args[0] == {"tactic": "rfl", "proofState": 1}
        assert result.success
        assert result.proof_closed

    async def test_chain_stops_and_reports_the_step_that_failed(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n"]},
            {"message": "Lean error:\nunknown identifier `bogus`"},
        ])
        result = await worker.step(state, "intro n; exact bogus")

        assert worker._send.await_count == 2
        assert not result.success
        assert "step 2 of 2" in result.next_state.error
        assert '"exact bogus"' in result.next_state.error
        assert "unknown identifier `bogus`" in result.next_state.error

    async def test_chain_does_not_execute_steps_after_a_step_that_failed(self):
        """A 3-step chain that fails on step 2 must never send step 3."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n"]},
            {"message": "Lean error:\nboom"},
            {"proofStatus": "Completed", "proofState": 99, "goals": []},
        ])
        await worker.step(state, "intro n; bad_tactic; rfl")
        assert worker._send.await_count == 2

    async def test_chain_stops_early_once_goal_closes(self):
        """If step 1 of a 3-step chain already closes the goal, steps 2
        and 3 must not run — there's nothing left to prove."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "Completed", "proofState": 1, "goals": []},
        ])
        result = await worker.step(state, "aesop; simp; omega")

        assert worker._send.await_count == 1
        assert result.success
        assert result.proof_closed

    async def test_single_tactic_error_message_is_not_annotated_with_step_info(self):
        """A non-chained tactic's error must look exactly as it did before
        chaining existed — no 'step 1 of 1' noise."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "message": "Lean error:\nunknown identifier `bogus`",
        })
        result = await worker.step(state, "exact bogus")
        assert result.next_state.error == "Lean error:\nunknown identifier `bogus`"


# ---------------------------------------------------------------------------
# LeanWorker.step() intermediate-state checkpointing (fast, mocks _send)
# ---------------------------------------------------------------------------

class TestLeanWorkerStepIntermediateStates:
    """
    Each genuinely-verified sub-step of a chained candidate must be exposed
    as its own checkpoint, not just the chain's final outcome — otherwise a
    multi-step candidate is all-or-nothing: a later step failing discards
    everything earlier that DID compile. No real Lean needed — _send mocked.
    """

    def _make_worker_with_cached_state(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        state = make_proof_state(["some goal"])
        worker._proof_state_cache[state.stable_hash()] = 0
        return worker, state

    async def test_single_tactic_has_no_intermediate_states(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "", "proofState": 1, "goals": ["⊢ True"],
        })
        result = await worker.step(state, "simp")
        assert result.intermediate_states == ()

    async def test_successful_chain_exposes_all_but_the_last_step(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n → True"]},
            {"proofStatus": "", "proofState": 2, "goals": ["n : Nat\nh : n = n\n⊢ True"]},
            {"proofStatus": "Completed", "proofState": 3, "goals": []},
        ])
        result = await worker.step(state, "intro n; intro h; trivial")

        assert len(result.intermediate_states) == 2
        assert result.intermediate_states[0].tactic_trace == ("intro n",)
        assert result.intermediate_states[1].tactic_trace == ("intro n", "intro h")
        # The final step's outcome is next_state, not a third intermediate.
        assert result.proof_closed

    async def test_intermediate_states_have_increasing_depth(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ A"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ B"]},
        ])
        result = await worker.step(state, "tac1; tac2")
        assert result.intermediate_states[0].depth == state.depth + 1

    async def test_failed_chain_still_exposes_steps_that_succeeded_first(self):
        """A 3-step chain failing on step 3 must still expose the
        checkpoints from steps 1 and 2, which genuinely compiled."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ A"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ B"]},
            {"message": "Lean error:\nboom"},
        ])
        result = await worker.step(state, "tac1; tac2; bad_tac3")

        assert not result.success
        assert len(result.intermediate_states) == 2
        assert result.intermediate_states[0].tactic_trace == ("tac1",)
        assert result.intermediate_states[1].tactic_trace == ("tac1", "tac2")

    async def test_chain_failing_on_first_step_has_no_intermediate_states(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={"message": "Lean error:\nboom"})
        result = await worker.step(state, "bad_tac; tac2")
        assert result.intermediate_states == ()

    async def test_intermediate_state_is_cached_so_a_later_step_can_continue_from_it(self):
        """The whole point of exposing a checkpoint is that a future turn
        can call step() again starting from it — which requires its
        stable_hash() to already be in the proof-state cache, since step()
        looks the REPL id up from the state alone."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ A"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ B"]},
        ])
        result = await worker.step(state, "tac1; tac2")
        checkpoint = result.intermediate_states[0]

        # Now continue from that checkpoint with a brand-new tactic.
        worker._send = AsyncMock(return_value={
            "proofStatus": "Completed", "proofState": 5, "goals": [],
        })
        follow_up = await worker.step(checkpoint, "omega")
        assert follow_up.success
        # Confirms the lookup succeeded against the REPL id recorded for
        # the checkpoint (proofState 1), not a cache-miss error.
        sent_proof_state = worker._send.await_args.args[0]["proofState"]
        assert sent_proof_state == 1


# ---------------------------------------------------------------------------
# Integration tests (slow, real Lean)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found"
)
@pytest.mark.asyncio
class TestSubprocessExecutor:

    @pytest_asyncio.fixture
    async def executor(self):
        """Start one executor before each test, shut it down after."""
        exec_ = SubprocessExecutor(load_mathlib=False)
        await exec_.start()
        yield exec_
        await exec_.close()

    async def test_reset_simple_theorem(self, executor):
        # reset() against a real REPL should return an open ProofState.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        assert isinstance(state, ProofState)
        assert not state.is_closed
        assert not state.is_error
        assert state.num_goals == 1

    async def test_step_intro(self, executor):
        # "intro n" on a ∀ goal strips the quantifier and exposes the body.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.success
        assert not result.proof_closed
        assert result.next_state.num_goals == 1
        assert "n + 0 = n" in result.next_state.goals[0].target

    async def test_step_simp_closes(self, executor):
        # "intro n" then "simp" is a complete proof.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.success
        assert r2.proof_closed

    async def test_step_failing_tactic(self, executor):
        # "ring" on a ∀ goal fails — Mathlib not loaded in this fixture
        # (load_mathlib=False for speed); even with Mathlib, ring requires
        # intro first. Either way the REPL reports an error.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "ring")
        assert not result.success
        assert result.next_state.is_error

    async def test_full_proof_trace(self, executor):
        # tactic_trace must accumulate every tactic applied since reset().
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        r1 = await executor.step(state, "intro n")
        r2 = await executor.step(r1.next_state, "simp")
        assert r2.next_state.tactic_trace == ("intro n", "simp")

    async def test_elapsed_ms_recorded(self, executor):
        # Each StepResult must record how long the REPL took.
        state = await executor.reset(
            "theorem foo : ∀ n : Nat, n + 0 = n := by"
        )
        result = await executor.step(state, "intro n")
        assert result.elapsed_ms > 0

    async def test_two_executors_independent(self):
        # Two SubprocessExecutor instances each own their own REPL process.
        # They must be able to run concurrent proofs without interfering.
        exec0 = SubprocessExecutor(load_mathlib=False)
        exec1 = SubprocessExecutor(load_mathlib=False)
        await exec0.start()
        await exec1.start()
        try:
            s0, s1 = await asyncio.gather(
                exec0.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
                exec1.reset("theorem foo : ∀ n : Nat, n + 0 = n := by"),
            )

            async def full_proof(executor, state):
                r1 = await executor.step(state, "intro n")
                r2 = await executor.step(r1.next_state, "simp")
                return r2.proof_closed

            closed0, closed1 = await asyncio.gather(
                full_proof(exec0, s0),
                full_proof(exec1, s1),
            )
            assert closed0
            assert closed1
        finally:
            await exec0.close()
            await exec1.close()


# ---------------------------------------------------------------------------
# prove_parallel integration tests (slow, real Lean)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found"
)
@pytest.mark.asyncio
class TestProveParallelIntegration:

    async def test_k_searches_prove_same_theorem(self):
        # k LedgerSearch + k SubprocessExecutor pairs all attempt the same
        # theorem concurrently via prove_parallel. MockPolicy supplies tactics
        # so no LLM API calls are needed. Real Lean can close this theorem with
        # just "simp" in one step, so we only assert overall success.
        k = 3
        policy = MockPolicy(tactics=["simp", "ring", "omega", "intro n"])

        executors = [SubprocessExecutor(load_mathlib=False) for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])

        try:
            searches = [
                LedgerSearch(policy=policy, executor=e)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=50,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            for e in executors:
                await e.close()

    async def test_all_searches_fail_returns_failure(self):
        # All k searches fail because every tactic is invalid Lean syntax.
        # prove_parallel must return failure rather than crashing.
        k = 2
        policy = MockPolicy(tactics=["not_a_tactic", "also_invalid"])

        executors = [SubprocessExecutor(load_mathlib=False) for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])

        try:
            searches = [
                LedgerSearch(policy=policy, executor=e)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=10,
            )
            assert not result.success
        finally:
            for e in executors:
                await e.close()


# ---------------------------------------------------------------------------
# End-to-end tests (slow, real Lean + real Anthropic API)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found",
)
@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY"),
    reason="ANTHROPIC_API_KEY not set",
)
@pytest.mark.asyncio(loop_scope="class")
class TestEndToEnd:
    # Mathlib loads once per class (shared_lean fixture).  The parallel test
    # still starts k=2 fresh executors — reusing the shared one there would risk
    # corrupting the REPL's stdout buffer if that search gets cancelled first.

    @pytest_asyncio.fixture(scope="class", loop_scope="class")
    async def shared_lean(self):
        """Start one Mathlib-loaded executor shared across all non-parallel tests."""
        policy = AnthropicPolicy()
        executor = SubprocessExecutor()
        await executor.start()
        yield policy, executor
        await executor.close()
        await policy.close()

    async def test_anthropic_proves_simple_theorem(self, shared_lean):
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove("theorem foo : ∀ n : Nat, n + 0 = n := by", budget=10)
        assert result.success
        assert len(result.proof_trace) > 0

    async def test_anthropic_prove_parallel(self, shared_lean):
        # k independent searches run concurrently. Fresh executors so cancellation
        # can't corrupt the shared REPL's stdout buffer.
        policy, _ = shared_lean
        k = 2
        executors = [SubprocessExecutor() for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])
        try:
            searches = [
                LedgerSearch(policy=policy, executor=e, k=8)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=10,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            for e in executors:
                await e.close()

    async def test_binomial_square(self, shared_lean):
        # Level 1: algebraic identity over Int requiring a Mathlib tactic.
        # ring normalises both sides of a polynomial equation — it's only
        # available after LeanProject is imported (load_mathlib=True default).
        #
        # Expected proof: intro a b; ring
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=12)
        result = await search.prove(
            "theorem binomial_sq : ∀ a b : Int, (a + b)^2 = a^2 + 2*a*b + b^2 := by",
            budget=50,
        )
        assert result.success
        assert len(result.proof_trace) > 0

    async def test_contrapositive(self, shared_lean):
        # Level 2: propositional logic — modus tollens / contrapositive.
        # Requires genuine multi-step reasoning: intro, apply, exact.
        # simp/omega/ring do not apply here.
        #
        # Expected proof: intro p q hpq hnq hp; exact hnq (hpq hp)
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove(
            "theorem contrapositive : ∀ (p q : Prop), (p → q) → ¬q → ¬p := by",
            budget=20,
        )
        assert result.success
        assert len(result.proof_trace) > 0


# ---------------------------------------------------------------------------
# End-to-end tests (slow, real Lean + real DeepSeek API)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found",
)
@pytest.mark.skipif(
    not os.environ.get("DEEPSEEK_API_KEY"),
    reason="DEEPSEEK_API_KEY not set",
)
@pytest.mark.asyncio(loop_scope="class")
class TestDeepSeekEndToEnd:
    # Mathlib loads once per class (shared_lean fixture). Same rationale as
    # TestEndToEnd — parallel test uses fresh executors to avoid cancellation issues.

    @pytest_asyncio.fixture(scope="class", loop_scope="class")
    async def shared_lean(self):
        """Start one Mathlib-loaded executor shared across all non-parallel tests."""
        policy = DeepSeekPolicy()
        executor = SubprocessExecutor()
        await executor.start()
        yield policy, executor
        await executor.close()
        await policy.close()

    async def test_deepseek_proves_simple_theorem(self, shared_lean):
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove("theorem foo : ∀ n : Nat, n + 0 = n := by", budget=10)
        assert result.success
        assert len(result.proof_trace) > 0

    async def test_deepseek_prove_parallel(self, shared_lean):
        policy, _ = shared_lean
        k = 2
        executors = [SubprocessExecutor() for _ in range(k)]
        await asyncio.gather(*[e.start() for e in executors])
        try:
            searches = [
                LedgerSearch(policy=policy, executor=e, k=8)
                for e in executors
            ]
            result = await prove_parallel(
                "theorem foo : ∀ n : Nat, n + 0 = n := by",
                searches=searches,
                budget=10,
            )
            assert result.success
            assert len(result.proof_trace) > 0
        finally:
            for e in executors:
                await e.close()

    async def test_deepseek_add_comm(self, shared_lean):
        # Level 1: commutativity of natural number addition.
        # Requires intro n m then omega — tests that DeepSeek generates a
        # meaningful two-step proof for a non-trivial arithmetic theorem.
        #
        # Expected proof: intro n m; omega
        policy, executor = shared_lean
        search = LedgerSearch(policy=policy, executor=executor, k=8)
        result = await search.prove(
            "theorem add_comm_nat : ∀ n m : Nat, n + m = m + n := by",
            budget=20,
        )
        assert result.success
        assert len(result.proof_trace) > 0
