"""
Unit tests for search/ledger_search.py — LLM-guided proof search over a
Ledger, with no value function or priority queue.

These use MockPolicy (and small custom test policies below, for behavior
MockPolicy can't exercise — abandonment, bogus state ids, banned tactics)
plus MockExecutor. No real Lean or API calls.
"""

from __future__ import annotations

import asyncio

from core.executor import StepResult
from core.ledger import Ledger
from core.proof_state import ProofState, make_goal, make_proof_state
from lean.mock_executor import MockExecutor
from policy.base import DirectorResponse
from policy.mock import MockPolicy
from search.ledger_search import LedgerSearch, ProofResult, prove_parallel


class ErroringExecutor:
    """Test-only executor whose reset() always returns a parse-error state."""

    capacity = 1

    async def reset(self, theorem: str, preamble: str = "") -> ProofState:
        return ProofState(goals=(), error="Lean parse error: unexpected token")

    async def step(self, state, tactic):
        raise AssertionError("step() should never be called after a parse error")

    async def close(self) -> None:
        pass


class AlwaysCloseExecutor:
    """
    Test-only executor that closes the proof on ANY tactic it receives.

    Used to prove that banned tactics are stripped out before ever reaching
    the executor — not merely that MockExecutor's own tactic simulation
    happens not to recognize them as closing. If the filter were broken,
    this executor would immediately "succeed" on the first banned tactic
    handed to it.
    """

    capacity = 1

    async def reset(self, theorem: str, preamble: str = "") -> ProofState:
        return make_proof_state(["dummy goal"])

    async def step(self, state: ProofState, tactic: str) -> StepResult:
        closed_state = ProofState(goals=(), tactic_trace=state.tactic_trace + (tactic,))
        return StepResult(next_state=closed_state, tactic=tactic)

    async def close(self) -> None:
        pass


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def make_search(
    tactics: list[str] | None = None,
    capacity: int = 2,
) -> LedgerSearch:
    return LedgerSearch(
        policy=MockPolicy(tactics=tactics),
        executor=MockExecutor(capacity=capacity),
    )


# ---------------------------------------------------------------------------
# LedgerSearch — basic proving behavior
# ---------------------------------------------------------------------------

class TestLedgerSearchProving:

    def test_proves_simple_theorem(self):
        search = make_search(tactics=["simp", "ring", "omega"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.success
        assert len(result.proof_trace) > 0
        assert result.nodes_visited >= 1

    def test_proof_trace_contains_closing_tactic(self):
        search = make_search(tactics=["simp"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.success
        assert "simp" in result.proof_trace

    def test_multi_step_proof(self):
        search = make_search(tactics=["intro n", "simp", "ring"])
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            budget=20,
        ))
        assert result.success
        assert "intro n" in result.proof_trace
        assert "simp" in result.proof_trace

    def test_budget_exhaustion_returns_failure(self):
        search = make_search(tactics=["ring"])  # ring won't close ∀ goal
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            budget=1,
        ))
        assert not result.success
        assert result.proof_trace == []
        assert result.failure_reason == "budget_exhausted"

    def test_nodes_visited_tracked(self):
        search = make_search()
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=50,
        ))
        assert result.nodes_visited >= 1

    def test_elapsed_ms_is_positive(self):
        search = make_search()
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.elapsed_ms >= 0.0

    def test_theorem_stored_in_result(self):
        theorem = "theorem foo : n + 0 = n := by"
        search = make_search()
        result = asyncio.run(search.prove(theorem, budget=10))
        assert result.theorem == theorem

    def test_all_tactics_fail_returns_failure(self):
        search = make_search(tactics=["blah", "nope", "invalid"])
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert not result.success

    def test_malformed_theorem_does_not_crash(self):
        """MockExecutor doesn't simulate real Lean parse errors for arbitrary
        strings — it just treats them as an (unsolvable) goal. The point
        here is just that prove() never crashes on bad input."""
        search = make_search()
        result = asyncio.run(search.prove(
            "this is not valid lean",
            budget=10,
        ))
        assert isinstance(result, ProofResult)
        assert not result.success or result.success

    def test_parse_error_returns_failure_immediately(self):
        search = LedgerSearch(policy=MockPolicy(), executor=ErroringExecutor())
        result = asyncio.run(search.prove("not valid lean at all", budget=10))
        assert not result.success
        assert result.failure_reason == "parse_error"
        assert result.nodes_visited == 0

    def test_capacity_respected(self):
        search = LedgerSearch(
            policy=MockPolicy(tactics=["simp", "ring"]),
            executor=MockExecutor(capacity=1),
        )
        result = asyncio.run(search.prove(
            "theorem foo : n + 0 = n := by",
            budget=10,
        ))
        assert result.success


# ---------------------------------------------------------------------------
# LedgerSearch — director-specific behavior (abandonment, bad ids, banned tactics)
# ---------------------------------------------------------------------------

class TestLedgerSearchDirectorBehavior:

    def test_banned_tactics_are_filtered(self):
        """sorry/admit must never close a proof, even if the director proposes them."""

        class BannedTacticPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                chosen = next(iter(ledger.frontier))
                return DirectorResponse(
                    chosen_state_id=chosen,
                    abandoned_state_ids=[],
                    tactic="sorry",
                )

            async def close(self):
                pass

        search = LedgerSearch(policy=BannedTacticPolicy(), executor=MockExecutor())
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))
        assert not result.success

    def test_embedded_sorry_is_filtered_not_just_bare_sorry(self):
        """A tactic like 'exact absurd hcard (by sorry)' smuggles sorry in as
        a nested term-mode proof — it must be rejected even though it isn't
        literally the string "sorry". Uses AlwaysCloseExecutor so a real Lean
        REPL would accept the tactic; only the filter can stop it."""

        class EmbeddedSorryPolicy:
            def __init__(self):
                self._tactics = iter([
                    "exact absurd hcard (by sorry)",
                    "have h := by admit",
                    "simp",
                ])

            async def get_next_action(self, theorem, ledger, premises):
                chosen = next(iter(ledger.frontier))
                return DirectorResponse(
                    chosen_state_id=chosen,
                    abandoned_state_ids=[],
                    tactic=next(self._tactics),
                )

            async def close(self):
                pass

        search = LedgerSearch(
            policy=EmbeddedSorryPolicy(), executor=AlwaysCloseExecutor()
        )
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))

        assert result.success
        # The sorry/admit-bearing tactics must never reach the executor —
        # "simp" (the only clean one, proposed on the third turn) is what
        # actually closes it.
        assert result.proof_trace == ["simp"]

    def test_abandoning_the_only_state_is_refused_so_the_search_continues(self):
        """An abandonment that would empty the frontier is NOT honoured.

        The loop terminates on `not ledger.frontier`, so honouring such a
        request ends the entire search — which is never what the director
        means by pruning. Observed live on imo2011_q3: turn 25 abandoned 11
        states at once and the run reported frontier_exhausted having spent
        only 25 of its 50 calls. Deciding when to stop is the budget's job.

        The search must therefore run to budget here (and still terminate —
        the original point of this test was that it must not loop forever)."""

        class AbandonOnlyStatePolicy:
            def __init__(self):
                self.turn = 0

            async def get_next_action(self, theorem, ledger, premises):
                self.turn += 1
                only_state = next(iter(ledger.frontier))
                if self.turn == 1:
                    # Fail a tactic first so there's something to abandon.
                    return DirectorResponse(only_state, [], "nope")
                # Abandon the only state while "choosing" a different,
                # nonexistent id — not the same self-referential case.
                return DirectorResponse("some-other-id", [only_state], "simp")

            async def close(self):
                pass

        search = LedgerSearch(policy=AbandonOnlyStatePolicy(), executor=MockExecutor())
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=10))
        assert not result.success
        # The refused abandon keeps the frontier alive, so the run now uses
        # the budget it was given instead of dying on turn 2.
        assert result.failure_reason == "budget_exhausted"
        assert result.nodes_visited == 10

    def test_self_abandon_of_chosen_state_is_ignored(self):
        """A director response that both chooses and abandons the same
        state in one turn is self-contradictory. Choosing a state signals
        intent to continue it, so the self-abandon must be ignored rather
        than honored — this was a real bug that silently killed an
        otherwise-solvable search (see traces/ from the diff_implies_cont
        failure it caused)."""

        class SelfContradictingPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                chosen = next(iter(ledger.frontier))
                return DirectorResponse(
                    chosen_state_id=chosen,
                    abandoned_state_ids=[chosen],  # contradicts choosing it
                    tactic="simp",
                )

            async def close(self):
                pass

        search = LedgerSearch(policy=SelfContradictingPolicy(), executor=MockExecutor())
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=10))
        # simp actually closes "n + 0 = n" — the self-abandon must not have
        # prevented the tactic from being tried.
        assert result.success
        assert result.nodes_visited == 1

    def test_bogus_chosen_state_id_does_not_crash(self):
        """If the director names a state that isn't in the frontier, the
        search should skip that turn gracefully rather than erroring."""

        class BogusIdPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                return DirectorResponse(
                    chosen_state_id="does-not-exist",
                    abandoned_state_ids=[],
                    tactic="simp",
                )

            async def close(self):
                pass

        search = LedgerSearch(policy=BogusIdPolicy(), executor=MockExecutor())
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))
        assert not result.success
        assert result.failure_reason == "budget_exhausted"
        assert result.nodes_visited == 5

    def test_failed_tactics_are_recorded_in_ledger_for_next_call(self):
        """A failing tactic at a state should not evict that state from the
        frontier — it stays available for a future director call."""

        calls: list[Ledger] = []

        class RecordingPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                calls.append(ledger)
                chosen = next(iter(ledger.frontier))
                if len(calls) == 1:
                    return DirectorResponse(chosen, [], "nope")
                return DirectorResponse(chosen, [], "simp")

            async def close(self):
                pass

        search = LedgerSearch(policy=RecordingPolicy(), executor=MockExecutor())
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))

        assert result.success
        # The second call's ledger should show the state still in frontier,
        # plus a recorded failure from the first call's "nope" tactic.
        second_ledger = calls[1]
        assert len(second_ledger.frontier) == 1
        state_id = next(iter(second_ledger.frontier))
        assert len(second_ledger.failures_for(state_id)) == 1
        assert second_ledger.failures_for(state_id)[0].tactic == "nope"

    def test_successful_tactics_are_recorded_in_ledger(self):
        """Regression test for a real budget-burning loop: a state is never
        evicted from the frontier after a successful expansion (so the
        director can backtrack to it), and stable_hash is goals-only, so
        re-applying a tactic that already worked lands on the identical
        child id — the frontier doesn't even change size. If successes go
        unrecorded, the director sees that state still open with no
        evidence it ever touched it and can re-derive the same step until
        the budget runs out. Observed live on a DeepSeek imo1968 run: one
        nlinarith that succeeded every time was re-proposed 5 times,
        burning 10% of the budget."""

        calls: list[Ledger] = []

        class RecordingPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                calls.append(ledger)
                chosen = next(iter(ledger.frontier))
                # "intro n" advances but does NOT close the ∀ goal, so the
                # parent stays open alongside its new child — exactly the
                # shape that produced the live loop.
                if len(calls) == 1:
                    return DirectorResponse(chosen, [], "intro n")
                return DirectorResponse(next(reversed(ledger.frontier)), [], "simp")

            async def close(self):
                pass

        search = LedgerSearch(policy=RecordingPolicy(), executor=MockExecutor())
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by", budget=5
        ))

        assert result.success
        second_ledger = calls[1]
        root_id = next(iter(second_ledger.frontier))
        successes = [
            e for e in second_ledger.entries
            if e.outcome == "success" and e.parent_id == root_id
        ]
        assert len(successes) == 1
        assert successes[0].tactic == "intro n"
        # The child id must be recorded too — that's what tells the director
        # where to continue instead of re-running the same tactic.
        assert successes[0].child_id is not None
        assert successes[0].child_id in second_ledger.frontier

    def test_repeating_a_successful_tactic_is_visible_to_the_next_call(self):
        """End-to-end: after a tactic succeeds at a state, the NEXT
        director call's serialized prompt must say so, so the model can
        tell it already did that here."""
        from policy.base import serialize_ledger

        calls: list[Ledger] = []

        class RecordingPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                calls.append(ledger)
                chosen = next(iter(ledger.frontier))
                if len(calls) == 1:
                    return DirectorResponse(chosen, [], "intro n")
                return DirectorResponse(next(reversed(ledger.frontier)), [], "simp")

            async def close(self):
                pass

        search = LedgerSearch(policy=RecordingPolicy(), executor=MockExecutor())
        asyncio.run(search.prove("theorem foo : ∀ n : ℕ, n + 0 = n := by", budget=5))

        prompt = serialize_ledger("theorem foo := by", calls[1], [])
        assert "APPLIED SUCCESSFULLY" in prompt
        assert "intro n" in prompt

    def test_reasoning_persists_into_ledger_across_turns(self):
        """The director's stated plan for a state should be visible on the
        ledger passed into the NEXT call, not just returned and discarded."""

        calls: list[Ledger] = []

        class ReasoningPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                calls.append(ledger)
                chosen = next(iter(ledger.frontier))
                if len(calls) == 1:
                    return DirectorResponse(
                        chosen, [], "nope",
                        reasoning="Trying nope first because it seemed promising.",
                    )
                return DirectorResponse(chosen, [], "simp", reasoning="")

            async def close(self):
                pass

        search = LedgerSearch(policy=ReasoningPolicy(), executor=MockExecutor())
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=5))

        assert result.success
        second_ledger = calls[1]
        state_id = next(iter(second_ledger.frontier))
        assert (
            second_ledger.reasoning[state_id]
            == "Trying nope first because it seemed promising."
        )

    def test_explicit_abandon_removes_state_but_search_continues_via_new_states(self):
        """Abandoning one state should not end the search if other open
        states remain (e.g. a sibling produced earlier)."""

        class AbandonOneContinueOtherPolicy:
            def __init__(self):
                self.turn = 0
                self.root_id = None

            async def get_next_action(self, theorem, ledger, premises):
                self.turn += 1
                if self.turn == 1:
                    # First turn: a dead-end tactic on root that fails and
                    # leaves root as the only frontier state.
                    self.root_id = next(iter(ledger.frontier))
                    return DirectorResponse(self.root_id, [], "nope")
                if self.turn == 2:
                    # Second turn: advance root toward the goal, producing a
                    # child. Root stays in the frontier alongside it.
                    return DirectorResponse(self.root_id, [], "intro n")
                # Third turn: explicitly abandon root and continue its child
                # (the successor of "intro n") instead.
                child_id = next(sid for sid in ledger.frontier if sid != self.root_id)
                return DirectorResponse(child_id, [self.root_id], "simp")

            async def close(self):
                pass

        search = LedgerSearch(
            policy=AbandonOneContinueOtherPolicy(), executor=MockExecutor()
        )
        result = asyncio.run(search.prove(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by", budget=10
        ))
        assert result.success
        assert "intro n" in result.proof_trace
        assert "simp" in result.proof_trace


# ---------------------------------------------------------------------------
# Intermediate-state checkpointing
# ---------------------------------------------------------------------------

class TestLedgerSearchIntermediateStates:
    """
    Every genuinely-verified sub-step of a chained candidate (see
    StepResult.intermediate_states) must become its own frontier state, not
    just the chain's final outcome — otherwise a multi-step candidate is
    all-or-nothing: the director can only ever continue from the very end
    of whatever chain last succeeded, with no way back to an earlier
    checkpoint if further extending it keeps failing.
    """

    def test_intermediate_states_are_added_to_the_frontier(self):
        class ChainedExecutor:
            capacity = 1

            async def reset(self, theorem, preamble=""):
                return make_proof_state(["dummy goal"])

            async def step(self, state, tactic):
                checkpoint = ProofState(
                    goals=(make_goal("intermediate goal"),),
                    depth=state.depth + 1,
                    tactic_trace=state.tactic_trace + ("step1",),
                )
                final_state = ProofState(
                    goals=(make_goal("final goal"),),
                    depth=state.depth + 2,
                    tactic_trace=state.tactic_trace + ("step1", "step2"),
                )
                return StepResult(
                    next_state=final_state,
                    tactic=tactic,
                    intermediate_states=(checkpoint,),
                )

            async def close(self):
                pass

        captured_ledgers: list[Ledger] = []

        class RecordingPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                captured_ledgers.append(ledger)
                chosen = next(iter(ledger.frontier))
                return DirectorResponse(chosen, [], "step1; step2")

            async def close(self):
                pass

        search = LedgerSearch(policy=RecordingPolicy(), executor=ChainedExecutor())
        asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=1))

        ledger = captured_ledgers[0]
        goal_targets = {s.goals[0].target for s in ledger.frontier.values() if s.goals}
        assert "intermediate goal" in goal_targets
        assert "final goal" in goal_targets

    def test_intermediate_states_from_a_failed_candidate_still_get_added(self):
        """A chain that fails partway must still expose the checkpoints
        from the steps that DID succeed before the failure."""

        class PartialFailExecutor:
            capacity = 1

            async def reset(self, theorem, preamble=""):
                return make_proof_state(["dummy goal"])

            async def step(self, state, tactic):
                checkpoint = ProofState(
                    goals=(make_goal("survived checkpoint"),),
                    depth=state.depth + 1,
                    tactic_trace=state.tactic_trace + ("step1",),
                )
                error_state = ProofState(
                    goals=state.goals,
                    error="Lean error:\nboom",
                    depth=state.depth,
                    tactic_trace=state.tactic_trace,
                )
                return StepResult(
                    next_state=error_state,
                    tactic=tactic,
                    intermediate_states=(checkpoint,),
                )

            async def close(self):
                pass

        captured_ledgers: list[Ledger] = []

        class RecordingPolicy:
            async def get_next_action(self, theorem, ledger, premises):
                captured_ledgers.append(ledger)
                chosen = next(iter(ledger.frontier))
                return DirectorResponse(chosen, [], "step1; bad_step2")

            async def close(self):
                pass

        search = LedgerSearch(policy=RecordingPolicy(), executor=PartialFailExecutor())
        asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=1))

        ledger = captured_ledgers[0]
        goal_targets = {s.goals[0].target for s in ledger.frontier.values() if s.goals}
        assert "survived checkpoint" in goal_targets


# ---------------------------------------------------------------------------
# prove_parallel
# ---------------------------------------------------------------------------

class TestLedgerSearchProveParallel:

    def test_returns_success_when_any_search_succeeds(self):
        searches = [make_search(tactics=["simp"]) for _ in range(3)]
        result = asyncio.run(prove_parallel(
            "theorem foo : n + 0 = n := by",
            searches=searches,
            budget=10,
        ))
        assert result.success

    def test_returns_failure_when_all_searches_fail(self):
        searches = [make_search(tactics=["blah", "nope"]) for _ in range(3)]
        result = asyncio.run(prove_parallel(
            "theorem foo : n + 0 = n := by",
            searches=searches,
            budget=5,
        ))
        assert not result.success

    def test_multi_step_proof_found_in_parallel(self):
        searches = [make_search(tactics=["intro n", "simp", "ring"]) for _ in range(2)]
        result = asyncio.run(prove_parallel(
            "theorem foo : ∀ n : ℕ, n + 0 = n := by",
            searches=searches,
            budget=20,
        ))
        assert result.success
        assert "intro n" in result.proof_trace


class TestAbandonmentIsRecoverable:
    """
    Two defects found by inspecting the raw REPL log of a real imo2011_q3
    run: the director abandoned a state on turn 24, asked for it back on
    turn 25, and the search both discarded that turn AND terminated with
    half its budget unspent.
    """

    def test_choosing_a_previously_abandoned_state_restores_it(self):
        """The exact imo2011_q3 sequence: a state is abandoned on one turn
        and explicitly chosen on a later one. Before restore() the turn was
        silently discarded — the executor was never called at all.

        Turn 1 expands the root so a second state exists (an abandon that
        would empty the frontier is refused, which would mask this).
        Turn 2 works on the child and abandons the root.
        Turn 3 asks for the root back; the executor MUST be asked to step it.
        """
        stepped: list[str] = []

        class CountingExecutor(MockExecutor):
            async def step(self, state, tactic):
                stepped.append(tactic)
                return await super().step(state, tactic)

        class AbandonThenReselect:
            def __init__(self):
                self.turn = 0
                self.root = None

            async def get_next_action(self, theorem, ledger, premises):
                self.turn += 1
                ids = list(ledger.frontier)
                if self.turn == 1:
                    self.root = ids[0]
                    return DirectorResponse(self.root, [], "intro n")
                if self.turn == 2:
                    child = [i for i in ids if i != self.root]
                    return DirectorResponse(
                        child[0] if child else ids[0],
                        [self.root] if child else [],
                        "nope",
                    )
                # Turn 3+: ask for the abandoned root back.
                return DirectorResponse(self.root, [], "reselected-tactic")

            async def close(self):
                pass

        search = LedgerSearch(policy=AbandonThenReselect(), executor=CountingExecutor())
        asyncio.run(search.prove("theorem foo : ∀ n : ℕ, n + 0 = n := by", budget=3))

        assert "reselected-tactic" in stepped, (
            "turn 3 chose a previously abandoned state and was discarded "
            "instead of restoring it"
        )

    def test_abandon_that_would_empty_the_frontier_is_ignored(self):
        """Directly exercises the refusal: the policy tries to abandon every
        open state every turn, and the search must still run to budget."""

        class AbandonEverything:
            async def get_next_action(self, theorem, ledger, premises):
                every = list(ledger.frontier)
                return DirectorResponse("nonexistent-id", every, "simp")

        search = LedgerSearch(policy=AbandonEverything(), executor=MockExecutor())
        result = asyncio.run(search.prove("theorem foo : n + 0 = n := by", budget=6))
        assert result.failure_reason == "budget_exhausted"
        assert result.nodes_visited == 6

    def test_partial_abandon_is_still_honoured(self):
        """The refusal must be narrow — pruning that leaves something open
        still works, or the director loses the ability to prune at all."""
        from core.ledger import Ledger as _L
        from core.proof_state import make_proof_state as _mps

        ledger = _L()
        a = ledger.add_state(_mps(["goal a"]))
        b = ledger.add_state(_mps(["goal b"]))
        ledger.abandon([a])
        assert a not in ledger.frontier
        assert b in ledger.frontier
