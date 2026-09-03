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

import json
import os
import pytest
import pytest_asyncio
import asyncio
from unittest.mock import AsyncMock
from lean.repl import (
    LeanWorker,
    SubprocessExecutor,
    _split_top_level_tactics,
    _annotate_chain_error,
    _parse_goals,
    _candidate_boundaries,
    _peel_bare_have,
    _is_parse_error,
    _is_have_decomposition,
    LEAN_PROJECT_DIR,
)
from core.executor import StepResult
from core.proof_state import ProofState, make_goal, make_proof_state
from policy.mock import MockPolicy
from policy.anthropic import AnthropicPolicy
from policy.deepseek import DeepSeekPolicy
from search.ledger_search import LedgerSearch, prove_parallel


# Lean rejects a plain ';' chain outright, so step() preflights the whole
# string against the REPL and gets a parse error back before falling through
# to the split. Mocks for chained tactics must include that first response or
# they do not describe the real protocol.
_PARSE_REJECT = {"message": "Lean error:\n<input>:1:7: expected end of input"}


def _lean_like_send(responses):
    """A `_send` stub that rejects chains the way Lean's parser does.

    step() now discovers step boundaries by offering Lean progressively
    shorter prefixes, so a stub that just replays a fixed list will hand a
    success back for "tac1; tac2" and the test silently checks nothing. Real
    Lean answers "expected end of input" for any string with a top-level ';',
    so the stub does too, and the canned responses are consumed only by
    strings Lean would actually accept.

    This is the same lesson as tests/lean/test_recorded_goals.py: a mock that
    encodes what we believe rather than what Lean does is how a 24% goal
    corruption rate survived 387 green tests.
    """
    remaining = iter(responses)

    async def _send(payload):
        tactic = payload.get("tactic", "")
        if _candidate_boundaries(tactic):
            return _PARSE_REJECT
        return next(remaining)

    return _send


# ---------------------------------------------------------------------------
# Goals reach the model exactly as Lean wrote them (fast, no Lean needed)
# ---------------------------------------------------------------------------

class TestGoalsAreCarriedVerbatim:
    """
    There used to be a `_parse_goal_string` here that rebuilt Lean's goal
    text into hypothesis/target fields, and the prompt and the state hash
    were both built from the rebuilt version. Lean wraps long lines, and the
    parser only understood one-line entries, so:

      * a hypothesis whose type wrapped lost its name line (no " : ") and its
        continuation lines — it vanished entirely
      * a target that wrapped was cut off after its first line
      * a continuation line containing a colon became an invented hypothesis

    Measured over 3704 recorded goals: 890 corrupted (24%) — 653 deletions,
    468 truncations, 305 fabrications. 1061 deleted hypotheses were mostly
    the model's own `have` sub-lemmas (218 named `key`), since a decomposition
    is exactly the kind of long statement that wraps. The model noticed and
    misdiagnosed it 53 times across 20 traces.

    The parser is gone. These tests pin the invariant that replaced it.
    """

    def test_goals_reach_the_state_unchanged(self):
        raw = ["n : Nat\nh : n > 0\n⊢ n + 0 = n", "⊢ True"]
        goals = _parse_goals(raw)
        assert [g.text for g in goals] == raw
        assert [g.serialize() for g in goals] == raw

    def test_wrapped_hypothesis_survives(self):
        """The `key` case, verbatim from traces/eval_20260825_223800 seq 135 —
        a lemma the model had just created, deleted from its own context."""
        raw = ("x y z : ℝ\n"
               "key :\n"
               "  ∀ (a b c : ℝ),\n"
               "    0 < a → a * b * c ≥ 1 → (a ^ 5 - a ^ 2) ≥ (a ^ 2 - b * c)\n"
               "⊢ (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2) ≥\n"
               "    0")
        shown = _parse_goals([raw])[0].serialize()
        assert shown == raw
        assert "key :" in shown              # the lemma is still there
        assert "0 < a → a * b * c ≥ 1" in shown   # …with its statement
        assert shown.rstrip().endswith("0")  # the target is not cut off

    def test_wrapped_target_is_not_truncated(self):
        raw = "hn : 0 < n\n⊢ AdmissibleMark n A ∧\n    ∀ (B : Finset ℝ), 2 ≤ L A B"
        shown = _parse_goals([raw])[0].serialize()
        assert shown == raw
        assert "∀ (B : Finset ℝ)" in shown

    def test_continuation_line_is_not_promoted_to_a_hypothesis(self):
        """`∀ (B : Finset ℝ),` contains " : ", so the old parser rendered it
        as a hypothesis ABOVE the goal it had been cut from."""
        raw = "hn : 0 < n\n⊢ ∃ B,\n    ∀ (B : Finset ℝ), P B"
        assert _parse_goals([raw])[0].serialize() == raw

    def test_empty_and_blank_goals_are_dropped(self):
        assert _parse_goals([]) == ()
        assert _parse_goals(["", "   "]) == ()


class TestStateIdentityUsesLeansText:
    """stable_hash decides whether two branches are the same proof position.
    Built from the parsed fields it merged states that differed only in a
    deleted hypothesis: 17 buckets of genuinely different goals collided."""

    def test_goals_differing_only_in_a_wrapped_hypothesis_are_distinct(self):
        a = ProofState(goals=_parse_goals(["key :\n  ∀ a, a = a\n⊢ P"]))
        b = ProofState(goals=_parse_goals(["key :\n  ∀ a, a = 1\n⊢ P"]))
        assert a.stable_hash() != b.stable_hash()

    def test_case_label_keeps_states_distinct(self):
        """Two goals identical apart from Lean's case tag are NOT merged.
        Tempting to merge — 18 such pairs exist in the recorded corpus — but
        the model targets goals by that tag ("case pos => exact …"), so a
        merge can route such a tactic to the wrong state. Over-splitting is
        safe; under-splitting is the bug this module exists to prevent."""
        a = ProofState(goals=_parse_goals(["case succ\nn : ℕ\n⊢ P"]))
        b = ProofState(goals=_parse_goals(["case zero\nn : ℕ\n⊢ P"]))
        c = ProofState(goals=_parse_goals(["n : ℕ\n⊢ P"]))
        assert a.stable_hash() != b.stable_hash()
        assert a.stable_hash() != c.stable_hash()

    def test_inaccessible_renumbering_does_not_split_a_state(self):
        a = ProofState(goals=_parse_goals(["h✝¹ : P\n⊢ Q"]))
        b = ProofState(goals=_parse_goals(["h✝ : P\n⊢ Q"]))
        assert a.stable_hash() == b.stable_hash()


# ---------------------------------------------------------------------------
# _split_top_level_tactics / _annotate_chain_error (fast, pure functions)
#
# SCOPE NOTE. _split_top_level_tactics is no longer the harness's splitter —
# since 091226cd, Lean decides where a chain is cut (_discover_steps offers it
# progressively shorter prefixes). The only surviving caller is
# _peel_bare_have, which reads `parts[0]` and whether `parts` is empty; nothing
# reads parts[1:]. So roughly twenty of the assertions below check more surface
# than any caller depends on.
#
# They are kept deliberately, not by neglect: each protection rule here (the
# `case`/`next`/`conv` bodies, `fun x =>`, focus blocks, anonymous-constructor
# brackets) came from a real mis-split, and re-deriving that grammar knowledge
# would be expensive. Treat a failure in these classes as "the grammar model
# changed", not as "the harness is broken" — and do not read the size of this
# section as a measure of how much production depends on it.
# ---------------------------------------------------------------------------

class TestCandidateBoundaries:
    """Where a tactic COULD be cut. Deliberately a superset of the real cut
    points — bracket depth is lexical and unambiguous, while deciding which
    cuts are real is the guesswork that was wrong five times. Lean adjudicates
    in _discover_steps."""

    def test_top_level_semicolons_are_offered(self):
        assert _candidate_boundaries("intro n; simp; omega") == [7, 13]

    def test_semicolons_inside_brackets_are_not_offered(self):
        assert _candidate_boundaries("simp [a, b]; omega") == [11]
        assert _candidate_boundaries("refine ⟨a, by tac; more⟩") == []

    def test_the_combinator_is_never_a_boundary(self):
        """Splitting '<;>' corrupts the token itself into two invalid
        fragments, unlike other bad splits which merely mean the wrong thing."""
        assert _candidate_boundaries("cases h <;> simp") == []

    def test_branch_bodies_ARE_offered_and_lean_rejects_them(self):
        """The key difference from the old splitter: cuts inside an induction
        branch are offered as candidates rather than suppressed by a rule.
        Lean then refuses the truncated prefix, so the construct stays whole —
        without us needing to know that `with |` opens a branch body."""
        tactic = "induction xs with | nil => intro a; simp | cons h t => simp"
        assert _candidate_boundaries(tactic) != []

    def test_no_semicolons_means_no_boundaries(self):
        assert _candidate_boundaries("simp") == []


class TestPeelBareHave:
    """"have NAME : STMT := by REST" is decomposed deliberately, not to work
    around parsing — the whole string parses fine. Lean must not be consulted
    here or it would run the sub-proof atomically, which is the behaviour this
    replaced: 347 inlined sub-lemmas on tournament_champion, every sampled
    failure a mechanical slip inside the `by` block discarding a correct
    decomposition."""

    def test_have_with_inline_proof_is_peeled(self):
        assert _peel_bare_have("have h : P := by intro y; simp") == (
            "have h : P", "intro y; simp")

    def test_have_ending_in_a_bare_by_still_peels(self):
        """"have h : T := by" with nothing after it is a syntax error in Lean,
        so sending it whole burns a turn. The bare `have` is plainly the
        intent and opens the sub-goal. 22 recorded tactics have this shape."""
        assert _peel_bare_have("have hmod : 2 ^ n % 7 = 1 := by") == (
            "have hmod : 2 ^ n % 7 = 1", "")

    def test_have_without_a_stated_type_is_not_peeled(self):
        assert _peel_bare_have("have h := by simp") is None

    def test_a_plain_chain_is_not_peeled(self):
        assert _peel_bare_have("intro n; simp") is None


class TestDiscoverStepsAsksLeanWhereToCut:
    """The orchestration: offer progressively shorter prefixes, and the first
    one Lean parses is the next tactic.

    The stub below declares which strings are atomic, standing in for Lean's
    grammar. That is the point — the production code no longer contains that
    knowledge anywhere.
    """

    def _worker_where_atomic(self, atomic, results=None):
        """A worker whose Lean accepts exactly `atomic` strings."""
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        state = make_proof_state(["some goal"])
        worker._proof_state_cache[state.stable_hash()] = 0
        counter = {"n": 0}
        results = results or {}

        async def _send(payload):
            t = payload.get("tactic", "")
            if t not in atomic:
                return _PARSE_REJECT
            if t in results:
                return results[t]
            counter["n"] += 1
            return {"proofStatus": "", "proofState": counter["n"],
                    "goals": [f"⊢ after {t}"]}

        worker._send = _send
        return worker, state

    async def test_an_embedded_unknown_construct_is_kept_whole(self):
        """The gap the preflight alone could not close: a construct our rules
        mangle, sitting inside a genuine chain. The whole string does not
        parse, so a preflight cannot save it — but shortening from the right
        finds `skip`, and then the remainder parses whole."""
        worker, state = self._worker_where_atomic(
            {"skip", "first | rfl; rfl | simp"})
        sent = []
        inner = worker._send

        async def spy(payload):
            sent.append(payload.get("tactic"))
            return await inner(payload)

        worker._send = spy
        await worker.step(state, "skip; first | rfl; rfl | simp")
        executed = [t for t in sent if t in {"skip", "first | rfl; rfl | simp"}]
        assert executed == ["skip", "first | rfl; rfl | simp"]
        assert "first | rfl" not in sent or sent.count("first | rfl") == 0

    async def test_a_genuine_chain_is_still_split(self):
        worker, state = self._worker_where_atomic({"intro n", "simp", "omega"})
        sent = []
        inner = worker._send

        async def spy(payload):
            sent.append(payload.get("tactic"))
            return await inner(payload)

        worker._send = spy
        await worker.step(state, "intro n; simp; omega")
        assert [t for t in sent if t in {"intro n", "simp", "omega"}] == [
            "intro n", "simp", "omega"]

    async def test_longest_prefix_wins_over_a_shorter_one_that_also_parses(self):
        """A truncated construct can be valid syntax that fails later, so a
        shortest-first scan would accept it and reintroduce the truncation."""
        whole = "induction n with | zero => simp; ring | succ k => simp"
        truncated = "induction n with | zero => simp"
        worker, state = self._worker_where_atomic({whole, truncated})
        sent = []
        inner = worker._send

        async def spy(payload):
            sent.append(payload.get("tactic"))
            return await inner(payload)

        worker._send = spy
        await worker.step(state, whole)
        assert sent[0] == whole
        assert truncated not in sent


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


class TestSplitProtectsStructuredAlternatives:
    """
    A ';' inside the body of an `induction/cases ... with | alt => ...`
    alternative sequences that branch — it is not a step separator. Splitting
    there ships a truncated alternative list, which Lean rejects with
    "unsolved goals" because the remaining branches were never sent.

    Measured cost of getting this wrong: 51 truncated tactics across 576 in
    one 14-problem evaluation. imo2026_q3_spec_share_bounds sent
    "induction xs with | nil => intro a" — and nothing else — thirteen times
    in a row (raw REPL log seq 339-351). The model is told only that the step
    failed, so it spent 14 consecutive turns rewriting a `nil` branch that had
    never run, trying eleven different bodies, none of which reached Lean.
    imo2026_q6 lost its final four turns the same way.

    Confirmed against a real Lean REPL: the endpoint accepts
    "induction n with | zero => rfl | succ k ih => rw [Nat.succ_add]; rw [ih]"
    as a single tactic, while a plain "intro h; exact h" is still rejected
    with "expected end of input" — so chains must still be split, just not
    inside a branch.
    """

    def test_semicolon_inside_an_induction_branch_is_not_split(self):
        tactic = ("induction xs with | nil => intro a; simp "
                  "| cons hd tl ih => intro a; simp [ih]")
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_leading_chain_still_splits_but_the_induction_stays_whole(self):
        tactic = ("intro k; induction k with | zero => simp "
                  "| succ n ih => rw [Nat.succ_mul]; omega")
        assert _split_top_level_tactics(tactic) == [
            "intro k",
            "induction k with | zero => simp | succ n ih => rw [Nat.succ_mul]; omega",
        ]

    def test_cases_alternatives_are_protected_too(self):
        tactic = "cases xs with | nil => intro a; rfl | cons hd tl => intro a; simp"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_nested_alternatives_stay_in_one_piece(self):
        tactic = ("induction l with | nil => simp "
                  "| cons a t ih => cases t with | nil => simp | cons b t' => simp; ring")
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_rcases_with_pattern_still_splits(self):
        """`rcases h with a | b` has a '|' but opens no branch bodies (no
        '=>'), so a following ';' is still a real step separator."""
        assert _split_top_level_tactics("rcases h with a | b; simp") == [
            "rcases h with a | b", "simp",
        ]

    def test_case_tag_body_is_protected(self):
        """`case`/`next`/`conv` open a body with no '|' and no 'with', so a
        rule keyed on those keywords misses them. The rule is keyed on the
        '=>' itself instead."""
        tactic = "case pos => exact h; simp"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_next_body_is_protected(self):
        tactic = "next => intro x; simp"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_conv_block_is_protected(self):
        tactic = "conv => rw [foo]; rfl"
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_lambda_arrow_does_not_stop_splitting(self):
        """A '=>' from a lambda opens no body — "exact fun x => x; simp"
        really is two steps, so a "fun"/"λ" in the current segment suppresses
        the stop."""
        assert _split_top_level_tactics("exact fun x => x; simp") == [
            "exact fun x => x", "simp",
        ]

    def test_lambda_after_an_earlier_top_level_bar_still_splits(self):
        """Regression: keying the stop on "a '|' was seen earlier" made the
        flag sticky, so an unrelated lambda later in the string wrongly
        stopped the split and shipped a top-level ';' to Lean."""
        assert _split_top_level_tactics(
            "rcases h with a | b; exact fun x => x; simp"
        ) == ["rcases h with a | b", "exact fun x => x", "simp"]

    def test_lambda_inside_a_branch_body_does_not_reopen_splitting(self):
        tactic = ("induction xs with | nil => exact fun x => x; simp "
                  "| cons h t => simp")
        assert _split_top_level_tactics(tactic) == [tactic]

    def test_lambda_in_a_have_term_proof_still_splits(self):
        assert _split_top_level_tactics("have h : P := fun n => f n; simp") == [
            "have h : P := fun n => f n", "simp",
        ]


class TestSplitProtectsFocusBlocks:
    """
    Lean's focus dot runs its body on one goal and requires that goal to be
    closed. So "· simp; omega" is one tactic: splitting it into "· simp" plus
    "omega" demands that `simp` alone close the goal, and the step fails with
    "unsolved goals" when it does not.

    Confirmed against a real Lean REPL: "· rw [Nat.add_comm]; rfl" parses and
    runs, reporting an error raised from *inside* the bullet body.
    """

    def test_semicolon_inside_a_focus_block_is_not_split(self):
        assert _split_top_level_tactics("· unfold padicValNat; simp [hp]") == [
            "· unfold padicValNat; simp [hp]",
        ]

    def test_consecutive_focus_blocks_are_separated(self):
        assert _split_top_level_tactics("constructor; · simp; ring; · omega") == [
            "constructor", "· simp; ring", "· omega",
        ]

    def test_separator_semicolon_before_a_dot_is_dropped(self):
        """The ';' between two blocks separates them rather than sequencing
        anything, so it must not survive as a dangling "· sorry;"."""
        assert _split_top_level_tactics("by_cases h : P; · sorry; · sorry") == [
            "by_cases h : P", "· sorry", "· sorry",
        ]

    def test_focus_placeholder_inside_brackets_is_not_a_focus_block(self):
        """`(· ≤ ·)` is Lean's anonymous-function placeholder, not a focus
        dot — it sits inside brackets and must not start a new part."""
        assert _split_top_level_tactics("have h := (A ∪ B).sort (· ≤ ·); simp") == [
            "have h := (A ∪ B).sort (· ≤ ·)", "simp",
        ]


class TestSplitTracksAnonymousConstructorBrackets:
    """
    ⟨⟩ must count toward bracket depth. Without it, a "by" inside an
    anonymous constructor reads as a top-level `by`, aborts the scan, and the
    whole string ships to Lean with its top-level ';' intact — which the
    tactic endpoint rejects with "expected end of input". Seen live at raw
    REPL log seq 561, 686 and 687.
    """

    def test_by_inside_anonymous_constructor_does_not_abort_the_split(self):
        tactic = ("refine ⟨a + b - 180/n, by linarith, ?_, by ring⟩; "
                  "have hnpos : (0:ℝ) < 180/(n:ℝ)")
        assert _split_top_level_tactics(tactic) == [
            "refine ⟨a + b - 180/n, by linarith, ?_, by ring⟩",
            "have hnpos : (0:ℝ) < 180/(n:ℝ)",
        ]

    def test_semicolon_inside_anonymous_constructor_is_not_a_separator(self):
        assert _split_top_level_tactics("exact ⟨by simp; omega, h⟩") == [
            "exact ⟨by simp; omega, h⟩",
        ]

    def test_have_with_anonymous_constructor_proof_then_a_real_chain(self):
        tactic = "have hmn : m ≠ 0 ∧ n ≠ 0 := ⟨by omega, by omega⟩; rw [foo]"
        assert _split_top_level_tactics(tactic) == [
            "have hmn : m ≠ 0 ∧ n ≠ 0 := ⟨by omega, by omega⟩", "rw [foo]",
        ]


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
        assert "step 3 in this chain" in result
        assert '"exact y"' in result
        assert "unknown identifier `y`" in result

    def test_no_step_total_is_claimed(self):
        """Lean decides the boundaries as execution proceeds, so the total is
        unknown when a chain fails early. Claiming "step 2 of 2" for a
        three-piece candidate would say its third piece ran."""
        result = _annotate_chain_error("boom", ["intro n", "bogus"], 1)
        assert "of 2" not in result and "step 2 in this chain" in result

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
        assert "hidden sorry" in result.next_state.error.lower()

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
        assert result.next_state.goals[0].text == "n : Nat\n⊢ n = n"


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

    async def test_two_step_chain_sends_each_step_against_prior_proofstate(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n"]},
            {"proofStatus": "Completed", "proofState": 2, "goals": []},
        ]))
        result = await worker.step(state, "intro n; rfl")

        assert worker._send.await_count == 3
        preflight, first_call, second_call = worker._send.await_args_list
        assert preflight.args[0] == {"tactic": "intro n; rfl", "proofState": 0}
        assert first_call.args[0] == {"tactic": "intro n", "proofState": 0}
        assert second_call.args[0] == {"tactic": "rfl", "proofState": 1}
        assert result.success
        assert result.proof_closed

    async def test_trace_records_what_lean_ran_not_what_the_model_wrote(self):
        """proof_trace must be the executed steps, or it is not a proof.

        Measured on eval_20260902_140914 (imo2005_q3, solved 2/2): pasting the
        recorded trace back into Lean failed with "No goals to be solved".
        The trace held the director's original
            have hB : ... := by positivity; ...; field_simp; ring
        while Lean had actually been sent the PEELED `have hB : ...` and the
        rest as separate steps against a different goal. Checkpoints already
        recorded the executed steps; the two terminal states recorded the raw
        string, so one trace mixed both conventions.
        """
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ P", "⊢ Q"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ Q"]},
            {"proofStatus": "Completed", "proofState": 3, "goals": []},
        ]))
        result = await worker.step(state, "have h : P := by simp; exact h")

        assert result.proof_closed
        trace = list(result.next_state.tactic_trace)
        assert trace == ["have h : P", "simp", "exact h"], trace
        assert "have h : P := by simp; exact h" not in trace, (
            "the unsplit original must not appear — it is not what Lean ran"
        )

    async def test_unsplit_tactic_still_records_itself_verbatim(self):
        """The fix must not change the common case: a single tactic that Lean
        accepts whole is recorded exactly as written."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Completed", "proofState": 1, "goals": [],
        })
        result = await worker.step(state, "omega")
        assert list(result.next_state.tactic_trace) == ["omega"]

    async def test_chain_stops_and_reports_the_step_that_failed(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n"]},
            {"message": "Lean error:\nunknown identifier `bogus`"},
        ]))
        result = await worker.step(state, "intro n; exact bogus")

        assert worker._send.await_count == 3
        assert not result.success
        assert "step 2 in this chain" in result.next_state.error
        assert '"exact bogus"' in result.next_state.error
        assert "unknown identifier `bogus`" in result.next_state.error

    async def test_chain_does_not_execute_steps_after_a_step_that_failed(self):
        """A 3-step chain that fails on step 2 must never send step 3."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n"]},
            {"message": "Lean error:\nboom"},
            {"proofStatus": "Completed", "proofState": 99, "goals": []},
        ]))
        await worker.step(state, "intro n; bad_tactic; rfl")
        # Count the *executed* steps, not the probes: boundary discovery
        # sends extra candidates that Lean rejects without running anything.
        sent = [c.args[0]["tactic"] for c in worker._send.await_args_list]
        assert "rfl" not in sent, f"step 3 ran after step 2 failed: {sent}"

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

class TestPreflightWholeTactic:
    """
    `_split_top_level_tactics` models a fragment of the Lean grammar by hand,
    and has been wrong five times ('<;>', nested 'by', ⟨⟩ depth, 'with |'
    alternative bodies, '·' focus blocks, 'case'/'next'/'conv' bodies). Each
    miss silently mutilated a correct tactic: imo2026_q3_spec_share_bounds
    spent 14 consecutive turns debugging an induction branch that had never
    been sent, and imo2026_q6 lost its final four turns the same way.
    Constructs the splitter still gets wrong are known to exist — verified
    against a real REPL, "first | t; t | t", "repeat t; t" and "iterate n t; t"
    all parse whole and are still split.

    So step() treats the split as a hint. When it claims a chain, Lean is
    asked first: a parse error is ~1ms and mutates no proof state, while a
    successful parse means the model wrote one atomic tactic that must not be
    taken apart.
    """

    def _make_worker_with_cached_state(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        state = make_proof_state(["some goal"])
        worker._proof_state_cache[state.stable_hash()] = 0
        return worker, state

    async def test_a_construct_lean_parses_whole_is_never_taken_apart(self):
        """The regression this whole mechanism exists for: even if the
        splitter wrongly claims two steps, Lean parsing the string means it
        is sent intact."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "Completed", "proofState": 1, "goals": [],
        })
        tactic = "first | rfl; rfl | rfl"
        assert len(_split_top_level_tactics(tactic)) > 1  # splitter is wrong here
        result = await worker.step(state, tactic)

        assert worker._send.await_count == 1
        assert worker._send.await_args_list[0].args[0] == {
            "tactic": tactic, "proofState": 0,
        }
        assert result.proof_closed

    async def test_preflight_result_is_reused_not_re_executed(self):
        """A tactic that parses must run exactly once — re-sending it after
        the probe would pay for an expensive tactic twice."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 7, "goals": ["⊢ B"]},
        ])
        await worker.step(state, "induction n with | zero => simp; ring | succ k ih => simp")
        assert worker._send.await_count == 1

    async def test_a_genuine_chain_falls_back_to_the_split(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ A"]},
            {"proofStatus": "Completed", "proofState": 2, "goals": []},
        ]))
        result = await worker.step(state, "intro n; rfl")

        sent = [c.args[0]["tactic"] for c in worker._send.await_args_list]
        assert sent == ["intro n; rfl", "intro n", "rfl"]
        assert result.proof_closed

    async def test_single_tactic_is_never_preflighted(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "proofStatus": "", "proofState": 1, "goals": ["⊢ True"],
        })
        await worker.step(state, "simp")
        assert worker._send.await_count == 1

    async def test_have_decomposition_is_never_preflighted(self):
        """"have NAME : STMT := by REST" parses whole, so preflighting it
        would silently undo the deliberate bare-sub-goal split — the one
        split that exists for checkpointing rather than for parsing."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=[
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ P", "⊢ Q"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ Q"]},
        ])
        await worker.step(state, "have h : P := by simp")

        sent = [c.args[0]["tactic"] for c in worker._send.await_args_list]
        assert sent == ["have h : P", "simp"]

    async def test_elaboration_failure_is_not_mistaken_for_a_parse_error(self):
        """"unknown identifier" means Lean parsed and ran it — the string is
        one tactic and must not be split afterwards."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(return_value={
            "message": "Lean error:\nunknown identifier `bogus`",
        })
        await worker.step(state, "induction n with | zero => exact bogus; rfl | succ k ih => simp")
        assert worker._send.await_count == 1


class TestIsParseError:

    def test_position_prefixed_syntax_error_is_a_parse_error(self):
        assert _is_parse_error(
            {"message": "Lean error:\n<input>:1:7: expected end of input"})

    def test_elaboration_error_is_not_a_parse_error(self):
        assert not _is_parse_error({"message": "Lean error:\nunsolved goals"})

    def test_error_in_messages_list_is_inspected_too(self):
        assert not _is_parse_error(
            {"messages": [{"data": "Unknown constant `foo`"}]})

    def test_successful_response_is_not_a_parse_error(self):
        assert not _is_parse_error({"proofState": 1, "goals": []})


class TestIsHaveDecomposition:

    def test_have_with_inline_proof_is_a_decomposition(self):
        t = "have h : P := by intro y; simp"
        assert _is_have_decomposition(t, _split_top_level_tactics(t))

    def test_have_without_inline_proof_is_not(self):
        t = "have hp; simp"
        assert not _is_have_decomposition(t, _split_top_level_tactics(t))

    def test_plain_chain_is_not(self):
        t = "intro k; simp"
        assert not _is_have_decomposition(t, _split_top_level_tactics(t))

    def test_have_later_in_a_chain_is_not_the_leading_construct(self):
        """The split there begins with the chain, not the have, so the whole
        string is a genuine chain and Lean will reject it anyway."""
        t = "intro k; have h : P := by simp"
        assert not _is_have_decomposition(t, _split_top_level_tactics(t))


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
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["n : Nat\n⊢ n = n → True"]},
            {"proofStatus": "", "proofState": 2, "goals": ["n : Nat\nh : n = n\n⊢ True"]},
            {"proofStatus": "Completed", "proofState": 3, "goals": []},
        ]))
        result = await worker.step(state, "intro n; intro h; trivial")

        assert len(result.intermediate_states) == 2
        assert result.intermediate_states[0].tactic_trace == ("intro n",)
        assert result.intermediate_states[1].tactic_trace == ("intro n", "intro h")
        # The final step's outcome is next_state, not a third intermediate.
        assert result.proof_closed

    async def test_intermediate_states_have_increasing_depth(self):
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ A"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ B"]},
        ]))
        result = await worker.step(state, "tac1; tac2")
        assert result.intermediate_states[0].depth == state.depth + 1

    async def test_failed_chain_still_exposes_steps_that_succeeded_first(self):
        """A 3-step chain failing on step 3 must still expose the
        checkpoints from steps 1 and 2, which genuinely compiled."""
        worker, state = self._make_worker_with_cached_state()
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ A"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ B"]},
            {"message": "Lean error:\nboom"},
        ]))
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
        worker._send = AsyncMock(side_effect=_lean_like_send([
            {"proofStatus": "", "proofState": 1, "goals": ["⊢ A"]},
            {"proofStatus": "", "proofState": 2, "goals": ["⊢ B"]},
        ]))
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
        assert "n + 0 = n" in result.next_state.goals[0].text

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
        search = LedgerSearch(policy=policy, executor=executor)
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
                LedgerSearch(policy=policy, executor=e)
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
        search = LedgerSearch(policy=policy, executor=executor)
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
        search = LedgerSearch(policy=policy, executor=executor)
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
        search = LedgerSearch(policy=policy, executor=executor)
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
                LedgerSearch(policy=policy, executor=e)
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
        search = LedgerSearch(policy=policy, executor=executor)
        result = await search.prove(
            "theorem add_comm_nat : ∀ n m : Nat, n + m = m + n := by",
            budget=20,
        )
        assert result.success
        assert len(result.proof_trace) > 0


# ---------------------------------------------------------------------------
# Raw REPL exchange logging (LeanWorker._log_exchange)
# ---------------------------------------------------------------------------

class TestRawLeanLog:
    """
    The raw JSONL log is the only unabridged record of what Lean said.

    Everything downstream loses information: repl.py surfaces msg_errors[0]
    and drops any further errors in the same response, the Ledger stores one
    error string per attempt, and traces/ record the rendered PROMPT — which
    caps tactic lists at 15 per state (2807 lists were capped across our
    existing traces, one hiding 672 attempts) and errors at 2000 chars. So
    "what did Lean actually return" was unanswerable after a run finished.
    """

    def _worker(self, path):
        w = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False, raw_log_path=path)
        return w

    def _read(self, path):
        return [json.loads(l) for l in path.read_text().splitlines() if l.strip()]

    def test_logs_nothing_when_no_path_configured(self, tmp_path):
        w = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        w._log_exchange({"tactic": "simp"}, {"goals": []}, 1.0)
        assert list(tmp_path.iterdir()) == []

    def test_records_request_and_full_response(self, tmp_path):
        p = tmp_path / "worker1.jsonl"
        w = self._worker(p)
        w._log_exchange({"tactic": "simp", "proofState": 0}, {"goals": [], "env": 1}, 12.5)

        rows = self._read(p)
        assert len(rows) == 1
        assert rows[0]["request"] == {"tactic": "simp", "proofState": 0}
        assert rows[0]["response"] == {"goals": [], "env": 1}
        assert rows[0]["seq"] == 1
        assert rows[0]["elapsed_ms"] == 12.5

    def test_preserves_every_error_not_just_the_first(self, tmp_path):
        """The whole point: repl.py's extraction takes msg_errors[0], so a
        response carrying several errors reaches the model as one. The raw
        log must keep all of them or the loss is unrecoverable."""
        p = tmp_path / "worker1.jsonl"
        w = self._worker(p)
        w._log_exchange(
            {"tactic": "have h : P := by nlinarith"},
            {"messages": [
                {"severity": "error", "data": "linarith failed to find a contradiction"},
                {"severity": "error", "data": "unsolved goals\n⊢ P"},
                {"severity": "error", "data": "internal exception #5"},
            ]},
            40.0,
        )
        errs = [m["data"] for m in self._read(p)[0]["response"]["messages"]]
        assert len(errs) == 3
        assert "internal exception #5" in errs

    def test_appends_across_exchanges_with_increasing_seq(self, tmp_path):
        p = tmp_path / "worker1.jsonl"
        w = self._worker(p)
        for i in range(3):
            w._log_exchange({"tactic": f"t{i}"}, {"goals": []}, 1.0)
        assert [r["seq"] for r in self._read(p)] == [1, 2, 3]

    def test_records_timeouts_which_are_invisible_downstream(self, tmp_path):
        """A tactic that never returns produces no Ledger entry and no prompt
        text, so without an explicit record the raw log would skip it and the
        run would look like the tactic was never tried."""
        p = tmp_path / "worker1.jsonl"
        w = self._worker(p)
        w._log_exchange({"tactic": "slow"}, None, 30000.0, error="timeout")

        row = self._read(p)[0]
        assert row["error"] == "timeout"
        assert row["response"] is None

    def test_logging_failure_never_breaks_the_search(self, tmp_path):
        """Diagnostics must not be able to take down a proof run."""
        w = self._worker(tmp_path / "no_such_dir" / "worker1.jsonl")
        w._log_exchange({"tactic": "simp"}, {"goals": []}, 1.0)  # must not raise

    def test_unicode_survives_round_trip(self, tmp_path):
        """Lean goals are full of ℝ, ⊢, ≥ — they must stay readable."""
        p = tmp_path / "worker1.jsonl"
        w = self._worker(p)
        w._log_exchange({"tactic": "nlinarith"}, {"goals": ["x y : ℝ ⊢ x ≥ y"]}, 1.0)
        assert "ℝ" in p.read_text()
        assert self._read(p)[0]["response"]["goals"] == ["x y : ℝ ⊢ x ≥ y"]


# ---------------------------------------------------------------------------
# proofState cache hygiene across problems
# ---------------------------------------------------------------------------

class TestResetClearsProofStateCache:
    """
    stable_hash covers the goal TEXT only, not the environment it was
    elaborated in. With per-problem preambles each problem gets its own
    environment, so two problems can render an identical goal while meaning
    different things — reusing a cached proofState across that boundary would
    silently run tactics against the wrong context. Cheapest correct guard is
    to drop the cache at each reset.
    """

    async def test_cache_is_dropped_on_reset(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        worker._proof_state_cache["stale-hash-from-a-previous-problem"] = 99
        worker._send = AsyncMock(return_value={
            "sorries": [{"proofState": 0, "goal": "⊢ True"}],
            "env": 1,
        })

        await worker.reset("theorem foo : True := by")

        assert "stale-hash-from-a-previous-problem" not in worker._proof_state_cache


class TestWorkerRestartRecovery:
    """
    A stuck tactic forces the subprocess to be killed (see the TimeoutError
    branch in _send), which wipes _proof_state_cache. Every state the Ledger
    holds then points at REPL ids that no longer exist.

    Measured before this existed: a 155s `simp` killed the worker on turn 9 of
    imo2026_q1_terminal_value, and 41 of the remaining 49 turns never reached
    Lean — the run scored 0/50 and read in the results exactly like a model
    failure. A ProofState carries its full tactic path, so the state can be
    re-derived by replaying it from a fresh reset.
    """

    async def test_rebuilds_a_state_whose_repl_id_was_lost(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        worker._last_theorem = "theorem foo : True := by"
        state = ProofState(goals=(make_goal("True"),), tactic_trace=("trivial",))

        calls = []

        async def fake_reset(theorem, preamble=""):
            calls.append(("reset", theorem))
            base = make_proof_state(["True"])
            worker._proof_state_cache[base.stable_hash()] = 0
            return base, 0

        async def fake_step(st, tac):
            calls.append(("step", tac))
            worker._proof_state_cache[state.stable_hash()] = 7
            return StepResult(next_state=state, tactic=tac)

        worker.reset = fake_reset
        worker.step = fake_step
        assert await worker._rebuild_state(state) == 7
        assert calls == [("reset", "theorem foo : True := by"), ("step", "trivial")]

    async def test_gives_up_when_no_theorem_recorded(self):
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        assert await worker._rebuild_state(make_proof_state(["x"])) is None

    async def test_does_not_recurse_while_already_rebuilding(self):
        """_rebuild_state calls step(), which can cache-miss again. Without the
        guard that is unbounded recursion."""
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        worker._last_theorem = "theorem foo : True := by"
        worker._rebuilding = True
        assert await worker._rebuild_state(make_proof_state(["x"])) is None

    async def test_unrecoverable_miss_reports_the_worker_lost_sentinel(self):
        """The search keys on this exact error to end the trial rather than
        spend its remaining budget."""
        from lean.repl import WORKER_LOST_ERROR
        worker = LeanWorker(LEAN_PROJECT_DIR, load_mathlib=False)
        state = make_proof_state(["some goal"])          # never cached
        result = await worker.step(state, "simp")
        assert result.next_state.error == WORKER_LOST_ERROR
