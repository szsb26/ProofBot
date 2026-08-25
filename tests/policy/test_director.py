"""
Unit tests for the director-call machinery in policy/base.py:
serialize_ledger, parse_director_response, and BaseLLMPolicy.get_next_action.

These are the pieces search/ledger_search.py relies on instead of a priority
queue — serialize_ledger turns a Ledger into prompt text, parse_director_response
turns the LLM's JSON reply back into a DirectorResponse, and get_next_action
wires the two together with a never-raises fallback contract: on any API
or parse failure it continues an arbitrary frontier state rather than
propagating the error, so one bad turn cannot end the search.

There is deliberately no k-candidates-per-turn mechanism: the director
proposes exactly one tactic per call (see search/ledger_search.py's module
docstring for why — the k-candidates design let a single turn spawn several
permanent frontier branches, and the model often used the slots to encode
one sequential plan rather than genuinely independent alternatives).
"""

from __future__ import annotations

import json
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from core.ledger import Ledger
from core.proof_state import ProofState, make_goal, make_proof_state
from policy.base import (
    DIRECTOR_SYSTEM_PROMPT,
    DirectorResponse,
    parse_director_response,
    serialize_ledger,
)
from policy.deepseek import DeepSeekPolicy


# ---------------------------------------------------------------------------
# serialize_ledger
# ---------------------------------------------------------------------------

class TestSerializeLedger:

    def test_includes_theorem(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n + 0 = n"]))
        text = serialize_ledger("theorem foo : n + 0 = n := by", ledger, [])
        assert "theorem foo : n + 0 = n := by" in text

    def test_lists_open_state_with_goal(self):
        ledger = Ledger()
        state = make_proof_state(["n + 0 = n"], [[("n", "ℕ")]])
        state_id = ledger.add_state(state)
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert state_id in text
        assert "n + 0 = n" in text
        assert "n : ℕ" in text

    def test_open_states_capped_when_frontier_is_large(self):
        """Without a cap, the frontier can grow unboundedly (e.g. once
        every verified sub-step of a chained candidate becomes its own
        state) and showing all of them would reproduce the same
        runaway-prompt-size problem the tactic-eviction cap exists to
        prevent. Deepest (most-progressed) states are kept when over
        budget."""
        ledger = Ledger()
        for i in range(25):
            ledger.add_state(make_proof_state([f"goal number {i}"], depth=i))

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "showing 20 of 25" in text
        # Depths 5-24 (the 20 deepest) are kept...
        assert "goal number 24" in text
        assert "goal number 5" in text
        # ...depths 0-4 (the shallowest 5) are evicted.
        assert "goal number 0" not in text
        assert "goal number 4" not in text

    def test_open_states_not_capped_at_or_below_budget(self):
        ledger = Ledger()
        for i in range(20):
            ledger.add_state(make_proof_state([f"goal number {i}"], depth=i))

        text = serialize_ledger("theorem foo := by", ledger, [])
        open_states_section = text.split("## Currently Open States")[1].split("##")[0]
        assert "showing" not in open_states_section
        for i in range(20):
            assert f"goal number {i}" in text

    def test_exhausted_attempts_omitted_for_states_evicted_from_display(self):
        ledger = Ledger()
        for i in range(25):
            state_id = ledger.add_state(make_proof_state([f"goal number {i}"], depth=i))
            if i == 0:
                # A shallow state (guaranteed to be evicted) with a
                # recorded failure — its failure history must not leak
                # into the prompt once the state itself is off-screen.
                ledger.record_failure(state_id, "a_uniquely_named_failed_tactic", "tactic_failed")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "a_uniquely_named_failed_tactic" not in text

    def test_root_state_shows_path_as_root(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n + 0 = n"]))
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "(root)" in text

    def test_non_root_state_shows_tactic_path(self):
        ledger = Ledger()
        state = ProofState(
            goals=(make_goal("n = n"),),
            depth=2,
            tactic_trace=("intro n", "simp"),
        )
        ledger.add_state(state)
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "intro n, simp" in text

    def test_summarizes_dead_branches_with_category_counts(self):
        ledger = Ledger()
        state = make_proof_state(["n = n"])
        state_id = ledger.add_state(state)
        ledger.record_failure(state_id, "bad1", "hallucinated_lemma")
        ledger.record_failure(state_id, "bad2", "hallucinated_lemma")
        ledger.record_failure(state_id, "bad3", "type_mismatch")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "Exhausted Attempts" in text
        assert "hallucinated_lemma×2" in text
        assert "type_mismatch×1" in text

    def test_failure_summary_and_tactic_list_are_on_separate_lines(self):
        """The summary line had no trailing newline, so every failed state
        in every prompt rendered as
        "...tactic_failed×1Tactics already tried here — do not repeat"."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_failure(state_id, "omega", "tactic_failed")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "tactic_failed×1Tactics" not in text
        assert "tactic_failed×1\nTactics already tried here" in text

    def test_failure_count_is_singular_for_one_tactic(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_failure(state_id, "omega", "tactic_failed")
        assert "1 tactic tried" in serialize_ledger("theorem foo := by", ledger, [])

    def test_lists_specific_failed_tactics_to_prevent_verbatim_repeats(self):
        """The model must be able to see exactly which tactics already
        failed at a state, not just aggregate counts — otherwise it can't
        tell it's about to repeat a verbatim failure."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_failure(state_id, "omega", "tactic_failed")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "Tactics already tried here" in text
        assert "omega" in text

    def test_repeated_identical_failed_tactic_is_deduplicated(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        for _ in range(4):
            ledger.record_failure(state_id, "omega", "tactic_failed")
        ledger.record_failure(state_id, "ring_nf", "tactic_failed")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert text.count("- omega") == 1
        assert "- ring_nf" in text

    def test_tried_tactics_list_is_capped_with_omitted_note(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        # Long (>30 char) tactics so none qualify for short-tactic protection.
        for i in range(20):
            ledger.record_failure(
                state_id, f"exact SomeVeryLongLemmaName.tactic_number_{i}", "tactic_failed"
            )

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "showing 15 of 20 unique" in text
        # Most recent ones should be the ones kept
        assert "tactic_number_19" in text
        assert "tactic_number_0" not in text

    def test_short_generic_tactics_are_never_evicted_even_when_old(self):
        """A bare tactic like "omega" tried once, long before many longer
        tactics fill up the recency cap, must still appear — otherwise the
        model can't tell it already tried the exact thing it's about to
        propose again."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_failure(state_id, "omega", "tactic_failed")
        for i in range(20):
            ledger.record_failure(
                state_id, f"exact SomeVeryLongLemmaName.tactic_number_{i}", "tactic_failed"
            )

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "- omega" in text
        # Still evicts old long tactics to keep the long-tactic budget bounded
        assert "tactic_number_0" not in text
        assert "tactic_number_19" in text

    def test_many_short_tactics_still_cap_long_tactics_at_zero(self):
        """Regression test: when >=15 distinct short tactics accumulate,
        the long-tactic budget hits exactly 0. A naive `list[-0:]` slice
        returns the WHOLE list in Python (since -0 == 0), not an empty
        one — silently disabling the cap entirely instead of showing
        none. This is exactly what happened on a real tournament_champion
        trace: a state with 16 short tactics ended up displaying all 289
        long ones (305 total) instead of being capped near 15, ballooning
        that turn's prompt past 100K characters."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        for i in range(16):
            ledger.record_failure(state_id, f"omega{i}", "tactic_failed")
        for i in range(50):
            ledger.record_failure(
                state_id,
                f"have h{i} : some_long_proposition_{i} := by some_long_proof_term_{i}",
                "tactic_failed",
            )

        text = serialize_ledger("theorem foo := by", ledger, [])
        shown = text.count("\n  - ")
        assert shown == 16, f"expected only the 16 short tactics to show, got {shown} entries"
        assert "showing 16 of 66 unique" in text

    def test_long_multiline_tactic_is_truncated_and_flattened(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        long_tactic = "induction n with\n| zero => simp\n| succ n ih => " + ("x" * 150)
        ledger.record_failure(state_id, long_tactic, "tactic_failed")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "\n| zero" not in text  # flattened to one line
        assert "…" in text  # truncated

    def test_no_dead_branch_section_when_nothing_failed(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n = n"]))
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "Exhausted Attempts" not in text

    def test_abandoned_state_failures_excluded_from_summary(self):
        ledger = Ledger()
        state = make_proof_state(["n = n"])
        state_id = ledger.add_state(state)
        ledger.record_failure(state_id, "bad", "hallucinated_lemma")
        ledger.abandon([state_id])

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "Exhausted Attempts" not in text
        assert state_id not in text

    def test_includes_premises_when_present(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n = n"]))
        text = serialize_ledger("theorem foo := by", ledger, ["Nat.add_zero"])
        assert "Nat.add_zero" in text

    def test_omits_premises_section_when_empty(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n = n"]))
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "Potentially Relevant Lemmas" not in text

    def test_task_section_asks_for_exactly_one_tactic(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n = n"]))
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "exactly one tactic" in text

    def test_shows_tactics_already_applied_successfully(self):
        """A state stays in the frontier after being expanded (so it can be
        backtracked to), and stable_hash is goals-only, so re-applying a
        tactic that already worked lands on the identical child id — the
        frontier doesn't even change size. Without surfacing successes the
        director sees the state still open with no evidence it touched it,
        and loops re-deriving the same step. Observed live: a DeepSeek run
        burned 10% of its budget re-running one nlinarith that succeeded
        every time."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_success(state_id, "nlinarith [ha, hb]", "child123")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "APPLIED SUCCESSFULLY" in text
        assert "nlinarith [ha, hb]" in text
        # The resulting state id must be shown, so the director knows where
        # to continue instead of re-running the tactic.
        assert "child123" in text

    def test_no_applied_section_when_nothing_succeeded_yet(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n = n"]))
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "APPLIED SUCCESSFULLY" not in text

    def test_applied_successfully_deduplicates_repeats(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        for _ in range(4):
            ledger.record_success(state_id, "simp", "child123")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert text.count("- simp → produced state child123") == 1

    def test_applied_successes_of_other_states_not_shown(self):
        """Successes are attributed per-state; a success recorded against a
        state that isn't displayed must not leak into the prompt."""
        ledger = Ledger()
        shown_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_success("some-other-state", "a_uniquely_named_tactic", "x")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "a_uniquely_named_tactic" not in text

    def test_shows_persisted_reasoning_for_open_state(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.set_reasoning(state_id, "Plan to close via induction on n.")
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "Plan to close via induction on n." in text

    def test_no_plan_line_when_no_reasoning_recorded(self):
        ledger = Ledger()
        ledger.add_state(make_proof_state(["n = n"]))
        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "Last stated plan" not in text

    def test_shows_raw_error_under_failed_tactic(self):
        """The model must see the actual Lean diagnostic, not just a
        category label — otherwise it can't tell *why* a tactic failed
        (wrong lemma name vs. wrong argument shape vs. type mismatch)."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_failure(
            state_id,
            "exact Finset.card_lt_card hsub",
            "type_mismatch",
            "Lean error:\ntype mismatch\n  hsub\nhas type\n  s ⊆ t\nbut is expected to have type\n  s ⊂ t",
        )

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "s ⊆ t" in text
        assert "s ⊂ t" in text

    def test_no_error_line_when_error_is_blank(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_failure(state_id, "omega", "tactic_failed")

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "→" not in text

    def test_pathologically_long_error_is_capped(self):
        """Guards against reintroducing an unbounded-blob risk into the
        prompt (the same class of issue that overflowed the asyncio
        stream buffer for verbose apply?/exact? responses) — a huge raw
        error must be truncated, not passed through verbatim."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        huge_error = "Try this: " + ("x" * 5000)
        ledger.record_failure(state_id, "exact?", "tactic_failed", huge_error)

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert "[truncated]" in text
        assert len(text) < len(huge_error) + 2000

    def test_error_shown_survives_tactic_dedup(self):
        """When an identical tactic is retried and deduplicated to one
        display line, its error must still be shown (from the first
        occurrence), not silently dropped."""
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        ledger.record_failure(
            state_id, "omega", "tactic_failed", "unsolved goals\n⊢ False"
        )
        ledger.record_failure(
            state_id, "omega", "tactic_failed", "unsolved goals\n⊢ False"
        )

        text = serialize_ledger("theorem foo := by", ledger, [])
        assert text.count("- omega") == 1
        assert "unsolved goals" in text


# ---------------------------------------------------------------------------
# DIRECTOR_SYSTEM_PROMPT guidance
# ---------------------------------------------------------------------------

class TestDirectorSystemPromptGuidance:
    """
    The director can only use a capability it has been told exists. These
    assert the prompt actually teaches the two facts that unlock sub-goal
    decomposition — the structural move behind proofs that need a reusable
    helper lemma (IMO 1968 tetrahedron, tournament_champion).

    Motivation, measured from real traces: the director proposed 347
    inlined sub-lemmas of the form `have h : ∀ ... := by <long chain>`, and
    every sampled one failed on a mechanical error *inside* the `by` block.
    Everything after `by` is executed as one atomic unit, so those failures
    discarded the whole decomposition and surfaced only a single error. A
    bare `have h : STMT` instead opens STMT as its own goal, which the
    search can then prove incrementally with per-step feedback.
    """

    def test_prompt_explains_that_a_state_may_have_several_goals(self):
        assert "SEVERAL goals" in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_explains_tactics_apply_to_the_first_goal(self):
        assert "FIRST goal" in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_teaches_bare_have_to_open_a_subgoal(self):
        assert "have name : statement" in DIRECTOR_SYSTEM_PROMPT
        assert "NO `:= by ...` proof" in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_warns_that_inline_by_proofs_are_all_or_nothing(self):
        assert "atomic unit" in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_does_not_deny_the_combinator_our_splitter_supports(self):
        """lean/repl.py has a dedicated branch keeping `<;>` intact through
        the chain splitter, commented "apply to every resulting goal". The
        prompt used to flatly assert "Every tactic applies to the FIRST goal
        only", i.e. tell the model a combinator we deliberately support does
        not exist. Additive correction only — the first-goal default it
        already described is still stated."""
        assert "<;>" in DIRECTOR_SYSTEM_PROMPT
        assert "FIRST goal only" in DIRECTOR_SYSTEM_PROMPT   # default still stated
        assert "Every tactic applies to the FIRST goal only" not in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_does_not_promise_an_uncapped_frontier(self):
        """serialize_ledger caps the displayed frontier at
        _MAX_OPEN_STATES_SHOWN, and the rendered header truthfully says
        "showing 20 of 22" — but the system prompt claimed every open state
        was shown, contradicting it. Real cost: 24 turns of one
        tournament_champion run had states hidden while the prompt promised
        otherwise."""
        assert "every currently open proof state" not in DIRECTOR_SYSTEM_PROMPT
        assert "more than you can see" in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_asks_for_exactly_one_tactic(self):
        assert "exactly ONE tactic" in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_explains_semicolon_chaining(self):
        assert "';'" in DIRECTOR_SYSTEM_PROMPT

    def test_prompt_teaches_first_combinator_for_hedging(self):
        assert "first | tac1 | tac2" in DIRECTOR_SYSTEM_PROMPT


# ---------------------------------------------------------------------------
# parse_director_response
# ---------------------------------------------------------------------------

class TestParseDirectorResponse:

    def test_parses_well_formed_json(self):
        raw = json.dumps({
            "abandon": [],
            "abandon_reason": "",
            "chosen_state": "a1b2c3d4",
            "tactic": "simp",
        })
        resp = parse_director_response(raw, fallback_state_id="fallback")
        assert resp.chosen_state_id == "a1b2c3d4"
        assert resp.abandoned_state_ids == []
        assert resp.tactic == "simp"

    def test_extracts_json_from_surrounding_text(self):
        raw = (
            "Sure, here's my decision:\n```json\n"
            + json.dumps({"chosen_state": "abc", "tactic": "omega"})
            + "\n```\nHope that helps!"
        )
        resp = parse_director_response(raw, fallback_state_id="fallback")
        assert resp.chosen_state_id == "abc"
        assert resp.tactic == "omega"

    def test_parses_abandon_list_and_reason(self):
        raw = json.dumps({
            "abandon": ["dead1", "dead2"],
            "abandon_reason": "wrong approach",
            "chosen_state": "alive",
            "tactic": "tauto",
        })
        resp = parse_director_response(raw, fallback_state_id="fallback")
        assert resp.abandoned_state_ids == ["dead1", "dead2"]

    def test_falls_back_on_malformed_json(self):
        resp = parse_director_response("not json at all", fallback_state_id="fb")
        assert resp.chosen_state_id == "fb"
        assert resp.abandoned_state_ids == []
        assert resp.tactic == "simp"

    def test_falls_back_when_chosen_state_missing(self):
        raw = json.dumps({"tactic": "simp"})
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.chosen_state_id == "fb"

    def test_falls_back_tactic_to_simp_when_tactic_missing(self):
        raw = json.dumps({"chosen_state": "abc"})
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.tactic == "simp"

    def test_falls_back_tactic_to_simp_when_tactic_blank(self):
        raw = json.dumps({"chosen_state": "abc", "tactic": ""})
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.tactic == "simp"

    def test_allows_semicolon_chained_tactic(self):
        raw = json.dumps({"chosen_state": "abc", "tactic": "intro n; simp; ring"})
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.tactic == "intro n; simp; ring"

    def test_abandon_list_filters_non_strings(self):
        raw = json.dumps({
            "abandon": ["ok", 123, None],
            "chosen_state": "abc",
            "tactic": "simp",
        })
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.abandoned_state_ids == ["ok"]

    def test_parses_reasoning_field(self):
        raw = json.dumps({
            "reasoning": "Try induction on n since the goal is universally quantified.",
            "chosen_state": "abc",
            "tactic": "induction n",
        })
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.reasoning == "Try induction on n since the goal is universally quantified."

    def test_reasoning_defaults_to_empty_string_when_missing(self):
        raw = json.dumps({"chosen_state": "abc", "tactic": "simp"})
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.reasoning == ""

    def test_reasoning_defaults_to_empty_string_when_not_a_string(self):
        raw = json.dumps({"chosen_state": "abc", "tactic": "simp", "reasoning": 42})
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.reasoning == ""

    def test_fallback_response_has_empty_reasoning(self):
        resp = parse_director_response("not json at all", fallback_state_id="fb")
        assert resp.reasoning == ""

    def test_tactic_field_not_a_string_falls_back_to_simp(self):
        raw = json.dumps({"chosen_state": "abc", "tactic": ["simp", "ring"]})
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.tactic == "simp"


# ---------------------------------------------------------------------------
# parse_director_response — malformed/truncated recovery
#
# A live eval run of imo1968_tetrahedron showed the director's raw response
# comes back as broken JSON on a meaningful fraction of turns — sometimes a
# genuine token-budget cutoff mid-reasoning, sometimes the model just
# forgets the final '}'. Before this recovery path existed, ANY of these
# discarded the whole response (including correct, on-strategy reasoning)
# down to an empty-reasoning, "simp" default. These tests pin the recovered
# behavior for each shape actually observed.
# ---------------------------------------------------------------------------

class TestParseDirectorResponseRecovery:

    def test_recovers_when_final_brace_is_missing(self):
        raw = (
            '{"reasoning": "Use wlog on the maximal edge to force a '
            'contradiction.", "abandon": [], "abandon_reason": "", '
            '"chosen_state": "36793c2b", "tactic": "nlinarith"'
        )
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.chosen_state_id == "36793c2b"
        assert resp.reasoning == "Use wlog on the maximal edge to force a contradiction."
        assert resp.tactic == "nlinarith"

    def test_recovers_tactic_containing_brackets(self):
        # A tactic like "nlinarith [h1, h2]" has a ']' inside the string —
        # a naive text.find("]") would stop there instead of at the real
        # end of the JSON value.
        raw = (
            '{"reasoning": "close it", "chosen_state": "s1", '
            '"tactic": "nlinarith [h1, h2]"'
        )
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.tactic == "nlinarith [h1, h2]"

    def test_recovers_when_trailing_content_makes_json_invalid(self):
        # A stray unquoted token after an otherwise-intact object breaks
        # strict json.loads, but every real field before it is still
        # recoverable via regex.
        raw = (
            '{"reasoning": "case split", "chosen_state": "c1", '
            '"tactic": "linarith", "note": unquoted_text}'
        )
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.chosen_state_id == "c1"
        assert resp.reasoning == "case split"
        assert resp.tactic == "linarith"

    def test_recovers_partial_reasoning_when_cut_off_mid_string(self):
        raw = '{"reasoning": "The key insight is to use wlog on the maximal edge and then'
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.reasoning == (
            "The key insight is to use wlog on the maximal edge and then"
        )
        # No tactic ever came through — still falls back to simp.
        assert resp.tactic == "simp"
        assert resp.chosen_state_id == "fb"

    def test_recovers_tactic_cut_off_mid_string_falls_back_to_simp(self):
        """A tactic string with no closing quote (cut off mid-write by the
        token budget) has no complete value to recover — falls back to
        simp rather than yielding a truncated, likely-invalid tactic."""
        raw = (
            '{"reasoning": "ok", "chosen_state": "s1", '
            '"tactic": "have h : AB < AC + AD := by nlinari'
        )
        resp = parse_director_response(raw, fallback_state_id="fb")
        assert resp.tactic == "simp"

    def test_completely_unparseable_text_still_falls_back_cleanly(self):
        resp = parse_director_response(
            "The model wrote prose instead of JSON this time.",
            fallback_state_id="fb",
        )
        assert resp.chosen_state_id == "fb"
        assert resp.reasoning == ""
        assert resp.tactic == "simp"


# ---------------------------------------------------------------------------
# BaseLLMPolicy.get_next_action (via DeepSeekPolicy with a mocked client)
# ---------------------------------------------------------------------------

def _make_api_response(text: str) -> MagicMock:
    message = MagicMock()
    message.content = text
    choice = MagicMock()
    choice.message = message
    response = MagicMock()
    response.choices = [choice]
    return response


class TestGetNextAction:

    def _make_policy(self):
        patcher = patch("policy.deepseek.AsyncOpenAI")
        MockClient = patcher.start()
        mock_instance = MagicMock()
        mock_instance.close = AsyncMock()
        MockClient.return_value = mock_instance
        policy = DeepSeekPolicy(api_key="test-key")
        return policy, mock_instance, patcher

    def _ledger_with_one_state(self):
        ledger = Ledger()
        state_id = ledger.add_state(make_proof_state(["n = n"]))
        return ledger, state_id

    async def test_returns_parsed_director_response(self):
        policy, client, patcher = self._make_policy()
        try:
            raw = json.dumps({"chosen_state": "will-be-overridden", "tactic": "simp"})
            client.chat.completions.create = AsyncMock(return_value=_make_api_response(raw))
            ledger, state_id = self._ledger_with_one_state()

            resp = await policy.get_next_action("theorem foo := by", ledger, [])
            assert isinstance(resp, DirectorResponse)
            assert resp.tactic == "simp"
        finally:
            patcher.stop()

    async def test_reasoning_flows_through_to_response_and_ledger(self):
        policy, client, patcher = self._make_policy()
        try:
            raw = json.dumps({
                "reasoning": "Close the reflexive goal directly.",
                "chosen_state": "will-be-overridden",
                "tactic": "rfl",
            })
            client.chat.completions.create = AsyncMock(return_value=_make_api_response(raw))
            ledger, state_id = self._ledger_with_one_state()

            resp = await policy.get_next_action("theorem foo := by", ledger, [])
            assert resp.reasoning == "Close the reflexive goal directly."

            # The caller (LedgerSearch) is responsible for persisting this into
            # the ledger — get_next_action itself only returns it.
            ledger.set_reasoning(resp.chosen_state_id, resp.reasoning)
            assert ledger.reasoning[resp.chosen_state_id] == "Close the reflexive goal directly."
        finally:
            patcher.stop()

    async def test_uses_director_system_prompt(self):
        policy, client, patcher = self._make_policy()
        try:
            raw = json.dumps({"chosen_state": "x", "tactic": "simp"})
            client.chat.completions.create = AsyncMock(return_value=_make_api_response(raw))
            ledger, _ = self._ledger_with_one_state()

            await policy.get_next_action("theorem foo := by", ledger, [])

            _, kwargs = client.chat.completions.create.call_args
            assert kwargs["messages"][0]["content"] == DIRECTOR_SYSTEM_PROMPT
        finally:
            patcher.stop()

    async def test_uses_director_max_tokens_not_regular_max_tokens(self):
        patcher = patch("policy.deepseek.AsyncOpenAI")
        MockClient = patcher.start()
        mock_instance = MagicMock()
        mock_instance.close = AsyncMock()
        MockClient.return_value = mock_instance
        policy = DeepSeekPolicy(api_key="test-key", max_tokens=256, director_max_tokens=999)
        try:
            raw = json.dumps({"chosen_state": "x", "tactic": "simp"})
            mock_instance.chat.completions.create = AsyncMock(
                return_value=_make_api_response(raw)
            )
            ledger, _ = self._ledger_with_one_state()

            await policy.get_next_action("theorem foo := by", ledger, [])

            _, kwargs = mock_instance.chat.completions.create.call_args
            assert kwargs["max_tokens"] == 999
        finally:
            patcher.stop()

    async def test_thinking_disabled_by_default_for_director_call(self):
        policy, client, patcher = self._make_policy()
        try:
            raw = json.dumps({"chosen_state": "x", "tactic": "simp"})
            client.chat.completions.create = AsyncMock(return_value=_make_api_response(raw))
            ledger, _ = self._ledger_with_one_state()

            await policy.get_next_action("theorem foo := by", ledger, [])

            _, kwargs = client.chat.completions.create.call_args
            assert kwargs["extra_body"]["thinking"] == {"type": "disabled"}
        finally:
            patcher.stop()

    async def test_falls_back_gracefully_on_api_failure(self):
        policy, client, patcher = self._make_policy()
        try:
            client.chat.completions.create = AsyncMock(side_effect=Exception("network error"))
            ledger, state_id = self._ledger_with_one_state()

            resp = await policy.get_next_action("theorem foo := by", ledger, [])

            assert resp.chosen_state_id == state_id
            assert resp.abandoned_state_ids == []
            assert resp.tactic == "simp"
        finally:
            patcher.stop()
