"""
Base class for LLM-backed director policies.

Handles ledger serialization, response parsing, and the get_next_action()
interface. Subclasses only need to implement _call_api() and close().

Shared by AnthropicPolicy, DeepSeekPolicy, ClaudeCLIPolicy, and any future
LLM backend.
"""

from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass

from core.ledger import Ledger

logger = logging.getLogger(__name__)

# A single failed director call is worth absorbing — one dropped connection
# should not end a search that is otherwise going fine. A *run* of them is a
# different thing: an exhausted credit balance, a revoked key or a wrong model
# name fails identically on every call, and the "simp" fallback then quietly
# turns the rest of the budget into meaningless turns while still costing
# wall-clock time and producing a trace full of noise. After this many
# consecutive failures the error is raised instead, so the run stops with the
# real reason visible.
_MAX_CONSECUTIVE_API_FAILURES = 3


DIRECTOR_SYSTEM_PROMPT = (
    "You are an expert Lean 4 theorem prover assistant guiding a proof "
    "search. You will be shown the currently open proof states (the "
    "frontier) and a summary of dead-end attempts already tried. If there "
    "are more open states than fit, the list says so and shows the "
    "deepest ones, so the frontier may hold more than you can see. Your "
    "job is to decide where to focus next.\n"
    "\n"
    # The director call is stateless: one user message, no conversation
    # history (see policy/anthropic.py). The model was never told so, and
    # had no reason to treat `reasoning` as anything but narration — yet
    # that field is the only channel between turns.
    "You have no memory of previous turns. Each turn you are shown the "
    "search's recorded state and nothing else — you did not \"just\" do "
    "anything, and you cannot recall what you were thinking. Everything "
    "below about what to write down follows from that.\n"
    "\n"
    "Rules:\n"
    "- First, in \"reasoning\", think through the actual mathematical "
    "strategy for the chosen state — the real argument (case split, key "
    "inequality, sub-lemma, contradiction, WLOG reduction, etc.), not "
    "just which Lean tactic to try next. Write it as a note to someone "
    "who will read it later with no memory of you: it is the ONLY thing "
    "you can pass to a future turn that is not visible in the goal text. "
    "If you work out that an approach cannot succeed — a substitution "
    "that collapses to a tautology, a lemma that is false — say so "
    "plainly there. That is worth more than the plan it replaces.\n"
    "- Choose exactly one state (\"chosen_state\") to continue from. Copy "
    "its id exactly as shown in the state's bracket label, e.g. for "
    "\"[state a1b2c3d4]\" use \"a1b2c3d4\" — do not include the word \"state\" "
    "or the brackets. You may choose any state in \"Currently Open States\" "
    "or in \"Abandoned States\", and nothing else.\n"
    "- You may abandon any open state you believe is a dead end — list "
    "its id in \"abandon\" with a brief \"abandon_reason\". Do not abandon a "
    "state just because a few tactics failed on it; only abandon it if "
    "you believe the overall approach that led there is wrong. Never put "
    "the same id in both \"abandon\" and \"chosen_state\" — choosing a state "
    "means you want to keep working on it. Abandoning is reversible: "
    "abandoned states are listed with the reason you gave, and naming one "
    "as \"chosen_state\" resumes it exactly where it was left. The reason "
    "you write is kept and shown, so make it the finding, not a label.\n"
    "- Propose exactly ONE tactic for the chosen state. Check BOTH lists "
    "shown for that state first. Never propose a tactic that appears "
    "verbatim in \"Tactics already tried here\" — those failed, and will "
    "fail the same way again. Each failed tactic is shown with Lean's "
    "actual error message (marked with \"→\") — read it before retrying a "
    "similar idea: it tells you the real reason (wrong lemma name, wrong "
    "argument shape, type mismatch, etc.), which is far more useful than "
    "guessing again blindly. Likewise never re-propose a tactic listed "
    "under \"Tactics already APPLIED SUCCESSFULLY here\": a state stays "
    "open after being expanded so you can come back to it, so re-running "
    "a tactic that already worked just re-derives the exact same state "
    "and wastes the turn — to build on that work, choose the resulting "
    "state instead.\n"
    "- Your tactic must be syntactically valid Lean 4, with no "
    "explanations, numbering, backticks, or code fences.\n"
    # This rule used to read "a tactic applies to the FIRST goal only, so
    # the goals are worked through in order". False as a claim about
    # tactics — all_goals, on_goal, case and rotate_left are themselves
    # tactics — and the model obeyed it: 9 goal-selection tactics in 3025
    # sent. imo2026_q5 then spent ~24 turns on a false goal 1 with both
    # halves of the theorem untouched behind it. Verified live:
    # case/on_goal/all_goals/any_goals act without reordering, while
    # pick_goal/rotate_*/swap permute the tuple — and stable_hash is
    # order-sensitive, so those spawn duplicate nodes.
    "- A state may hold SEVERAL goals, shown as \"Goal 1/3\", \"Goal 2/3\", … "
    "and often carrying a Lean case tag such as \"case hconst\". ALL of "
    "them must eventually be proved — the state is finished only when "
    "every goal is closed — so closing any one of them is progress, in "
    "whatever order you like.\n"
    "  By default a tactic acts on the FIRST goal. You are not restricted "
    "to it. To work on another goal, use ordinary Lean tactics:\n"
    "      case <tag> => tac    act on the goal carrying that case tag\n"
    "      on_goal n => tac     act on goal n\n"
    "      all_goals tac        act on every goal; fails unless it works on all\n"
    "      any_goals tac        act on every goal; keeps whatever succeeds\n"
    "  Prefer these: they leave the goal order alone. `pick_goal n`, "
    "`rotate_left` and `swap` also work but reorder the list, which "
    "produces a state that duplicates work already recorded elsewhere, so "
    "reach for them last.\n"
    "- To combine several steps inside your one tactic:\n"
    "      tac1; tac2           run tac1, then tac2 on whatever goal is FIRST afterwards — which may be a different goal, e.g. if tac1 closed the one it acted on\n"
    "      tac1 <;> tac2        run tac2 on every goal tac1 PRODUCED (none, if tac1 produced none — not the same as all_goals)\n"
    "      first | tac1 | tac2  try alternatives in order; hedge with this rather than describing several plans, as there is one slot\n"
    "      try tac              run tac, tolerate failure\n"
    "      (tac1; tac2)         group, e.g. inside `on_goal n => (…)`\n"
    "  If a step in a ';' chain fails, the error you see next turn says "
    "which step it was, and the steps before it are kept.\n"
    "- To establish an intermediate fact, write `have name : statement` "
    "with NO `:= by ...` proof attached. That opens `statement` as a new "
    "goal you can then prove step by step over the following turns, and "
    "hands the original goal `name` as a usable hypothesis. Strongly "
    "prefer this over `have name : statement := by <several tactics>` "
    "whenever the sub-proof is not a confident one-liner: everything "
    "after `by` is verified as one atomic unit, so a single mistake "
    "anywhere inside it discards the whole attempt and tells you only one "
    "error — while a bare `have` lets you attack the sub-goal "
    "incrementally, with real error feedback on every step, and keeps the "
    "progress you have already made. This is also the only way to build a "
    "reusable lemma you intend to apply more than once.\n"
    # imo2026_q5: `hconst` was false for the functions the theorem
    # characterises — substituting f t = t + c reduces it to
    # 0 <= 2c(y-x), which fails when y < x. The model suspected it at
    # turn 45 and kept going; the state from before the `have` was open
    # and displayed the whole time.
    "- A `have` you have not yet proved is a claim, not a fact. Before "
    "committing turns to it, check it: if the theorem tells you the "
    "answer's shape, substitute that shape in and see whether your claim "
    "survives. If a goal has resisted many different tactics, treat \"my "
    "claim is false\" as a live possibility alongside \"I have not found "
    "the right tactic\" — a false claim can never be closed, however many "
    "tactics you try. When that happens you can work a different goal in "
    "the same state, or choose the state from before you introduced the "
    "claim and state a corrected one.\n"
    "- NEVER write `sorry` or `admit`, anywhere in a tactic — not as a "
    "step, not inside `:= by ...`, and not as a `first | ... | sorry` "
    "fallback. Such a tactic is rejected without being run, so the whole "
    "turn is lost, including any legitimate steps chained before it. When "
    "you want to defer part of the work, use the bare `have` above "
    "instead: that is the supported way to say \"I will prove this later\", "
    "and unlike `sorry` it keeps the sub-goal open and tracked for you.\n"
    "- Respond with JSON only, matching exactly this shape:\n"
    "{\"reasoning\": \"<your natural-language plan for the chosen state>\", "
    "\"abandon\": [\"<state_id>\", ...], \"abandon_reason\": \"<brief reason, or "
    "empty string if abandon is empty>\", \"chosen_state\": \"<state_id>\", "
    "\"tactic\": \"<your single tactic, or ;-chained sequence>\"}"
)


@dataclass
class DirectorResponse:
    """
    The director's decision for one turn of ledger-guided search: which open
    state to continue from (and which, if any, to give up on), plus the
    single tactic to try there.

    Attributes:
        reasoning: The director's stated natural-language plan for the
                   chosen state this turn. Persisted in the Ledger and shown
                   back on future turns (see Ledger.set_reasoning), so the
                   model's own prior plan for a branch isn't lost between
                   calls the way its hidden reasoning tokens are.
        tactic: The single tactic string to try (may itself be a ';'-chained
                sequence, or use Lean's `first | ... | ...` to hedge). There
                is deliberately no k-candidates-per-turn mechanism: proposing
                several independent tactics per turn let the model encode a
                sequential plan as if it were several parallel hedges, which
                spawned one permanent frontier branch per proposal and caused
                uncontrolled, untriaged branching ("tree poisoning").
    """
    chosen_state_id: str
    abandoned_state_ids: list[str]
    tactic: str
    reasoning: str = ""
    # Why the abandoned states were given up on. The prompt has always asked
    # for this field; until now it was parsed nowhere and discarded, so the
    # information was requested from the model every turn and thrown away.
    # It is what labels each entry in the resumable-abandoned-states list.
    abandon_reason: str = ""


_MAX_TRIED_TACTICS_SHOWN = 15
# Outlier guard, not a routine trim. This was 100, which truncated 18% of all
# tactics ever sent (486 of 2688) while the prompt tells the director "do not
# repeat verbatim" and "read the error before retrying a similar idea" — it
# cannot do either against a clipped tactic. Measured across the traces, 44
# distinct tactics rendered IDENTICALLY to another attempt on the same state
# once cut at 100. Raising it to 600 (past the 722-char worst case seen) costs
# ~1% of prompt size: only 12 lines in a 100K-char turn-50 prompt were
# truncated at all, because _MAX_TRIED_TACTICS_SHOWN already bounds the volume.
# Capping HOW MANY entries are shown controls size; capping how long each one
# is controls almost nothing and deletes the distinguishing tail.
_MAX_TACTIC_DISPLAY_LEN = 600
# Abandon reasons are PROSE, not tactics, and used to share the cap above.
# At 100 that truncated 93% of them (1567 of 1674 written across all runs),
# discarding 187,683 characters of the director's own explanations — and since
# a sentence puts its conclusion last, it kept the setup and cut the finding.
# One real example, imo2026_q5 turn 37, where the model had written exactly the
# durable result we later went looking for a place to store:
#   full: "diagonal x=y=z substitutions into hcross/hqm are provably
#          degenerate, only ever yielding trivial (f(z)-z)^2>=0; need
#          asymmetric substitution instead"
#   shown: "...only ever yielding trivial …"     <- both the tautology and the
#                                                   remedy cut off
# At 400 only 2% truncate (p90 is 320 chars); the list is already capped at
# _MAX_RETIRED_STATES_SHOWN entries, so the worst case is ~2% of prompt size.
_MAX_ABANDON_REASON_DISPLAY_LEN = 400
# Cap on the resumable-abandoned list. Each entry is one short line (no goal
# text), so this is far cheaper than the open-state cap — but one observed run
# retired 52 states, and an uncapped list would grow for the whole search.
_MAX_RETIRED_STATES_SHOWN = 25
# Cap on how many open states get shown at once. Without this, the frontier
# can grow unboundedly — e.g. once every verified sub-step of a chained
# candidate becomes its own frontier state — and showing all of them would
# reproduce the same runaway-prompt-size problem as the tactic-eviction cap
# (a single turn's prompt once reached ~120K characters before that was
# fixed). When over budget, the deepest (most-progressed) states are kept,
# since they represent the most work already verified.
_MAX_OPEN_STATES_SHOWN = 20
# Bare/generic tactics (e.g. "omega", "simp", "ring") are cheap to remember
# and exactly the ones most likely to be blindly retried once they age out
# of a recency-capped list — so they're never evicted, regardless of order.
_SHORT_TACTIC_MAX_LEN = 30
# Generous cap on the raw Lean error shown per tactic: full text for the
# common case (type mismatch, unknown identifier, unsolved goals are
# normally well under this), truncated only for pathological outliers like
# apply?/exact? dumping dozens of "Try this" suggestions onto one line.
_MAX_ERROR_DISPLAY_LEN = 2000


def _format_tactic_for_display(tactic: str) -> str:
    """Collapse a (possibly multi-line) tactic to one truncated display line."""
    oneline = " ".join(tactic.split())
    if len(oneline) > _MAX_TACTIC_DISPLAY_LEN:
        return oneline[:_MAX_TACTIC_DISPLAY_LEN] + "…"
    return oneline


def _format_reason_for_display(reason: str) -> str:
    """Collapse an abandon reason to one line, capped as prose not as a tactic."""
    oneline = " ".join(reason.split())
    if len(oneline) > _MAX_ABANDON_REASON_DISPLAY_LEN:
        return oneline[:_MAX_ABANDON_REASON_DISPLAY_LEN] + "…"
    return oneline


def _format_error_for_display(error: str) -> str:
    """Cap a raw Lean error to a generous length rather than a category label."""
    text = error.strip()
    if len(text) > _MAX_ERROR_DISPLAY_LEN:
        return text[:_MAX_ERROR_DISPLAY_LEN] + "… [truncated]"
    return text


def serialize_ledger(
    theorem: str,
    ledger: Ledger,
    premises: list[str],
) -> str:
    """
    Render a Ledger into prompt text for the director call.

    Lists every open state with the tactic path that reached it, then a
    per-state summary of failed attempts: category counts plus the specific
    tactic strings already tried (deduplicated, most-recent-first, capped),
    so the model can check "have I already tried this" before re-proposing
    a tactic verbatim rather than only seeing an aggregate failure count.
    Abandoned states are listed compactly — id, goal count, depth and the
    reason given — but WITHOUT their goal text, so they stay resumable
    without costing the context a full state would. They used to be omitted
    entirely, which made abandonment a one-way door: the search can restore a
    state the director re-selects, but the director had no way to name one it
    could no longer see. In practice it named them anyway, by reading ids out
    of its own persisted reasoning prose — 13 of 1953 turns across our traces
    chose an id that appeared ONLY in that prose. That was us leaking stale
    ids and then treating the resulting selection as a mistake.
    """
    parts = [f"## Theorem\n\n{theorem}\n"]

    all_open = list(ledger.frontier.items())
    if len(all_open) > _MAX_OPEN_STATES_SHOWN:
        # Stable sort: ties keep their original (insertion) order, so
        # among equal-depth states the more-recently-added ones win.
        shown_open = sorted(all_open, key=lambda kv: -kv[1].depth)[:_MAX_OPEN_STATES_SHOWN]
        omitted = len(all_open) - len(shown_open)
        parts.append(
            f"\n## Currently Open States "
            f"(showing {len(shown_open)} of {len(all_open)}, deepest first — "
            f"{omitted} shallower state(s) omitted)\n"
        )
    else:
        shown_open = all_open
        parts.append("\n## Currently Open States\n")

    shown_state_ids = {state_id for state_id, _ in shown_open}

    # Successful expansions, keyed by the state they were applied to. A
    # state stays in the frontier after being expanded (so it can be
    # backtracked to), and re-applying a tactic that already worked lands
    # on the identical child id — so without showing this, the director
    # has no way to tell it already tried that tactic here and can loop
    # re-deriving the same step until the budget runs out.
    done_by_parent: dict[str, list] = {}
    for entry in ledger.entries:
        if entry.outcome == "success" and entry.parent_id in shown_state_ids:
            done_by_parent.setdefault(entry.parent_id, []).append(entry)

    for state_id, state in shown_open:
        path = ", ".join(state.tactic_trace) if state.tactic_trace else "(root)"
        parts.append(f"\n[state {state_id}] (path: {path})\n{state.serialize()}\n")
        # Every plan ever stated for this state, oldest first, with the turn
        # that wrote it. The turn numbers are the ONLY temporal information
        # anywhere in this prompt — the director call carries no conversation
        # history, so without them a refutation from thirty turns ago is
        # indistinguishable from the thought it had a moment before.
        history = ledger.reasoning.get(state_id) or []
        if history:
            lines = "\n".join(f"  - Turn {n}: {text}" for n, text in history)
            label = (
                "Stated plan for this state:"
                if len(history) == 1
                else "Stated plans for this state, oldest first "
                     "(earlier conclusions still hold unless refuted):"
            )
            parts.append(f"{label}\n{lines}\n")
        applied = done_by_parent.get(state_id)
        if applied:
            seen_applied: list[tuple[str, str]] = []
            for e in applied:
                key = (e.tactic, e.child_id or "")
                if key not in seen_applied:
                    seen_applied.append(key)
            lines = "\n".join(
                f"  - {_format_tactic_for_display(t)} → produced state {cid}"
                for t, cid in seen_applied[-_MAX_TRIED_TACTICS_SHOWN:]
            )
            parts.append(
                "Tactics already APPLIED SUCCESSFULLY here — re-running one "
                "just re-derives the same state, so continue from the "
                "resulting state instead:\n"
                f"{lines}\n"
            )

    # Abandoned-but-resumable states. Compact by design: id, size, depth and
    # the director's own reason — no goal text, so a long-running search that
    # has parked dozens of branches costs a few hundred bytes rather than
    # re-rendering every state it ever pruned. Deepest first, matching how
    # open states are ordered, and capped for the same runaway-prompt reason.
    if ledger.retired:
        retired = sorted(
            ledger.retired.items(), key=lambda kv: -kv[1].depth
        )[:_MAX_RETIRED_STATES_SHOWN]
        total = len(ledger.retired)
        header = "\n## Abandoned States (resumable — name the id as chosen_state)\n"
        if total > len(retired):
            header = (
                f"\n## Abandoned States (resumable — name the id as "
                f"chosen_state; showing {len(retired)} of {total}, deepest "
                f"first)\n"
            )
        parts.append(header)
        for sid, st in retired:
            n = len(st.goals)
            why = ledger.abandon_reasons.get(sid, "")
            why = f' — "{_format_reason_for_display(why)}"' if why else ""
            parts.append(
                f"  {sid}  {n} goal{'s' if n != 1 else ''}  depth {st.depth}{why}\n"
            )

    dead_by_parent: dict[str, list] = {}
    for entry in ledger.entries:
        if entry.outcome != "success" and entry.parent_id in shown_state_ids:
            dead_by_parent.setdefault(entry.parent_id, []).append(entry)

    if dead_by_parent:
        parts.append("\n## Exhausted Attempts (context — do not blindly repeat)\n")
        for state_id, failures in dead_by_parent.items():
            # Count only — deliberately NO error-category breakdown. There
            # used to be a substring-matching categoriser; audited over 2847
            # real Lean errors from our own traces it had two branches that
            # never fired once (they tested for "maximum heart beats" and
            # "failed to synthesize"; Lean actually says "maximum number of
            # heartbeats" and "typeclass instance problem is stuck") and a
            # catch-all holding a third of everything, filing 287 genuine
            # refutations alongside 43 resource failures. A wrong label next
            # to the raw error is worse than no label: a resource failure
            # shown as "tactic_failed" reads as evidence the goal is
            # unprovable, and a director was observed abandoning a TRUE lemma
            # (Imo2005Q3's key_insight) on exactly that reading. It has since
            # been deleted outright — the raw Lean error printed under each
            # tactic below is the ground truth, uncompressed.
            noun = "tactic" if len(failures) == 1 else "tactics"
            parts.append(
                f"\nstate {state_id}: {len(failures)} {noun} tried, all failed\n"
            )

            seen: list[str] = []
            errors_by_tactic: dict[str, str] = {}
            for f in failures:
                if f.tactic not in seen:
                    seen.append(f.tactic)
                    errors_by_tactic[f.tactic] = f.error

            # Short/generic tactics are never evicted — they're cheap to
            # keep and exactly the ones a recency cap would otherwise drop
            # right before the model blindly re-tries them (e.g. "omega"
            # tried once long ago, then proposed again once it ages out).
            short = {t for t in seen if len(t) <= _SHORT_TACTIC_MAX_LEN}
            long_recent_budget = max(_MAX_TRIED_TACTICS_SHOWN - len(short), 0)
            long_tactics = [t for t in seen if t not in short]
            # `long_tactics[-0:]` is the WHOLE list, not empty — Python
            # treats -0 as 0, so a naive negative slice here silently
            # disables the cap entirely once short tactics alone reach the
            # display budget. Must special-case zero explicitly.
            kept_long = set(long_tactics[-long_recent_budget:] if long_recent_budget else [])
            shown = [t for t in seen if t in short or t in kept_long]

            tactic_lines = []
            for t in shown:
                line = f"  - {_format_tactic_for_display(t)}"
                err = errors_by_tactic.get(t, "")
                if err:
                    line += f"\n    → {_format_error_for_display(err)}"
                tactic_lines.append(line)
            tactic_lines = "\n".join(tactic_lines)
            omitted_note = (
                f" (showing {len(shown)} of {len(seen)} unique)"
                if len(seen) > len(shown)
                else ""
            )
            parts.append(
                f"Tactics already tried here{omitted_note} — do not repeat verbatim:\n"
                f"{tactic_lines}"
            )

    if premises:
        lemma_block = "\n".join(f"- {p}" for p in premises)
        parts.append(f"\n\n## Potentially Relevant Lemmas\n\n{lemma_block}")

    parts.append(
        f"\n\n## Task\n\n"
        f"Choose exactly one state to continue from — open, or one you "
        f"abandoned earlier — optionally abandon any you consider dead ends, "
        f"and propose exactly one tactic for your chosen state."
    )
    return "".join(parts)


# Matches the body of a JSON string (between its quotes): any run of
# non-quote/non-backslash characters, or a backslash followed by one
# escaped character (\", \\, \n, the two hex digits of a \uXXXX escape
# consumed one at a time by the [^"\\] branch, etc.).
_JSON_STRING_BODY = r'(?:[^"\\]|\\.)*'


def _json_unescape(raw: str) -> str:
    """Decode a JSON string body (no surrounding quotes) via json.loads,
    falling back to the raw text if it contains a dangling escape (e.g. a
    \\uXXXX cut off mid-sequence by truncation)."""
    try:
        return json.loads(f'"{raw}"')
    except json.JSONDecodeError:
        return raw


def _find_matching_bracket(text: str, open_pos: int, open_ch: str, close_ch: str) -> int | None:
    """
    Find the index of the close_ch matching the open_ch at text[open_pos],
    tracking string context so a close_ch inside a quoted string (e.g. the
    ']' inside a tactic like "nlinarith [h1, h2]") isn't mistaken for the
    real closing bracket. Returns None if the text ends first (the array
    was truncated before it closed).
    """
    depth = 1
    in_string = False
    i = open_pos + 1
    while i < len(text):
        c = text[i]
        if in_string:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_string = False
        else:
            if c == '"':
                in_string = True
            elif c == open_ch:
                depth += 1
            elif c == close_ch:
                depth -= 1
                if depth == 0:
                    return i
        i += 1
    return None


def _extract_json_string_field(text: str, key: str) -> str | None:
    """
    Regex-recover a single string field's value from malformed or
    truncated JSON, once a strict json.loads on the full response has
    already failed. Handles two shapes seen in practice: (1) the field
    itself is intact but something *else* in the response is broken (extra
    trailing content, a stray bracket, a missing final '}') — the
    closing-quote-anchored regex recovers it whole; (2) the response was
    cut off by the token budget mid-string, so there is no closing quote
    before the text ends — the second regex recovers whatever text came
    through before the cutoff instead of discarding it.
    """
    m = re.search(rf'"{key}"\s*:\s*"({_JSON_STRING_BODY})"', text)
    if m:
        return _json_unescape(m.group(1))
    m = re.search(rf'"{key}"\s*:\s*"({_JSON_STRING_BODY})$', text, re.DOTALL)
    if m:
        return m.group(1)
    return None


def _extract_complete_json_string_field(text: str, key: str) -> str | None:
    """
    Like _extract_json_string_field, but only accepts a value that reached
    its closing quote — never a partial value salvaged from a mid-string
    cutoff. Used for the tactic field: a tactic string truncated mid-write
    is overwhelmingly likely to be invalid Lean syntax (unlike partial
    reasoning prose, which is still useful even cut off), so there is
    nothing worth salvaging — falling back to "simp" is strictly better
    than handing the executor a guaranteed-broken tactic string.
    """
    m = re.search(rf'"{key}"\s*:\s*"({_JSON_STRING_BODY})"', text)
    return _json_unescape(m.group(1)) if m else None


def _extract_json_string_array_field(text: str, key: str) -> list[str] | None:
    """
    Regex-recover a string-array field's elements the same way — e.g. a
    tactics array that never got its closing ']' still yields every
    complete tactic string that came through before the cutoff (only a
    final, mid-write element is dropped). Also tolerates trailing garbage
    after a *properly* closed array, a shape seen when the model appends
    an extra element outside the array by mistake.
    """
    m = re.search(rf'"{key}"\s*:\s*\[', text)
    if not m:
        return None
    open_pos = m.end() - 1
    close = _find_matching_bracket(text, open_pos, "[", "]")
    body = text[open_pos + 1:close] if close is not None else text[open_pos + 1:]
    return [_json_unescape(g) for g in re.findall(rf'"({_JSON_STRING_BODY})"', body)]


def parse_director_response(text: str, fallback_state_id: str) -> DirectorResponse:
    """
    Parse the director's JSON response.

    Tries a strict json.loads first. If that fails — most often because
    the response was cut off before its closing brace, or the model wrote
    slightly malformed JSON around an otherwise-intact tactic string —
    falls back to regex-recovering each field independently, so a
    truncated or garbled response doesn't discard reasoning and a tactic
    that actually came through intact. Only returns the "simp" fallback
    tactic when nothing usable can be recovered at all. Never raises.
    """
    data = None
    try:
        start = text.index("{")
        end = text.rindex("}") + 1
        data = json.loads(text[start:end])
    except (ValueError, json.JSONDecodeError):
        pass

    chosen = abandoned = reasoning = tactic = None
    abandon_reason = None
    if isinstance(data, dict):
        try:
            chosen = data.get("chosen_state")
            chosen = chosen if isinstance(chosen, str) and chosen else None
            abandon_field = data.get("abandon", [])
            abandoned = [s for s in abandon_field if isinstance(s, str)] if isinstance(abandon_field, list) else None
            reasoning = data.get("reasoning")
            reasoning = reasoning if isinstance(reasoning, str) else None
            tactic_field = data.get("tactic")
            tactic = tactic_field if isinstance(tactic_field, str) and tactic_field.strip() else None
            ar = data.get("abandon_reason")
            abandon_reason = ar if isinstance(ar, str) else None
        except (KeyError, TypeError):
            pass
    abandoned = abandoned or []

    if chosen is None:
        chosen = _extract_json_string_field(text, "chosen_state")
    if reasoning is None:
        reasoning = _extract_json_string_field(text, "reasoning")
    if not tactic:
        recovered = _extract_complete_json_string_field(text, "tactic")
        if recovered and recovered.strip():
            tactic = recovered
    if not abandoned:
        recovered_abandon = _extract_json_string_array_field(text, "abandon")
        if recovered_abandon:
            abandoned = recovered_abandon
    if abandon_reason is None:
        abandon_reason = _extract_json_string_field(text, "abandon_reason")

    return DirectorResponse(
        chosen_state_id=chosen or fallback_state_id,
        abandoned_state_ids=abandoned,
        tactic=tactic or "simp",
        reasoning=reasoning or "",
        abandon_reason=abandon_reason or "",
    )


class BaseLLMPolicy:
    """
    Shared logic for LLM-backed director policies.

    Subclasses implement _call_api() to handle the provider-specific API call.
    get_next_action() handles ledger serialization, parsing, and error
    fallback.
    """

    def __init__(
        self,
        model: str,
        max_tokens: int = 256,
        temperature: float = 1.0,
        director_max_tokens: int = 16000,
        director_thinking: bool = False,
    ):
        self._model = model
        self._max_tokens = max_tokens
        self._temperature = temperature
        # The director call (get_next_action) reasons over a growing ledger
        # rather than one isolated goal, so it gets its own token budget and
        # its own thinking toggle. Left off by default until the ledger
        # mechanism itself is validated — see get_next_action.
        self._director_max_tokens = director_max_tokens
        self._director_thinking = director_thinking
        self._consecutive_api_failures = 0

    async def get_next_action(
        self,
        theorem: str,
        ledger: Ledger,
        premises: list[str],
    ) -> DirectorResponse:
        """
        Ask the LLM to choose which open state to continue from (or abandon),
        and propose a single tactic for its choice.

        Absorbs an isolated API failure — falls back to continuing an
        arbitrary frontier state with a "simp" tactic — so one dropped
        connection cannot end an otherwise healthy search. But it does NOT
        absorb a persistent one: after _MAX_CONSECUTIVE_API_FAILURES failures
        in a row the exception is re-raised, because a condition that fails
        every call (spent credits, bad key, wrong model) would otherwise turn
        the rest of the budget into "simp" turns that cost time and teach
        nothing, with no indication in the output of what went wrong.

        Requires a non-empty ledger.frontier; callers are responsible for
        stopping the search once the frontier is empty.
        """
        fallback_id = next(iter(ledger.frontier))
        user_prompt = serialize_ledger(theorem, ledger, premises)
        try:
            raw_text = await self._call_api(
                user_prompt,
                system_prompt=DIRECTOR_SYSTEM_PROMPT,
                max_tokens=self._director_max_tokens,
                enable_thinking=self._director_thinking,
            )
        except Exception as e:
            self._consecutive_api_failures += 1
            logger.warning(
                "director API call failed (%d in a row): %s: %s",
                self._consecutive_api_failures, type(e).__name__, e,
            )
            if self._consecutive_api_failures >= _MAX_CONSECUTIVE_API_FAILURES:
                raise
            return DirectorResponse(
                chosen_state_id=fallback_id,
                abandoned_state_ids=[],
                tactic="simp",
            )
        self._consecutive_api_failures = 0
        return parse_director_response(raw_text, fallback_id)

    async def _call_api(
        self,
        user_prompt: str,
        system_prompt: str = DIRECTOR_SYSTEM_PROMPT,
        max_tokens: int | None = None,
        enable_thinking: bool = False,
    ) -> str:
        """Call the provider API and return the raw response text."""
        raise NotImplementedError

    async def close(self) -> None:
        pass
