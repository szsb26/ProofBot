"""
Base class for LLM-backed tactic policies.

Handles prompt construction, response parsing, and the get_tactics() interface.
Subclasses only need to implement _call_api() and close().

Shared by AnthropicPolicy, DeepSeekPolicy, and any future LLM backend.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass

from core.ledger import Ledger
from core.policy import TacticCandidate
from core.proof_state import ProofState


SYSTEM_PROMPT = (
    "You are an expert Lean 4 theorem prover assistant. "
    "Given a proof state, output tactic candidates that could make progress "
    "toward closing the proof.\n\n"
    "Rules:\n"
    "- Output exactly one Lean 4 tactic per line, with no other text.\n"
    "- Order tactics from most likely to succeed to least likely.\n"
    "- Do not include explanations, numbering, backticks, or code fences.\n"
    "- Each line must be a single, syntactically valid Lean 4 tactic.\n"
    "- For goals starting with `∀`, always put `intro` tactics first — introduce "
    "all bound variables in one step (e.g. `intro n` for `∀ n : ℕ`, or "
    "`intro a b` for `∀ a b : Int`). Never apply ring/simp/omega to a `∀` goal "
    "without introducing variables first.\n"
    "- If you cannot generate enough distinct tactics, repeat your best guess "
    "rather than outputting fewer lines."
)


def build_user_prompt(state: ProofState, premises: list[str], k: int) -> str:
    parts = ["## Current Proof State\n\n", state.serialize()]
    if premises:
        lemma_block = "\n".join(f"- {p}" for p in premises)
        parts.append(f"\n\n## Potentially Relevant Lemmas\n\n{lemma_block}")
    parts.append(
        f"\n\n## Task\n\n"
        f"Generate exactly {k} tactic candidates, one per line, ordered from "
        f"most to least promising:"
    )
    return "".join(parts)


def parse_tactics(text: str, k: int) -> list[str]:
    """
    Extract clean tactic strings from a raw LLM response.

    Strips leading numbering (e.g. "1." or "1)"), backticks, and blank lines.
    Deduplicates while preserving order. Falls back to ["simp"] if nothing
    parseable is found.
    """
    lines: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line[0].isdigit():
            line = line.lstrip("0123456789").lstrip(". )").strip()
        elif line.startswith("- "):
            line = line[2:].strip()
        line = line.strip("`").strip()
        if line:
            lines.append(line)

    seen: set[str] = set()
    unique: list[str] = []
    for t in lines:
        if t not in seen:
            seen.add(t)
            unique.append(t)

    return unique[:k] if unique else ["simp"]


DIRECTOR_SYSTEM_PROMPT = (
    "You are an expert Lean 4 theorem prover assistant guiding a proof search. "
    "You will be shown every currently open proof state (the frontier) and a "
    "summary of dead-end attempts already tried. Your job is to decide where "
    "to focus next.\n\n"
    "Rules:\n"
    "- First, in \"reasoning\", think through the actual mathematical "
    "strategy for the chosen state — the real argument (case split, key "
    "inequality, sub-lemma, contradiction, WLOG reduction, etc.), not just "
    "which Lean tactic to try next.\n"
    "- If you are not fully confident of the exact Mathlib lemma name or its "
    "argument order, do not guess a specific identifier — prefer `apply?`, "
    "`exact?`, or a general-purpose tactic (`aesop`, `simp`, `omega`, "
    "`nlinarith`) that can find or verify the step itself instead of naming "
    "a lemma you are unsure of.\n"
    "- You may abandon any open state you believe is a dead end — list its id "
    "in \"abandon\" with a brief \"abandon_reason\". Do not abandon a state "
    "just because a few tactics failed on it; only abandon it if you believe "
    "the overall approach that led there is wrong. Never put the same id in "
    "both \"abandon\" and \"chosen_state\" — choosing a state means you want "
    "to keep working on it.\n"
    "- Choose exactly one open state (\"chosen_state\") to continue from. "
    "Copy its id exactly as shown in the state's bracket label, e.g. for "
    "\"[state a1b2c3d4]\" use \"a1b2c3d4\" — do not include the word \"state\" "
    "or the brackets.\n"
    "- Propose exactly ONE tactic for the chosen state. Check BOTH lists "
    "shown for your chosen state first. Never propose a tactic that appears "
    "verbatim in \"Tactics already tried here\" — those failed, and will "
    "fail the same way again. Each failed tactic is shown with Lean's actual "
    "error message (marked with \"→\") — read it before retrying a similar "
    "idea: it tells you the real reason (wrong lemma name, wrong argument "
    "shape, type mismatch, etc.), which is far more useful than guessing "
    "again blindly. Likewise never re-propose a tactic listed under "
    "\"Tactics already APPLIED SUCCESSFULLY here\": a state stays open after "
    "being expanded so you can come back to it, so re-running a tactic that "
    "already worked just re-derives the exact same state and wastes the "
    "turn — to build on that work, choose the resulting state instead.\n"
    "- Your tactic must be syntactically valid Lean 4, with no explanations, "
    "numbering, backticks, or code fences. You may chain multiple steps with "
    "';' (e.g. \"intro n; simp\") to carry out one sequential plan — each "
    "step is run in sequence and, if one fails, the error you see next turn "
    "will say exactly which step of the chain it was, not just the chain as "
    "a whole. If you genuinely want to hedge between distinct alternatives "
    "rather than commit to one, use Lean's own `first | tac1 | tac2 | ...` "
    "combinator inside your single tactic string, rather than describing "
    "several separate plans — there is only one slot.\n"
    "- A state may hold SEVERAL goals (they are labelled in the state text). "
    "Every tactic applies to the FIRST goal only, so the goals are worked "
    "through in order.\n"
    "- To establish an intermediate fact, write `have name : statement` with "
    "NO `:= by ...` proof attached. That opens `statement` as a new first "
    "goal you can then prove step by step over the following turns, and "
    "hands the original goal `name` as a usable hypothesis. Strongly prefer "
    "this over `have name : statement := by <several tactics>` whenever the "
    "sub-proof is not a confident one-liner: everything after `by` is "
    "verified as one atomic unit, so a single mistake anywhere inside it "
    "discards the whole attempt and tells you only one error — while a bare "
    "`have` lets you attack the sub-goal incrementally, with real error "
    "feedback on every step, and keeps the progress you have already made. "
    "This is also the only way to build a reusable lemma you intend to apply "
    "more than once.\n"
    "- Respond with JSON only, matching exactly this shape:\n"
    '{"reasoning": "<your natural-language plan for the chosen state>", '
    '"abandon": ["<state_id>", ...], "abandon_reason": "<brief reason, or '
    'empty string if abandon is empty>", "chosen_state": "<state_id>", '
    '"tactic": "<your single tactic, or ;-chained sequence>"}'
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


_MAX_TRIED_TACTICS_SHOWN = 15
_MAX_TACTIC_DISPLAY_LEN = 100
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
    Abandoned states are omitted entirely; once given up on, they no longer
    cost context.
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
        plan = ledger.reasoning.get(state_id)
        if plan:
            parts.append(f"Last stated plan for this state: {plan}\n")
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

    dead_by_parent: dict[str, list] = {}
    for entry in ledger.entries:
        if entry.outcome != "success" and entry.parent_id in shown_state_ids:
            dead_by_parent.setdefault(entry.parent_id, []).append(entry)

    if dead_by_parent:
        parts.append("\n## Exhausted Attempts (context — do not blindly repeat)\n")
        for state_id, failures in dead_by_parent.items():
            counts: dict[str, int] = {}
            for f in failures:
                counts[f.outcome] = counts.get(f.outcome, 0) + 1
            summary = ", ".join(
                f"{cat}×{n}" for cat, n in sorted(counts.items(), key=lambda x: -x[1])
            )
            parts.append(
                f"\nstate {state_id}: {len(failures)} tactics tried, all failed — {summary}"
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
        f"Choose exactly one open state to continue from, optionally abandon "
        f"any you consider dead ends, and propose exactly one tactic for "
        f"your chosen state."
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

    return DirectorResponse(
        chosen_state_id=chosen or fallback_state_id,
        abandoned_state_ids=abandoned,
        tactic=tactic or "simp",
        reasoning=reasoning or "",
    )


class BaseLLMPolicy:
    """
    Shared logic for LLM-backed tactic policies.

    Subclasses implement _call_api() to handle the provider-specific API call.
    get_tactics() handles prompt building, parsing, and error fallback.
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

    async def get_tactics(
        self,
        state: ProofState,
        premises: list[str],
        k: int = 8,
    ) -> list[TacticCandidate]:
        """
        Call the LLM with the current proof state and return k tactic candidates.

        Never raises — falls back to [TacticCandidate("simp")] on any error.
        """
        user_prompt = build_user_prompt(state, premises, k)
        try:
            raw_text = await self._call_api(user_prompt)
        except Exception:
            return [TacticCandidate(tactic="simp", log_prob=0.0)]

        tactics = parse_tactics(raw_text, k)
        return [
            TacticCandidate(tactic=t, log_prob=float(-i))
            for i, t in enumerate(tactics)
        ]

    async def get_next_action(
        self,
        theorem: str,
        ledger: Ledger,
        premises: list[str],
    ) -> DirectorResponse:
        """
        Ask the LLM to choose which open state to continue from (or abandon),
        and propose a single tactic for its choice.

        Never raises — falls back to continuing an arbitrary frontier state
        with a "simp" tactic on any error. Requires a non-empty
        ledger.frontier; callers are responsible for stopping the search once
        the frontier is empty.
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
        except Exception:
            return DirectorResponse(
                chosen_state_id=fallback_id,
                abandoned_state_ids=[],
                tactic="simp",
            )
        return parse_director_response(raw_text, fallback_id)

    async def _call_api(
        self,
        user_prompt: str,
        system_prompt: str = SYSTEM_PROMPT,
        max_tokens: int | None = None,
        enable_thinking: bool = False,
    ) -> str:
        """Call the provider API and return the raw response text."""
        raise NotImplementedError

    async def close(self) -> None:
        pass
