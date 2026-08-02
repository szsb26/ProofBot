"""
Base class for LLM-backed tactic policies.

Handles prompt construction, response parsing, and the get_tactics() interface.
Subclasses only need to implement _call_api() and close().

Shared by AnthropicPolicy, DeepSeekPolicy, and any future LLM backend.
"""

from __future__ import annotations

import json
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
    "- First, in \"reasoning\", write a SHORT natural-language plan (2-4 "
    "sentences, never more) : what mathematical fact or proof step you are "
    "trying to establish next at the state you choose, and why you believe "
    "it moves the proof forward. Keep it brief — you have a limited response "
    "budget shared with the rest of this JSON, and an unfinished response is "
    "discarded entirely, so a long reasoning that leaves no room for the "
    "\"tactics\" array is worse than a short one.\n"
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
    "- Propose tactic candidates for the chosen state only, ordered from most "
    "to least promising. Check the \"Tactics already tried here\" list for "
    "your chosen state first — never propose a tactic that already appears "
    "there verbatim, since it is guaranteed to fail the same way again. Each "
    "failed tactic is shown with Lean's actual error message (marked with "
    "\"→\") — read it before retrying a similar idea: it tells you the real "
    "reason (wrong lemma name, wrong argument shape, type mismatch, etc.), "
    "which is far more useful than guessing again blindly.\n"
    "- Each tactic must be a single, syntactically valid Lean 4 tactic, with "
    "no explanations, numbering, backticks, or code fences. You may chain "
    "steps with ';' (e.g. \"intro n; simp\") — each step is run in sequence "
    "and, if one fails, the error you see next turn will say exactly which "
    "step of the chain it was, not just the chain as a whole.\n"
    "- Respond with JSON only, matching exactly this shape:\n"
    '{"reasoning": "<your SHORT natural-language plan for the chosen state>", '
    '"abandon": ["<state_id>", ...], "abandon_reason": "<brief reason, or '
    'empty string if abandon is empty>", "chosen_state": "<state_id>", '
    '"tactics": ["<tactic 1>", "<tactic 2>", ...]}'
)


@dataclass
class DirectorResponse:
    """
    The director's decision for one turn of ledger-guided search: which open
    state to continue from (and which, if any, to give up on), plus tactic
    candidates for the chosen state.

    Attributes:
        reasoning: The director's stated natural-language plan for the
                   chosen state this turn. Persisted in the Ledger and shown
                   back on future turns (see Ledger.set_reasoning), so the
                   model's own prior plan for a branch isn't lost between
                   calls the way its hidden reasoning tokens are.
    """
    chosen_state_id: str
    abandoned_state_ids: list[str]
    tactics: list[TacticCandidate]
    reasoning: str = ""


_MAX_TRIED_TACTICS_SHOWN = 15
_MAX_TACTIC_DISPLAY_LEN = 100
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
    k: int,
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

    parts.append("\n## Currently Open States\n")
    for state_id, state in ledger.frontier.items():
        path = ", ".join(state.tactic_trace) if state.tactic_trace else "(root)"
        parts.append(f"\n[state {state_id}] (path: {path})\n{state.serialize()}\n")
        plan = ledger.reasoning.get(state_id)
        if plan:
            parts.append(f"Last stated plan for this state: {plan}\n")

    dead_by_parent: dict[str, list] = {}
    for entry in ledger.entries:
        if entry.outcome != "success" and entry.parent_id in ledger.frontier:
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
            kept_long = set(
                [t for t in seen if t not in short][-long_recent_budget:]
            )
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
        f"any you consider dead ends, and propose {k} tactic candidates for "
        f"your chosen state."
    )
    return "".join(parts)


def parse_director_response(text: str, k: int, fallback_state_id: str) -> DirectorResponse:
    """
    Parse the director's JSON response.

    Never raises — falls back to continuing fallback_state_id with a single
    ["simp"] candidate on any malformed or missing data, mirroring the
    fallback contract of parse_tactics().
    """
    try:
        start = text.index("{")
        end = text.rindex("}") + 1
        data = json.loads(text[start:end])

        chosen = data.get("chosen_state")
        if not isinstance(chosen, str) or not chosen:
            chosen = fallback_state_id

        abandoned = [s for s in data.get("abandon", []) if isinstance(s, str)]

        reasoning = data.get("reasoning")
        if not isinstance(reasoning, str):
            reasoning = ""

        raw_tactics = [
            t for t in data.get("tactics", [])
            if isinstance(t, str) and t.strip()
        ]
        if not raw_tactics:
            raw_tactics = ["simp"]

        tactics = [
            TacticCandidate(tactic=t, log_prob=float(-i))
            for i, t in enumerate(raw_tactics[:k])
        ]
        return DirectorResponse(
            chosen_state_id=chosen,
            abandoned_state_ids=abandoned,
            tactics=tactics,
            reasoning=reasoning,
        )
    except (ValueError, KeyError, TypeError, json.JSONDecodeError):
        return DirectorResponse(
            chosen_state_id=fallback_state_id,
            abandoned_state_ids=[],
            tactics=[TacticCandidate(tactic="simp", log_prob=0.0)],
            reasoning="",
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
        director_max_tokens: int = 4096,
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
        k: int = 8,
    ) -> DirectorResponse:
        """
        Ask the LLM to choose which open state to continue from (or abandon),
        and generate k tactic candidates for its choice.

        Never raises — falls back to continuing an arbitrary frontier state
        with a single ["simp"] candidate on any error. Requires a non-empty
        ledger.frontier; callers are responsible for stopping the search once
        the frontier is empty.
        """
        fallback_id = next(iter(ledger.frontier))
        user_prompt = serialize_ledger(theorem, ledger, premises, k)
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
                tactics=[TacticCandidate(tactic="simp", log_prob=0.0)],
            )
        return parse_director_response(raw_text, k, fallback_id)

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
