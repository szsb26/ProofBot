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
    "- You may abandon any open state you believe is a dead end — list its id "
    "in \"abandon\" with a brief \"abandon_reason\". Do not abandon a state "
    "just because a few tactics failed on it; only abandon it if you believe "
    "the overall approach that led there is wrong.\n"
    "- Choose exactly one open state (\"chosen_state\") to continue from.\n"
    "- Propose tactic candidates for the chosen state only, ordered from most "
    "to least promising.\n"
    "- Each tactic must be a single, syntactically valid Lean 4 tactic, with "
    "no explanations, numbering, backticks, or code fences.\n"
    "- Respond with JSON only, matching exactly this shape:\n"
    '{"abandon": ["<state_id>", ...], "abandon_reason": "<brief reason, or '
    'empty string if abandon is empty>", "chosen_state": "<state_id>", '
    '"tactics": ["<tactic 1>", "<tactic 2>", ...]}'
)


@dataclass
class DirectorResponse:
    """
    The director's decision for one turn of ledger-guided search: which open
    state to continue from (and which, if any, to give up on), plus tactic
    candidates for the chosen state.
    """
    chosen_state_id: str
    abandoned_state_ids: list[str]
    tactics: list[TacticCandidate]


def serialize_ledger(
    theorem: str,
    ledger: Ledger,
    premises: list[str],
    k: int,
) -> str:
    """
    Render a Ledger into prompt text for the director call.

    Lists every open state with the tactic path that reached it, then a
    compact per-state summary of failed attempts (dead branches are never
    replayed verbatim — only their category counts). Abandoned states are
    omitted entirely; once given up on, they no longer cost context.
    """
    parts = [f"## Theorem\n\n{theorem}\n"]

    parts.append("\n## Currently Open States\n")
    for state_id, state in ledger.frontier.items():
        path = ", ".join(state.tactic_trace) if state.tactic_trace else "(root)"
        parts.append(f"\n[state {state_id}] (path: {path})\n{state.serialize()}\n")

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
        )
    except (ValueError, KeyError, TypeError, json.JSONDecodeError):
        return DirectorResponse(
            chosen_state_id=fallback_state_id,
            abandoned_state_ids=[],
            tactics=[TacticCandidate(tactic="simp", log_prob=0.0)],
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
        director_max_tokens: int = 512,
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
