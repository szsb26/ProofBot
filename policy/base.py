"""
Base class for LLM-backed tactic policies.

Handles prompt construction, response parsing, and the get_tactics() interface.
Subclasses only need to implement _call_api() and close().

Shared by AnthropicPolicy, DeepSeekPolicy, and any future LLM backend.
"""

from __future__ import annotations

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


class BaseLLMPolicy:
    """
    Shared logic for LLM-backed tactic policies.

    Subclasses implement _call_api() to handle the provider-specific API call.
    get_tactics() handles prompt building, parsing, and error fallback.
    """

    def __init__(self, model: str, max_tokens: int = 256):
        self._model = model
        self._max_tokens = max_tokens

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

    async def _call_api(self, user_prompt: str) -> str:
        """Call the provider API and return the raw response text."""
        raise NotImplementedError

    async def close(self) -> None:
        pass
