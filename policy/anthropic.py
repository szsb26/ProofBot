"""
Anthropic-backed policy model for generating Lean 4 tactic candidates.

Calls Claude with the serialized proof state and a list of relevant premises,
and parses the response into a ranked list of TacticCandidate objects.

Usage:
    policy = AnthropicPolicy()  # reads ANTHROPIC_API_KEY from env
    candidates = await policy.get_tactics(state, premises, k=8)
"""

from __future__ import annotations

import os

from anthropic import AsyncAnthropic

from core.policy import TacticCandidate
from core.proof_state import ProofState


_SYSTEM_PROMPT = (
    "You are an expert Lean 4 theorem prover assistant. "
    "Given a proof state, output tactic candidates that could make progress "
    "toward closing the proof.\n\n"
    "Rules:\n"
    "- Output exactly one Lean 4 tactic per line, with no other text.\n"
    "- Order tactics from most likely to succeed to least likely.\n"
    "- Do not include explanations, numbering, backticks, or code fences.\n"
    "- Each line must be a single, syntactically valid Lean 4 tactic.\n"
    "- If using `intro`, always specify the variable name (e.g. `intro n`).\n"
    "- If you cannot generate enough distinct tactics, repeat your best guess "
    "rather than outputting fewer lines."
)


def _build_user_prompt(state: ProofState, premises: list[str], k: int) -> str:
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


def _parse_tactics(text: str, k: int) -> list[str]:
    """
    Extract clean tactic strings from Claude's raw response.

    Strips leading numbering (e.g. "1." or "1)"), backticks, and blank lines.
    Deduplicates while preserving order. Falls back to ["simp"] if nothing
    parseable is found.
    """
    lines: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        # Strip leading "1." / "1)" / "- " style prefixes
        if line[0].isdigit():
            line = line.lstrip("0123456789").lstrip(". )").strip()
        elif line.startswith("- "):
            line = line[2:].strip()
        # Strip surrounding backticks
        line = line.strip("`").strip()
        if line:
            lines.append(line)

    # Deduplicate, preserve order
    seen: set[str] = set()
    unique: list[str] = []
    for t in lines:
        if t not in seen:
            seen.add(t)
            unique.append(t)

    return unique[:k] if unique else ["simp"]


class AnthropicPolicy:
    """
    Generates Lean 4 tactic candidates by calling the Anthropic API.
    Satisfies the PolicyModel protocol.

    Args:
        model:      Claude model ID to use.
        max_tokens: Upper bound on response length. 256 is enough for k<=16 tactics.
        api_key:    Anthropic API key. Defaults to ANTHROPIC_API_KEY env var.
    """

    def __init__(
        self,
        model: str = "claude-haiku-4-5-20251001",
        max_tokens: int = 256,
        api_key: str | None = None,
    ):
        self._model = model
        self._max_tokens = max_tokens
        self._client = AsyncAnthropic(
            api_key=api_key or os.environ.get("ANTHROPIC_API_KEY", "")
        )

    async def get_tactics(
        self,
        state: ProofState,
        premises: list[str],
        k: int = 8,
    ) -> list[TacticCandidate]:
        """
        Call Claude with the current proof state and return k tactic candidates.

        Never raises — if the API call fails or returns unparseable output,
        falls back to returning [TacticCandidate("simp")].
        """
        user_prompt = _build_user_prompt(state, premises, k)

        try:
            message = await self._client.messages.create(
                model=self._model,
                max_tokens=self._max_tokens,
                system=_SYSTEM_PROMPT,
                messages=[{"role": "user", "content": user_prompt}],
            )
            raw_text = message.content[0].text
        except Exception:
            return [TacticCandidate(tactic="simp", log_prob=0.0)]

        tactics = _parse_tactics(raw_text, k)

        # Assign descending log probs by position: first tactic is highest priority.
        # The Anthropic API does not expose per-token log probs, so we use rank order
        # as a proxy (consistent with MockPolicy's convention).
        return [
            TacticCandidate(tactic=t, log_prob=float(-i))
            for i, t in enumerate(tactics)
        ]

    async def close(self) -> None:
        await self._client.close()
