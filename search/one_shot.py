"""
One-shot proving: the north-star baseline this whole project has to beat.

No ledger, no frontier, no per-tactic verification loop — just ask the
model for a complete Lean 4 proof in one call, try it against the real
theorem, and (optionally) feed back Lean's actual error a bounded number
of times and let the model try again. This is meant to approximate what a
capable engineer already gets for free by pasting a theorem into Claude
and fixing it by hand a couple of times — the bar LedgerSearch's tree
machinery has to clear to be worth having at all.
"""

from __future__ import annotations

import re
import time
from dataclasses import dataclass

from core.executor import LeanExecutor
from policy.base import BaseLLMPolicy
from search.ledger_search import ProofResult, _classify_tactic_error, _contains_banned_tactic

ONE_SHOT_SYSTEM_PROMPT = (
    "You are an expert Lean 4 theorem prover. Given a theorem statement "
    "ending in `:= by`, write the complete tactic-mode proof that goes "
    "after `by`.\n\n"
    "Rules:\n"
    "- Output ONLY the proof's tactic code — no theorem header, no `:= by`, "
    "no markdown code fences, no explanation before or after.\n"
    "- The proof may span multiple lines/tactics (e.g. separated by ';' or "
    "newlines) — write whatever real Lean 4 tactic proof the theorem "
    "actually needs, however long that takes.\n"
    "- Never use `sorry` or `admit` — an incomplete proof is a failed "
    "proof, not a placeholder to fill in later."
)

FIX_USER_TEMPLATE = (
    "## Theorem\n\n{theorem}\n\n"
    "## Your previous attempt\n\n{previous_proof}\n\n"
    "## Lean's error\n\n{error}\n\n"
    "That attempt did not compile. Write a corrected complete proof "
    "(same output rules as before: tactic code only, no header, no fences)."
)

_CODE_FENCE = re.compile(r"```(?:lean4?)?\s*\n?(.*?)```", re.DOTALL)
_THEOREM_HEADER = re.compile(r"^\s*theorem\b.*?:=\s*by\b", re.DOTALL)


def _extract_proof_code(text: str) -> str:
    """
    Pull the actual tactic code out of a raw model response, tolerating the
    two deviations seen in practice: wrapping the answer in a markdown code
    fence despite being told not to, and including the theorem header/`:=
    by` again instead of only the tactic body.
    """
    text = text.strip()
    fence_match = _CODE_FENCE.search(text)
    if fence_match:
        text = fence_match.group(1).strip()
    text = _THEOREM_HEADER.sub("", text).strip()
    return text


@dataclass(frozen=True)
class OneShotResult:
    """Extends ProofResult's shape with attempts_used, since 'nodes' isn't
    the right word for a one-shot-plus-fixes run."""
    result: ProofResult
    attempts_used: int


class OneShotProve:
    """
    Usage:
        prover = OneShotProve(policy, executor, max_fixes=3)
        result = await prover.prove(theorem)

    max_fixes=3 matches the project's own bar: search only earns its keep
    if it beats one-shot plus a small, human-scale number of fix attempts.
    """

    def __init__(
        self,
        policy: BaseLLMPolicy,
        executor: LeanExecutor,
        max_fixes: int = 3,
        max_tokens: int = 8000,
        enable_thinking: bool = True,
    ):
        self.policy = policy
        self.executor = executor
        self.max_fixes = max_fixes
        self.max_tokens = max_tokens
        self.enable_thinking = enable_thinking

    async def prove(self, theorem: str) -> OneShotResult:
        start = time.perf_counter()
        initial_state = await self.executor.reset(theorem)

        if initial_state.is_error:
            return OneShotResult(
                result=ProofResult(
                    success=False, proof_trace=[], nodes_visited=0,
                    elapsed_ms=(time.perf_counter() - start) * 1000,
                    theorem=theorem, error=initial_state.error or "Lean parse error",
                    failure_reason="parse_error",
                ),
                attempts_used=0,
            )
        if initial_state.is_closed:
            return OneShotResult(
                result=ProofResult(
                    success=True, proof_trace=[], nodes_visited=0,
                    elapsed_ms=(time.perf_counter() - start) * 1000,
                    theorem=theorem,
                ),
                attempts_used=0,
            )

        tactic_errors: dict[str, int] = {}
        previous_proof = ""
        previous_error = ""

        for attempt in range(self.max_fixes + 1):
            if attempt == 0:
                prompt = f"## Theorem\n\n{theorem}"
            else:
                prompt = FIX_USER_TEMPLATE.format(
                    theorem=theorem, previous_proof=previous_proof, error=previous_error,
                )

            try:
                raw = await self.policy._call_api(
                    prompt,
                    system_prompt=ONE_SHOT_SYSTEM_PROMPT,
                    max_tokens=self.max_tokens,
                    enable_thinking=self.enable_thinking,
                )
            except Exception as e:
                return OneShotResult(
                    result=ProofResult(
                        success=False, proof_trace=[], nodes_visited=attempt,
                        elapsed_ms=(time.perf_counter() - start) * 1000,
                        theorem=theorem, error=str(e), failure_reason="draft_failed",
                        tactic_errors=tactic_errors,
                    ),
                    attempts_used=attempt,
                )

            proof_code = _extract_proof_code(raw)

            if not proof_code or _contains_banned_tactic(proof_code):
                previous_proof = proof_code
                previous_error = (
                    "empty response" if not proof_code
                    else "rejected: sorry/admit are not allowed"
                )
                continue

            result = await self.executor.step(initial_state, proof_code)

            if result.proof_closed:
                return OneShotResult(
                    result=ProofResult(
                        success=True,
                        proof_trace=list(result.next_state.tactic_trace),
                        nodes_visited=attempt + 1,
                        elapsed_ms=(time.perf_counter() - start) * 1000,
                        theorem=theorem,
                        tactic_errors=tactic_errors,
                    ),
                    attempts_used=attempt + 1,
                )

            err = result.next_state.error or "unsolved goals"
            category = _classify_tactic_error(err)
            tactic_errors[category] = tactic_errors.get(category, 0) + 1
            previous_proof = proof_code
            previous_error = err

        return OneShotResult(
            result=ProofResult(
                success=False, proof_trace=[], nodes_visited=self.max_fixes + 1,
                elapsed_ms=(time.perf_counter() - start) * 1000,
                theorem=theorem, failure_reason="fixes_exhausted",
                tactic_errors=tactic_errors,
            ),
            attempts_used=self.max_fixes + 1,
        )

    async def close(self) -> None:
        await self.policy.close()
