"""
TracingPolicy: wraps a BaseLLMPolicy so every director call is recorded
verbatim — the exact prompt sent and the exact raw response received —
without changing how the search consumes it (still returns a normal
DirectorResponse).

Requires a BaseLLMPolicy-compatible object (something with _call_api,
_director_max_tokens, _director_thinking) so the raw pre-parse response
text can be captured. MockPolicy doesn't have these — there's no real LLM
call to trace, so wrapping it wouldn't be meaningful.

Used by both scripts/trace_search.py (always renders to a file) and
eval/harness.py's --trace flag (renders only for trials that fail).
"""

from __future__ import annotations

from core.ledger import Ledger
from policy.base import DIRECTOR_SYSTEM_PROMPT, DirectorResponse, parse_director_response, serialize_ledger


class TracingPolicy:
    """
    Drop-in wrapper around a BaseLLMPolicy: same get_next_action/close
    interface, but every turn's prompt and raw response are buffered in
    .lines and available via render(). Pass verbose=True to also print
    each turn live as it happens.
    """

    def __init__(self, inner_policy, verbose: bool = False):
        self._inner = inner_policy
        self.turn = 0
        self.lines: list[str] = []
        self._verbose = verbose

    def _emit(self, text: str) -> None:
        self.lines.append(text)
        if self._verbose:
            print(text, flush=True)

    async def get_next_action(
        self,
        theorem: str,
        ledger: Ledger,
        premises: list[str],
        k: int = 8,
    ) -> DirectorResponse:
        self.turn += 1
        prompt = serialize_ledger(theorem, ledger, premises, k)
        self._emit(f"\n{'=' * 80}\nTURN {self.turn} — PROMPT SENT TO LLM\n{'=' * 80}")
        self._emit(prompt)

        fallback_id = next(iter(ledger.frontier))
        raw_text = await self._inner._call_api(
            prompt,
            system_prompt=DIRECTOR_SYSTEM_PROMPT,
            max_tokens=self._inner._director_max_tokens,
            enable_thinking=self._inner._director_thinking,
        )
        self._emit(f"\n{'-' * 80}\nTURN {self.turn} — RAW RESPONSE FROM LLM\n{'-' * 80}")
        self._emit(raw_text)

        resp = parse_director_response(raw_text, k, fallback_id)
        self._emit(f"\n{'-' * 80}\nTURN {self.turn} — PARSED DECISION\n{'-' * 80}")
        self._emit(f"chosen_state: {resp.chosen_state_id}")
        self._emit(f"abandoned: {resp.abandoned_state_ids}")
        self._emit(f"reasoning: {resp.reasoning}")
        self._emit(f"tactics: {[c.tactic for c in resp.tactics]}")
        return resp

    async def close(self) -> None:
        await self._inner.close()

    def render(self) -> str:
        """Full trace text captured so far, newline-joined."""
        return "\n".join(self.lines)
