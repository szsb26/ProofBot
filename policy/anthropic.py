"""
Anthropic-backed tactic policy for Lean 4 proof search.

Calls Claude with the serialized proof state and returns ranked tactic candidates.

Usage:
    policy = AnthropicPolicy()  # reads ANTHROPIC_API_KEY from env
    candidates = await policy.get_tactics(state, premises, k=8)
"""

from __future__ import annotations

import os

import httpx
from anthropic import AsyncAnthropic

from policy.base import BaseLLMPolicy, SYSTEM_PROMPT

# The SDK's own default read timeout (600s) is measured between bytes
# received, but a *non-streaming* call gives httpx nothing to measure until
# the entire response is buffered server-side — so a request that stalls
# mid-generation (confirmed live: a director call once hung for ~2 hours
# with an ESTABLISHED connection and no error) can sail past that default
# with no error at all. A much tighter read timeout, combined with actually
# streaming the response (see _call_api), gives httpx real per-chunk
# progress to measure against, so a genuine stall fails fast instead of
# hanging indefinitely.
_TIMEOUT = httpx.Timeout(connect=10.0, read=180.0, write=60.0, pool=60.0)


class AnthropicPolicy(BaseLLMPolicy):
    """
    Generates Lean 4 tactic candidates by calling the Anthropic API.
    Satisfies the PolicyModel protocol.

    Args:
        model:      Claude model ID to use.
        max_tokens: Upper bound on response length.
        api_key:    Anthropic API key. Defaults to ANTHROPIC_API_KEY env var.
    """

    def __init__(
        self,
        model: str = "claude-haiku-4-5-20251001",
        max_tokens: int = 256,
        temperature: float = 1.0,
        api_key: str | None = None,
        director_max_tokens: int = 16000,
        director_thinking: bool = False,
    ):
        super().__init__(
            model=model,
            max_tokens=max_tokens,
            temperature=temperature,
            director_max_tokens=director_max_tokens,
            director_thinking=director_thinking,
        )
        self._client = AsyncAnthropic(
            api_key=api_key or os.environ.get("ANTHROPIC_API_KEY", ""),
            timeout=_TIMEOUT,
        )

    async def _call_api(
        self,
        user_prompt: str,
        system_prompt: str = SYSTEM_PROMPT,
        max_tokens: int | None = None,
        enable_thinking: bool = False,
    ) -> str:
        # The newest Claude models (e.g. Sonnet 5) think by default even
        # when `thinking` is omitted entirely — omitting it is NOT the same
        # as disabling it. Without an explicit `disabled`, a call with a
        # modest max_tokens budget can have the whole thing consumed by
        # invisible thinking, leaving zero tokens for the actual text and
        # returning "" (confirmed live against a real call). `disabled`/
        # `adaptive` are both confirmed accepted by the API for this model
        # family — pass one explicitly rather than omitting.
        #
        # system_prompt is identical on every single director call — every
        # turn, every trial, every problem — so it's marked cacheable. The
        # user_prompt (serialize_ledger's output) is NOT cached: its
        # "Currently Open States"/"Exhausted Attempts" sections get
        # re-sorted and re-capped each turn rather than purely growing at
        # the end, so there's no stable prefix for later turns to match.
        #
        # Streamed rather than a single buffered create() call: a
        # non-streaming request gives httpx nothing to measure progress
        # against until the whole response is ready, so a mid-generation
        # stall can sail past the read timeout with no error (see _TIMEOUT).
        # Streaming delivers real per-chunk progress, so the same timeout
        # actually catches a genuine stall instead of just a slow-but-alive
        # long response.
        async with self._client.messages.stream(
            model=self._model,
            max_tokens=max_tokens or self._max_tokens,
            temperature=self._temperature,
            system=[
                {
                    "type": "text",
                    "text": system_prompt,
                    "cache_control": {"type": "ephemeral"},
                },
            ],
            messages=[{"role": "user", "content": user_prompt}],
            thinking={"type": "adaptive"} if enable_thinking else {"type": "disabled"},
        ) as stream:
            message = await stream.get_final_message()
        # Even with thinking disabled, find text block(s) by type rather
        # than assuming content[0] — cheap insurance against relying on
        # positional assumptions that already broke once.
        return "".join(block.text for block in message.content if block.type == "text")

    async def close(self) -> None:
        await self._client.close()
