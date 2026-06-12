"""
Anthropic-backed tactic policy for Lean 4 proof search.

Calls Claude with the serialized proof state and returns ranked tactic candidates.

Usage:
    policy = AnthropicPolicy()  # reads ANTHROPIC_API_KEY from env
    candidates = await policy.get_tactics(state, premises, k=8)
"""

from __future__ import annotations

import os

from anthropic import AsyncAnthropic

from policy.base import BaseLLMPolicy, SYSTEM_PROMPT


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
        api_key: str | None = None,
    ):
        super().__init__(model=model, max_tokens=max_tokens)
        self._client = AsyncAnthropic(
            api_key=api_key or os.environ.get("ANTHROPIC_API_KEY", "")
        )

    async def _call_api(self, user_prompt: str) -> str:
        message = await self._client.messages.create(
            model=self._model,
            max_tokens=self._max_tokens,
            system=SYSTEM_PROMPT,
            messages=[{"role": "user", "content": user_prompt}],
        )
        return message.content[0].text

    async def close(self) -> None:
        await self._client.close()
