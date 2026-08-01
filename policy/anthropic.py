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
        temperature: float = 1.0,
        api_key: str | None = None,
        director_max_tokens: int = 1024,
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
            api_key=api_key or os.environ.get("ANTHROPIC_API_KEY", "")
        )

    async def _call_api(
        self,
        user_prompt: str,
        system_prompt: str = SYSTEM_PROMPT,
        max_tokens: int | None = None,
        enable_thinking: bool = False,
    ) -> str:
        # enable_thinking is not yet wired up for Claude (would use the
        # `thinking` extended-thinking param) — accepted for interface
        # parity with DeepSeekPolicy, currently a no-op here.
        message = await self._client.messages.create(
            model=self._model,
            max_tokens=max_tokens or self._max_tokens,
            temperature=self._temperature,
            system=system_prompt,
            messages=[{"role": "user", "content": user_prompt}],
        )
        return message.content[0].text

    async def close(self) -> None:
        await self._client.close()
