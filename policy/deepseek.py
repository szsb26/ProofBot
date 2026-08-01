"""
DeepSeek-backed tactic policy for Lean 4 proof search.

Calls the DeepSeek API (OpenAI-compatible) with the serialized proof state
and returns ranked tactic candidates.

Usage:
    policy = DeepSeekPolicy()  # reads DEEPSEEK_API_KEY from env
    candidates = await policy.get_tactics(state, premises, k=8)

Available models:
    deepseek-v4-flash  — fast, cheap, good for most theorems
    deepseek-v4-pro    — slower, more powerful reasoning
"""

from __future__ import annotations

import os

from openai import AsyncOpenAI

from policy.base import BaseLLMPolicy, SYSTEM_PROMPT


class DeepSeekPolicy(BaseLLMPolicy):
    """
    Generates Lean 4 tactic candidates by calling the DeepSeek API.
    Satisfies the PolicyModel protocol.

    The DeepSeek API is OpenAI-compatible, so we use the openai SDK with
    a custom base_url pointing to DeepSeek's servers.

    Args:
        model:      DeepSeek model ID (deepseek-v4-flash or deepseek-v4-pro).
        max_tokens: Upper bound on response length.
        api_key:    DeepSeek API key. Defaults to DEEPSEEK_API_KEY env var.
    """

    def __init__(
        self,
        model: str = "deepseek-v4-flash",
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
        self._client = AsyncOpenAI(
            api_key=api_key or os.environ.get("DEEPSEEK_API_KEY", ""),
            base_url="https://api.deepseek.com",
        )

    async def _call_api(
        self,
        user_prompt: str,
        system_prompt: str = SYSTEM_PROMPT,
        max_tokens: int | None = None,
        enable_thinking: bool = False,
    ) -> str:
        # DeepSeek's v4 models reason by default, sometimes burning thousands
        # of tokens before answering — disabled unless the caller (currently
        # only the director call, via director_thinking) explicitly wants it.
        thinking_body = {"type": "enabled"} if enable_thinking else {"type": "disabled"}
        response = await self._client.chat.completions.create(
            model=self._model,
            max_tokens=max_tokens or self._max_tokens,
            temperature=self._temperature,
            extra_body={"thinking": thinking_body},
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
        )
        return response.choices[0].message.content or ""

    async def close(self) -> None:
        await self._client.close()
