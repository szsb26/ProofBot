"""
Claude-CLI-backed tactic policy for Lean 4 proof search.

Shells out to the `claude` CLI (Claude Code) in headless print mode instead
of calling the Anthropic API directly. This reuses whatever authentication
Claude Code already has configured (subscription login or its own API key)
instead of requiring a separate ANTHROPIC_API_KEY.

Usage:
    policy = ClaudeCLIPolicy()  # uses `claude` from PATH
    candidates = await policy.get_tactics(state, premises, k=8)
"""

from __future__ import annotations

import asyncio
import shutil

from policy.base import BaseLLMPolicy, SYSTEM_PROMPT

_DISALLOWED_TOOLS = "Bash,Edit,Write,Read,WebFetch,WebSearch,Task,NotebookEdit"


class ClaudeCLIPolicy(BaseLLMPolicy):
    """
    Generates Lean 4 tactic candidates by invoking `claude --print` as a
    subprocess for each proof state, instead of calling the Anthropic API
    with an API key. Satisfies the PolicyModel protocol.

    Args:
        model:    Model alias/name passed to `claude --model`
                  (e.g. "sonnet", "opus", "haiku").
        cli_path: Path to the `claude` binary. Defaults to whatever
                  `claude` resolves to on PATH.
    """

    def __init__(
        self,
        model: str = "sonnet",
        max_tokens: int = 256,
        temperature: float = 1.0,
        cli_path: str | None = None,
        director_max_tokens: int = 4096,
        director_thinking: bool = False,
    ):
        super().__init__(
            model=model,
            max_tokens=max_tokens,
            temperature=temperature,
            director_max_tokens=director_max_tokens,
            director_thinking=director_thinking,
        )
        self._cli_path = cli_path or shutil.which("claude")
        if self._cli_path is None:
            raise RuntimeError(
                "claude CLI not found on PATH. Install Claude Code "
                "(https://claude.com/claude-code), or pass cli_path explicitly."
            )

    async def _call_api(
        self,
        user_prompt: str,
        system_prompt: str = SYSTEM_PROMPT,
        max_tokens: int | None = None,
        enable_thinking: bool = False,
    ) -> str:
        # max_tokens isn't a CLI flag (Claude Code manages its own output
        # budget) — accepted for interface parity with AnthropicPolicy /
        # DeepSeekPolicy only. enable_thinking maps to a higher effort
        # level, the closest CLI-exposed lever to "think harder".
        args = [
            self._cli_path,
            "--print",
            "--model", self._model,
            "--system-prompt", system_prompt,
            "--output-format", "text",
            "--disallowedTools", _DISALLOWED_TOOLS,
        ]
        if enable_thinking:
            args += ["--effort", "high"]
        args += ["--", user_prompt]

        proc = await asyncio.create_subprocess_exec(
            *args,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        stdout, stderr = await proc.communicate()
        if proc.returncode != 0:
            raise RuntimeError(
                f"claude CLI exited {proc.returncode}: {stderr.decode().strip()}"
            )
        return stdout.decode()

    async def close(self) -> None:
        pass
