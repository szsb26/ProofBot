"""
Claude-CLI-backed tactic policy for Lean 4 proof search.

Shells out to the `claude` CLI (Claude Code) in headless print mode instead
of calling the Anthropic API directly. This reuses whatever authentication
Claude Code already has configured (subscription login or its own API key)
instead of requiring a separate ANTHROPIC_API_KEY.

Usage:
    policy = ClaudeCLIPolicy()  # auto-detects the claude binary

COST / RATE-LIMIT NOTE (measured, not estimated):
The CLI injects its own scaffolding into every invocation. On a trivial
prompt:
    default                                    23,817 tokens
    + --system-prompt (replaces the default)   17,279 tokens
    + all built-in tools disallowed             9,974 tokens
~10K tokens per call is the floor, and tool JSON schemas are the single
biggest lever — hence the long _DISALLOWED_TOOLS list below. At 150 director
calls per trial that is ~1.8M tokens of overhead, which will exhaust a
consumer subscription's rate limit well before a full-budget trial finishes.
Use a small --budget when running through this policy.
"""

from __future__ import annotations

import asyncio
import glob
import json
import os
import shutil

from policy.base import BaseLLMPolicy, DIRECTOR_SYSTEM_PROMPT

# Every built-in tool, disabled: we want a plain completion, not an agent
# loop that might decide to go read files. Also the biggest single lever on
# injected context (~17.3K -> ~10.0K tokens per call).
_DISALLOWED_TOOLS = (
    "Bash,Edit,Write,Read,WebFetch,WebSearch,Task,NotebookEdit,"
    "Glob,Grep,TodoWrite,BashOutput,KillShell,SlashCommand"
)

# Generous stdout buffer: the JSON envelope carries the full response plus
# usage metadata on a single line, and asyncio's 64KB default would raise
# "Separator is found, but chunk is longer than limit" on a long reply.
_STREAM_LIMIT = 10 * 1024 * 1024


def _find_cli(cli_path: str | None = None) -> str:
    """
    Locate the `claude` binary.

    PATH alone is not enough: when Claude Code is installed via the VS Code
    extension the binary lives inside the extension directory and never gets
    symlinked onto PATH, so shutil.which() returns None on an otherwise
    perfectly working install.
    """
    if cli_path:
        return cli_path

    env_path = os.environ.get("CLAUDE_CODE_EXECPATH")
    if env_path and os.path.exists(env_path):
        return env_path

    on_path = shutil.which("claude")
    if on_path:
        return on_path

    matches = sorted(glob.glob(os.path.expanduser(
        "~/.vscode/extensions/anthropic.claude-code-*/resources/native-binary/claude"
    )))
    if matches:
        return matches[-1]

    raise RuntimeError(
        "claude CLI not found. Tried $CLAUDE_CODE_EXECPATH, PATH, and the "
        "VS Code extension directory. Install Claude Code "
        "(https://claude.com/claude-code), or pass cli_path explicitly."
    )


class ClaudeCLIPolicy(BaseLLMPolicy):
    """
    Generates Lean 4 tactic candidates by invoking `claude --print` as a
    subprocess for each proof state, instead of calling the Anthropic API
    with an API key. Satisfies the PolicyModel protocol.

    Args:
        model:     Model alias/name passed to `claude --model`
                   (e.g. "sonnet", "opus", "haiku").
        cli_path:  Path to the `claude` binary. Auto-detected when omitted.
        timeout_s: Hard per-call timeout. The CLI exposes no max_tokens, so
                   this is the only bound on a runaway generation.
    """

    def __init__(
        self,
        model: str = "sonnet",
        max_tokens: int = 256,
        temperature: float = 1.0,
        cli_path: str | None = None,
        director_max_tokens: int = 16000,
        director_thinking: bool = False,
        timeout_s: float = 300.0,
    ):
        super().__init__(
            model=model,
            max_tokens=max_tokens,
            temperature=temperature,
            director_max_tokens=director_max_tokens,
            director_thinking=director_thinking,
        )
        self._cli_path = _find_cli(cli_path)
        self._timeout_s = timeout_s

    async def _call_api(
        self,
        user_prompt: str,
        system_prompt: str = DIRECTOR_SYSTEM_PROMPT,
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
            # json, not text: a rate-limit refusal comes back as exit code 0
            # with the error in the payload. Parsed as text it would sail
            # through as a valid "response" and silently degrade the turn
            # into the director's blind "simp" fallback.
            "--output-format", "json",
            "--disallowedTools", _DISALLOWED_TOOLS,
        ]
        if enable_thinking:
            args += ["--effort", "high"]

        proc = await asyncio.create_subprocess_exec(
            *args,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            limit=_STREAM_LIMIT,
        )
        # The prompt goes over stdin rather than argv: serialized ledgers
        # routinely run to tens of KB and would risk the argv size limit.
        try:
            stdout, stderr = await asyncio.wait_for(
                proc.communicate(user_prompt.encode()),
                timeout=self._timeout_s,
            )
        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()
            raise RuntimeError(f"claude CLI timed out after {self._timeout_s}s")

        if proc.returncode != 0:
            raise RuntimeError(
                f"claude CLI exited {proc.returncode}: {stderr.decode().strip()[:500]}"
            )

        try:
            payload = json.loads(stdout.decode(errors="replace"))
        except json.JSONDecodeError as e:
            raise RuntimeError(
                "claude CLI returned non-JSON output: "
                f"{stdout.decode(errors='replace')[:500]}"
            ) from e

        if payload.get("is_error"):
            raise RuntimeError(
                f"claude CLI reported an error: {str(payload.get('result', payload))[:500]}"
            )

        return payload.get("result", "") or ""

    async def close(self) -> None:
        pass
