"""
Tests for policy/claude_cli.py

Unit tests mock asyncio.create_subprocess_exec — no real CLI invocation, no
subscription usage consumed. The integration test at the bottom is skipped
unless RUN_CLAUDE_CLI_TEST=1, since every real call spends ~10K tokens of the
CLI's injected context against the user's rate limit.
"""

from __future__ import annotations

import json
import os
from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from policy.base import DIRECTOR_SYSTEM_PROMPT
from policy.claude_cli import ClaudeCLIPolicy, _DISALLOWED_TOOLS


def _mock_proc(stdout: bytes, returncode: int = 0, stderr: bytes = b""):
    proc = MagicMock()
    proc.returncode = returncode
    proc.communicate = AsyncMock(return_value=(stdout, stderr))
    proc.kill = MagicMock()
    proc.wait = AsyncMock()
    return proc


def _envelope(result: str, is_error: bool = False) -> bytes:
    return json.dumps({"result": result, "is_error": is_error}).encode()


@pytest.fixture
def policy():
    return ClaudeCLIPolicy(model="haiku", cli_path="/fake/claude")


class TestClaudeCLIPolicyCall:

    async def test_returns_result_field_from_json_envelope(self, policy):
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(_envelope("simp\nring")))):
            assert await policy._call_api("goal here") == "simp\nring"

    async def test_prompt_is_sent_on_stdin_not_argv(self, policy):
        """Serialized ledgers run to tens of KB; passing one as an argv
        element would risk the argument size limit."""
        fake = _mock_proc(_envelope("ok"))
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=fake)) as spawn:
            await policy._call_api("MY_UNIQUE_PROMPT")

        assert not any("MY_UNIQUE_PROMPT" in str(a) for a in spawn.await_args.args)
        fake.communicate.assert_awaited_once_with(b"MY_UNIQUE_PROMPT")

    async def test_system_prompt_replaces_the_cli_default(self, policy):
        """--system-prompt, not --append-system-prompt: measured to cut the
        CLI's injected context from ~23.8K to ~17.3K tokens per call."""
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(_envelope("ok")))) as spawn:
            await policy._call_api("g", system_prompt=DIRECTOR_SYSTEM_PROMPT)

        argv = list(spawn.await_args.args)
        assert argv[argv.index("--system-prompt") + 1] == DIRECTOR_SYSTEM_PROMPT
        assert "--append-system-prompt" not in argv

    async def test_all_builtin_tools_are_disabled(self, policy):
        """We want a plain completion, not an agent loop — and dropping the
        tool schemas is the biggest lever on injected context
        (~17.3K -> ~10.0K tokens per call)."""
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(_envelope("ok")))) as spawn:
            await policy._call_api("g")

        argv = list(spawn.await_args.args)
        disallowed = argv[argv.index("--disallowedTools") + 1]
        for tool in ("Bash", "Read", "Write", "Edit", "WebFetch", "Task", "Grep", "Glob"):
            assert tool in disallowed, f"{tool} should be disabled"

    async def test_runs_headless_with_json_output(self, policy):
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(_envelope("ok")))) as spawn:
            await policy._call_api("g")

        argv = list(spawn.await_args.args)
        assert "--print" in argv
        assert argv[argv.index("--output-format") + 1] == "json"
        assert argv[argv.index("--model") + 1] == "haiku"

    async def test_effort_flag_only_when_thinking_enabled(self, policy):
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(_envelope("ok")))) as spawn:
            await policy._call_api("g", enable_thinking=False)
        assert "--effort" not in list(spawn.await_args.args)

        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(_envelope("ok")))) as spawn:
            await policy._call_api("g", enable_thinking=True)
        argv = list(spawn.await_args.args)
        assert argv[argv.index("--effort") + 1] == "high"

    async def test_nonzero_exit_raises(self, policy):
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(b"", returncode=1, stderr=b"boom"))):
            with pytest.raises(RuntimeError, match="exited 1"):
                await policy._call_api("g")

    async def test_is_error_envelope_raises(self, policy):
        """A rate-limit refusal comes back as exit code 0 with is_error set.
        If that were accepted as a valid completion it would parse as a
        director response and silently degrade the turn into a blind "simp"
        — burning the whole budget while appearing to run fine."""
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(_envelope("rate limited", is_error=True)))):
            with pytest.raises(RuntimeError, match="reported an error"):
                await policy._call_api("g")

    async def test_non_json_output_raises(self, policy):
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(b"not json at all"))):
            with pytest.raises(RuntimeError, match="non-JSON"):
                await policy._call_api("g")

    async def test_missing_result_field_returns_empty_string(self, policy):
        with patch("asyncio.create_subprocess_exec",
                   AsyncMock(return_value=_mock_proc(json.dumps({"is_error": False}).encode()))):
            assert await policy._call_api("g") == ""

    async def test_timeout_kills_the_subprocess_and_raises(self):
        pol = ClaudeCLIPolicy(model="haiku", cli_path="/fake/claude", timeout_s=0.01)
        fake = _mock_proc(_envelope("never"))

        async def _hang(*a, **k):
            await asyncio.sleep(10)

        import asyncio
        fake.communicate = _hang
        with patch("asyncio.create_subprocess_exec", AsyncMock(return_value=fake)):
            with pytest.raises(RuntimeError, match="timed out"):
                await pol._call_api("g")
        fake.kill.assert_called_once()

    async def test_close_is_a_noop(self, policy):
        await policy.close()  # each call is its own subprocess


class TestFindCLI:
    """
    Regression coverage: resolving via PATH alone raised RuntimeError on a
    perfectly working install, because the VS Code extension keeps its
    binary inside the extension directory and never symlinks it onto PATH.
    """

    def test_explicit_path_wins(self):
        from policy.claude_cli import _find_cli
        assert _find_cli("/explicit/claude") == "/explicit/claude"

    def test_falls_back_to_exec_path_env_var(self, tmp_path, monkeypatch):
        from policy.claude_cli import _find_cli
        fake = tmp_path / "claude"
        fake.write_text("#!/bin/sh\n")
        monkeypatch.setenv("CLAUDE_CODE_EXECPATH", str(fake))
        monkeypatch.setattr("shutil.which", lambda _: None)
        assert _find_cli() == str(fake)

    def test_falls_back_to_vscode_extension_when_not_on_path(self, monkeypatch):
        from policy.claude_cli import _find_cli
        monkeypatch.delenv("CLAUDE_CODE_EXECPATH", raising=False)
        monkeypatch.setattr("shutil.which", lambda _: None)
        monkeypatch.setattr("glob.glob", lambda _: ["/vscode/ext/claude"])
        assert _find_cli() == "/vscode/ext/claude"

    def test_raises_with_guidance_when_genuinely_absent(self, monkeypatch):
        from policy.claude_cli import _find_cli
        monkeypatch.delenv("CLAUDE_CODE_EXECPATH", raising=False)
        monkeypatch.setattr("shutil.which", lambda _: None)
        monkeypatch.setattr("glob.glob", lambda _: [])
        with pytest.raises(RuntimeError, match="cli_path"):
            _find_cli()


@pytest.mark.skipif(
    not os.environ.get("RUN_CLAUDE_CLI_TEST"),
    reason="RUN_CLAUDE_CLI_TEST not set (real call consumes subscription usage)",
)
class TestClaudeCLIPolicyIntegration:

    async def test_real_cli_call_returns_text(self):
        pol = ClaudeCLIPolicy(model="haiku")
        out = await pol._call_api(
            "Reply with exactly: integration-ok",
            system_prompt="Answer concisely, no preamble.",
        )
        assert "integration-ok" in out
        await pol.close()
