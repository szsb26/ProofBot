"""
Tests for run.py — the mathematician-facing CLI.

TestParseArgs        — fast, no I/O; validates argument defaults and overrides
TestCLIWithMock      — fast, no Lean, no API; uses --policy mock end-to-end
TestCLIIntegration   — slow, real Lean, no API; uses --policy mock with real REPL
TestCLIEndToEnd      — slow, real Lean + real Anthropic API; full stack via CLI
"""

import os
import pytest
import asyncio
from unittest.mock import patch

from lean.repl import LEAN_PROJECT_DIR
from run import parse_args, main


# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

class TestParseArgs:

    def test_defaults(self):
        args = parse_args(["theorem foo : n + 0 = n := by"])
        assert args.theorem == "theorem foo : n + 0 = n := by"
        assert args.workers == 1
        assert args.budget == 100
        assert args.policy == "anthropic"
        assert args.model == "claude-haiku-4-5-20251001"
        assert args.api_key is None

    def test_workers_and_budget(self):
        args = parse_args(["thm", "--workers", "4", "--budget", "50"])
        assert args.workers == 4
        assert args.budget == 50

    def test_short_flags(self):
        args = parse_args(["thm", "-k", "3", "-b", "25"])
        assert args.workers == 3
        assert args.budget == 25

    def test_mock_policy(self):
        args = parse_args(["thm", "--policy", "mock"])
        assert args.policy == "mock"

    def test_mock_tactics_override(self):
        args = parse_args(["thm", "--policy", "mock", "--tactics", "simp,ring"])
        assert args.tactics == "simp,ring"

    def test_model_override(self):
        args = parse_args(["thm", "--model", "claude-sonnet-4-6"])
        assert args.model == "claude-sonnet-4-6"

    def test_api_key_flag(self):
        args = parse_args(["thm", "--api-key", "sk-test"])
        assert args.api_key == "sk-test"


# ---------------------------------------------------------------------------
# CLI with mock policy (no Lean, no API key)
# ---------------------------------------------------------------------------

_SIMPLE = "theorem foo : n + 0 = n := by"       # no ∀ — MockExecutor closes with simp
_FORALL  = "theorem foo : ∀ n : Nat, n + 0 = n := by"  # real Lean only


_MOCK_FLAGS = ["--policy", "mock", "--executor", "mock"]


class TestCLIWithMock:

    def test_success_exits_zero(self):
        # simp closes n + 0 = n in MockExecutor → exit code 0
        result = main([_SIMPLE, *_MOCK_FLAGS, "--tactics", "simp,ring", "--budget", "10"])
        assert result == 0

    def test_failure_exits_one(self):
        # Invalid tactics → MockExecutor never closes → exit code 1
        result = main([_SIMPLE, *_MOCK_FLAGS, "--tactics", "not_a_tactic,also_invalid", "--budget", "5"])
        assert result == 1

    def test_parallel_workers_with_mock(self):
        result = main([_SIMPLE, *_MOCK_FLAGS, "--tactics", "simp,ring,omega", "--workers", "3", "--budget", "10"])
        assert result == 0

    def test_missing_api_key_exits_with_error(self, capsys):
        # anthropic policy with no key should print an error and exit 1
        with patch.dict("os.environ", {}, clear=True):
            with patch("run.load_dotenv"):  # prevent .env from loading a key
                with pytest.raises(SystemExit) as exc:
                    main([_SIMPLE, "--policy", "anthropic", "--executor", "mock"])
        assert exc.value.code == 1
        captured = capsys.readouterr()
        assert "ANTHROPIC_API_KEY" in captured.err

    def test_output_contains_proof_trace(self, capsys):
        main([_SIMPLE, *_MOCK_FLAGS, "--tactics", "simp", "--budget", "10"])
        captured = capsys.readouterr()
        assert "simp" in captured.out
        assert "✓" in captured.out

    def test_failure_output_suggests_options(self, capsys):
        main([_SIMPLE, *_MOCK_FLAGS, "--tactics", "not_a_tactic", "--budget", "3"])
        captured = capsys.readouterr()
        assert "✗" in captured.out
        assert "--budget" in captured.out or "--workers" in captured.out


# ---------------------------------------------------------------------------
# CLI integration tests (slow, real Lean, no API key needed)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found",
)
class TestCLIIntegration:

    def test_proves_simple_theorem_with_real_lean(self):
        # MockPolicy supplies tactics; SubprocessExecutor verifies them against real Lean.
        result = main([
            _FORALL,
            "--policy", "mock",
            "--tactics", "simp,ring,omega,intro n",
            "--budget", "20",
        ])
        assert result == 0

    def test_parallel_workers_with_real_lean(self):
        result = main([
            _FORALL,
            "--policy", "mock",
            "--tactics", "simp,ring,omega,intro n",
            "--workers", "3",
            "--budget", "20",
        ])
        assert result == 0

    def test_proof_trace_printed(self, capsys):
        main([
            _FORALL,
            "--policy", "mock",
            "--tactics", "simp,ring,omega,intro n",
            "--budget", "20",
        ])
        captured = capsys.readouterr()
        assert "Lean 4 proof:" in captured.out
        assert ":= by" in captured.out


# ---------------------------------------------------------------------------
# Full end-to-end via CLI (slow, real Lean + real Anthropic API)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not LEAN_PROJECT_DIR.exists(),
    reason="lean_project not found",
)
@pytest.mark.skipif(
    not os.environ.get("ANTHROPIC_API_KEY"),
    reason="ANTHROPIC_API_KEY not set",
)
class TestCLIEndToEnd:

    def test_simple_theorem(self, capsys):
        # Full stack: Claude Haiku → BestFirstSearch → real Lean REPL.
        # ∀ n : Nat, n + 0 = n is closed by simp in one step.
        result = main([
            "theorem foo : ∀ n : Nat, n + 0 = n := by",
            "--budget", "20",
        ])
        assert result == 0
        out = capsys.readouterr().out
        assert "✓" in out
        assert "Lean 4 proof:" in out

    def test_binomial_square(self, capsys):
        # Level 1: arithmetic identity over Int — requires a Mathlib tactic
        # (ring, exact Int.add_sq, etc.). Not provable by simp or omega alone.
        result = main([
            "theorem binomial_sq : ∀ a b : Int, (a + b)^2 = a^2 + 2*a*b + b^2 := by",
            "--budget", "20",
        ])
        assert result == 0
        out = capsys.readouterr().out
        assert "✓" in out
        assert "Lean 4 proof:" in out

    def test_contrapositive(self, capsys):
        # Level 2: propositional logic requiring multi-step intro/exact reasoning.
        # simp, omega, and ring all fail here — Claude must reason logically.
        result = main([
            "theorem contrapositive : ∀ (p q : Prop), (p → q) → ¬q → ¬p := by",
            "--budget", "20",
        ])
        assert result == 0
        out = capsys.readouterr().out
        assert "✓" in out
        assert "Lean 4 proof:" in out

    def test_parallel_search(self, capsys):
        # 3 independent searches via the CLI --workers flag.
        result = main([
            "theorem foo : ∀ n : Nat, n + 0 = n := by",
            "--workers", "3",
            "--budget", "20",
        ])
        assert result == 0
        out = capsys.readouterr().out
        assert "✓" in out
