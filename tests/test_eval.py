"""
Tests for eval/problems.py, eval/harness.py, and eval.py CLI.

TestSelectProblems   — fast, no I/O; validates problem filtering logic
TestEvalProblems     — fast, no I/O; validates the problem set itself
TestRunEval          — fast, mock executor + mock policy; validates harness
TestEvalCLI          — fast, mock executor + mock policy; validates CLI
"""

import json
import os
import pytest

from eval.problems import (
    PROBLEMS,
    DIFFICULTIES,
    PROBLEM_BY_NAME,
    EvalProblem,
    select_problems,
)
from eval.harness import run_eval, EvalSummary, ProblemResult
from run_eval import parse_args, main


# ---------------------------------------------------------------------------
# Problem set integrity
# ---------------------------------------------------------------------------

class TestEvalProblems:

    def test_all_names_unique(self):
        names = [p.name for p in PROBLEMS]
        assert len(names) == len(set(names))

    def test_all_difficulties_valid(self):
        for p in PROBLEMS:
            assert p.difficulty in DIFFICULTIES, f"{p.name} has unknown difficulty"

    def test_all_statements_end_with_by(self):
        for p in PROBLEMS:
            assert p.statement.strip().endswith(":= by"), (
                f"{p.name} statement does not end with ':= by'"
            )

    def test_problem_by_name_index_complete(self):
        assert set(PROBLEM_BY_NAME.keys()) == {p.name for p in PROBLEMS}

    def test_every_tier_has_at_least_one_problem(self):
        tiers_present = {p.difficulty for p in PROBLEMS}
        assert tiers_present == set(DIFFICULTIES)


# ---------------------------------------------------------------------------
# Problem filtering
# ---------------------------------------------------------------------------

class TestSelectProblems:

    def test_none_returns_all(self):
        assert select_problems(None) == PROBLEMS

    def test_empty_string_returns_all(self):
        assert select_problems("") == PROBLEMS

    def test_single_tier(self):
        result = select_problems("easy")
        assert all(p.difficulty == "easy" for p in result)
        expected = sum(1 for p in PROBLEMS if p.difficulty == "easy")
        assert len(result) == expected

    def test_multiple_tiers(self):
        result = select_problems("easy,medium")
        assert {p.difficulty for p in result} == {"easy", "medium"}
        expected = sum(1 for p in PROBLEMS if p.difficulty in ("easy", "medium"))
        assert len(result) == expected

    def test_single_name(self):
        result = select_problems("add_zero")
        assert len(result) == 1
        assert result[0].name == "add_zero"

    def test_multiple_names(self):
        result = select_problems("add_zero,contrapositive")
        names = [p.name for p in result]
        assert "add_zero" in names
        assert "contrapositive" in names
        assert len(result) == 2

    def test_mixed_tier_and_name(self):
        result = select_problems("easy,contrapositive")
        names = {p.name for p in result}
        assert "contrapositive" in names
        easy_names = {p.name for p in PROBLEMS if p.difficulty == "easy"}
        assert easy_names.issubset(names)

    def test_no_duplicates_when_name_already_in_tier(self):
        result = select_problems("easy,add_zero")
        names = [p.name for p in result]
        assert names.count("add_zero") == 1

    def test_preserves_canonical_order(self):
        result = select_problems("easy")
        easy_in_order = [p for p in PROBLEMS if p.difficulty == "easy"]
        assert result == easy_in_order

    def test_unknown_token_raises(self):
        with pytest.raises(ValueError, match="Unknown filter token"):
            select_problems("not_a_real_problem")

    def test_unknown_tier_raises(self):
        with pytest.raises(ValueError, match="Unknown filter token"):
            select_problems("impossible")

    def test_whitespace_trimmed(self):
        result = select_problems(" easy , medium ")
        assert {p.difficulty for p in result} == {"easy", "medium"}


# ---------------------------------------------------------------------------
# Harness (mock executor + mock policy — no Lean, no API)
# ---------------------------------------------------------------------------

_TWO_PROBLEMS = [PROBLEM_BY_NAME["add_zero"], PROBLEM_BY_NAME["contrapositive"]]


class TestRunEval:

    @pytest.fixture
    def mock_stack(self):
        from lean.mock_executor import MockExecutor
        from policy.mock import MockPolicy
        policy = MockPolicy(tactics=["simp", "intro n", "intro p q"])
        executors = [MockExecutor()]
        return policy, executors

    @pytest.mark.asyncio
    async def test_returns_eval_summary(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        assert isinstance(summary, EvalSummary)

    @pytest.mark.asyncio
    async def test_total_matches_problem_count(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        assert summary.total == len(_TWO_PROBLEMS)
        assert len(summary.results) == len(_TWO_PROBLEMS)

    @pytest.mark.asyncio
    async def test_pass_rate_consistent(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        assert 0.0 <= summary.pass_rate <= 1.0
        assert summary.passed <= summary.total

    @pytest.mark.asyncio
    async def test_by_difficulty_keys_match_tiers_present(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        # _TWO_PROBLEMS = easy + medium
        assert "easy" in summary.by_difficulty
        assert "medium" in summary.by_difficulty
        assert "hard" not in summary.by_difficulty

    @pytest.mark.asyncio
    async def test_metadata_stored(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=42,
            policy_name="mock",
            model_name="test-model",
        )
        assert summary.policy == "mock"
        assert summary.model == "test-model"
        assert summary.budget == 42
        assert summary.workers == 1

    @pytest.mark.asyncio
    async def test_save_creates_json(self, mock_stack, tmp_path):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        path = summary.save(str(tmp_path))
        assert os.path.exists(path)
        with open(path) as f:
            data = json.load(f)
        assert data["total"] == 2
        assert "results" in data
        assert "by_difficulty" in data
        assert "timestamp" in data

    @pytest.mark.asyncio
    async def test_saved_filename_contains_timestamp(self, mock_stack, tmp_path):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        path = summary.save(str(tmp_path))
        assert f"eval_{summary.timestamp}.json" in path

    @pytest.mark.asyncio
    async def test_results_contain_proof_trace_on_success(self, mock_stack):
        policy, executors = mock_stack
        # MockExecutor closes "n + 0 = n" with simp
        summary = await run_eval(
            problems=[PROBLEM_BY_NAME["add_zero"]],
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        successful = [r for r in summary.results if r.success]
        for r in successful:
            assert len(r.proof_trace) > 0

    @pytest.mark.asyncio
    async def test_trials_fields_populated(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
            trials=3,
        )
        assert summary.trials == 3
        for r in summary.results:
            assert r.trials == 3
            assert 0 <= r.passes <= 3

    @pytest.mark.asyncio
    async def test_mean_pass_rate_in_range(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
            trials=3,
        )
        assert 0.0 <= summary.mean_pass_rate <= 1.0

    @pytest.mark.asyncio
    async def test_single_trial_passes_fields_consistent(self, mock_stack):
        policy, executors = mock_stack
        summary = await run_eval(
            problems=_TWO_PROBLEMS,
            policy=policy,
            executors=executors,
            budget=10,
            policy_name="mock",
            model_name="mock",
        )
        assert summary.trials == 1
        for r in summary.results:
            assert r.trials == 1
            assert r.passes in (0, 1)
            assert r.success == (r.passes == 1)


# ---------------------------------------------------------------------------
# CLI (mock executor + mock policy)
# ---------------------------------------------------------------------------

_MOCK_FLAGS = ["--policy", "mock", "--executor", "mock"]


class TestEvalCLI:

    def test_parse_defaults(self):
        args = parse_args([])
        assert args.problems is None
        assert args.policy == "anthropic"
        assert args.workers == 1
        assert args.budget == 100

    def test_parse_problems_flag(self):
        args = parse_args(["--problems", "easy"])
        assert args.problems == "easy"

    def test_parse_short_flags(self):
        args = parse_args(["-k", "2", "-b", "50"])
        assert args.workers == 2
        assert args.budget == 50

    def test_parse_trials_flag(self):
        args = parse_args(["-t", "3"])
        assert args.trials == 3

    def test_trials_default_is_one(self):
        args = parse_args([])
        assert args.trials == 1

    def test_runs_subset_with_mock(self):
        result = main(["--problems", "easy", *_MOCK_FLAGS, "--budget", "5"])
        assert result == 0

    def test_unknown_problem_filter_exits_one(self):
        with pytest.raises(SystemExit) as exc:
            main(["--problems", "not_a_real_thing", *_MOCK_FLAGS])
        assert exc.value.code == 1

    def test_missing_api_key_exits_one(self, capsys):
        import unittest.mock as mock
        with mock.patch.dict("os.environ", {}, clear=True):
            with mock.patch("run_eval.load_dotenv"):
                with pytest.raises(SystemExit) as exc:
                    main(["--problems", "easy", "--policy", "anthropic", "--executor", "mock"])
        assert exc.value.code == 1
        assert "ANTHROPIC_API_KEY" in capsys.readouterr().err

    def test_saves_json_to_results_dir(self, tmp_path, monkeypatch):
        import run_eval as run_eval_module
        monkeypatch.setattr(run_eval_module, "RESULTS_DIR", tmp_path)
        main(["--problems", "easy", *_MOCK_FLAGS, "--budget", "5"])
        json_files = list(tmp_path.glob("eval_*.json"))
        assert len(json_files) == 1
        with open(json_files[0]) as f:
            data = json.load(f)
        easy_count = sum(1 for p in PROBLEMS if p.difficulty == "easy")
        assert data["total"] == easy_count
