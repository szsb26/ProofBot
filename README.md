# Theorem Prover

A best-first proof search system for Lean 4, backed by an LLM policy.

This repo implements a generalized mathematical theorem prover using Large Language Models. In naive LLM theorem provers,  users 1) give a theorem to the LLM to prove, and then 2) the LLM attempts to prove it in a one-shot manner. The drawbacks of this are obvious - because the LLM is not running Lean verification of each of its statements, hallucination or wrong derivations occur in the output response. 

This repo instead implements a generalized framework for mathematical theorem provers. Specifically, a theorem prover is a combination of 2 components: A) the LLM, and B) the underlying search algorithm guiding the LLM. The search algorithm used is rather flexible. For ex., the simplest approach uses the Best First Search, which is a simple priority queue which ranks candidate Lean tactics. A more complex search algorithm is MCTS, which requires a value network and Monte Carlo rollouts to guide the LLM. Because each mathematical statement output by the LLM is rigorously verified by LEAN, and the search algorithm looks ahead in the proof, generalized mathematical theorem provers are much more accurate than using the LLM alone.

## Architecture

```
prove_parallel(theorem, searches=[...], budget=100)
    └── asyncio.gather(search_0.prove(), search_1.prove(), ..., search_k.prove())
            │
            └── BestFirstSearch          (one priority queue per instance)
                    │
                    ├── PolicyModel      (tactic generator — AnthropicPolicy or MockPolicy)
                    ├── ValueModel       (state evaluator — HeuristicValue)
                    └── LeanExecutor     (tactic verifier — SubprocessExecutor or MockExecutor)
                            │
                            └── LeanWorker → lake exe repl  (one OS process)
```

**Parallelism**: create k `SubprocessExecutor` + `BestFirstSearch` pairs and run them with `prove_parallel`. Each search has its own Lean REPL process and priority queue — they explore the proof tree independently and concurrently.

## Prerequisites

- Python 3.11
- Lean 4 / Mathlib (built via `lake build` inside `lean_project/`)

## Setup

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e .
```

## Running tests

```bash
# Fast tests only (no Lean, no API key)
pytest tests/ --ignore=tests/lean/test_repl.py

# All tests including Lean integration (no API key needed)
pytest tests/

# End-to-end tests: real Claude API + real Lean (requires ANTHROPIC_API_KEY)
ANTHROPIC_API_KEY=sk-... .venv/bin/python -m pytest tests/lean/test_repl.py::TestEndToEnd -v
```

### End-to-end test suite (`TestEndToEnd`)

These tests exercise the full stack: Claude Haiku generates tactic candidates via the Anthropic API, `BestFirstSearch` drives the proof search, and `SubprocessExecutor` verifies each tactic against a real `lake exe repl` process.

| Test | Theorem | Expected proof |
|---|---|---|
| `test_anthropic_proves_simple_theorem` | `∀ n : Nat, n + 0 = n` | `simp` |
| `test_anthropic_prove_parallel` | `∀ n : Nat, n + 0 = n` | `simp` (3 parallel searches) |
| `test_binomial_square` | `∀ a b : Int, (a + b)² = a² + 2·a·b + b²` | `intro a b; ring` |
| `test_contrapositive` | `∀ (p q : Prop), (p → q) → ¬q → ¬p` | `intro p q hpq hnq hp; exact hnq (hpq hp)` |

The first two tests verify basic plumbing. The last two are more meaningful: `test_binomial_square` requires Claude to produce `ring` (a Mathlib tactic not reachable by `simp` or `omega`), and `test_contrapositive` requires a multi-step propositional logic proof where `simp`/`omega`/`ring` all fail.

**Cost**: each test makes 1–3 Claude Haiku API calls (~$0.001 total). Runtime is ~30–40 seconds, dominated by Lean REPL startup.

## API Usage

Set your API key before running:

```bash
export ANTHROPIC_API_KEY=sk-...
```

### Single search (1 worker)

The simplest end-to-end run. One Lean REPL process, one priority queue, one proof attempt.

```python
import asyncio
from policy.anthropic import AnthropicPolicy
from lean.repl import SubprocessExecutor
from value.heuristic import HeuristicValue
from search.best_first import BestFirstSearch

async def main():
    policy = AnthropicPolicy()          # Claude generates tactic candidates
    executor = SubprocessExecutor()     # one Lean REPL subprocess
    value = HeuristicValue()            # heuristic: fewer goals = more promising

    await executor.start()
    search = BestFirstSearch(policy=policy, executor=executor, value=value)

    result = await search.prove(
        "theorem foo : ∀ n : ℕ, n + 0 = n := by",
        budget=100,
    )

    print(result)           # ProofResult(success=True, steps=2, ...)
    if result.success:
        print(result.proof_trace)   # ["intro n", "simp"]

    await executor.close()

asyncio.run(main())
```

### Parallel search (k workers)

k independent searches run concurrently — each with its own Lean REPL and priority queue.

```python
import asyncio
from policy.anthropic import AnthropicPolicy
from lean.repl import SubprocessExecutor
from value.heuristic import HeuristicValue
from search.best_first import BestFirstSearch, prove_parallel

async def main():
    k = 4
    policy = AnthropicPolicy()
    value = HeuristicValue()

    # Each search gets its own executor (its own Lean REPL process)
    executors = [SubprocessExecutor() for _ in range(k)]
    for e in executors:
        await e.start()

    searches = [
        BestFirstSearch(policy=policy, executor=e, value=value)
        for e in executors
    ]

    result = await prove_parallel(
        "theorem foo : ∀ n : ℕ, n + 0 = n := by",
        searches=searches,
        budget=100,
    )

    print(result)
    for e in executors:
        await e.close()

asyncio.run(main())
```

Each component is swappable:
- Replace `AnthropicPolicy` with `MockPolicy` to test without API calls
- Replace `SubprocessExecutor` with `MockExecutor` to test without Lean
- Replace `HeuristicValue` with a trained value model in later phases
- `BestFirstSearch` can be replaced with more complex search algorithms like MCTSSearch(TODO)

## Key modules

| Module | Purpose |
|---|---|
| `core/proof_state.py` | `ProofState`, `Goal`, `Hypothesis` data types |
| `core/executor.py` | `LeanExecutor` protocol + `StepResult` |
| `core/policy.py` | `PolicyModel` protocol + `TacticCandidate` |
| `core/value.py` | `ValueModel` protocol |
| `lean/repl.py` | `LeanWorker` (REPL subprocess) + `SubprocessExecutor` |
| `lean/mock_executor.py` | `MockExecutor` for testing without Lean |
| `policy/mock.py` | `MockPolicy` — fixed tactics, no API calls |
| `policy/anthropic.py` | `AnthropicPolicy` — calls Claude API |
| `value/heuristic.py` | `HeuristicValue` — goal count + depth heuristic |
| `search/best_first.py` | `BestFirstSearch` + `prove_parallel` |
