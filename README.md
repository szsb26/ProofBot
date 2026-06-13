# Theorem Prover

A best-first proof search system for Lean 4, backed by an LLM policy.

Naive LLM theorem provers ask the model to prove a theorem in one shot. Because the LLM never runs Lean to verify its output, hallucinations and invalid derivations slip through. This repo takes a different approach: the LLM generates candidate tactics, and every candidate is immediately verified by a real Lean 4 process. A search algorithm (currently Best First Search) explores the proof tree, guided by the LLM and a value heuristic, until a complete proof is found or the budget is exhausted.

The policy (LLM backend) and the search algorithm are both pluggable. Anthropic's Claude and DeepSeek are supported out of the box; adding a new provider requires implementing one method.

---

## Using the prover (no Python required)

This section is for mathematicians who want to prove theorems from the command line without writing any code.

### 1. Get an API key

The prover uses an LLM to generate proof steps. Choose a provider:

**Option A — Anthropic (Claude)**

1. Go to [console.anthropic.com](https://console.anthropic.com) and create an account
2. Navigate to **API Keys** and create a new key (starts with `sk-ant-...`)

**Option B — DeepSeek**

1. Go to [platform.deepseek.com](https://platform.deepseek.com) and create an account
2. Navigate to **API Keys** and create a new key (starts with `sk-...`)

### 2. One-time setup

```bash
# Clone the repo
git clone <repo-url>
cd theorem_prover

# Create a Python environment and install dependencies
python -m venv .venv
source .venv/bin/activate      # on Windows: .venv\Scripts\activate
pip install -e .

# Build the Lean project (downloads and compiles Mathlib — takes ~5 minutes)
cd lean_project && lake build && cd ..
```

### 3. Set your API key

Create a `.env` file in the project root so you don't have to set it every session:

```
# For Anthropic:
ANTHROPIC_API_KEY=sk-ant-...

# For DeepSeek:
DEEPSEEK_API_KEY=sk-...
```

Or export it in your shell each session:

```bash
export ANTHROPIC_API_KEY=sk-ant-...
# or
export DEEPSEEK_API_KEY=sk-...
```

### 4. Prove a theorem

Pass your Lean 4 theorem statement as a string. The statement must end with `:= by`:

```bash
# Using Claude (default)
python run.py "theorem add_comm_example : ∀ n m : Nat, n + m = m + n := by"

# Using DeepSeek
python run.py "theorem add_comm_example : ∀ n m : Nat, n + m = m + n := by" --policy deepseek
```

Example output:
```
Theorem : theorem add_comm_example : ∀ n m : Nat, n + m = m + n := by
Search  : 1 worker, budget=100, policy=anthropic (claude-haiku-4-5-20251001)

Starting Lean workers... ready.
Searching...

✓  Proof found in 3.1s (2 nodes)

Lean 4 proof:
  theorem add_comm_example : ∀ n m : Nat, n + m = m + n := by
    intro n m
    omega
```

The **Lean 4 proof** block at the bottom is a complete, verified proof you can paste directly into your Lean file.

### 5. Writing theorem statements

Your theorem statement should be valid Lean 4 syntax ending in `:= by`. Some examples:

```bash
# Natural number arithmetic
python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by"

# Integer algebra (uses Mathlib's ring tactic)
python run.py "theorem foo : ∀ a b : Int, (a + b)^2 = a^2 + 2*a*b + b^2 := by"

# Propositional logic
python run.py "theorem foo : ∀ (p q : Prop), (p → q) → ¬q → ¬p := by"

# Give your theorem a meaningful name
python run.py "theorem my_lemma : ∀ n : Nat, n * 2 = n + n := by"
```

### 6. When the search fails

If the prover returns `✗ No proof found`, try:

```bash
# Give it more search budget (default is 100 nodes)
python run.py "theorem foo : ..." --budget 300

# Run multiple independent searches in parallel
python run.py "theorem foo : ..." --workers 4

# Both together for harder theorems
python run.py "theorem foo : ..." --workers 4 --budget 200

# Switch to a more powerful model
python run.py "theorem foo : ..." --model claude-sonnet-4-6                # Anthropic
python run.py "theorem foo : ..." --policy deepseek --model deepseek-reasoner  # DeepSeek
```

**Cost**: the default models (Claude Haiku, DeepSeek Chat) cost roughly $0.001 per proof attempt.

---

## Architecture

```
prove_parallel(theorem, searches=[...], budget=100)
    └── asyncio.gather(search_0.prove(), search_1.prove(), ..., search_k.prove())
            │
            └── BestFirstSearch          (one priority queue per instance)
                    │
                    ├── PolicyModel      (tactic generator — AnthropicPolicy / DeepSeekPolicy / MockPolicy)
                    ├── ValueModel       (state evaluator — HeuristicValue)
                    └── LeanExecutor     (tactic verifier — SubprocessExecutor or MockExecutor)
                            │
                            └── LeanWorker → lake exe repl  (one OS process)
```

**Parallelism**: create k `SubprocessExecutor` + `BestFirstSearch` pairs and run them with `prove_parallel`. Each search has its own Lean REPL process and priority queue — they explore the proof tree independently and concurrently.

**Policy**: the `PolicyModel` protocol (`core/policy.py`) defines a single method:

```python
async def get_tactics(state: ProofState, premises: list[str], k: int) -> list[TacticCandidate]
```

`AnthropicPolicy` and `DeepSeekPolicy` both extend `BaseLLMPolicy` (`policy/base.py`), which handles prompt construction, response parsing, and error fallback. Adding a new provider means subclassing `BaseLLMPolicy` and implementing `_call_api(user_prompt) -> str`.

---

## Prerequisites

- Python 3.11
- Lean 4 / Mathlib (built via `lake build` inside `lean_project/`)

## Setup

```bash
python -m venv .venv
source .venv/bin/activate
pip install -e .
```

## Quick start

```bash
# Anthropic
export ANTHROPIC_API_KEY=sk-ant-...
python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by"

# DeepSeek
export DEEPSEEK_API_KEY=sk-...
python run.py "theorem foo : ∀ n : Nat, n + 0 = n := by" --policy deepseek
```

**Options:**

```
python run.py "theorem ..." --policy anthropic    # use Claude (default)
python run.py "theorem ..." --policy deepseek     # use DeepSeek
python run.py "theorem ..." --workers 4           # run 4 parallel searches
python run.py "theorem ..." --budget 200          # expand up to 200 nodes per search
python run.py "theorem ..." --model deepseek-reasoner   # override the model
python run.py "theorem ..." --api-key sk-...      # pass key directly
```

---

## Running tests

```bash
# Fast unit tests (no Lean, no API key) — seconds
source .venv/bin/activate
pytest tests/ --ignore=tests/lean/test_repl.py -q

# Lean infrastructure tests (no API key, no Mathlib load) — ~30s
LEAN_SKIP_MATHLIB=1 pytest tests/lean/test_repl.py -k "not EndToEnd" -q

# Full suite including end-to-end (loads Mathlib, ~5 min startup per worker)
ANTHROPIC_API_KEY=sk-ant-... DEEPSEEK_API_KEY=sk-... pytest tests/ -q
```

`LEAN_SKIP_MATHLIB=1` skips the `import LeanProject` step so REPL workers start in ~1s instead of ~300s. Use it when running infrastructure tests that don't exercise Mathlib tactics (`ring`, `linarith`, etc.).

### Test suite overview

| Class | Lean | API | What it tests |
|---|---|---|---|
| `TestParseGoalString` | No | No | Goal string parser |
| `TestParseTactics` | No | No | LLM response parser |
| `TestBuildUserPrompt` | No | No | Prompt builder |
| `TestAnthropicPolicyGetTactics` | No | No (mocked) | AnthropicPolicy unit tests |
| `TestDeepSeekPolicyGetTactics` | No | No (mocked) | DeepSeekPolicy unit tests |
| `TestSubprocessExecutor` | Yes | No | Lean REPL executor |
| `TestProveParallelIntegration` | Yes | No (mock policy) | k parallel searches |
| `TestCLIWithMock` | No | No | CLI arg parsing + mock stack |
| `TestCLIIntegration` | Yes | No (mock policy) | CLI with real Lean |
| `TestEndToEnd` | Yes | Anthropic | Full stack: Claude + Lean (simple + add_comm + contrapositive) |
| `TestDeepSeekEndToEnd` | Yes | DeepSeek | Full stack: DeepSeek + Lean (simple + parallel + add_comm) |
| `TestCLIEndToEnd` | Yes | Anthropic | Full stack via CLI |
| `TestCLIDeepSeekEndToEnd` | Yes | DeepSeek | Full stack via CLI + DeepSeek |

---

## API Usage

### Single search (1 worker)

```python
import asyncio
from policy.anthropic import AnthropicPolicy   # or: from policy.deepseek import DeepSeekPolicy
from lean.repl import SubprocessExecutor
from value.heuristic import HeuristicValue
from search.best_first import BestFirstSearch

async def main():
    policy = AnthropicPolicy()       # reads ANTHROPIC_API_KEY from env
    executor = SubprocessExecutor()
    value = HeuristicValue()

    await executor.start()
    search = BestFirstSearch(policy=policy, executor=executor, value=value)

    result = await search.prove(
        "theorem foo : ∀ n : ℕ, n + 0 = n := by",
        budget=100,
    )

    if result.success:
        print(result.proof_trace)    # e.g. ["intro n", "simp"]

    await executor.close()
    await policy.close()

asyncio.run(main())
```

### Parallel search (k workers)

```python
import asyncio
from policy.deepseek import DeepSeekPolicy     # or AnthropicPolicy
from lean.repl import SubprocessExecutor
from value.heuristic import HeuristicValue
from search.best_first import BestFirstSearch, prove_parallel

async def main():
    k = 4
    policy = DeepSeekPolicy()        # reads DEEPSEEK_API_KEY from env
    value = HeuristicValue()

    executors = [SubprocessExecutor() for _ in range(k)]
    await asyncio.gather(*[e.start() for e in executors])

    searches = [
        BestFirstSearch(policy=policy, executor=e, value=value)
        for e in executors
    ]

    result = await prove_parallel(
        "theorem foo : ∀ n : ℕ, n + 0 = n := by",
        searches=searches,
        budget=100,
    )

    print(result.success, result.proof_trace)

    for e in executors:
        await e.close()
    await policy.close()

asyncio.run(main())
```

Each component is swappable:
- Replace `AnthropicPolicy`/`DeepSeekPolicy` with `MockPolicy` to test without API calls
- Replace `SubprocessExecutor` with `MockExecutor` to test without Lean
- Replace `HeuristicValue` with a trained value model
- `BestFirstSearch` can be replaced with more complex search algorithms like MCTSSearch (TODO)

---

## Supported policies

| Policy | Provider | Default model | Key env var |
|---|---|---|---|
| `AnthropicPolicy` | Anthropic | `claude-haiku-4-5-20251001` | `ANTHROPIC_API_KEY` |
| `DeepSeekPolicy` | DeepSeek | `deepseek-chat` | `DEEPSEEK_API_KEY` |
| `MockPolicy` | — | — | — |

All LLM policies extend `BaseLLMPolicy` (`policy/base.py`). To add a new provider, subclass `BaseLLMPolicy` and implement `_call_api(user_prompt: str) -> str`.

---

## Value model

The priority queue in `BestFirstSearch` ranks states by a value estimate from `HeuristicValue`:

```
value = exp(-(1.0 × num_goals + 0.05 × depth))
```

States with fewer open goals and shallower depth are explored first. This requires no training data — it is a deliberate baseline for early development.

**Replacing it**: implement the `ValueModel` protocol in `core/value.py` and pass your model to `BestFirstSearch`. A trained value network would learn to predict the probability that a state leads to a closed proof — a much stronger signal than goal count alone.

---

## Key modules

| Module | Purpose |
|---|---|
| `core/proof_state.py` | `ProofState`, `Goal`, `Hypothesis` data types |
| `core/executor.py` | `LeanExecutor` protocol + `StepResult` |
| `core/policy.py` | `PolicyModel` protocol + `TacticCandidate` |
| `core/value.py` | `ValueModel` protocol |
| `lean/repl.py` | `LeanWorker` (REPL subprocess) + `SubprocessExecutor` |
| `lean/mock_executor.py` | `MockExecutor` for testing without Lean |
| `policy/base.py` | `BaseLLMPolicy` — shared prompt/parse logic for LLM policies |
| `policy/anthropic.py` | `AnthropicPolicy` — calls Claude API |
| `policy/deepseek.py` | `DeepSeekPolicy` — calls DeepSeek API (OpenAI-compatible) |
| `policy/mock.py` | `MockPolicy` — fixed tactics, no API calls |
| `value/heuristic.py` | `HeuristicValue` — goal count + depth heuristic |
| `search/best_first.py` | `BestFirstSearch` + `prove_parallel` |
| `run.py` | CLI entrypoint for mathematicians |
