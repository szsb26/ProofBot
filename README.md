# ProofBot

An LLM-guided proof search system for Lean 4.

Naive LLM theorem provers ask the model to prove a theorem in one shot. Because the LLM never runs Lean to verify its output, hallucinations and invalid derivations slip through. ProofBot takes a different approach: the LLM proposes a tactic, and it is immediately verified by a real Lean 4 process. A `Ledger` records every open proof state and every tactic attempted against it. Each turn, one LLM call reads the full ledger and decides both which state to continue from (or abandon) and which single tactic to try there, until a complete proof is found or the budget is exhausted.

The policy (LLM backend) is pluggable. Anthropic's Claude and DeepSeek are supported out of the box; adding a new provider requires implementing one method.

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

Requires Python 3.11 and Lean 4.

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

### 4b. Interactive mode (recommended for sessions)

Lean workers take ~10 minutes to load Mathlib on first start. If you want to prove several theorems in a row, use `--interactive` (`-i`) to load Mathlib once and then submit theorems one at a time:

```bash
python run.py --interactive
# or with DeepSeek:
python run.py --interactive --policy deepseek
```

```
Starting Lean workers (loading Mathlib, ~10 min first run)... ready.

Interactive mode — 1 worker, budget=100, policy=anthropic (claude-haiku-4-5-20251001)
Enter a theorem statement, or 'quit' to exit.

theorem> theorem foo : ∀ n : Nat, n + 0 = n := by
Searching...
✓  Proof found in 2.3s (3 nodes)

Lean 4 proof:
  theorem foo : ∀ n : Nat, n + 0 = n := by
    intro n
    simp

theorem> quit
Goodbye.
```

- The `:= by` suffix is added automatically if you omit it
- Type `quit`, `exit`, or press `Ctrl+C` to exit
- All other flags (`--workers`, `--budget`, `--model`, etc.) work the same way

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

For the full set of options — `--budget`, `--workers`, `--model`, `--policy`,
`--interactive` — run `python run.py --help`. On a hard theorem, raising
`--budget` and switching to a stronger model are the two levers that matter
most.


## Architecture

```
prove_parallel(theorem, searches=[...], budget=100)
    └── asyncio.gather(search_0.prove(), search_1.prove(), ..., search_k.prove())
            │
            └── LedgerSearch            (one Ledger per instance — no priority queue)
                    │
                    ├── PolicyModel      (tactic + director generator — AnthropicPolicy / DeepSeekPolicy / MockPolicy)
                    └── LeanExecutor     (tactic verifier — SubprocessExecutor or MockExecutor)
                            │
                            └── LeanWorker → lake exe repl  (one OS process)
```

**Parallelism**: create k `SubprocessExecutor` + `LedgerSearch` pairs and run them with `prove_parallel`. Each search has its own Lean REPL process and its own ledger — they explore the proof tree independently and concurrently.

**Policy**: the `PolicyModel` protocol (`core/policy.py`) defines the tactic-generation method used by the director call:

```python
async def get_next_action(theorem: str, ledger: Ledger, premises: list[str]) -> DirectorResponse
```

`DirectorResponse` carries which open state to continue from, any states to abandon, and exactly one tactic for the chosen state — it may be `;`-chained, or use Lean's `first | tac1 | tac2` to hedge. `AnthropicPolicy` and `DeepSeekPolicy` both extend `BaseLLMPolicy` (`policy/base.py`), which handles ledger serialization, response parsing, and error fallback. Adding a new provider means subclassing `BaseLLMPolicy` and implementing `_call_api(user_prompt, system_prompt, max_tokens, enable_thinking) -> str`.

---


## Running tests

```bash
# Fast unit tests (no Lean, no API key) — seconds
source .venv/bin/activate
pytest tests/ --ignore=tests/lean/test_repl.py -q

# Lean infrastructure tests (no API key, no Mathlib load) — ~30s
LEAN_SKIP_MATHLIB=1 pytest tests/lean/test_repl.py -k "not EndToEnd" -q

# Full suite including end-to-end (loads Mathlib, ~10 min startup per worker)
ANTHROPIC_API_KEY=sk-ant-... DEEPSEEK_API_KEY=sk-... pytest tests/ -q
```

`LEAN_SKIP_MATHLIB=1` skips the `import LeanProject` step so REPL workers start in ~1s instead of ~300s. Use it when running infrastructure tests that don't exercise Mathlib tactics (`ring`, `linarith`, etc.).


## Supported policies

| Policy | Provider | Default model | Key env var |
|---|---|---|---|
| `AnthropicPolicy` | Anthropic | `claude-haiku-4-5-20251001` | `ANTHROPIC_API_KEY` |
| `DeepSeekPolicy` | DeepSeek | `deepseek-v4-flash` | `DEEPSEEK_API_KEY` |
| `MockPolicy` | — | — | — |

All LLM policies extend `BaseLLMPolicy` (`policy/base.py`). To add a new provider, subclass `BaseLLMPolicy` and implement `_call_api(user_prompt: str) -> str`.

---


## Evaluation

`run_eval.py` runs a curated problem set (tiers: `easy`, `medium`, `hard`, `stretch`, `imo`) and writes results to `results/eval_<timestamp>.json`.

```bash
python run_eval.py                                    # all problems
python run_eval.py --problems imo --budget 50         # one tier
python run_eval.py --problems imo1968_tetrahedron     # one problem by name
python run_eval.py --problems imo --trials 3 --trace  # pass@k + save traces of failures
```

The `imo` tier is 22 real competition problems lifted from Mathlib's `Archive/Imo`. Each ships a `reference_proof` that was replayed in this harness and required to close to zero goals, so provability is established rather than assumed — `scripts/verify_problem_set.py` re-checks them all in one command. Mathlib's helper lemmas are used for that verification but never shown to the prover: they are sub-lemmas, the decomposition a solver has to invent, and discovering them is the capability under test.

`--trace` saves the director's verbatim prompt and raw response for every turn of a failed trial to `traces/eval_<timestamp>/`. This is the primary debugging tool — at temperature 1.0 you cannot reproduce a specific failed attempt by re-running it. `scripts/trace_search.py` does the same for a single ad-hoc theorem.

### Where the prover currently stands

**The prover solves real IMO problems.** Given only the bare theorem statement
— no helper lemmas, no hints — it finds and verifies complete Lean proofs of
competition problems from the International Mathematical Olympiad.

Measured 2026-08-25, budget 50, temperature 1.0. Rows marked † were
re-measured 2026-09-01, after a round of harness fixes (goal-text rendering,
tactic-boundary splitting).

| Problem | DeepSeek v4 Pro | Claude Sonnet 5 |
|---|---|---|
| `imo1959_q1` — gcd / coprimality | ✓ 3/3, 14 nodes | ✓ 2/2, 10 nodes † |
| `imo1964_q1a` — modular arithmetic | ✓ 3/3, 41 nodes | ✓ 2/2, **8 nodes** † |
| `imo1963_q5` — trigonometric identity | ~ 1/3, 47 nodes | ✓ 2/2, 17 nodes † |
| `imo2005_q3` — algebraic inequality | ✗ 0/3 | ✓ 2/2, 27 nodes |
| `imo2011_q3` — functional equation | ✗ 0/3 | ✗ 0/1, budget exhausted † |

This is a **small sample** — 5 of the 22 problems in the `imo` tier, and 5 of
45 in the repo overall — chosen to span domains rather than to be
representative, and with uneven trial counts between the two columns. Read
solved/not-solved and node counts as the signal, not the rates. Run
`--problems imo` for the full tier.

---

