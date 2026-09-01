# Known issues

Running list of defects and open questions, maintained as evaluations run.

**Rules for this file.** Every entry cites the evidence that established it and
where to re-check it. An entry moves to *Fixed* only when a run or test
demonstrates the change, not when the code is written. Claims that turned out
to be wrong go to *Retracted* rather than being deleted — several hours were
lost re-investigating hypotheses that had already been refuted once.

**Before adding an entry, read the artifacts.** `results/eval_*.json`,
`traces/eval_*/*.txt`, and `traces/eval_*/lean/*.jsonl` (written under
`--trace`) usually already contain the answer. Three separate investigations
here reconstructed something downstream instead of reading the primary record,
and each produced a wrong conclusion.

---

## Open — evidence-backed

### 1. Sub-lemmas are never checked before being invested in
Each failed run opens **8–34 distinct `have` subgoals** and closes none.
Deliberate refutation attempts number **under one per 50-turn run** across 21
failed runs.

The model *can* already test a claim — `have h : ¬(∀ …) := by push_neg; exact
⟨…⟩` is a legal single tactic, and Lean verifies it. Nothing frames that as a
legitimate move, and nothing would act on the result: a proven refutation adds
a hypothesis to one state, leaves the false goal open, and does not touch
sibling states carrying the same claim.

Cost when it bites: `imo2026_q1a_termination` spent 50 turns on
`d + a*b < d*a + d*b`, refuted by `m=2, n=3`.

### 2. Refuted facts do not persist
`imo2026_q1a_termination` produced three counterexamples to its own goal
(turns 3, 37, 45) and acted on none durably. `Ledger.reasoning` keeps only the
*latest* plan per state, so each was overwritten within a turn or two.

There is no object a refutation can attach to: abandonment is keyed to a state
id, and a state id hashes the whole goal bundle, so the same claim under a
different parameterisation is an unrelated state. Trace shows the identical
false inequality live in `a722c37e`, `fe963742` and `7f0d9359`; only the first
was ever abandoned.

### 3. Every run consumes its entire budget
21 of 21 failed runs used all 50 turns. No run converged, backed out, or
restarted from the root with a different plan. A wrong choice at turn 3 costs
the whole run.

### 4. Escalation to arithmetic hammering
`nlinarith`/`linarith` share rises **25% → 38%** between first and last third
of a run (individual runs 19%→62%, 25%→69%, 38%→88%). Late turns permute hint
lists rather than change the argument.

Partly self-inflicted: "never repeat a tactic verbatim" plus the exhausted-
attempts list makes "find an untried hint combination" the locally rational
move. Not universal — problems that are not inequality-shaped sit at 0%.

### 5. `internal exception #5` loses Lean's real error
`#5` is `abortTactic` (index 5 of `Lean.internalExceptionsRef`, read from a
live REPL). It arrives as `keys=['message']` with `messages[]` empty, no
goals — five opaque words where Lean knew the cause.

Occurs at **7.8%** of tactic steps on a well-formed problem
(`eval_20260827_183214`), so it is not an artifact of the preamble bug.
Triggering tactics observed: `set`, `let` (probe, with an unresolvable name),
and `rw`, `rcases … <;> …` (live run). The unifying cause is **not known**.

Possible fix, untested: re-send the failing tactic through `cmd` mode, where
errors do land in `messages[]`, purely to recover the text.

### 6. The 30s `_send` timeout fires, invisibly
4 of 511 tactic steps (0.8%) in `eval_20260825_223800`; three were the same
`div_le_div_iff` shape. Each costs ~65s (timeout plus drain). Recorded only in
the raw JSONL — no Ledger entry, no prompt text — so the model retried the
hanging tactic twice more with no way to know it had hung.

### 7. Prompt bloat: paths and duplicated plans
A deep state's `path:` field reproduces every tactic verbatim including long
`first | … | …` chains (~800 chars for one state). Early turns render the same
"Last stated plan" paragraph on four states at once. Both grow with the
frontier.

### 8. The test suite writes into `results/`
`pytest tests/` runs `run_eval` with `LEAN_SKIP_MATHLIB=1`, producing 0/5
easy-tier results interleaved by timestamp with real runs (120 mock easy-tier
files on record). Nearly caused a config difference to be read as a
regression. Tests should write to a temp dir.

---

## Open questions

- **Does the refutation gap generalise?** Measured on `imo2026_q1a`; the
  `imo2011_q3` and `imo2005_q3` traces are on disk and unchecked.
- **Is `imo2011_q3` reachable at all?** 0/5 across Sonnet and DeepSeek. The
  model recovers the key lemma `hxt` reliably but never instantiates it at two
  different base points to get `a·f a + b·f b ≤ 2·f a·f b` — 0/50 turns in
  both trials, though it states the idea in words at turn 1 / turn 7.
- **Why does DeepSeek over-assert falsity?** 29 claims across 15 runs vs
  Sonnet's 2 across 8, dose-dependent on outcome. Cause unknown; it is *not*
  tool-failure misreading (see Retracted).
- **Do the 2026 statements hold?** `benchmarks/imo2026/*/solution.lean` are
  sorry-free proofs of exactly these statements and are not yet wired into
  `scripts/verify_problem_set.py`. Until then a 2026 failure cannot distinguish
  model limitation from a mis-transcribed statement.
- **Contamination vs formalisation style.** 2011 problems are bare statements;
  2026 problems ship 6+ custom definitions. Any old-vs-new comparison is
  confounded until style is held constant.

---

## Fixed

- **Statements declaring their own definitions were unprovable** (`43740dd4`).
  A proofState does not carry declarations made in the same command as the
  theorem, so every tactic naming one failed — including `exact h`. All 15
  IMO 2026 problems were impossible by construction. `results/eval_20260827_161523.json`
  (0/3) measures this bug, **not** the model. After: own-definition errors
  283 → 0, tactic success 20% → 62%.
- **`_proof_state_cache` collision across environments** (`43740dd4`). Keyed on
  goal text only; per-problem environments made identical goal text ambiguous.
  Now cleared at each `reset()`.
- **Abandonment was irreversible** (`3e7e3f99`). Cost up to 24 of 50 turns per
  run. `Ledger.retired` + `restore()`.
- **Abandoning every state killed the search** (`3e7e3f99`). `imo2011_q3`
  reported `frontier_exhausted` with half its budget unspent.
- **Error classifier was unreliable and fed to the model** (`3e7e3f99`). Two of
  nine categories matched strings Lean never emits; the catch-all held a third
  of all errors. Removed from prompt and telemetry.
- **No record of raw Lean I/O** (`3e7e3f99`). `traces/eval_*/lean/*.jsonl`.

---

## Retracted — do not re-investigate

- **"The model echoes the prompt placeholder as a tactic."** A regex matching
  the system prompt logged at the top of every trace. Never happened.
- **"`repl.py` drops Lean's real error behind `message`."** The two fields are
  mutually exclusive (thrown tactic vs produced state). 0 co-occurrences in
  511 steps.
- **"`msg_errors[0]` discards further errors."** Lean's elaborator
  short-circuits; 0 of 5 probes produced multi-error responses on the tactic
  path.
- **"Falsity assertions follow tool crashes."** 17% of DeepSeek's fell on a
  turn showing a crash, against a 24% base rate — slightly anti-correlated.
- **"Multi-variable generalisation distinguishes wins from losses."** 1/7 wins,
  1/9 losses.
- **"The 30s timeout never fires."** It does, at 0.8% — see Open #6.
- **"`internal exception #5` is `set`/`let` specifically."** `rw` and
  `rcases … <;>` also produce it.
