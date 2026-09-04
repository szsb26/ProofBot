# Goal granularity: how a proof state should be represented

**Status: open. Nothing decided, nothing implemented.** This records what we
established on 2026-09-02 so it does not have to be re-derived, and states the
questions we have not answered yet.

The trigger was `imo2026_q5` (`traces/eval_20260902_134559`), where the search
spent roughly 24 of 50 turns proving a lemma that is false, while both halves
of the actual theorem sat untouched behind it in the same state.

---

## 1. What we have today

`ProofState.goals` is a `tuple[Goal, ...]` — the whole list of open goals.
Identity is `stable_hash`, a hash of the goal *text* only (not depth, not
path). `is_closed` is `len(goals) == 0`. One node in the `Ledger` = one such
list.

This is **not an independent design decision**. It mirrors Lean: the REPL
hands out an integer handle per *tactic state*, and a tactic state is a list
of goals. `LeanWorker._proof_state_cache` maps our content hash to that
integer. Since every edge in our tree is "send this tactic string to that
integer", the node has to be whatever the integer refers to.

One thing *is* our own choice and differs from Lean: Lean is handle-addressed
(two states reached by different routes are different integers even if
identical); we are content-addressed, so converging paths collapse to one
node. Deliberate — see the `stable_hash` docstring.

## 2. Verified constraints (probed against a live REPL, 2026-09-02)

- **A tactic hits the first goal.** That is Lean's convention for making
  linear proof scripts unambiguous, not a logical necessity.
- **Any goal is addressable.** Demonstrated on a 3-goal state:
  `pick_goal 3` reorders; `on_goal 3 => omega` closes goal 3 in place leaving
  1 and 2; `rotate_left` cycles; `all_goals tac` hits every goal.
- **`case name => tac` works only when goals are named.** A bare `have foo :`
  produces `case foo`. `refine ⟨?_, ?_⟩` names its holes `refine_1`,
  `refine_2`, … — an earlier draft of this note claimed they were anonymous
  and that `case` failed on them; that is wrong. Observed directly in
  `traces/eval_20260903_123103`, where Lean reported `case refine_1` /
  `case refine_2` and the director addressed them by those tags.
- **`case tag => tac` must CLOSE the goal it selects.** Probed 2026-09-03 on
  a 2-goal state with a tactic that progresses without finishing
  (`constructor` on `P ∧ P`): `case right => constructor` returned
  "unsolved goals" and banked NOTHING, while `on_goal 2 =>`, `pick_goal 2`,
  `all_goals` and `any_goals` all kept the partial result. `case` is the only
  form of the six with this property, and it is why a multi-goal state can
  become a turn sink: every attempt at a non-first goal must be a complete
  proof of that branch, written from scratch.
- **The tactic endpoint gives no per-goal handle.** After `constructor`:
  `goals=2, proofState=6, sorries=None`. One handle, whole list.
- **The `cmd` endpoint does.** A command containing several `sorry` holes
  returns one `proofState` per hole, and they are independently steppable out
  of order. This is already how `reset()` bootstraps every search — one hole.
- **Cost of re-entering `cmd` mode:** median 70 ms, p90 3.4 s, max 23 s
  (measured over 97 replays), because it re-elaborates from the theorem.

## 3. What we learned about the failure

Three facts combine badly:

1. a bare `have` puts the **unproven claim first**,
2. tactics hit the first goal,
3. both goals live behind **one handle**.

So the moment the model writes a bare `have`, the whole search points at its
own new claim. In `imo2026_q5` that claim (`hconst`) is false — substituting
the theorem's own answer form `f t = t + c` reduces it to `0 ≤ 2c(y − x)`,
which fails whenever `y < x`. The run ended with all three goals still open:
`case hconst`, `case mp`, `case mpr`. `mpr` had been proven inside a dozen
turns in an earlier run; here it was never touched.

The model **suspected** the lemma was false at turn 45 ("my target hconst
statement itself may need correction") and kept going for five more turns.
The state from before the `have` was open and displayed the entire time, so
the escape route was visible and unused.

## 4. Finding 1 — the LLM should be able to work any goal in a state

Agreed 2026-09-02. Today it effectively cannot, for two reasons:

- **The prompt states the constraint and offers no way around it.** "A tactic
  applies to the FIRST goal only, so the goals are worked through in order —
  unless you use a combinator that targets more than one: `tac1 <;> tac2`…"
  `<;>` hits *every* goal, not a chosen one. `pick_goal`, `on_goal`,
  `rotate_left`, `case name =>` are never mentioned.
- **The `have` rule compounds it**: "opens `statement` as a new first goal you
  can then prove step by step over the following turns."

Together these describe the q5 failure as the intended procedure.

Behaviour matches: across **3,025 tactics ever sent**, goal-selection
constructs appear 9 times (`pick_goal` 1, `on_goal` 0, `rotate_left` 3,
`case … =>` 1, `swap` 4).

**Update 2026-09-03 — partly answered, and not by the data structure.**
The prompt's ranking was deleted: it had said "prefer" case/on_goal/
all_goals/any_goals and "reach for [pick_goal/rotate_left/swap] last" on the
duplicate-node grounds above. That traded a trivial bookkeeping cost for the
model's ability to make incremental progress, since only `case` requires
closing its goal. imo2026_q5 (`traces/eval_20260903_123103`) spent 33 of 50
turns re-authoring one all-or-nothing `case mpr =>` block; at turn 27 it
moved deliberately from `on_goal` to `case` for robustness against shifting
indices — sound reasoning — and unknowingly gave up progress-banking, with
nothing in the system able to tell it. The six constructs are now listed as
facts, the closure asymmetry stated, and nothing ranked.

**Still open:** whether the *ledger* should be able to attribute failure per
goal or prune one branch. That is the data-structure question below, and
nothing measured so far requires it.

## 5. The design question we have not answered

**Should a node be a goal list, or a single goal?**

Per-goal nodes would buy: failure attribution ("18 tactics failed on
`hconst`, 0 tried on `mp`"), independent pruning of one branch, and
out-of-order work without spending a tactic on reordering.

They would cost:

- **Tactics that act across goals** — `<;>`, `all_goals` — stop being
  expressible against a single-goal node.
- **The success signal changes meaning.** Today `proofStatus == "Completed"`
  on a continuous path means *the theorem is proven*, and it is what stops
  `sorry` and `native_decide` being accepted. With independent holes,
  `Completed` means *this hole closed*: in the probe, one hole reported
  `Completed` while the theorem still had an unproven `have`. Something must
  then reassemble the pieces and re-verify the whole. That guard would need
  rethinking, not reusing.
- **Leaving the tactic endpoint.** Per-goal handles cannot be obtained from
  it at any price; they require re-entering `cmd` mode with a hole skeleton,
  with the re-elaboration cost above.

**Not yet established:** whether a hole skeleton preserves *dependency*
correctly — a `have h : P` means the continuation gets `h : P` in context.
Verified for `refine ⟨?_, ?_, ?_⟩` (independent goals); **not** verified for
the `have` case, which is the shape that matters. Probe this before going
further.

## 6. Related

`docs/draft-sketch-prove.md` proposes proving each sub-lemma in its own fresh
search. That is the same insight from the other direction: sub-lemmas want
their own isolated handle. Whatever we decide here should be consistent with
that, or explicitly supersede it.

## 7. Deliberately not decided here

- whether to add goal-selection guidance to the prompt
- whether to key failure records on the first goal's hash rather than the
  state's (a ledger-side change that gives attribution without touching the
  execution model)
- whether to detect and surface a stuck sub-goal, and name the state to
  retreat to
