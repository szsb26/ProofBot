# Tetrahedron vertex-triangle problem

**Problem.** Prove that in any tetrahedron there is a vertex such that the
three edge lengths meeting at that vertex are the side lengths of some
triangle.

Solved using this repo's search stack (`search/best_first.py`,
`policy/claude_cli.py`, `lean/repl.py`) against real Lean 4 + Mathlib — not
mocked. This doc reports exactly what the search found on its own, what I
assembled by hand, and the fully machine-verified result.

**Total time:** ~8 minutes wall-clock end to end (12:31:51–12:39:47),
starting from a warm Lean worker (Mathlib had already been built earlier in
the session — that one-time `lake build` cost isn't counted here). Of that:
- **~2m09s** — Lean worker startup + both search attempts combined
  (reported by `BestFirstSearch` itself: 50.5s for `vertex_pair_lemma`,
  43.7s for the failed direct attempt on the full theorem — 94.2s of actual
  search time, plus worker startup).
- **~5m47s** — hand-assembling the 6-way case split, iterating against the
  real Lean compiler (`lake env lean`) to fix two rounds of errors (a
  `subst` direction bug in the max-extraction step), and writing this doc.

So the part the search contributed (finding+verifying the actual hard
lemma) took under a minute; most of the wall-clock went to the
architecture/assembly work a human (or an unbuilt draft-sketch-prove
pipeline, see `docs/draft-sketch-prove.md`) would need to do around it.

## 1. Formalization

A tetrahedron `ABCD` has 6 edges. Each of its 4 faces is a genuine
(non-degenerate) triangle, so its 3 edges satisfy the strict triangle
inequality — this is the only geometric fact the proof needs; it doesn't
require Lean's Euclidean-geometry library or the actual 3D coordinates,
just the 6 edge lengths and the 12 face inequalities they imply. That makes
the theorem below slightly *more general* than the geometric statement: it
holds for any 6 positive reals satisfying the 4 faces' triangle
inequalities, whether or not they're realizable as an actual embedded
tetrahedron.

```lean
theorem tetra_vertex_triangle
    (AB AC AD BC BD CD : ℝ)
    (hAB : 0 < AB) (hAC : 0 < AC) (hAD : 0 < AD)
    (hBC : 0 < BC) (hBD : 0 < BD) (hCD : 0 < CD)
    (hABC1 : AB < AC + BC) (hABC2 : AC < AB + BC) (hABC3 : BC < AB + AC)
    (hABD1 : AB < AD + BD) (hABD2 : AD < AB + BD) (hABD3 : BD < AB + AD)
    (hACD1 : AC < AD + CD) (hACD2 : AD < AC + CD) (hACD3 : CD < AC + AD)
    (hBCD1 : BC < BD + CD) (hBCD2 : BD < BC + CD) (hBCD3 : CD < BC + BD) :
    (AB < AC + AD ∧ AC < AB + AD ∧ AD < AB + AC) ∨   -- vertex A
    (AB < BC + BD ∧ BC < AB + BD ∧ BD < AB + BC) ∨   -- vertex B
    (AC < BC + CD ∧ BC < AC + CD ∧ CD < AC + BC) ∨   -- vertex C
    (AD < BD + CD ∧ BD < AD + CD ∧ CD < AD + BD)      -- vertex D
```

## 2. What the search actually found vs. what I wrote

Ran via a small driver script (`BestFirstSearch` + `ClaudeCLIPolicy`,
model `sonnet`, one warm Lean worker):

**Attempt 1 — feed the raw theorem above straight to search.**
`success=False, nodes=9, failure_reason=queue_drained,
tactic_errors={'wrong_arguments': 3, 'tactic_failed': 53, 'syntax_error': 1}`.
It burned its budget guessing tactics and never found the key move (there
isn't a flat sequence of independent single-line tactics that closes this —
see below). This matches what we discussed earlier about the search having
no planning ability: the missing step here is exactly the "chain a plan,
don't guess flat tactics" gap from `docs/draft-sketch-prove.md`.

**The actual mathematical core, isolated as a standalone lemma:**
the argument only works once you fix *which* edge is the longest. Isolating
that step as its own goal:

```lean
theorem vertex_pair_lemma
    (x y1 y2 z1 z2 : ℝ)
    (hx : 0 < x) (hy1 : 0 < y1) (hy2 : 0 < y2) (hz1 : 0 < z1) (hz2 : 0 < z2)
    (hxy1 : y1 ≤ x) (hxy2 : y2 ≤ x) (hxz1 : z1 ≤ x) (hxz2 : z2 ≤ x)
    (hface1 : x < y1 + z1) (hface2 : x < y2 + z2) :
    (x < y1 + y2 ∧ y1 < x + y2 ∧ y2 < x + y1) ∨
    (x < z1 + z2 ∧ z1 < x + z2 ∧ z2 < x + z1)
```
(`x` = a candidate longest edge between two vertices P,Q; `y1,y2` = the
other two edges at P; `z1,z2` = the other two edges at Q; `hface1,hface2`
= the two faces containing `x` are genuine triangles.)

**Attempt 2 — feed this isolated lemma to search.**
`success=True, nodes=6, elapsed=50.5s`, proof trace:

```lean
by_contra h
simp only [not_or, not_and_or, not_lt] at h
rcases h with ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> linarith
```

This is genuinely the hard part of the problem, and it's a cleaner proof
than the one I'd sketched by hand (`by_contra` on the whole disjunction,
push the negation through both conjunctions at once, then let `linarith`
kill all 9 resulting cases in one shot) — the search found this
independently.

**What I wrote by hand:** everything the search *didn't* attempt — reducing
the full theorem to `vertex_pair_lemma`, which requires (a) identifying the
globally longest edge among all 6 (existence via nested `max` + `max_choice`,
6-way case split on which named edge it equals) and (b) applying
`vertex_pair_lemma` with the right variable assignment in each of the 6
cases and repackaging its two-way result into the right slot of the
four-way disjunction. This part is bookkeeping, not search — deciding
*which* case split to perform is exactly the kind of multi-step plan flat
tactic search can't discover, but once decided, executing it is mechanical.

## 3. Full proof — verified end-to-end

Assembled both pieces and checked the complete file with
`lake env lean` against this repo's built Mathlib (exit code 0, no errors,
only harmless "unused variable" warnings on `vertex_pair_lemma`'s `hx`,
`hz1`, `hz2`):

```lean
theorem vertex_pair_lemma
    (x y1 y2 z1 z2 : ℝ)
    (hx : 0 < x) (hy1 : 0 < y1) (hy2 : 0 < y2) (hz1 : 0 < z1) (hz2 : 0 < z2)
    (hxy1 : y1 ≤ x) (hxy2 : y2 ≤ x) (hxz1 : z1 ≤ x) (hxz2 : z2 ≤ x)
    (hface1 : x < y1 + z1) (hface2 : x < y2 + z2) :
    (x < y1 + y2 ∧ y1 < x + y2 ∧ y2 < x + y1) ∨
    (x < z1 + z2 ∧ z1 < x + z2 ∧ z2 < x + z1) := by
  by_contra h
  simp only [not_or, not_and_or, not_lt] at h
  rcases h with ⟨h1 | h1 | h1, h2 | h2 | h2⟩ <;> linarith

theorem tetra_vertex_triangle
    (AB AC AD BC BD CD : ℝ)
    (hAB : 0 < AB) (hAC : 0 < AC) (hAD : 0 < AD)
    (hBC : 0 < BC) (hBD : 0 < BD) (hCD : 0 < CD)
    (hABC1 : AB < AC + BC) (hABC2 : AC < AB + BC) (hABC3 : BC < AB + AC)
    (hABD1 : AB < AD + BD) (hABD2 : AD < AB + BD) (hABD3 : BD < AB + AD)
    (hACD1 : AC < AD + CD) (hACD2 : AD < AC + CD) (hACD3 : CD < AC + AD)
    (hBCD1 : BC < BD + CD) (hBCD2 : BD < BC + CD) (hBCD3 : CD < BC + BD) :
    (AB < AC + AD ∧ AC < AB + AD ∧ AD < AB + AC) ∨
    (AB < BC + BD ∧ BC < AB + BD ∧ BD < AB + BC) ∨
    (AC < BC + CD ∧ BC < AC + CD ∧ CD < AC + BC) ∨
    (AD < BD + CD ∧ BD < AD + CD ∧ CD < AD + BD) := by
  -- Find the globally longest edge M, and which named edge it equals.
  obtain ⟨M, hMAB, hMAC, hMAD, hMBC, hMBD, hMCD, hMeq⟩ :
      ∃ M : ℝ, AB ≤ M ∧ AC ≤ M ∧ AD ≤ M ∧ BC ≤ M ∧ BD ≤ M ∧ CD ≤ M ∧
        (AB = M ∨ AC = M ∨ AD = M ∨ BC = M ∨ BD = M ∨ CD = M) := by
    refine ⟨max AB (max AC (max AD (max BC (max BD CD)))), le_max_left _ _,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
    · rcases max_choice AB (max AC (max AD (max BC (max BD CD)))) with h | h
      · exact Or.inl h.symm
      rcases max_choice AC (max AD (max BC (max BD CD))) with h2 | h2
      · exact Or.inr (Or.inl (h.trans h2).symm)
      rcases max_choice AD (max BC (max BD CD)) with h3 | h3
      · exact Or.inr (Or.inr (Or.inl (h.trans (h2.trans h3)).symm))
      rcases max_choice BC (max BD CD) with h4 | h4
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h.trans (h2.trans (h3.trans h4))).symm)))
      rcases max_choice BD CD with h5 | h5
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (h.trans (h2.trans (h3.trans (h4.trans h5)))).symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (h.trans (h2.trans (h3.trans (h4.trans h5)))).symm))))
  -- Case on which edge achieves the max; hand the two "trivial" endpoints
  -- and the two faces containing that edge to vertex_pair_lemma.
  rcases hMeq with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases vertex_pair_lemma AB AC AD BC BD hAB hAC hAD hBC hBD hMAC hMAD hMBC hMBD
      hABC1 hABD1 with ⟨p, q, r⟩ | ⟨p, q, r⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · rcases vertex_pair_lemma AC AB AD BC CD hAC hAB hAD hBC hCD hMAB hMAD hMBC hMCD
      hABC2 hACD1 with ⟨p, q, r⟩ | ⟨p, q, r⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
  · rcases vertex_pair_lemma AD AB AC BD CD hAD hAB hAC hBD hCD hMAB hMAC hMBD hMCD
      hABD2 hACD2 with ⟨p, q, r⟩ | ⟨p, q, r⟩
    · exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))
  · rcases vertex_pair_lemma BC AB BD AC CD hBC hAB hBD hAC hCD hMAB hMBD hMAC hMCD
      hABC3 hBCD1 with ⟨p, q, r⟩ | ⟨p, q, r⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
  · rcases vertex_pair_lemma BD AB BC AD CD hBD hAB hBC hAD hCD hMAB hMBC hMAD hMCD
      hABD3 hBCD2 with ⟨p, q, r⟩ | ⟨p, q, r⟩
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))
  · rcases vertex_pair_lemma CD AC BC AD BD hCD hAC hBC hAD hBD hMAC hMBC hMAD hMBD
      hACD3 hBCD3 with ⟨p, q, r⟩ | ⟨p, q, r⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩))
```

Verification: `lake env lean LeanProject/Scratch3.lean` (in
`lean_project/`), exit code 0.

## 4. The solution, in natural language

This follows the verified Lean proof step for step — including the
`by_contra` structure the search itself found for the hard part, not a
separately-invented argument.

**Setup.** Let `ABCD` be a tetrahedron. Each of its four faces is an
honest, non-degenerate triangle (three points of a tetrahedron are never
collinear), so the three edges of every face satisfy the strict triangle
inequality: each edge is shorter than the sum of the other two.

**Pick the longest edge.** A tetrahedron has six edges, so among them
there is one of maximum length — say it's `PQ` (if several edges tie for
longest, pick any one of them). Call the other two vertices `R` and `S`.
The three edges meeting at `P` are `PQ, PR, PS`; the three meeting at `Q`
are `PQ, QR, QS`. Because `PQ` is the longest edge overall, it is at least
as long as each of `PR, PS, QR, QS`.

**Claim: vertex `P` or vertex `Q` works.** Look at the triple at `P`:
`PQ, PR, PS`. Two of its three triangle-inequality checks are automatic:
since `PR ≤ PQ` and `PS > 0`, we get `PR < PQ + PS` for free, and
symmetrically `PS < PQ + PR`. So the *only* thing that could stop `P`'s
triple from being a valid triangle is the third check, `PQ < PR + PS`.
The exact same reasoning applies at `Q`: the only possible obstruction
there is `PQ < QR + QS`.

**Suppose neither works.** That means both obstructions hold at once:
`PQ ≥ PR + PS` and `PQ ≥ QR + QS`.

Now bring in the two faces that contain the edge `PQ`: triangle `PQR` and
triangle `PQS`. Being genuine triangles, they give
`PQ < PR + QR` and `PQ < PS + QS`. Add these two:

```
2·PQ < (PR + QR) + (PS + QS) = (PR + PS) + (QR + QS)
```

But our assumption for contradiction says `(PR + PS) + (QR + QS) ≤ PQ + PQ = 2·PQ`.
Chaining the two: `2·PQ < (PR+PS)+(QR+QS) ≤ 2·PQ`, i.e. `2·PQ < 2·PQ` —
impossible.

**Conclusion.** The assumption that neither `P` nor `Q` works is false, so
at least one of them does: its three edges satisfy the triangle
inequality, meaning they're the side lengths of some triangle. Since every
tetrahedron has *some* longest edge, this vertex always exists. ∎

The only place a computer was actually needed was verifying that the
9-way case split behind "suppose neither works" really does collapse to a
contradiction in every case — which is exactly what the search confirmed
mechanically via `linarith` rather than by hand-checking 9 sign cases.
