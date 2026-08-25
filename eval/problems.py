"""
Curated evaluation problem set for the Lean 4 theorem prover.

20 problems across four difficulty tiers:
  easy    — 1-2 tactic steps; simp / ring / omega
  medium  — 3-5 steps; propositional logic or multi-step arithmetic
  hard    — multiple sub-goals or requires knowing specific Mathlib lemma names
  stretch — likely beyond current search; needs induction or deep Mathlib lookup
"""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class EvalProblem:
    name: str
    statement: str
    difficulty: str   # "easy" | "medium" | "hard" | "stretch" | "imo"
    description: str = ""   # natural-language statement of what's being proved
    tags: list[str] = field(default_factory=list)
    # A proof of `statement` already confirmed to close to zero goals in this
    # harness. Provenance, not something the prover ever sees: it is the
    # evidence that the statement is both well-formed and TRUE, and it lets
    # the set be re-verified after a Mathlib bump. tournament_champion sat
    # here for weeks as a provably false theorem — several full-budget search
    # runs were spent on it before anyone checked — because nothing recorded
    # whether a proof had ever existed. See scripts/verify_problem_set.py.
    #
    # Tactic proofs are stored as the body only (no leading `by`, since
    # `statement` already ends in `:= by`); term-mode proofs are stored as a
    # bare term and applied with `exact`.
    reference_proof: str = ""
    # Auxiliary lemmas/definitions the reference proof needs, which are NOT in
    # scope for `statement` on its own (Archive helper lemmas are local to
    # their file and are not exported by `import Mathlib`). Prepended when
    # re-verifying. Deliberately never shown to the prover: discovering the
    # decomposition is the capability under test.
    reference_preamble: str = ""
    # Where the statement came from, e.g. "Mathlib Archive/Imo/Imo1959Q1.lean".
    source: str = ""


PROBLEMS: list[EvalProblem] = [

    # -------------------------------------------------------------------------
    # Easy — 1-2 steps, core tactics (simp / ring / omega)
    # -------------------------------------------------------------------------

    # Adding zero to any natural number leaves it unchanged.
    EvalProblem(
        name="add_zero",
        statement="theorem eval_add_zero : ∀ n : Nat, n + 0 = n := by",
        difficulty="easy",
        description="Adding zero to any natural number leaves it unchanged.",
        tags=["arithmetic", "nat"],
    ),
    # Multiplying any natural number by 1 leaves it unchanged.
    EvalProblem(
        name="mul_one",
        statement="theorem eval_mul_one : ∀ n : Nat, n * 1 = n := by",
        difficulty="easy",
        description="Multiplying any natural number by 1 leaves it unchanged.",
        tags=["arithmetic", "nat"],
    ),
    # Addition of natural numbers is commutative: n + m = m + n.
    EvalProblem(
        name="add_comm_nat",
        statement="theorem eval_add_comm_nat : ∀ n m : Nat, n + m = m + n := by",
        difficulty="easy",
        description="Addition of natural numbers is commutative: n + m equals m + n.",
        tags=["arithmetic", "nat"],
    ),
    # The binomial square identity: (a + b)² = a² + 2ab + b², over the integers.
    EvalProblem(
        name="binomial_square",
        statement="theorem eval_binomial_sq : ∀ a b : Int, (a + b)^2 = a^2 + 2*a*b + b^2 := by",
        difficulty="easy",
        description="Binomial square identity: (a + b)² = a² + 2ab + b², over the integers.",
        tags=["algebra", "int"],
    ),
    # Doubling a number is the same as adding it to itself: n * 2 = n + n.
    EvalProblem(
        name="double_eq_add_self",
        statement="theorem eval_double_eq_add_self : ∀ n : Nat, n * 2 = n + n := by",
        difficulty="easy",
        description="Doubling a number is the same as adding it to itself: n * 2 = n + n.",
        tags=["arithmetic", "nat"],
    ),

    # -------------------------------------------------------------------------
    # Medium — 3-5 steps; propositional logic or multi-step arithmetic
    # -------------------------------------------------------------------------

    # The contrapositive: if p implies q, then not-q implies not-p.
    EvalProblem(
        name="contrapositive",
        statement="theorem eval_contrapositive : ∀ (p q : Prop), (p → q) → ¬q → ¬p := by",
        difficulty="medium",
        description="The contrapositive law: if p implies q, then not-q implies not-p.",
        tags=["logic", "prop"],
    ),
    # Conjunction is commutative: if p and q both hold, then q and p both hold.
    EvalProblem(
        name="and_comm_prop",
        statement="theorem eval_and_comm : ∀ (p q : Prop), p ∧ q → q ∧ p := by",
        difficulty="medium",
        description="Conjunction is commutative: p ∧ q implies q ∧ p.",
        tags=["logic", "prop"],
    ),
    # Left disjunction introduction: if p holds, then p or q holds.
    EvalProblem(
        name="or_intro",
        statement="theorem eval_or_intro : ∀ (p q : Prop), p → p ∨ q := by",
        difficulty="medium",
        description="Left disjunction introduction: if p holds then p ∨ q holds.",
        tags=["logic", "prop"],
    ),
    # Every successor of a natural number is strictly positive: 0 < n + 1.
    EvalProblem(
        name="succ_pos",
        statement="theorem eval_succ_pos : ∀ n : Nat, 0 < n + 1 := by",
        difficulty="medium",
        description="Every successor is strictly positive: 0 < n + 1 for all natural n.",
        tags=["arithmetic", "nat"],
    ),
    # Integer addition is commutative and associative: a + b + c = c + b + a.
    EvalProblem(
        name="add_assoc_comm_int",
        statement="theorem eval_add_assoc_comm_int : ∀ a b c : Int, a + b + c = c + b + a := by",
        difficulty="medium",
        description="Integer addition satisfies a + b + c = c + b + a (associativity + commutativity).",
        tags=["algebra", "int"],
    ),
    # Implication is transitive: if p → q and q → r, then p → r.
    EvalProblem(
        name="impl_trans",
        statement="theorem eval_impl_trans : ∀ (p q r : Prop), (p → q) → (q → r) → p → r := by",
        difficulty="medium",
        description="Implication is transitive: (p → q) and (q → r) together give p → r.",
        tags=["logic", "prop"],
    ),
    # Every natural number is at most its successor: n ≤ n + 1.
    EvalProblem(
        name="nat_le_succ",
        statement="theorem eval_nat_le_succ : ∀ n : Nat, n ≤ n + 1 := by",
        difficulty="medium",
        description="Every natural number is strictly less than its successor: n ≤ n + 1.",
        tags=["arithmetic", "nat"],
    ),

    # -------------------------------------------------------------------------
    # Hard — multiple sub-goals or requires specific Mathlib lemma names
    # -------------------------------------------------------------------------

    # De Morgan's law: the negation of (p or q) implies (not p) and (not q).
    EvalProblem(
        name="de_morgan_not_or",
        statement="theorem eval_de_morgan_not_or : ∀ (p q : Prop), ¬(p ∨ q) → ¬p ∧ ¬q := by",
        difficulty="hard",
        description="De Morgan's law: ¬(p ∨ q) implies ¬p ∧ ¬q.",
        tags=["logic", "prop"],
    ),
    # Disjunctive syllogism: from (p or q) and (not p), conclude q.
    EvalProblem(
        name="or_resolve",
        statement="theorem eval_or_resolve : ∀ (p q : Prop), (p ∨ q) → ¬p → q := by",
        difficulty="hard",
        description="Disjunctive syllogism: from p ∨ q and ¬p, conclude q.",
        tags=["logic", "prop"],
    ),
    # Divisibility is transitive: if a divides b and b divides c, then a divides c.
    EvalProblem(
        name="dvd_trans_nat",
        statement="theorem eval_dvd_trans_nat : ∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c := by",
        difficulty="hard",
        description="Divisibility is transitive: a ∣ b and b ∣ c implies a ∣ c.",
        tags=["number-theory", "nat"],
    ),
    # Distributing multiplication: n * (n + 1) equals n² + n.
    EvalProblem(
        name="nat_mul_succ_expand",
        statement="theorem eval_nat_mul_succ_expand : ∀ n : Nat, n * (n + 1) = n * n + n := by",
        difficulty="hard",
        description="Expanding n * (n + 1) gives n² + n (distributivity of multiplication).",
        tags=["algebra", "nat"],
    ),
    # The integers are totally ordered: if a ≤ b and b ≤ a, then a = b.
    EvalProblem(
        name="int_le_antisymm",
        statement="theorem eval_int_le_antisymm : ∀ a b : Int, a ≤ b → b ≤ a → a = b := by",
        difficulty="hard",
        description="Antisymmetry of ≤ on integers: a ≤ b and b ≤ a implies a = b.",
        tags=["order", "int"],
    ),

    # -------------------------------------------------------------------------
    # Stretch — likely beyond current search depth; included to track progress
    # -------------------------------------------------------------------------

    # Every differentiable real function is continuous.
    EvalProblem(
        name="diff_implies_cont",
        statement="theorem eval_diff_implies_cont : ∀ (f : ℝ → ℝ), Differentiable ℝ f → Continuous f := by",
        difficulty="stretch",
        description="Every differentiable real-valued function is continuous.",
        tags=["analysis", "real"],
    ),
    # Powers of 2 grow faster than the naturals: 2ⁿ > n for all n.
    EvalProblem(
        name="two_pow_gt_self",
        statement="theorem eval_two_pow_gt_self : ∀ n : Nat, 2^n > n := by",
        difficulty="stretch",
        description="Powers of 2 strictly dominate the naturals: 2ⁿ > n for all n ≥ 0.",
        tags=["arithmetic", "nat", "induction"],
    ),
    # The sum of the first n natural numbers equals n(n+1)/2, or equivalently 2·∑i = n(n+1).
    # Uses Finset.sum instead of ∑ notation to avoid needing `open BigOperators` in the REPL.
    EvalProblem(
        name="sum_range_formula",
        statement="theorem eval_sum_range_formula : ∀ n : Nat, 2 * Finset.sum (Finset.range (n + 1)) id = n * (n + 1) := by",
        difficulty="stretch",
        description="Gauss's sum formula: 2 times the sum of 0..n equals n(n+1).",
        tags=["arithmetic", "nat", "induction", "combinatorics"],
    ),
    # AIME-style distance problem: a car travels distance d at speed p (ℚ).
    # Driving faster by 2 saves 1 hour; driving faster by 9 (vs original+2) saves another hour.
    # Requires clearing rational denominators (field_simp) then nonlinear arithmetic (nlinarith).
    # Correct answer is d = 252/25 (not 45/2 — verify: p = 18/5 satisfies both hypotheses).
    EvalProblem(
        name="aime_distance",
        statement="theorem eval_aime_distance (d p : ℚ) (hp : 0 < p) (hd : 0 < d) (h₁ : d / p = d / (p + 2) + 1) (h₂ : d / (p + 2) = d / (p + 9) + 1) : d = 252 / 25 := by",
        difficulty="stretch",
        description="AIME-style: given two rational speed/time equations, prove the unique distance d = 252/25. Needs field_simp to clear denominators then nlinarith.",
        tags=["algebra", "rat", "field_simp", "nlinarith"],
    ),

    # Every score leader in a tournament is a champion (king): for every player p
    # that beats c, there exists a player q that c beat and q beat p.
    # The proof uses a pigeonhole argument on win-set cardinalities.
    #
    # hirr (irreflexivity) is REQUIRED, not decorative: htour only constrains
    # distinct pairs (a ≠ b), so without hirr nothing rules out `beats x x` and
    # the statement is actually FALSE. Lean-verified counterexample via `decide`:
    # α := Bool, beats a b := (b = false), c := false, p := true — htour and hmax
    # both hold (every win-set is {false}, so all cardinalities are equal), yet no
    # q satisfies `beats c q ∧ beats q p`. Three separate search runs burned their
    # full budget rediscovering this hole (repeatedly deriving `beats c c` and
    # failing to contradict it) before it was tracked down.
    EvalProblem(
        name="tournament_champion",
        statement=(
            "theorem eval_tournament_champion "
            "{α : Type*} [Fintype α] [DecidableEq α] "
            "(beats : α → α → Prop) [DecidableRel beats] "
            "(hirr : ∀ a : α, ¬ beats a a) "
            "(htour : ∀ a b : α, a ≠ b → (beats a b ↔ ¬ beats b a)) "
            "(c : α) "
            "(hmax : ∀ x : α, (Finset.univ.filter (fun y => beats x y)).card ≤ "
            "                  (Finset.univ.filter (fun y => beats c y)).card) : "
            "∀ p : α, beats p c → ∃ q : α, beats c q ∧ beats q p := by"
        ),
        difficulty="stretch",
        description=(
            "Every score leader in a tournament is a champion: "
            "for every player p that beat c, there exists q such that c beat q and q beat p."
        ),
        tags=["combinatorics", "graph-theory", "finset", "tournament"],
    ),

    # IMO 1968: in any tetrahedron some vertex has its three incident edges
    # forming a triangle. Stated purely in terms of the 6 edge lengths and the
    # 12 face inequalities, so no Euclidean-geometry library is needed.
    #
    # This one specifically exercises sub-goal decomposition. The known proof
    # takes the globally longest edge, proves a reusable two-vertex lemma, and
    # applies it in each of 6 cases. Since a search is scoped to a single
    # theorem, that lemma has to be introduced *inside* the proof with
    # `have name : statement` — which is exactly the capability we want to
    # measure. A prover that can only extend one flat tactic chain forward
    # cannot express this proof's structure at all.
    EvalProblem(
        name="imo1968_tetrahedron",
        statement=(
            "theorem eval_imo1968_tetrahedron "
            "(AB AC AD BC BD CD : ℝ) "
            "(hAB : 0 < AB) (hAC : 0 < AC) (hAD : 0 < AD) "
            "(hBC : 0 < BC) (hBD : 0 < BD) (hCD : 0 < CD) "
            "(hABC1 : AB < AC + BC) (hABC2 : AC < AB + BC) (hABC3 : BC < AB + AC) "
            "(hABD1 : AB < AD + BD) (hABD2 : AD < AB + BD) (hABD3 : BD < AB + AD) "
            "(hACD1 : AC < AD + CD) (hACD2 : AD < AC + CD) (hACD3 : CD < AC + AD) "
            "(hBCD1 : BC < BD + CD) (hBCD2 : BD < BC + CD) (hBCD3 : CD < BC + BD) : "
            "(AB < AC + AD ∧ AC < AB + AD ∧ AD < AB + AC) ∨ "
            "(AB < BC + BD ∧ BC < AB + BD ∧ BD < AB + BC) ∨ "
            "(AC < BC + CD ∧ BC < AC + CD ∧ CD < AC + BC) ∨ "
            "(AD < BD + CD ∧ BD < AD + CD ∧ CD < AD + BD) := by"
        ),
        difficulty="stretch",
        description=(
            "IMO 1968: in any tetrahedron there is a vertex whose three incident "
            "edges are the side lengths of a triangle. Given the 6 edge lengths "
            "and the 4 faces' triangle inequalities, prove some vertex's three "
            "edges satisfy the triangle inequality."
        ),
        tags=["geometry", "real", "case-split", "sub-lemma", "linarith", "imo"],
    ),

    # -------------------------------------------------------------------------
    # Custom — put custom problems here
    # -------------------------------------------------------------------------


    # -------------------------------------------------------------------------
    # IMO — real competition problems lifted from Mathlib's Archive.
    #
    # Provability is not assumed: for each one, Mathlib's own proof (including
    # any helper lemmas defined alongside it) was replayed in this harness and
    # required to close to zero goals, and the standalone statement below was
    # required to elaborate to a real open goal. Helpers are NOT given to the
    # prover — discovering the decomposition is the capability under test — so
    # these are markedly harder than the tier name alone suggests and low pass
    # rates are expected.
    # -------------------------------------------------------------------------

    # imo1959_q1 — Mathlib Archive/Imo/Imo1959Q1.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1959_q1",
        statement="open Nat in theorem imo1959_q1 : ∀ n : ℕ, Coprime (21 * n + 4) (14 * n + 3) := by",
        difficulty="imo",
        description="Prove that the fraction `(21n+4)/(14n+3)` is irreducible for every natural number `n`.",
        tags=['imo', 'imo1959', 'number-theory'],
        source="Mathlib Archive/Imo/Imo1959Q1.lean",
        reference_proof="  exact fun n => coprime_of_dvd' fun k _ h1 h2 => calculation n k h1 h2",
        reference_preamble="/-\nCopyright (c) 2020 Kevin Lacker. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Kevin Lacker\n-/\n\n\n\n\nopen Nat\n\nnamespace Imo1959Q1\n\ntheorem calculation (n k : ℕ) (h1 : k ∣ 21 * n + 4) (h2 : k ∣ 14 * n + 3) : k ∣ 1 :=\n  have h3 : k ∣ 2 * (21 * n + 4) := h1.mul_left 2\n  have h4 : k ∣ 3 * (14 * n + 3) := h2.mul_left 3\n  have h5 : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by ring\n  (Nat.dvd_add_right h3).mp (h5 ▸ h4)\n\nend Imo1959Q1\n\nopen Imo1959Q1",
    ),

    # imo1963_q5 — Mathlib Archive/Imo/Imo1963Q5.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1963_q5",
        statement="open Real in theorem imo1963_q5 : cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7) = 1 / 2 := by",
        difficulty="imo",
        description="Prove that `cos (π / 7) - cos (2 * π / 7) + cos (3 * π / 7) = 1 / 2`.",
        tags=['imo', 'imo1963', 'real'],
        source="Mathlib Archive/Imo/Imo1963Q5.lean",
        reference_proof="  rw [← mul_right_inj' two_sin_pi_div_seven_ne_zero, mul_add, mul_sub, ← sin_two_mul,\n    two_mul_sin_mul_cos, two_mul_sin_mul_cos]\n  ring_nf\n  rw [← sin_pi_sub (π * (3 / 7)), sin_pi_mul_neg_div 2 7, sin_pi_mul_neg_div 1 7]\n  ring_nf",
        reference_preamble="/-\nCopyright (c) 2024 Rida Hamadani. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Rida Hamadani\n-/\n\n\n\nopen Real\n\nlemma two_sin_pi_div_seven_ne_zero : 2 * sin (π / 7) ≠ 0 := by\n  apply mul_ne_zero two_ne_zero (Real.sin_pos_of_pos_of_lt_pi _ _).ne' <;> linarith [pi_pos]\n\nlemma sin_pi_mul_neg_div (a b : ℝ) : sin (π * (- a / b)) = - sin (π * (a / b)) := by\n  ring_nf\n  exact sin_neg _",
    ),

    # imo1964_q1a — Mathlib Archive/Imo/Imo1964Q1.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1964_q1a",
        statement="open Nat in theorem imo1964_q1a (n : ℕ) (_ : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by",
        difficulty="imo",
        description="(a) Find all positive integers $n$ for which $2^n-1$ is divisible by $7$.",
        tags=['imo', 'imo1964', 'number-theory', 'inequality'],
        source="Mathlib Archive/Imo/Imo1964Q1.lean",
        reference_proof="  let t := n % 3\n  have : t < 3 := Nat.mod_lt _ (by decide)\n  calc 7 ∣ 2 ^ n - 1 ↔ 2 ^ n ≡ 1 [MOD 7] := by\n        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']\n        apply Nat.one_le_pow'\n    _ ↔ 2 ^ t ≡ 1 [MOD 7] := ⟨(two_pow_mod_seven n).symm.trans, (two_pow_mod_seven n).trans⟩\n    _ ↔ t = 0 := by interval_cases t <;> decide\n    _ ↔ 3 ∣ n := by rw [dvd_iff_mod_eq_zero]\n\ntheorem imo1964_q1b (n : ℕ) : ¬7 ∣ 2 ^ n + 1 := by\n  intro h\n  let t := n % 3\n  have : t < 3 := Nat.mod_lt _ (by decide)\n  have H : 2 ^ t + 1 ≡ 0 [MOD 7] := calc\n    2 ^ t + 1 ≡ 2 ^ n + 1 [MOD 7] := by gcongr ?_ + 1; exact (two_pow_mod_seven n).symm\n      _ ≡ 0 [MOD 7] := h.modEq_zero_nat\n  interval_cases t <;> contradiction",
        reference_preamble="/-\nCopyright (c) 2020 Kevin Buzzard. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Kevin Buzzard\n-/\n\n\n\nopen Nat\n\nnamespace Imo1964Q1\n\ntheorem two_pow_mod_seven (n : ℕ) : 2 ^ n ≡ 2 ^ (n % 3) [MOD 7] :=\n  let t := n % 3\n  calc 2 ^ n = 2 ^ (3 * (n / 3) + t) := by rw [Nat.div_add_mod]\n    _ = (2 ^ 3) ^ (n / 3) * 2 ^ t := by rw [pow_add, pow_mul]\n    _ ≡ 1 ^ (n / 3) * 2 ^ t [MOD 7] := by gcongr; decide\n    _ = 2 ^ t := by ring\n\nend Imo1964Q1\n\nopen Imo1964Q1",
    ),

    # imo1969_q1 — Mathlib Archive/Imo/Imo1969Q1.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1969_q1",
        statement="open Int Nat in theorem imo1969_q1 : Set.Infinite {a : ℕ | ∀ n : ℕ, ¬Nat.Prime (n ^ 4 + a)} := by",
        difficulty="imo",
        description="Prove that there are infinitely many natural numbers $a$ with the following property: the number $z = n^4 + a$ is not prime for any natural number $n$.",
        tags=['imo', 'imo1969', 'number-theory'],
        source="Mathlib Archive/Imo/Imo1969Q1.lean",
        reference_proof="  exact Set.infinite_of_injective_forall_mem aChoice_strictMono.injective aChoice_good",
        reference_preamble="/-\nCopyright (c) 2020 Kevin Lacker. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Kevin Lacker\n-/\n\n\n\n\nopen Int Nat\n\nnamespace Imo1969Q1\n\n/-- `goodNats` is the set of natural numbers satisfying the condition in the problem\nstatement, namely the `a : ℕ` such that `n^4 + a` is not prime for any `n : ℕ`. -/\ndef goodNats : Set ℕ :=\n  {a : ℕ | ∀ n : ℕ, ¬Nat.Prime (n ^ 4 + a)}\n\n\n\n\ntheorem factorization {m n : ℤ} :\n    ((n - m) ^ 2 + m ^ 2) * ((n + m) ^ 2 + m ^ 2) = n ^ 4 + 4 * m ^ 4 :=\n  pow_four_add_four_mul_pow_four.symm\n\n\n\n\ntheorem left_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < (n - m) ^ 2 + m ^ 2 := by nlinarith\n\ntheorem right_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < (n + m) ^ 2 + m ^ 2 := by nlinarith\n\n\n\n\ntheorem int_large {m : ℤ} (h : 1 < m) : 1 < m.natAbs := by\n  exact_mod_cast lt_of_lt_of_le h le_natAbs\n\ntheorem not_prime_of_int_mul' {m n : ℤ} {c : ℕ} (hm : 1 < m) (hn : 1 < n) (hc : m * n = (c : ℤ)) :\n    ¬Nat.Prime c :=\n  not_prime_of_int_mul (int_large hm).ne' (int_large hn).ne' hc\n\n/-- Every natural number of the form `n^4 + 4*m^4` is not prime. -/\ntheorem polynomial_not_prime {m : ℕ} (h1 : 1 < m) (n : ℕ) : ¬Nat.Prime (n ^ 4 + 4 * m ^ 4) := by\n  have h2 : 1 < (m : ℤ) := Int.ofNat_lt.mpr h1\n  refine not_prime_of_int_mul' (left_factor_large (n : ℤ) h2) (right_factor_large (n : ℤ) h2) ?_\n  apply factorization\n\n/-- We define $a_{choice}(b) := 4*(2+b)^4$, so that we can take $m = 2+b$ in `polynomial_not_prime`.\n-/\ndef aChoice (b : ℕ) : ℕ :=\n  4 * (2 + b) ^ 4\n\ntheorem aChoice_good (b : ℕ) : aChoice b ∈ goodNats :=\n  polynomial_not_prime (show 1 < 2 + b by linarith)\n\n/-- `aChoice` is a strictly monotone function; this is easily proven by chaining together lemmas\nin the `strictMono` namespace. -/\ntheorem aChoice_strictMono : StrictMono aChoice :=\n  ((strictMono_id.const_add 2).nat_pow (by decide)).const_mul (by decide)\n\nend Imo1969Q1\n\nopen Imo1969Q1",
    ),

    # imo1972_q5 — Mathlib Archive/Imo/Imo1972Q5.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1972_q5",
        statement="theorem imo1972_q5 (f g : ℝ → ℝ) (hf1 : ∀ x, ∀ y, f (x + y) + f (x - y) = 2 * f x * g y) (hf2 : ∀ y, ‖f y‖ ≤ 1) (hf3 : ∃ x, f x ≠ 0) (y : ℝ) : ‖g y‖ ≤ 1 := by",
        difficulty="imo",
        description="Problem: `f` and `g` are real-valued functions defined on the real line. For all `x` and `y`, `f(x + y) + f(x - y) = 2f(x)g(y)`. `f` is not identically zero and `|f(x)| ≤ 1` for all `x`.",
        tags=['imo', 'imo1972', 'real', 'inequality'],
        source="Mathlib Archive/Imo/Imo1972Q5.lean",
        reference_proof="  -- Suppose the conclusion does not hold.\n  by_contra! hneg\n  set S := Set.range fun x => ‖f x‖\n  -- Introduce `k`, the supremum of `f`.\n  let k : ℝ := sSup S\n  -- Show that `‖f x‖ ≤ k`.\n  have hk₁ : ∀ x, ‖f x‖ ≤ k := by\n    have h : BddAbove S := ⟨1, Set.forall_mem_range.mpr hf2⟩\n    intro x\n    exact le_csSup h (Set.mem_range_self x)\n  -- Show that `2 * (‖f x‖ * ‖g y‖) ≤ 2 * k`.\n  have hk₂ : ∀ x, 2 * (‖f x‖ * ‖g y‖) ≤ 2 * k := fun x ↦\n    calc\n      2 * (‖f x‖ * ‖g y‖) = ‖2 * f x * g y‖ := by simp [mul_assoc]\n      _ = ‖f (x + y) + f (x - y)‖ := by rw [hf1]\n      _ ≤ ‖f (x + y)‖ + ‖f (x - y)‖ := norm_add_le _ _\n      _ ≤ k + k := add_le_add (hk₁ _) (hk₁ _)\n      _ = 2 * k := (two_mul _).symm\n  set k' := k / ‖g y‖\n  -- Demonstrate that `k' < k` using `hneg`.\n  have H₁ : k' < k := by\n    have h₁ : 0 < k := by\n      obtain ⟨x, hx⟩ := hf3\n      calc\n        0 < ‖f x‖ := norm_pos_iff.mpr hx\n        _ ≤ k := hk₁ x\n    rw [div_lt_iff₀]\n    · apply lt_mul_of_one_lt_right h₁ hneg\n    · exact zero_lt_one.trans hneg\n  -- Demonstrate that `k ≤ k'` using `hk₂`.\n  have H₂ : k ≤ k' := by\n    have h₁ : ∃ x : ℝ, x ∈ S := by use ‖f 0‖; exact Set.mem_range_self 0\n    have h₂ : ∀ x, ‖f x‖ ≤ k' := by\n      intro x\n      rw [le_div_iff₀]\n      · apply (mul_le_mul_iff_right₀ zero_lt_two).mp (hk₂ x)\n      · exact zero_lt_one.trans hneg\n    apply csSup_le h₁\n    rintro y' ⟨yy, rfl⟩\n    exact h₂ yy\n  -- Conclude by obtaining a contradiction, `k' < k'`.\n  apply lt_irrefl k'\n  calc\n    k' < k := H₁\n    _ ≤ k' := H₂\n\n/-- IMO 1972 Q5\n\nProblem: `f` and `g` are real-valued functions defined on the real line. For all `x` and `y`,\n`f(x + y) + f(x - y) = 2f(x)g(y)`. `f` is not identically zero and `|f(x)| ≤ 1` for all `x`.\nProve that `|g(x)| ≤ 1` for all `x`.\n\nThis is a more concise version of the proof proposed by Ruben Van de Velde.\n-/\ntheorem imo1972_q5' (f g : ℝ → ℝ) (hf1 : ∀ x, ∀ y, f (x + y) + f (x - y) = 2 * f x * g y)\n    (hf2 : BddAbove (Set.range fun x => ‖f x‖)) (hf3 : ∃ x, f x ≠ 0) (y : ℝ) : ‖g y‖ ≤ 1 := by\n  obtain ⟨x, hx⟩ := hf3\n  set k := ⨆ x, ‖f x‖\n  have h : ∀ x, ‖f x‖ ≤ k := le_ciSup hf2\n  by_contra! H\n  have hgy : 0 < ‖g y‖ := by linarith\n  have k_pos : 0 < k := lt_of_lt_of_le (norm_pos_iff.mpr hx) (h x)\n  have : k / ‖g y‖ < k := (div_lt_iff₀ hgy).mpr (lt_mul_of_one_lt_right k_pos H)\n  have : k ≤ k / ‖g y‖ := by\n    suffices ∀ x, ‖f x‖ ≤ k / ‖g y‖ from ciSup_le this\n    intro x\n    suffices 2 * (‖f x‖ * ‖g y‖) ≤ 2 * k by\n      rwa [le_div_iff₀ hgy, ← mul_le_mul_iff_right₀ (zero_lt_two : (0 : ℝ) < 2)]\n    calc\n      2 * (‖f x‖ * ‖g y‖) = ‖2 * f x * g y‖ := by simp [mul_assoc]\n      _ = ‖f (x + y) + f (x - y)‖ := by rw [hf1]\n      _ ≤ ‖f (x + y)‖ + ‖f (x - y)‖ := abs_add_le _ _\n      _ ≤ 2 * k := by linarith [h (x + y), h (x - y)]\n  linarith",
        reference_preamble="/-\nCopyright (c) 2020 Ruben Van de Velde, Stanislas Polu. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Ruben Van de Velde, Stanislas Polu\n-/\n\n\n\n/--\nThis proof begins by introducing the supremum of `f`, `k ≤ 1` as well as `k' = k / ‖g y‖`. We then\nsuppose that the conclusion does not hold (`hneg`) and show that `k ≤ k'` (by\n`2 * (‖f x‖ * ‖g y‖) ≤ 2 * k` obtained from the main hypothesis `hf1`) and that `k' < k` (obtained\nfrom `hneg` directly), finally raising a contradiction with `k' < k'`.\n\n(Authored by Stanislas Polu inspired by Ruben Van de Velde).\n-/",
    ),

    # imo1977_q6_nat — Mathlib Archive/Imo/Imo1977Q6.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1977_q6_nat",
        statement="theorem imo1977_q6_nat (f : ℕ → ℕ) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by",
        difficulty="imo",
        description="Suppose `f : ℕ+ → ℕ+` satisfies `f(f(n)) < f(n + 1)` for all `n`.",
        tags=['imo', 'imo1977', 'functional-equation', 'inequality'],
        source="Mathlib Archive/Imo/Imo1977Q6.lean",
        reference_proof="  have h' (k n : ℕ) (hk : k ≤ n) : k ≤ f n := by\n    induction k generalizing n with\n    | zero => exact Nat.zero_le _\n    | succ k h_ind =>\n      apply Nat.succ_le_of_lt\n      calc\n        k ≤ f (f (n - 1)) := h_ind _ (h_ind (n - 1) (le_tsub_of_add_le_right hk))\n        _ < f n := tsub_add_cancel_of_le (le_trans (Nat.succ_le_succ (Nat.zero_le _)) hk) ▸ h _\n  have hf : ∀ n, n ≤ f n := fun n => h' n n rfl.le\n  have hf_mono : StrictMono f := strictMono_nat_of_lt_succ fun _ => lt_of_le_of_lt (hf _) (h _)\n  intro\n  exact Nat.eq_of_le_of_lt_succ (hf _) (hf_mono.lt_iff_lt.mp (h _))\n\nend Imo1977Q6\n\nopen Imo1977Q6\n\ntheorem imo1977_q6 (f : ℕ+ → ℕ+) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by\n  intro n\n  have := by\n    refine imo1977_q6_nat (fun m => if 0 < m then f m.toPNat' else 0) ?_ n\n    intro x; cases x\n    · simp\n    · simpa using h _\n  simpa",
        reference_preamble="/-\nCopyright (c) 2021 Tian Chen. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Tian Chen\n-/\n\n\n\n\nnamespace Imo1977Q6",
    ),

    # imo1988_q6 — Mathlib Archive/Imo/Imo1988Q6.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1988_q6",
        statement="theorem imo1988_q6 {a b : ℕ} (h : a * b + 1 ∣ a ^ 2 + b ^ 2) : ∃ d, d ^ 2 = (a ^ 2 + b ^ 2) / (a * b + 1) := by",
        difficulty="imo",
        description="Question 6 of IMO1988 is somewhat (in)famous. Several expert problem solvers could not tackle the question within the given time limit.",
        tags=['imo', 'imo1988', 'number-theory'],
        source="Mathlib Archive/Imo/Imo1988Q6.lean",
        reference_proof="  rcases h with ⟨k, hk⟩\n  rw [hk, Nat.mul_div_cancel_left _ (Nat.succ_pos (a * b))]\n  simp only [sq] at hk\n  apply constant_descent_vieta_jumping a b (H := fun a b => a * a + b * b = (a * b + 1) * k)\n      hk (fun x => k * x) (fun x => x * x - k) fun _ _ => False <;>\n    clear hk a b\n  · -- We will now show that the fibers of the solution set are described by a quadratic equation.\n    intro x y\n    rw [← Int.natCast_inj, ← sub_eq_zero]\n    apply eq_iff_eq_cancel_right.2\n    simp; ring\n  · -- Show that the solution set is symmetric in a and b.\n    intro x y\n    simp [add_comm (x * x), mul_comm x]\n  · -- Show that the claim is true if b = 0.\n    suffices ∀ a, a * a = k → ∃ d, d * d = k by simpa\n    rintro x rfl; use x\n  · -- Show that the claim is true if a = b.\n    intro x hx\n    suffices k ≤ 1 by\n      rw [Nat.le_add_one_iff, Nat.le_zero] at this\n      rcases this with (rfl | rfl)\n      · use 0; simp\n      · use 1; simp\n    contrapose! hx with k_lt_one\n    apply ne_of_lt\n    calc\n      x * x + x * x = x * x * 2 := by rw [mul_two]\n      _ ≤ x * x * k := Nat.mul_le_mul_left (x * x) k_lt_one\n      _ < (x * x + 1) * k := by linarith\n  · -- Show the descent step.\n    intro x y hx x_lt_y _ _ z h_root _ hV₀\n    constructor\n    · have hpos : 0 < z * z + x * x := by\n        apply add_pos_of_nonneg_of_pos\n        · apply mul_self_nonneg\n        · apply mul_pos <;> exact mod_cast hx\n      have hzx : z * z + x * x = (z * x + 1) * k := by\n        rw [← sub_eq_zero, ← h_root]\n        ring\n      rw [hzx] at hpos\n      replace hpos : 0 < z * x + 1 := pos_of_mul_pos_left hpos (Int.natCast_nonneg k)\n      replace hpos : 0 ≤ z * x := Int.le_of_lt_add_one hpos\n      apply nonneg_of_mul_nonneg_left hpos (mod_cast hx)\n    · contrapose! hV₀ with x_lt_z\n      apply ne_of_gt\n      calc\n        z * y > x * x := by apply mul_lt_mul' <;> lia\n        _ ≥ x * x - k := sub_le_self _ (Int.natCast_nonneg k)\n  · -- There is no base case in this application of Vieta jumping.\n    simp\n\n/-\nThe following example illustrates the use of constant descent Vieta jumping\nin the presence of a non-trivial base case.\n-/\nexample {a b : ℕ} (h : a * b ∣ a ^ 2 + b ^ 2 + 1) : 3 * a * b = a ^ 2 + b ^ 2 + 1 := by\n  rcases h with ⟨k, hk⟩\n  suffices k = 3 by simp_all; ring\n  simp only [sq] at hk\n  apply constant_descent_vieta_jumping a b (H := fun a b => a * a + b * b + 1 = a * b * k)\n      hk (fun x => k * x) (fun x => x * x + 1) fun x _ => x ≤ 1 <;>\n    clear hk a b\n  · -- We will now show that the fibers of the solution set are described by a quadratic equation.\n    intro x y\n    rw [← Int.natCast_inj, ← sub_eq_zero]\n    apply eq_iff_eq_cancel_right.2\n    simp; ring\n  · -- Show that the solution set is symmetric in a and b.\n    intro x y; ring_nf\n  · -- Show that the claim is true if b = 0.\n    simp\n  · -- Show that the claim is true if a = b.\n    intro x hx\n    have x_sq_dvd : x * x ∣ x * x * k := dvd_mul_right (x * x) k\n    rw [← hx] at x_sq_dvd\n    obtain ⟨y, hy⟩ : x * x ∣ 1 := by simpa only [Nat.dvd_add_self_left, add_assoc] using x_sq_dvd\n    obtain ⟨rfl, rfl⟩ : x = 1 ∧ y = 1 := by simpa [mul_eq_one] using hy.symm\n    simpa using hx.symm\n  · -- Show the descent step.\n    intro x y _ hx h_base _ z _ _ hV₀\n    constructor\n    · have zy_pos : z * y ≥ 0 := by rw [hV₀]; exact mod_cast Nat.zero_le _\n      apply nonneg_of_mul_nonneg_left zy_pos\n      lia\n    · contrapose! hV₀ with x_lt_z\n      apply ne_of_gt\n      push Not at h_base\n      calc\n        z * y > x * y := by gcongr; lia\n        _ ≥ x * (x + 1) := by apply mul_le_mul <;> lia\n        _ > x * x + 1 := by\n          rw [mul_add]\n          lia\n  · -- Show the base case.\n    intro x y h h_base\n    obtain rfl | rfl : x = 0 ∨ x = 1 := by rwa [Nat.le_add_one_iff, Nat.le_zero] at h_base\n    · simp at h\n    · rw [mul_one, one_mul, add_right_comm] at h\n      have y_dvd : y ∣ y * k := dvd_mul_right y k\n      rw [← h, Nat.dvd_add_left (dvd_mul_left y y)] at y_dvd\n      obtain rfl | rfl := (Nat.dvd_prime Nat.prime_two).mp y_dvd <;> apply mul_left_cancel₀\n      exacts [one_ne_zero, h.symm, two_ne_zero, h.symm]",
        reference_preamble="/-\nCopyright (c) 2019 Johan Commelin. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Johan Commelin\n-/\n\n\n\nattribute [local simp] sq\n\nnamespace Imo1988Q6\n\n/-- Constant descent Vieta jumping.\n\nThis proof technique allows one to prove an arbitrary proposition `claim`,\nby running a descent argument on a hyperbola `H` in the first quadrant of the plane,\nunder the following conditions:\n\n* `h₀`     : There exists an integral point `(x,y)` on the hyperbola `H`.\n* `H_symm` : The hyperbola has a symmetry along the diagonal in the plane.\n* `H_zero` : If an integral point `(x,0)` lies on the hyperbola `H`, then `claim` is true.\n* `H_diag` : If an integral point `(x,x)` lies on the hyperbola `H`, then `claim` is true.\n* `H_desc` : If `(x,y)` is an integral point on the hyperbola `H`,\n  with `x < y` then there exists a “smaller” point on `H`: a point `(x',y')` with `x' < y' ≤ x`.\n\nFor reasons of usability, the hyperbola `H` is implemented as an arbitrary predicate.\n(In question 6 of IMO1988, where this proof technique was first developed,\nthe predicate `claim` would be `∃ (d : ℕ), d ^ 2 = k` for some natural number `k`,\nand the predicate `H` would be `fun a b ↦ a * a + b * b = (a * b + 1) * k`.)\n\nTo ensure that the predicate `H` actually describes a hyperbola,\nthe user must provide arguments `B` and `C` that are used as coefficients for a quadratic equation.\nFinally, `H_quad` is the proof obligation that the quadratic equation\n  `(y:ℤ) * y - B x * y + C x = 0`\ndescribes the same hyperbola as the predicate `H`.\n\nFor extra flexibility, one must provide a predicate `base` on the integral points in the plane.\nIn the descent step `H_desc` this will give the user the additional assumption that\nthe point `(x,y)` does not lie in this base locus.\nThe user must provide a proof that the proposition `claim` is true\nif there exists an integral point `(x,y)` on the hyperbola `H` that lies in the base locus.\nIf such a base locus is not necessary, once can simply let it be `fun x y ↦ False`.\n-/\ntheorem constant_descent_vieta_jumping (x y : ℕ) {claim : Prop} {H : ℕ → ℕ → Prop} (h₀ : H x y)\n    (B : ℕ → ℤ) (C : ℕ → ℤ) (base : ℕ → ℕ → Prop)\n    (H_quad : ∀ {x y}, H x y ↔ (y : ℤ) * y - B x * y + C x = 0) (H_symm : ∀ {x y}, H x y ↔ H y x)\n    (H_zero : ∀ {x}, H x 0 → claim) (H_diag : ∀ {x}, H x x → claim)\n    (H_desc : ∀ {x y}, 0 < x → x < y → ¬base x y → H x y →\n      ∀ y', y' * y' - B x * y' + C x = 0 → y' = B x - y → y' * y = C x → 0 ≤ y' ∧ y' ≤ x)\n    (H_base : ∀ {x y}, H x y → base x y → claim) : claim := by\n  -- First of all, we may assume that x ≤ y.\n  -- We justify this using H_symm.\n  wlog hxy : x ≤ y\n  · rw [H_symm] at h₀; apply this y x h₀ B C base _ _ _ _ _ _ (le_of_not_ge hxy); assumption'\n  -- In fact, we can easily deal with the case x = y.\n  by_cases x_eq_y : x = y\n  · subst x_eq_y; exact H_diag h₀\n  -- Hence we may assume that x < y.\n  replace hxy : x < y := lt_of_le_of_ne hxy x_eq_y\n  clear x_eq_y\n  -- Consider the upper branch of the hyperbola defined by H.\n  let upper_branch : Set (ℕ × ℕ) := {p | H p.1 p.2 ∧ p.1 < p.2}\n  -- Note that the point p = (x,y) lies on the upper branch.\n  let p : ℕ × ℕ := ⟨x, y⟩\n  have hp : p ∈ upper_branch := ⟨h₀, hxy⟩\n  -- We also consider the exceptional set of solutions (a,b) that satisfy\n  -- a = 0 or a = b or B a = b or B a = b + a or that lie in the base locus.\n  let exceptional : Set (ℕ × ℕ) :=\n    {p | H p.1 p.2 ∧ (base p.1 p.2 ∨ p.1 = 0 ∨ p.1 = p.2 ∨ B p.1 = p.2 ∨ B p.1 = p.2 + p.1)}\n  -- Let S be the projection of the upper branch on to the y-axis\n  -- after removing the exceptional locus.\n  let S : Set ℕ := Prod.snd '' (upper_branch \\ exceptional)\n  -- The strategy is to show that the exceptional locus in nonempty\n  -- by running a descent argument that starts with the given point p = (x,y).\n  -- Our assumptions ensure that we can then prove the claim.\n  suffices exc : exceptional.Nonempty by\n    -- Suppose that there exists an element in the exceptional locus.\n    simp only [Set.Nonempty, Prod.exists, Set.mem_setOf_eq, exceptional] at exc\n    -- Let (a,b) be such an element, and consider all the possible cases.\n    rcases exc with ⟨a, b, hH, hb⟩\n    rcases hb with (_ | rfl | rfl | hB | hB)\n    -- The first three cases are rather easy to solve.\n    · solve_by_elim\n    · rw [H_symm] at hH; solve_by_elim\n    · solve_by_elim\n    -- The final two cases are very similar.\n    all_goals\n      -- Consider the quadratic equation that (a,b) satisfies.\n      rw [H_quad] at hH\n      -- We find the other root of the equation, and Vieta's formulas.\n      rcases vieta_formula_quadratic hH with ⟨c, h_root, hV₁, hV₂⟩\n      -- By substitutions we find that b = 0 or b = a.\n      simp only [hB, add_eq_left, add_right_inj] at hV₁\n      subst hV₁\n      rw [← Int.ofNat_zero] at *\n      rw [← H_quad] at h_root\n      -- And hence we are done by H_zero and H_diag.\n      solve_by_elim\n  -- To finish the main proof, we need to show that the exceptional locus is nonempty.\n  -- So we assume that the exceptional locus is empty, and work towards deriving a contradiction.\n  rw [Set.nonempty_iff_ne_empty]\n  intro exceptional_empty\n  -- Observe that S is nonempty.\n  have S_nonempty : S.Nonempty := by\n    -- It contains the image of p.\n    use p.2\n    apply Set.mem_image_of_mem\n    -- After all, we assumed that the exceptional locus is empty.\n    rwa [exceptional_empty, Set.diff_empty]\n  -- We are now set for an infinite descent argument.\n  -- Let m be the smallest element of the nonempty set S.\n  let m : ℕ := WellFounded.min Nat.lt_wfRel.wf S S_nonempty\n  have m_mem : m ∈ S := WellFounded.min_mem Nat.lt_wfRel.wf S S_nonempty\n  have m_min : ∀ k ∈ S, ¬k < m := fun k hk => WellFounded.not_lt_min Nat.lt_wfRel.wf S hk\n  -- It suffices to show that there is point (a,b) with b ∈ S and b < m.\n  rsuffices ⟨p', p'_mem, p'_small⟩ : ∃ p' : ℕ × ℕ, p'.2 ∈ S ∧ p'.2 < m\n  · solve_by_elim\n  -- Let (m_x, m_y) be a point on the upper branch that projects to m ∈ S\n  -- and that does not lie in the exceptional locus.\n  rcases m_mem with ⟨⟨mx, my⟩, ⟨⟨hHm, mx_lt_my⟩, h_base⟩, m_eq⟩\n  -- This means that m_y = m,\n  -- and the conditions H(m_x, m_y) and m_x < m_y are satisfied.\n  simp only at mx_lt_my hHm m_eq\n  simp only [exceptional, hHm, Set.mem_setOf_eq, true_and] at h_base\n  push Not at h_base\n  -- Finally, it also means that (m_x, m_y) does not lie in the base locus,\n  -- that m_x ≠ 0, m_x ≠ m_y, B(m_x) ≠ m_y, and B(m_x) ≠ m_x + m_y.\n  rcases h_base with ⟨h_base, hmx, hm_diag, hm_B₁, hm_B₂⟩\n  replace hmx : 0 < mx := pos_iff_ne_zero.mpr hmx\n  -- Consider the quadratic equation that (m_x, m_y) satisfies.\n  have h_quad := hHm\n  rw [H_quad] at h_quad\n  -- We find the other root of the equation, and Vieta's formulas.\n  rcases vieta_formula_quadratic h_quad with ⟨c, h_root, hV₁, hV₂⟩\n  -- Now we rewrite Vieta's formulas a bit, and apply the descent step.\n  replace hV₁ : c = B mx - my := eq_sub_of_add_eq' hV₁\n  rw [mul_comm] at hV₂\n  have Hc := H_desc hmx mx_lt_my h_base hHm c h_root hV₁ hV₂\n  -- This means that we may assume that c ≥ 0 and c ≤ m_x.\n  obtain ⟨c_nonneg, c_lt⟩ := Hc\n  -- In other words, c is a natural number.\n  lift c to ℕ using c_nonneg\n  -- Recall that we are trying find a point (a,b) such that b ∈ S and b < m.\n  -- We claim that p' = (c, m_x) does the job.\n  let p' : ℕ × ℕ := ⟨c, mx⟩\n  use p'\n  -- The second condition is rather easy to check, so we do that first.\n  constructor; swap\n  · rwa [m_eq] at mx_lt_my\n  -- Now we need to show that p' projects onto S. In other words, that c ∈ S.\n  -- We do that, by showing that it lies in the upper branch\n  -- (which is sufficient, because we assumed that the exceptional locus is empty).\n  apply Set.mem_image_of_mem\n  rw [exceptional_empty, Set.diff_empty]\n  -- Now we are ready to prove that p' = (c, m_x) lies on the upper branch.\n  -- We need to check two conditions: H(c, m_x) and c < m_x.\n  constructor <;> dsimp only\n  · -- The first condition is not so hard. After all, c is the other root of the quadratic equation.\n    rw [H_symm, H_quad]\n    simpa using h_root\n  · -- For the second condition, we note that it suffices to check that c ≠ m_x.\n    suffices hc : c ≠ mx from lt_of_le_of_ne (mod_cast c_lt) hc\n    -- However, recall that B(m_x) ≠ m_x + m_y.\n    -- If c = m_x, we can prove B(m_x) = m_x + m_y.\n    contrapose hm_B₂\n    subst c\n    simp [hV₁]\n    -- Hence p' = (c, m_x) lies on the upper branch, and we are done.\n\nend Imo1988Q6\n\nopen Imo1988Q6\n\n/-- Question 6 of IMO1988. If a and b are two natural numbers\nsuch that a*b+1 divides a^2 + b^2, show that their quotient is a perfect square. -/",
    ),

    # imo1994_q1 — Mathlib Archive/Imo/Imo1994Q1.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo1994_q1",
        statement="open Finset in theorem imo1994_q1 (n : ℕ) (m : ℕ) (A : Finset ℕ) (hm : #A = m + 1) (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ n) (hadd : ∀ a ∈ A, ∀ b ∈ A, a + b ≤ n → a + b ∈ A) : (m + 1) * (n + 1) ≤ 2 * ∑ x ∈ A, x := by",
        difficulty="imo",
        description="Let `m` and `n` be two positive integers.",
        tags=['imo', 'imo1994', 'combinatorics', 'inequality'],
        source="Mathlib Archive/Imo/Imo1994Q1.lean",
        reference_proof="  set a := orderEmbOfFin A hm\n  -- We sort the elements of `A`\n  have ha : ∀ i, a i ∈ A := fun i => orderEmbOfFin_mem A hm i\n  set rev := Equiv.subLeft (Fin.last m)\n  -- `i ↦ m-i`\n  -- We reindex the sum by fin (m+1)\n  have : ∑ x ∈ A, x = ∑ i : Fin (m + 1), a i := by\n    convert sum_image fun x _ y _ => a.eq_iff_eq.1\n    rw [← coe_inj]; simp [a]\n  rw [this]; clear this\n  -- The main proof is a simple calculation by rearranging one of the two sums\n  suffices hpair : ∀ k ∈ univ, a k + a (rev k) ≥ n + 1 by calc\n    2 * ∑ i : Fin (m + 1), a i = ∑ i : Fin (m + 1), a i + ∑ i : Fin (m + 1), a i := two_mul _\n    _ = ∑ i : Fin (m + 1), a i + ∑ i : Fin (m + 1), a (rev i) := by rw [Equiv.sum_comp rev]\n    _ = ∑ i : Fin (m + 1), (a i + a (rev i)) := sum_add_distrib.symm\n    _ ≥ ∑ i : Fin (m + 1), (n + 1) := sum_le_sum hpair\n    _ = (m + 1) * (n + 1) := by rw [sum_const, card_fin, Nat.nsmul_eq_mul]\n  -- It remains to prove the key inequality, by contradiction\n  rintro k -\n  by_contra! h : a k + a (rev k) < n + 1\n  -- We exhibit `k+1` elements of `A` greater than `a (rev k)`\n  set f : Fin (m + 1) ↪ ℕ :=\n    ⟨fun i => a i + a (rev k), .of_eq_imp_le (a.map_rel_iff.mp <| add_right_cancel · |>.le)⟩\n  -- Proof that the `f i` are greater than `a (rev k)` for `i ≤ k`\n  have hf : map f (Icc 0 k) ⊆ map a.toEmbedding (Ioc (rev k) (Fin.last m)) := by\n    intro x hx\n    simp only [Equiv.subLeft_apply, a, rev] at h\n    simp only [mem_map, mem_Icc, mem_Ioc, Fin.zero_le, true_and, Equiv.subLeft_apply,\n      Function.Embedding.coeFn_mk, RelEmbedding.coe_toEmbedding, f, rev] at hx ⊢\n    rcases hx with ⟨i, ⟨hi, rfl⟩⟩\n    have h1 : a i + a (Fin.last m - k) ≤ n := by unfold a; linarith only [h, a.monotone hi]\n    have h2 : a i + a (Fin.last m - k) ∈ A := hadd _ (ha _) _ (ha _) h1\n    rw [← mem_coe, ← range_orderEmbOfFin A hm, Set.mem_range] at h2\n    obtain ⟨j, hj⟩ := h2\n    refine ⟨j, ⟨?_, Fin.le_last j⟩, hj⟩\n    rw [← a.strictMono.lt_iff_lt, hj]\n    simpa using (hrange (a i) (ha i)).1\n  -- A set of size `k+1` embed in one of size `k`, which yields a contradiction\n  simpa [Fin.val_sub, tedious, rev] using card_le_card hf",
        reference_preamble="/-\nCopyright (c) 2021 Antoine Labelle. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Antoine Labelle\n-/\n\n\n\n\nopen Finset\n\nnamespace Imo1994Q1\n\ntheorem tedious (m : ℕ) (k : Fin (m + 1)) : m - ((m + 1 - ↑k) + m) % (m + 1) = ↑k := by\n  obtain ⟨k, hk⟩ := k\n  rw [Nat.lt_succ_iff, le_iff_exists_add] at hk\n  rcases hk with ⟨c, rfl⟩\n  have : (k + c + 1 - k) + (k + c) = c + (k + c + 1) := by lia\n  rw [Fin.val_mk, this, Nat.add_mod_right, Nat.mod_eq_of_lt, Nat.add_sub_cancel]\n  lia\n\nend Imo1994Q1\n\nopen Imo1994Q1",
    ),

    # imo2001_q6 — Mathlib Archive/Imo/Imo2001Q6.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2001_q6",
        statement="theorem imo2001_q6 (hd : 0 < d) (hdc : d < c) (hcb : c < b) (hba : b < a) (h : a * c + b * d = (a + b - c + d) * (-a + b + c + d)) : ¬Prime (a * b + c * d) := by",
        difficulty="imo",
        description="Let $a$, $b$, $c$, $d$ be integers with $a > b > c > d > 0$. Suppose that $$ a*c + b*d = (a + b - c + d) * (-a + b + c + d). $$ Prove that $a*b + c*d$ is not prime.",
        tags=['imo', 'imo2001', 'number-theory', 'inequality'],
        source="Mathlib Archive/Imo/Imo2001Q6.lean",
        reference_proof="  intro (h0 : Prime (a * b + c * d))\n  have ha : 0 < a := by lia\n  have hb : 0 < b := by lia\n  have hc : 0 < c := by lia\n  -- the key step is to show that `a*c + b*d` divides the product `(a*b + c*d) * (a*d + b*c)`\n  have dvd_mul : a * c + b * d ∣ (a * b + c * d) * (a * d + b * c) := by\n    use b ^ 2 + b * d + d ^ 2\n    linear_combination b * d * h\n  -- since `a*b + c*d` is prime (by assumption), it must divide `a*c + b*d` or `a*d + b*c`\n  obtain (h1 : a * b + c * d ∣ a * c + b * d) | (h2 : a * c + b * d ∣ a * d + b * c) :=\n    h0.left_dvd_or_dvd_right_of_dvd_mul dvd_mul\n  -- in both cases, we derive a contradiction\n  · have aux : 0 < a * c + b * d := by nlinarith only [ha, hb, hc, hd]\n    have : a * b + c * d ≤ a * c + b * d := Int.le_of_dvd aux h1\n    nlinarith only [hba, hcb, hdc, h, this]\n  · have aux : 0 < a * d + b * c := by nlinarith only [ha, hb, hc, hd]\n    have : a * c + b * d ≤ a * d + b * c := Int.le_of_dvd aux h2\n    nlinarith only [hba, hdc, h, this]",
        reference_preamble="/-\nCopyright (c) 2021 Sara Díaz Real. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Sara Díaz Real\n-/\n\n\n\nvariable {a b c d : ℤ}",
    ),

    # imo2005_q3 — Mathlib Archive/Imo/Imo2005Q3.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2005_q3",
        statement="theorem imo2005_q3 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z ≥ 1) : (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) + (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥ 0 := by",
        difficulty="imo",
        description="Let `x`, `y` and `z` be positive real numbers such that `xyz ≥ 1`. Prove that: `(x^5 - x^2)/(x^5 + y^2 + z^2) + (y^5 - y^2)/(y^5 + z^2 + x^2) + (z^5 - z^2)/(z^5 + x^2 + y^2) ≥ 0` The solution by Iurie Boreico from Moldova is presented, which won a special priz",
        tags=['imo', 'imo2005', 'real', 'inequality'],
        source="Mathlib Archive/Imo/Imo2005Q3.lean",
        reference_proof="  calc\n    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) + (y ^ 5 - y ^ 2) / (y ^ 5 + z ^ 2 + x ^ 2) +\n          (z ^ 5 - z ^ 2) / (z ^ 5 + x ^ 2 + y ^ 2) ≥\n        (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) + (y ^ 2 - z * x) / (y ^ 2 + z ^ 2 + x ^ 2) +\n          (z ^ 2 - x * y) / (z ^ 2 + x ^ 2 + y ^ 2) := by\n      gcongr ?_ + ?_ + ?_ <;> apply key_insight <;> linarith\n    _ = 1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) := by ring\n    _ ≥ 0 := by positivity",
        reference_preamble="/-\nCopyright (c) 2021 Manuel Candales. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Manuel Candales\n-/\n\n\n\n\nnamespace Imo2005Q3\n\ntheorem key_insight (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z ≥ 1) :\n    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) ≥ (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) := by\n  have key :\n    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2) -\n        (x ^ 5 - x ^ 2 * 1) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) =\n      (x ^ 3 - 1) ^ 2 * x ^ 2 * (y ^ 2 + z ^ 2) /\n        ((x ^ 5 + y ^ 2 + z ^ 2) * (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2))) := by field\n  have h₅ :\n    (x ^ 3 - 1) ^ 2 * x ^ 2 * (y ^ 2 + z ^ 2) /\n        ((x ^ 5 + y ^ 2 + z ^ 2) * (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2))) ≥ 0 := by positivity\n  calc\n    (x ^ 5 - x ^ 2) / (x ^ 5 + y ^ 2 + z ^ 2)\n      ≥ (x ^ 5 - x ^ 2 * 1) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) := by linarith only [key, h₅]\n    _ ≥ (x ^ 5 - x ^ 2 * (x * y * z)) / (x ^ 3 * (x ^ 2 + y ^ 2 + z ^ 2)) := by gcongr\n    _ = (x ^ 2 - y * z) / (x ^ 2 + y ^ 2 + z ^ 2) := by field\n\nend Imo2005Q3\n\nopen Imo2005Q3",
    ),

    # imo2006_q3 — Mathlib Archive/Imo/Imo2006Q3.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2006_q3",
        statement="open Real in theorem imo2006_q3 (M : ℝ) : (∀ a b c : ℝ, |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤ M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) ↔ 9 * sqrt 2 / 32 ≤ M := by",
        difficulty="imo",
        description="Determine the least real number $M$ such that $$ \\left| ab(a^2 - b^2) + bc(b^2 - c^2) + ca(c^2 - a^2) \\right| ≤ M (a^2 + b^2 + c^2)^2 $$ for all real numbers $a$, $b$, $c$.",
        tags=['imo', 'imo2006', 'real', 'inequality'],
        source="Mathlib Archive/Imo/Imo2006Q3.lean",
        reference_proof="  exact ⟨proof₂ M, fun h _ _ _ => proof₁.trans (by gcongr)⟩",
        reference_preamble="/-\nCopyright (c) 2021 Tian Chen. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Tian Chen\n-/\n\n\n\n\nopen Real\n\nnamespace Imo2006Q3\n\n/-- Replacing `x` and `y` with their average increases the left side. -/\ntheorem lhs_ineq {x y : ℝ} (hxy : 0 ≤ x * y) :\n    16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 3 := by\n  have : (x - y) ^ 2 * ((x + y) ^ 2 + 4 * (x * y)) ≥ 0 := by positivity\n  calc 16 * x ^ 2 * y ^ 2 * (x + y) ^ 2 ≤ ((x + y) ^ 2) ^ 2 * (x + y) ^ 2 := by gcongr; linarith\n    _ = ((x + y) ^ 2) ^ 3 := by ring\n\ntheorem four_pow_four_pos : (0 : ℝ) < 4 ^ 4 := by simp\n\ntheorem mid_ineq {s t : ℝ} : s * t ^ 3 ≤ (3 * t + s) ^ 4 / 4 ^ 4 := by\n  rw [le_div_iff₀ four_pow_four_pos]\n  have : 0 ≤ (s - t) ^ 2 * ((s + 7 * t) ^ 2 + 2 * (4 * t) ^ 2) := by positivity\n  linarith\n\n/-- Replacing `x` and `y` with their average decreases the right side. -/\ntheorem rhs_ineq {x y : ℝ} : 3 * (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) := by\n  have : 0 ≤ (x - y) ^ 2 := by positivity\n  linarith\n\ntheorem zero_lt_32 : (0 : ℝ) < 32 := by simp\n\ntheorem subst_wlog {x y z s : ℝ} (hxy : 0 ≤ x * y) (hxyz : x + y + z = 0) :\n    32 * |x * y * z * s| ≤ sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 := by\n  have hz : (x + y) ^ 2 = z ^ 2 := by linear_combination (x + y - z) * hxyz\n  have this :=\n    calc\n      2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)\n        ≤ _ * _ ^ 3 := by gcongr; exact lhs_ineq hxy\n      _ ≤ (3 * (x + y) ^ 2 + 2 * s ^ 2) ^ 4 / 4 ^ 4 := mid_ineq\n      _ ≤ (2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4 := by\n          gcongr (?_ + _) ^ 4 / _\n          apply rhs_ineq\n  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_\n  calc\n    (32 * |x * y * z * s|) ^ 2 = 32 * (2 * s ^ 2 * (16 * x ^ 2 * y ^ 2 * (x + y) ^ 2)) := by\n      rw [mul_pow, sq_abs, hz]; ring\n    _ ≤ 32 * ((2 * (x ^ 2 + y ^ 2 + (x + y) ^ 2) + 2 * s ^ 2) ^ 4 / 4 ^ 4) := by gcongr\n    _ = (sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2) ^ 2 := by\n      simp [field, hz]\n      ring\n\n/-- Proof that `M = 9 * sqrt 2 / 32` works with the substitution. -/\ntheorem subst_proof₁ (x y z s : ℝ) (hxyz : x + y + z = 0) :\n    |x * y * z * s| ≤ sqrt 2 / 32 * (x ^ 2 + y ^ 2 + z ^ 2 + s ^ 2) ^ 2 := by\n  wlog h' : 0 ≤ x * y generalizing x y z; swap\n  · rw [div_mul_eq_mul_div, le_div_iff₀' zero_lt_32]\n    exact subst_wlog h' hxyz\n  rcases (mul_nonneg_of_three x y z).resolve_left h' with h | h\n  · convert this y z x _ h using 2 <;> linarith\n  · convert this z x y _ h using 2 <;> linarith\n\ntheorem proof₁ {a b c : ℝ} :\n    |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤\n      9 * sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 :=\n  calc\n    _ = |(a - b) * (b - c) * (c - a) * -(a + b + c)| := by ring_nf\n    _ ≤ _ := subst_proof₁ (a - b) (b - c) (c - a) (-(a + b + c)) (by ring)\n    _ = _ := by ring\n\ntheorem proof₂ (M : ℝ)\n    (h : ∀ a b c : ℝ,\n      |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| ≤\n        M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2) :\n    9 * sqrt 2 / 32 ≤ M := by\n  set α := sqrt (2 : ℝ)\n  have hα : α ^ 2 = 2 := sq_sqrt (by simp)\n  let a := 2 - 3 * α\n  let c := 2 + 3 * α\n  calc _ = 18 ^ 2 * 2 * α / 48 ^ 2 := by ring\n    _ ≤ M := ?_\n  rw [div_le_iff₀ (by positivity)]\n  calc 18 ^ 2 * 2 * α\n      = 18 ^ 2 * α ^ 2 * α := by linear_combination -324 * α * hα\n    _ = abs (-(18 ^ 2 * α ^ 2 * α)) := by rw [abs_neg, abs_of_nonneg]; positivity\n    _ = |a * 2 * (a ^ 2 - 2 ^ 2) + 2 * c * (2 ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)| := by ring_nf!\n    _ ≤ M * (a ^ 2 + 2 ^ 2 + c ^ 2) ^ 2 := by apply h\n    _ = M * 48 ^ 2 := by linear_combination (324 * α ^ 2 + 1080) * M * hα\n\nend Imo2006Q3\n\nopen Imo2006Q3",
    ),

    # imo2008_q2a — Mathlib Archive/Imo/Imo2008Q2.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2008_q2a",
        statement="theorem imo2008_q2a (x y z : ℝ) (h : x * y * z = 1) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 ≥ 1 := by",
        difficulty="imo",
        description="(a) Prove that ``` x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 ≥ 1 ``` for all real numbers `x`,`y`, `z`, each different from 1, and satisfying `xyz = 1`.",
        tags=['imo', 'imo2008', 'real', 'inequality'],
        source="Mathlib Archive/Imo/Imo2008Q2.lean",
        reference_proof="  obtain ⟨a, b, c, ha, hb, hc, rfl, rfl, rfl⟩ := subst_abc h\n  obtain ⟨m, n, rfl, rfl⟩ : ∃ m n, b = c - m ∧ a = c - m - n := by use c - b, b - a; simp\n  have hm_ne_zero : m ≠ 0 := by contrapose hy; simpa [field]\n  have hn_ne_zero : n ≠ 0 := by contrapose hx; simpa [field]\n  have hmn_ne_zero : m + n ≠ 0 := by contrapose hz; field_simp; linarith\n  have hc_sub_sub : c - (c - m - n) = m + n := by abel\n  rw [ge_iff_le, ← sub_nonneg]\n  convert sq_nonneg ((c * (m ^ 2 + n ^ 2 + m * n) - m * (m + n) ^ 2) / (m * n * (m + n)))\n  simp [field, hc_sub_sub]; ring\n\ndef rationalSolutions :=\n  {s : ℚ × ℚ × ℚ | ∃ x y z : ℚ, s = (x, y, z) ∧ x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y * z = 1 ∧\n    x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = 1}\n\ntheorem imo2008_q2b : Set.Infinite rationalSolutions := by\n  let W := {s : ℚ × ℚ × ℚ | ∃ x y z : ℚ, s = (x, y, z) ∧\n    ∃ t : ℚ, t > 0 ∧ x = -(t + 1) / t ^ 2 ∧ y = t / (t + 1) ^ 2 ∧ z = -t * (t + 1)}\n  have hW_sub_S : W ⊆ rationalSolutions := by\n    intro s hs_in_W\n    rw [rationalSolutions]\n    simp only [Set.mem_setOf_eq] at hs_in_W ⊢\n    rcases hs_in_W with ⟨x, y, z, h₁, t, ht_gt_zero, hx_t, hy_t, hz_t⟩\n    use x, y, z\n    have key_gt_zero : 0 < t ^ 2 + t + 1 := by linarith [pow_pos ht_gt_zero 2, ht_gt_zero]\n    have h₂ : x ≠ 1 := by rw [hx_t]; simp [field]; linarith [key_gt_zero]\n    have h₃ : y ≠ 1 := by rw [hy_t]; simp [field]; linarith [key_gt_zero]\n    have h₄ : z ≠ 1 := by rw [hz_t]; linarith [key_gt_zero]\n    have h₅ : x * y * z = 1 := by rw [hx_t, hy_t, hz_t]; field\n    have h₆ : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = 1 := by\n      have hx1 : (x - 1) ^ 2 = (t ^ 2 + t + 1) ^ 2 / t ^ 4 := by\n        rw [hx_t]; field\n      have hy1 : (y - 1) ^ 2 = (t ^ 2 + t + 1) ^ 2 / (t + 1) ^ 4 := by\n        rw [hy_t]; field\n      have hz1 : (z - 1) ^ 2 = (t ^ 2 + t + 1) ^ 2 := by rw [hz_t]; ring\n      calc\n        x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 =\n            (x ^ 2 * t ^ 4 + y ^ 2 * (t + 1) ^ 4 + z ^ 2) / (t ^ 2 + t + 1) ^ 2 := by\n          rw [hx1, hy1, hz1]; field\n        _ = 1 := by rw [hx_t, hy_t, hz_t]; field\n    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩\n  have hW_inf : Set.Infinite W := by\n    let g : ℚ × ℚ × ℚ → ℚ := fun s => -s.2.2\n    let K := g '' W\n    have hK_not_bdd : ¬BddAbove K := by\n      rw [not_bddAbove_iff]\n      intro q\n      let t : ℚ := max (q + 1) 1\n      use t * (t + 1)\n      have h₁ : t * (t + 1) ∈ K := by\n        let x : ℚ := -(t + 1) / t ^ 2\n        let y : ℚ := t / (t + 1) ^ 2\n        set z : ℚ := -t * (t + 1) with hz_def\n        simp only [t, W, K, g, Set.mem_image, Prod.exists]\n        use x, y, z; constructor\n        · simp only [Set.mem_setOf_eq]\n          use x, y, z; constructor\n          · rfl\n          · use t; constructor\n            · simp only [t, gt_iff_lt, lt_max_iff]; right; trivial\n            exact ⟨rfl, rfl, rfl⟩\n        · have hg : -z = g (x, y, z) := rfl\n          rw [hg, hz_def]; ring\n      have h₂ : q < t * (t + 1) := by linarith [sq_nonneg t, le_max_left (q + 1) 1]\n      exact ⟨h₁, h₂⟩\n    have hK_inf : Set.Infinite K := by intro h; apply hK_not_bdd; exact Set.Finite.bddAbove h\n    exact hK_inf.of_image g\n  exact hW_inf.mono hW_sub_S",
        reference_preamble="/-\nCopyright (c) 2021 Manuel Candales. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Manuel Candales\n-/\n\n\n\n\nnamespace Imo2008Q2\n\ntheorem subst_abc {x y z : ℝ} (h : x * y * z = 1) :\n    ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = a / b ∧ y = b / c ∧ z = c / a := by\n  use x, 1, 1 / y\n  obtain ⟨⟨hx, hy⟩, _⟩ : (x ≠ 0 ∧ y ≠ 0) ∧ z ≠ 0 := by\n    have := h.symm ▸ one_ne_zero\n    simpa [not_or] using this\n  have : z * (y * x) = 1 := by rw [← h]; ac_rfl\n  simp [field, mul_assoc, *]",
    ),

    # imo2008_q3 — Mathlib Archive/Imo/Imo2008Q3.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2008_q3",
        statement="open Real in theorem imo2008_q3 : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt (2 * n) := by",
        difficulty="imo",
        description="Prove that there exist infinitely many positive integers `n` such that `n^2 + 1` has a prime divisor which is greater than `2n + √(2n)`.",
        tags=['imo', 'imo2008', 'number-theory', 'real', 'inequality'],
        source="Mathlib Archive/Imo/Imo2008Q3.lean",
        reference_proof="  intro N\n  obtain ⟨p, hpp, hineq₁, hpmod4⟩ := Nat.exists_prime_gt_modEq_one (N ^ 2 + 20) four_ne_zero\n  obtain ⟨n, hnat, hreal⟩ := p_lemma p hpp hpmod4 (by linarith [hineq₁, Nat.zero_le (N ^ 2)])\n  have hineq₂ : n ^ 2 + 1 ≥ p := Nat.le_of_dvd (n ^ 2).succ_pos hnat\n  have hineq₃ : n * n ≥ N * N := by linarith [hineq₁, hineq₂]\n  have hn_ge_N : n ≥ N := Nat.mul_self_le_mul_self_iff.1 hineq₃\n  exact ⟨n, hn_ge_N, p, hpp, hnat, hreal⟩",
        reference_preamble="/-\nCopyright (c) 2021 Manuel Candales. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Manuel Candales\n-/\n\n\n\n\nopen Real\n\nnamespace Imo2008Q3\n\ntheorem p_lemma (p : ℕ) (hpp : Nat.Prime p) (hp_mod_4_eq_1 : p ≡ 1 [MOD 4]) (hp_gt_20 : p > 20) :\n    ∃ n : ℕ, p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt (2 * n) := by\n  haveI := Fact.mk hpp\n  have hp_mod_4_ne_3 : p % 4 ≠ 3 := by linarith [show p % 4 = 1 from hp_mod_4_eq_1]\n  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr hp_mod_4_ne_3\n  let m := ZMod.valMinAbs y\n  let n := Int.natAbs m\n  have hnat₁ : p ∣ n ^ 2 + 1 := by\n    refine Int.natCast_dvd_natCast.mp ?_\n    simp only [n, Int.natAbs_sq, Int.natCast_pow, Int.natCast_succ]\n    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (m ^ 2 + 1) p).mp ?_\n    simp only [m, Int.cast_pow, Int.cast_add, Int.cast_one, ZMod.coe_valMinAbs]\n    rw [pow_two, ← hy]; exact neg_add_cancel 1\n  have hnat₂ : n ≤ p / 2 := ZMod.natAbs_valMinAbs_le y\n  have hnat₃ : 2 * n ≤ p := by lia\n  set k : ℕ := p - 2 * n with hnat₄\n  have hnat₅ : p ∣ k ^ 2 + 4 := by\n    obtain ⟨x, hx⟩ := hnat₁\n    have : (p : ℤ) ∣ (k : ℤ) ^ 2 + 4 := by\n      use (p : ℤ) - 4 * n + 4 * x\n      have hcast₁ : (k : ℤ) = p - 2 * n := by assumption_mod_cast\n      have hcast₂ : (n : ℤ) ^ 2 + 1 = p * x := by assumption_mod_cast\n      linear_combination ((k : ℤ) + p - 2 * n) * hcast₁ + 4 * hcast₂\n    assumption_mod_cast\n  have hnat₆ : p ≤ k ^ 2 + 4 := Nat.le_of_dvd (k ^ 2 + 3).succ_pos hnat₅\n  have hreal₁ : (k : ℝ) = p - 2 * n := by assumption_mod_cast\n  have hreal₂ : 20 < (p : ℝ) := by assumption_mod_cast\n  have hreal₃ : p ≤ (k : ℝ) ^ 2 + 4 := by assumption_mod_cast\n  have hreal₅ : 4 < (k : ℝ) := by\n    refine lt_of_pow_lt_pow_left₀ 2 k.cast_nonneg ?_\n    linarith only [hreal₂, hreal₃]\n  have hreal₆ : (k : ℝ) > sqrt (2 * n) := by\n    refine lt_of_pow_lt_pow_left₀ 2 k.cast_nonneg ?_\n    rw [sq_sqrt (by positivity)]\n    linarith only [hreal₁, hreal₃, hreal₅]\n  exact ⟨n, hnat₁, by linarith only [hreal₆, hreal₁]⟩\n\nend Imo2008Q3\n\nopen Imo2008Q3",
    ),

    # imo2008_q4 — Mathlib Archive/Imo/Imo2008Q4.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2008_q4",
        statement="open Real in theorem imo2008_q4 (f : ℝ → ℝ) (H₁ : ∀ x > 0, 0 < f x) : (∀ w x y z : ℝ, 0 < w → 0 < x → 0 < y → 0 < z → w * x = y * z → (f w ^ 2 + f x ^ 2) / (f (y ^ 2) + f (z ^ 2)) = (w ^ 2 + x ^ 2) / (y ^ 2 + z ^ 2)) ↔ (∀ x > 0, f x = x) ∨ ∀ x > 0, f x = 1 / x := by",
        difficulty="imo",
        description="Find all functions `f : (0,∞) → (0,∞)` (so, `f` is a function from the positive real numbers to the positive real numbers) such that ``` (f(w)^2 + f(x)^2)/(f(y^2) + f(z^2)) = (w^2 + x^2)/(y^2 + z^2) ``` for all positive real numbers `w`, `x`, `y`, `z`, satisfy",
        tags=['imo', 'imo2008', 'real', 'functional-equation', 'inequality'],
        source="Mathlib Archive/Imo/Imo2008Q4.lean",
        reference_proof="  constructor; swap\n  -- proof that f(x) = x and f(x) = 1/x satisfy the condition\n  · rintro (h | h)\n    · intro w x y z hw hx hy hz _\n      rw [h w hw, h x hx, h (y ^ 2) (pow_pos hy 2), h (z ^ 2) (pow_pos hz 2)]\n    · intro w x y z hw hx hy hz hprod\n      rw [h w hw, h x hx, h (y ^ 2) (pow_pos hy 2), h (z ^ 2) (pow_pos hz 2)]\n      field_simp\n      linear_combination - (z ^ 2 + y ^ 2) * (w ^ 2 + x ^ 2) * (w * x + y * z) * hprod\n  -- proof that the only solutions are f(x) = x or f(x) = 1/x\n  intro H₂\n  have h₀ : f 1 ≠ 0 := (H₁ 1 zero_lt_one).ne'\n  have h₁ : f 1 = 1 := by\n    specialize H₂ 1 1 1 1 zero_lt_one zero_lt_one zero_lt_one\n    grind\n  have h₂ : ∀ x > 0, (f x - x) * (f x - 1 / x) = 0 := by\n    intro x hx\n    have h1xss : 1 * x = sqrt x * sqrt x := by grind [mul_self_sqrt]\n    specialize H₂ 1 x (sqrt x) (sqrt x) zero_lt_one\n    grind [sqrt_pos]\n  have h₃ : ∀ x > 0, f x = x ∨ f x = 1 / x := by simpa [sub_eq_zero] using h₂\n  by_contra! ⟨⟨b, hb, hfb₁⟩, ⟨a, ha, hfa₁⟩⟩\n  obtain hfa₂ := Or.resolve_right (h₃ a ha) hfa₁\n  -- f(a) ≠ 1/a, f(a) = a\n  obtain hfb₂ := Or.resolve_left (h₃ b hb) hfb₁\n  -- f(b) ≠ b, f(b) = 1/b\n  have hab : 0 < a * b := by positivity\n  have habss : a * b = sqrt (a * b) * sqrt (a * b) := (mul_self_sqrt hab.le).symm\n  specialize H₂ a b (sqrt (a * b)) (sqrt (a * b)) ha hb (sqrt_pos.mpr hab) (sqrt_pos.mpr hab) habss\n  rw [sq_sqrt hab.le, ← two_mul (f (a * b)), ← two_mul (a * b)] at H₂\n  rw [hfa₂, hfb₂] at H₂\n  have h2ab_ne_0 : 2 * (a * b) ≠ 0 := by positivity\n  specialize h₃ (a * b) hab\n  rcases h₃ with hab₁ | hab₂\n  -- f(ab) = ab → b^4 = 1 → b = 1 → f(b) = b → false\n  · rw [hab₁] at H₂\n    field_simp at H₂\n    obtain hb₂ := abs_eq_one_of_pow_eq_one b 4 (show 4 ≠ 0 by simp) (by grind)\n    grind [abs_of_pos]\n  -- f(ab) = 1/ab → a^4 = 1 → a = 1 → f(a) = 1/a → false\n  · simp only [hab₂, field] at H₂\n    obtain ha₂ := abs_eq_one_of_pow_eq_one a 4 (show 4 ≠ 0 by simp) (by grind)\n    grind [abs_of_pos]",
        reference_preamble="/-\nCopyright (c) 2021 Manuel Candales. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Manuel Candales\n-/\n\n\n\n\nopen Real\n\nnamespace Imo2008Q4\n\ntheorem abs_eq_one_of_pow_eq_one (x : ℝ) (n : ℕ) (hn : n ≠ 0) (h : x ^ n = 1) : |x| = 1 := by\n  rw [← pow_left_inj₀ (abs_nonneg x) zero_le_one hn, one_pow, pow_abs, h, abs_one]\n\nend Imo2008Q4\n\nopen Imo2008Q4\n\nset_option linter.flexible false in",
    ),

    # imo2011_q3 — Mathlib Archive/Imo/Imo2011Q3.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2011_q3",
        statement="theorem imo2011_q3 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) ≤ y * f x + f (f x)) : ∀ x ≤ 0, f x = 0 := by",
        difficulty="imo",
        description="Let f : ℝ → ℝ be a function that satisfies f(x + y) ≤ y * f(x) + f(f(x)) for all x and y. Prove that f(x) = 0 for all x ≤ 0.",
        tags=['imo', 'imo2011', 'real', 'functional-equation', 'inequality'],
        source="Mathlib Archive/Imo/Imo2011Q3.lean",
        reference_proof="  -- reparameterize\n  have hxt : ∀ x t, f t ≤ t * f x - x * f x + f (f x) := fun x t =>\n    calc\n      f t = f (x + (t - x)) := by rw [add_eq_of_eq_sub' rfl]\n      _ ≤ (t - x) * f x + f (f x) := hf x (t - x)\n      _ = t * f x - x * f x + f (f x) := by rw [sub_mul]\n  have h_ab_combined : ∀ a b, a * f a + b * f b ≤ 2 * f a * f b := fun a b => by\n    linarith [hxt b (f a), hxt a (f b)]\n  have h_f_nonneg_of_pos : ∀ a < 0, 0 ≤ f a := fun a han =>\n    suffices a * f a ≤ 0 from nonneg_of_mul_nonpos_right this han\n    add_le_iff_nonpos_left.mp (h_ab_combined a (2 * f a))\n  have h_f_nonpos : ∀ x, f x ≤ 0 := fun x => by\n    by_contra h_suppose_not\n    -- If we choose a small enough argument for f, then we get a contradiction.\n    let s := (x * f x - f (f x)) / f x\n    have hm : min 0 s - 1 < s := (sub_one_lt _).trans_le (min_le_right 0 s)\n    have hml : min 0 s - 1 < 0 := (sub_one_lt _).trans_le (min_le_left 0 s)\n    suffices f (min 0 s - 1) < 0 from not_le.mpr this (h_f_nonneg_of_pos (min 0 s - 1) hml)\n    have hp : 0 < f x := not_le.mp h_suppose_not\n    calc\n      f (min 0 s - 1) ≤ (min 0 s - 1) * f x - x * f x + f (f x) := hxt x (min 0 s - 1)\n      _ < s * f x - x * f x + f (f x) := by linarith [mul_lt_mul_of_pos_right hm hp]\n      _ = 0 := by rw [(eq_div_iff hp.ne.symm).mp rfl]; linarith\n  have h_fx_zero_of_neg : ∀ x < 0, f x = 0 := fun x hxz =>\n    (h_f_nonpos x).antisymm (h_f_nonneg_of_pos x hxz)\n  intro x hx\n  obtain (h_x_neg : x < 0) | (rfl : x = 0) := hx.lt_or_eq\n  · exact h_fx_zero_of_neg _ h_x_neg\n  · suffices 0 ≤ f 0 from le_antisymm (h_f_nonpos 0) this\n    have hno : f (-1) = 0 := h_fx_zero_of_neg (-1) neg_one_lt_zero\n    have hp := hxt (-1) (-1)\n    rw [hno] at hp\n    linarith",
        reference_preamble="/-\nCopyright (c) 2021 David Renshaw. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: David Renshaw\n-/",
    ),

    # imo2011_q5 — Mathlib Archive/Imo/Imo2011Q5.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2011_q5",
        statement="open Int in theorem imo2011_q5 (f : ℤ → ℤ) (hpos : ∀ n : ℤ, 0 < f n) (hdvd : ∀ m n : ℤ, f (m - n) ∣ f m - f n) : ∀ m n : ℤ, f m ≤ f n → f m ∣ f n := by",
        difficulty="imo",
        description="Let `f` be a function from the set of integers to the set of positive integers. Suppose that, for any two integers `m` and `n`, the difference `f m - f n` is divisible by `f (m - n)`. Prove that, for all integers `m` and `n` with `f m ≤ f n`, the number `f n` ",
        tags=['imo', 'imo2011', 'number-theory', 'functional-equation', 'inequality', 'int'],
        source="Mathlib Archive/Imo/Imo2011Q5.lean",
        reference_proof="  intro m n h_fm_le_fn\n  rcases lt_or_eq_of_le h_fm_le_fn with h_fm_lt_fn | h_fm_eq_fn\n  · -- m < n\n    let d := f m - f (m - n)\n    have h_fn_dvd_d : f n ∣ d := by\n      rw [← sub_sub_self m n]\n      exact hdvd m (m - n)\n    have h_d_lt_fn : d < f n := calc\n      d < f m := sub_lt_self _ (hpos (m - n))\n      _ < f n := h_fm_lt_fn\n    have h_neg_d_lt_fn : -d < f n := by\n      calc\n        -d = f (m - n) - f m := neg_sub _ _\n        _ < f (m - n) := sub_lt_self _ (hpos m)\n        _ ≤ f n - f m := le_of_dvd (sub_pos.mpr h_fm_lt_fn) ?_\n        _ < f n := sub_lt_self _ (hpos m)\n      -- ⊢ f (m - n) ∣ f n - f m\n      rw [← Int.dvd_neg, neg_sub]\n      exact hdvd m n\n    have h_d_eq_zero : d = 0 := by\n      obtain hd | hd | hd : d > 0 ∨ d = 0 ∨ d < 0 := trichotomous d 0\n      · -- d > 0\n        have h₁ : f n ≤ d := le_of_dvd hd h_fn_dvd_d\n        have h₂ : ¬f n ≤ d := not_le.mpr h_d_lt_fn\n        contradiction\n      · -- d = 0\n        exact hd\n      · -- d < 0\n        have h₁ : f n ≤ -d := le_of_dvd (neg_pos.mpr hd) h_fn_dvd_d.neg_right\n        have h₂ : ¬f n ≤ -d := not_le.mpr h_neg_d_lt_fn\n        contradiction\n    have h₁ : f m = f (m - n) := sub_eq_zero.mp h_d_eq_zero\n    have h₂ : f (m - n) ∣ f m - f n := hdvd m n\n    rw [← h₁] at h₂\n    exact (dvd_iff_dvd_of_dvd_sub h₂).mp dvd_rfl\n  · -- m = n\n    rw [h_fm_eq_fn]",
        reference_preamble="/-\nCopyright (c) 2021 Alain Verberkmoes. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Alain Verberkmoes\n-/\n\n\n\n\nopen Int",
    ),

    # imo2013_q1 — Mathlib Archive/Imo/Imo2013Q1.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2013_q1",
        statement="theorem imo2013_q1 (n : ℕ+) (k : ℕ) : ∃ m : ℕ → ℕ+, (1 : ℚ) + (2 ^ k - 1) / n = ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := by",
        difficulty="imo",
        description="Prove that for any pair of positive integers k and n, there exist k positive integers m₁, m₂, ..., mₖ (not necessarily different) such that 1 + (2ᵏ - 1)/ n = (1 + 1/m₁) * (1 + 1/m₂) * ... * (1 + 1/mₖ).",
        tags=['imo', 'imo2013', 'combinatorics', 'rat'],
        source="Mathlib Archive/Imo/Imo2013Q1.lean",
        reference_proof="  induction k generalizing n with\n  | zero => use fun (_ : ℕ) => (1 : ℕ+); simp -- For the base case, any m works.\n  | succ pk hpk =>\n  obtain ⟨t, ht : ↑n = t + t⟩ | ⟨t, ht : ↑n = 2 * t + 1⟩ := (n : ℕ).even_or_odd\n  · -- even case\n    rw [← two_mul] at ht\n    -- Eliminate the zero case to simplify later calculations.\n    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero <| by\n      rintro (rfl : t = 0)\n      rw [Nat.mul_zero] at ht; exact PNat.ne_zero n ht\n    -- Now we have ht : ↑n = 2 * (t + 1).\n    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩\n    obtain ⟨pm, hpm⟩ := hpk t_succ\n    let m i := if i < pk then pm i else ⟨2 * t + 2 ^ pk.succ, arith_lemma pk t⟩\n    use m\n    have hmpk : (m pk : ℚ) = 2 * t + 2 ^ pk.succ := by\n      have : m pk = ⟨2 * t + 2 ^ pk.succ, _⟩ := if_neg (irrefl pk); simp [this]\n    calc\n      ((1 : ℚ) + (2 ^ pk.succ - 1) / (n : ℚ) : ℚ) = 1 + (2 * 2 ^ pk - 1) / (2 * (t + 1) : ℕ) := by\n        rw [ht, pow_succ']\n      _ = (1 + 1 / (2 * t + 2 * 2 ^ pk)) * (1 + (2 ^ pk - 1) / (↑t + 1)) := by\n        simp [field, -mul_eq_mul_right_iff]\n        ring\n      _ = (1 + 1 / (2 * t + 2 ^ pk.succ)) * (1 + (2 ^ pk - 1) / t_succ) := by\n        simp [pow_succ', PNat.mk_coe, t_succ]\n      _ = (∏ i ∈ Finset.range pk, (1 + 1 / (m i : ℚ))) * (1 + 1 / m pk) := by\n        rw [prod_lemma, hpm, ← hmpk, mul_comm]\n      _ = ∏ i ∈ Finset.range pk.succ, (1 + 1 / (m i : ℚ)) := by rw [← Finset.prod_range_succ _ pk]\n  · -- odd case\n    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩\n    obtain ⟨pm, hpm⟩ := hpk t_succ\n    let m i := if i < pk then pm i else ⟨2 * t + 1, Nat.succ_pos _⟩\n    use m\n    have hmpk : (m pk : ℚ) = 2 * t + 1 := by\n      have : m pk = ⟨2 * t + 1, _⟩ := if_neg (irrefl pk)\n      simp [this]\n    calc\n      ((1 : ℚ) + (2 ^ pk.succ - 1) / ↑n : ℚ) = 1 + (2 * 2 ^ pk - 1) / (2 * t + 1 : ℕ) := by\n        rw [ht, pow_succ']\n      _ = (1 + 1 / (2 * t + 1)) * (1 + (2 ^ pk - 1) / (t + 1)) := by\n        simp [field]\n        ring\n      _ = (1 + 1 / (2 * t + 1)) * (1 + (2 ^ pk - 1) / t_succ) := by norm_cast\n      _ = (∏ i ∈ Finset.range pk, (1 + 1 / (m i : ℚ))) * (1 + 1 / ↑(m pk)) := by\n        rw [prod_lemma, hpm, ← hmpk, mul_comm]\n      _ = ∏ i ∈ Finset.range pk.succ, (1 + 1 / (m i : ℚ)) := by rw [← Finset.prod_range_succ _ pk]",
        reference_preamble="/-\nCopyright (c) 2021 David Renshaw. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: David Renshaw\n-/\n\n\n\n\nnamespace Imo2013Q1\n\ntheorem arith_lemma (k n : ℕ) : 0 < 2 * n + 2 ^ k.succ := by positivity\n\ntheorem prod_lemma (m : ℕ → ℕ+) (k : ℕ) (nm : ℕ+) :\n    ∏ i ∈ Finset.range k, ((1 : ℚ) + 1 / ↑(if i < k then m i else nm)) =\n      ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := by\n  suffices ∀ i, i ∈ Finset.range k → (1 : ℚ) + 1 / ↑(if i < k then m i else nm) = 1 + 1 / m i from\n    Finset.prod_congr rfl this\n  grind\n\nend Imo2013Q1\n\nopen Imo2013Q1",
    ),

    # imo2013_q5 — Mathlib Archive/Imo/Imo2013Q5.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2013_q5",
        statement="theorem imo2013_q5 (f : ℚ → ℝ) (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y) (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y)) (H_fixed_point : ∃ a, 1 < a ∧ f a = a) : ∀ x, 0 < x → f x = x := by",
        difficulty="imo",
        description="Let `ℚ>₀` be the positive rational numbers. Let `f : ℚ>₀ → ℝ` be a function satisfying the conditions 1. `f(x) * f(y) ≥ f(x * y)` 2. `f(x + y) ≥ f(x) + f(y)` for all `x, y ∈ ℚ>₀`. Given that `f(a) = a` for some rational `a > 1`, prove that `f(x) = x` for all `",
        tags=['imo', 'imo2013', 'real', 'functional-equation', 'inequality', 'rat'],
        source="Mathlib Archive/Imo/Imo2013Q5.lean",
        reference_proof="  obtain ⟨a, ha1, hae⟩ := H_fixed_point\n  have H3 : ∀ x : ℚ, 0 < x → ∀ n : ℕ, 0 < n → ↑n * f x ≤ f (n * x) := by\n    intro x hx n hn\n    rcases n with - | n\n    · exact (lt_irrefl 0 hn).elim\n    induction n with\n    | zero => norm_num\n    | succ pn hpn =>\n      calc\n        ↑(pn + 2) * f x = (↑pn + 1 + 1) * f x := by norm_cast\n        _ = (↑pn + 1) * f x + f x := by ring\n        _ ≤ f (↑pn.succ * x) + f x := by norm_cast; grw [hpn pn.succ_pos]\n        _ ≤ f ((↑pn + 1) * x + x) := by exact_mod_cast H2 _ _ (mul_pos pn.cast_add_one_pos hx) hx\n        _ = f ((↑pn + 1 + 1) * x) := by ring_nf\n        _ = f (↑(pn + 2) * x) := by norm_cast\n  have H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n := by\n    intro n hn\n    have hf1 : 1 ≤ f 1 := by\n      have a_pos : (0 : ℝ) < a := Rat.cast_pos.mpr (zero_lt_one.trans ha1)\n      suffices ↑a * 1 ≤ ↑a * f 1 by rwa [← mul_le_mul_iff_right₀ a_pos]\n      calc\n        ↑a * 1 = ↑a := mul_one (a : ℝ)\n        _ = f a := hae.symm\n        _ = f (a * 1) := by rw [mul_one]\n        _ ≤ f a * f 1 := (H1 a 1) (zero_lt_one.trans ha1) zero_lt_one\n        _ = ↑a * f 1 := by rw [hae]\n    calc\n      (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm\n      _ ≤ (n : ℝ) * f 1 := by gcongr\n      _ ≤ f (n * 1) := H3 1 zero_lt_one n hn\n      _ = f n := by rw [mul_one]\n  have H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x := by\n    intro x hx\n    have hxnm1 : ∀ n : ℕ, 0 < n → (x : ℝ) ^ n - 1 < f x ^ n := by\n      intro n hn\n      calc\n        (x : ℝ) ^ n - 1 < f (x ^ n) :=\n            mod_cast fx_gt_xm1 (one_le_pow₀ hx.le) H1 H2 H4\n        _ ≤ f x ^ n := pow_f_le_f_pow hn hx H1 H4\n    have hx' : 1 < (x : ℝ) := mod_cast hx\n    have hxp : 0 < x := by positivity\n    exact le_of_all_pow_lt_succ' hx' (f_pos_of_pos hxp H1 H4) hxnm1\n  have h_f_commutes_with_pos_nat_mul : ∀ n : ℕ, 0 < n → ∀ x : ℚ, 0 < x → f (n * x) = n * f x := by\n    intro n hn x hx\n    have h2 : f (n * x) ≤ n * f x := by\n      rcases n with - | n\n      · exfalso; exact Nat.lt_asymm hn hn\n      rcases n with - | n\n      · norm_num\n      have hfneq : f n.succ.succ = n.succ.succ := by\n        have :=\n          fixed_point_of_gt_1 (Nat.one_lt_cast.mpr (Nat.succ_lt_succ n.succ_pos)) H1 H2 H4 H5 ha1\n            hae\n        rwa [Rat.cast_natCast n.succ.succ] at this\n      rw [← hfneq]\n      exact H1 (n.succ.succ : ℚ) x (Nat.cast_pos.mpr hn) hx\n    exact h2.antisymm (H3 x hx n hn)\n  -- For the final calculation, we expand x as (2 * x.num) / (2 * x.den), because\n  -- we need the top of the fraction to be strictly greater than 1 in order\n  -- to apply `fixed_point_of_gt_1`.\n  intro x hx\n  have H₀ : x * x.den = x.num := x.mul_den_eq_num\n  have H : x * (↑(2 * x.den) : ℚ) = (↑(2 * x.num) : ℚ) := by push_cast; linear_combination 2 * H₀\n  set x2denom := 2 * x.den\n  set x2num := 2 * x.num\n  have hx2pos : 0 < 2 * x.den := by positivity\n  have hx2cnezr : (x2denom : ℝ) ≠ (0 : ℝ) := by positivity\n  have : 0 < x.num := by rwa [Rat.num_pos]\n  have hx2num_gt_one : (1 : ℚ) < (2 * x.num : ℤ) := by norm_cast; linarith\n  apply mul_left_cancel₀ hx2cnezr\n  calc\n    x2denom * f x\n      = f (x2denom * x) := (h_f_commutes_with_pos_nat_mul x2denom hx2pos x hx).symm\n    _ = f x2num := by congr; linear_combination H\n    _ = x2num := fixed_point_of_gt_1 hx2num_gt_one H1 H2 H4 H5 ha1 hae\n    _ = ((x2num : ℚ) : ℝ) := by norm_cast\n    _ = (↑(x2denom * x) : ℝ) := by congr; linear_combination -H\n    _ = x2denom * x := by push_cast; rfl",
        reference_preamble="/-\nCopyright (c) 2021 David Renshaw. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: David Renshaw\n-/\n\n\n\n\nnamespace Imo2013Q5\n\ntheorem le_of_all_pow_lt_succ {x y : ℝ} (hx : 1 < x) (hy : 1 < y)\n    (h : ∀ n : ℕ, 0 < n → x ^ n - 1 < y ^ n) : x ≤ y := by\n  by_contra! hxy\n  have hxmy : 0 < x - y := sub_pos.mpr hxy\n  have hn : ∀ n : ℕ, 0 < n → (x - y) * (n : ℝ) ≤ x ^ n - y ^ n := by\n    intro n _\n    have hterm : ∀ i : ℕ, i ∈ Finset.range n → 1 ≤ x ^ i * y ^ (n - 1 - i) := by\n      intro i _\n      calc\n        1 ≤ x ^ i := one_le_pow₀ hx.le\n        _ = x ^ i * 1 := by ring\n        _ ≤ x ^ i * y ^ (n - 1 - i) := by gcongr; apply one_le_pow₀ hy.le\n    calc\n      (x - y) * (n : ℝ) = (n : ℝ) * (x - y) := by ring\n      _ = (∑ _i ∈ Finset.range n, (1 : ℝ)) * (x - y) := by\n        simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_range]\n      _ ≤ (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y) := by\n        gcongr with i hi; apply hterm i hi\n      _ = x ^ n - y ^ n := geom_sum₂_mul x y n\n  -- Choose n larger than 1 / (x - y).\n  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - y))\n  have hNp : 0 < N := mod_cast (one_div_pos.mpr hxmy).trans hN\n  have :=\n    calc\n      1 = (x - y) * (1 / (x - y)) := by field\n      _ < (x - y) * N := by gcongr\n      _ ≤ x ^ N - y ^ N := hn N hNp\n  linarith [h N hNp]\n\n/-- Like `le_of_all_pow_lt_succ`, but with a weaker assumption for `y`.\n-/\ntheorem le_of_all_pow_lt_succ' {x y : ℝ} (hx : 1 < x) (hy : 0 < y)\n    (h : ∀ n : ℕ, 0 < n → x ^ n - 1 < y ^ n) : x ≤ y := by\n  refine le_of_all_pow_lt_succ hx ?_ h\n  by_contra! hy'' : y ≤ 1\n  -- Then there exists y' such that 0 < y ≤ 1 < y' < x.\n  have h_y'_lt_x : (x + 1) / 2 < x := by linarith\n  have h1_lt_y' : 1 < (x + 1) / 2 := by linarith\n  set y' := (x + 1) / 2\n  have h_y_lt_y' : y < y' := by linarith\n  have hh : ∀ n, 0 < n → x ^ n - 1 < y' ^ n := by\n    intro n hn\n    calc\n      x ^ n - 1 < y ^ n := h n hn\n      _ ≤ y' ^ n := by gcongr\n  exact h_y'_lt_x.not_ge (le_of_all_pow_lt_succ hx h1_lt_y' hh)\n\ntheorem f_pos_of_pos {f : ℚ → ℝ} {q : ℚ} (hq : 0 < q)\n    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :\n    0 < f q := by\n  have num_pos : 0 < q.num := Rat.num_pos.mpr hq\n  have hmul_pos :=\n    calc\n      (0 : ℝ) < q.num := Int.cast_pos.mpr num_pos\n      _ = ((q.num.natAbs : ℤ) : ℝ) := congr_arg Int.cast (Int.natAbs_of_nonneg num_pos.le).symm\n      _ ≤ f q.num.natAbs := (H4 q.num.natAbs ((@Int.natAbs_pos q.num).mpr num_pos.ne.symm))\n      _ = f q.num := by rw [Nat.cast_natAbs, abs_of_nonneg num_pos.le]\n      _ = f (q * q.den) := by rw [← Rat.mul_den_eq_num]\n      _ ≤ f q * f q.den := H1 q q.den hq (Nat.cast_pos.mpr q.pos)\n  have h_f_denom_pos :=\n    calc\n      (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos\n      _ ≤ f q.den := H4 q.den q.pos\n  exact pos_of_mul_pos_left hmul_pos h_f_denom_pos.le\n\ntheorem fx_gt_xm1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 ≤ x)\n    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)\n    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y)) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :\n    (x - 1 : ℝ) < f x := by\n  have hx0 :=\n    calc\n      (x - 1 : ℝ) < ⌊x⌋₊ := mod_cast Nat.sub_one_lt_floor x\n      _ ≤ f ⌊x⌋₊ := H4 _ (Nat.floor_pos.2 hx)\n  obtain h_eq | h_lt := (Nat.floor_le <| zero_le_one.trans hx).eq_or_lt\n  · rwa [h_eq] at hx0\n  calc\n    (x - 1 : ℝ) < f ⌊x⌋₊ := hx0\n    _ < f (x - ⌊x⌋₊) + f ⌊x⌋₊ := (lt_add_of_pos_left _ (f_pos_of_pos (sub_pos.mpr h_lt) H1 H4))\n    _ ≤ f (x - ⌊x⌋₊ + ⌊x⌋₊) := (H2 _ _ (sub_pos.mpr h_lt) (Nat.cast_pos.2 (Nat.floor_pos.2 hx)))\n    _ = f x := by ring_nf\n\ntheorem pow_f_le_f_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n) {x : ℚ} (hx : 1 < x)\n    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n) :\n    f (x ^ n) ≤ f x ^ n := by\n  induction n with\n  | zero => exfalso; exact Nat.lt_asymm hn hn\n  | succ pn hpn =>\n    rcases pn with - | pn\n    · norm_num\n    have hpn' := hpn pn.succ_pos\n    rw [pow_succ x (pn + 1), pow_succ (f x) (pn + 1)]\n    have hxp : 0 < x := by positivity\n    calc\n      _ ≤ f (x ^ (pn + 1)) * f x := H1 (x ^ (pn + 1)) x (pow_pos hxp (pn + 1)) hxp\n      _ ≤ f x ^ (pn + 1) * f x := by gcongr; exact (f_pos_of_pos hxp H1 H4).le\n\ntheorem fixed_point_of_pos_nat_pow {f : ℚ → ℝ} {n : ℕ} (hn : 0 < n)\n    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)\n    (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x) {a : ℚ} (ha1 : 1 < a) (hae : f a = a) :\n    f (a ^ n) = a ^ n := by\n  have hh0 : (a : ℝ) ^ n ≤ f (a ^ n) := mod_cast H5 (a ^ n) (one_lt_pow₀ ha1 hn.ne')\n  have hh1 :=\n    calc\n      f (a ^ n) ≤ f a ^ n := pow_f_le_f_pow hn ha1 H1 H4\n      _ = (a : ℝ) ^ n := by rw [← hae]\n  exact mod_cast hh1.antisymm hh0\n\ntheorem fixed_point_of_gt_1 {f : ℚ → ℝ} {x : ℚ} (hx : 1 < x)\n    (H1 : ∀ x y, 0 < x → 0 < y → f (x * y) ≤ f x * f y)\n    (H2 : ∀ x y, 0 < x → 0 < y → f x + f y ≤ f (x + y)) (H4 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ f n)\n    (H5 : ∀ x : ℚ, 1 < x → (x : ℝ) ≤ f x) {a : ℚ} (ha1 : 1 < a) (hae : f a = a) : f x = x := by\n  -- Choose n such that 1 + x < a^n.\n  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 + x) ha1\n  have h_big_enough : (1 : ℚ) < a ^ N - x := lt_sub_iff_add_lt.mpr hN\n  have h1 :=\n    calc\n      (x : ℝ) + (a ^ N - x : ℚ) ≤ f x + (a ^ N - x : ℚ) := by gcongr; exact H5 x hx\n      _ ≤ f x + f (a ^ N - x) := by gcongr; exact H5 _ h_big_enough\n  have hxp : 0 < x := by positivity\n  have hNp : 0 < N := by by_contra! H; rw [Nat.le_zero.mp H] at hN; linarith\n  have h2 :=\n    calc\n      f x + f (a ^ N - x) ≤ f (x + (a ^ N - x)) := H2 x (a ^ N - x) hxp (by positivity)\n      _ = f (a ^ N) := by ring_nf\n      _ = a ^ N := fixed_point_of_pos_nat_pow hNp H1 H4 H5 ha1 hae\n      _ = x + (a ^ N - x) := by ring\n  have heq := h1.antisymm (mod_cast h2)\n  linarith [H5 x hx, H5 _ h_big_enough]\n\nend Imo2013Q5\n\nopen Imo2013Q5",
    ),

    # imo2019_q1 — Mathlib Archive/Imo/Imo2019Q1.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2019_q1",
        statement="theorem imo2019_q1 (f : ℤ → ℤ) : (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) ↔ f = 0 ∨ ∃ c, f = fun x => 2 * x + c := by",
        difficulty="imo",
        description="Determine all functions `f : ℤ → ℤ` such that, for all integers `a` and `b`, `f(2a) + 2f(b) = f(f(a+b))`.",
        tags=['imo', 'imo2019', 'functional-equation', 'inequality', 'int'],
        source="Mathlib Archive/Imo/Imo2019Q1.lean",
        reference_proof="  constructor; swap\n  -- easy way: f(x)=0 and f(x)=2x+c work.\n  · rintro (rfl | ⟨c, rfl⟩) <;> intros <;> norm_num; ring\n  -- hard way.\n  intro hf\n  -- functional equation\n  -- Using `h` for `(0, b)` and `(-1, b + 1)`, we get `f (b + 1) = f b + m`\n  obtain ⟨m, H⟩ : ∃ m, ∀ b, f (b + 1) = f b + m := by\n    refine ⟨(f 0 - f (-2)) / 2, fun b => ?_⟩\n    refine sub_eq_iff_eq_add'.1 (Int.eq_ediv_of_mul_eq_right two_ne_zero ?_)\n    have h1 : f 0 + 2 * f b = f (f b) := by simpa using hf 0 b\n    have h2 : f (-2) + 2 * f (b + 1) = f (f b) := by simpa using hf (-1) (b + 1)\n    linarith\n  -- Hence, `f` is an affine map, `f b = f 0 + m * b`\n  obtain ⟨c, H⟩ : ∃ c, ∀ b, f b = c + m * b := by\n    refine ⟨f 0, fun b => ?_⟩\n    induction b with\n    | zero => simp\n    | succ b ihb => simp [H, ihb, mul_add, add_assoc]\n    | pred b ihb =>\n      rw [← sub_eq_of_eq_add (H _)]\n      simp [ihb]; ring\n  -- Now use `hf 0 0` and `hf 0 1` to show that `m ∈ {0, 2}`\n  have H3 : 2 * c = m * c := by simpa [H, mul_add] using hf 0 0\n  obtain rfl | rfl : 2 = m ∨ m = 0 := by simpa [H, mul_add, H3] using hf 0 1\n  · right; use c; ext b; simp [H, add_comm]\n  · left; ext b; simpa [H, two_ne_zero] using H3",
        reference_preamble="/-\nCopyright (c) 2020 Kevin Buzzard. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Kevin Buzzard\n-/",
    ),

    # imo2019_q4 — Mathlib Archive/Imo/Imo2019Q4.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2019_q4",
        statement="open Nat Finset in theorem imo2019_q4 {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : (k ! : ℤ) = ∏ i ∈ range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) ↔ (k, n) = (1, 1) ∨ (k, n) = (3, 2) := by",
        difficulty="imo",
        description="Find all pairs `(k, n)` of positive integers such that ``` k! = (2 ^ n - 1)(2 ^ n - 2)(2 ^ n - 4)···(2 ^ n - 2 ^ (n - 1)) ``` We show in this file that this property holds iff `(k, n) = (1, 1) ∨ (k, n) = (3, 2)`.",
        tags=['imo', 'imo2019', 'combinatorics', 'inequality', 'int'],
        source="Mathlib Archive/Imo/Imo2019Q4.lean",
        reference_proof="  -- The implication `←` holds.\n  constructor\n  swap\n  · rintro (h | h) <;> rcases Prod.ext_iff.mp h with ⟨rfl, rfl⟩ <;> decide\n  intro h\n  -- We know that n < 6.\n  have := Imo2019Q4.upper_bound hk h\n  interval_cases n\n  -- n = 1\n  · norm_num at h; simp [le_antisymm h (succ_le_of_lt hk)]\n  -- n = 2\n  · right; congr; norm_num [prod_range_succ] at h; norm_cast at h; rwa [← factorial_inj']\n    norm_num\n  all_goals exfalso; simp [prod_range_succ] at h; norm_cast at h\n  -- n = 3\n  · refine monotone_factorial.ne_of_lt_of_lt_nat 5 ?_ ?_ _ h <;> decide\n  -- n = 4\n  · refine monotone_factorial.ne_of_lt_of_lt_nat 7 ?_ ?_ _ h <;> decide\n  -- n = 5\n  · refine monotone_factorial.ne_of_lt_of_lt_nat 10 ?_ ?_ _ h <;> decide",
        reference_preamble="/-\nCopyright (c) 2020 Floris van Doorn. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Floris van Doorn\n-/\n\n\n\n\nopen Nat Finset\n\nnamespace Imo2019Q4\n\ntheorem upper_bound {k n : ℕ} (hk : k > 0)\n    (h : (k ! : ℤ) = ∏ i ∈ range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i)) : n < 6 := by\n  have h2 : ∑ i ∈ range n, i < k := by\n    suffices emultiplicity 2 (k ! : ℤ) = ↑(∑ i ∈ range n, i : ℕ) by\n      rw [← Nat.cast_lt (α := ℕ∞), ← this]; change emultiplicity ((2 : ℕ) : ℤ) _ < _\n      simp_rw [Int.natCast_emultiplicity, emultiplicity_two_factorial_lt hk.lt.ne.symm]\n    rw [h, Finset.emultiplicity_prod Int.prime_two, Nat.cast_sum]\n    apply sum_congr rfl; intro i hi\n    rw [emultiplicity_sub_of_gt, emultiplicity_pow_self_of_prime Int.prime_two]\n    rwa [emultiplicity_pow_self_of_prime Int.prime_two,\n      emultiplicity_pow_self_of_prime Int.prime_two, Nat.cast_lt, ← mem_range]\n  rw [← not_le]; intro hn\n  apply _root_.ne_of_gt _ h\n  calc ∏ i ∈ range n, ((2 : ℤ) ^ n - (2 : ℤ) ^ i) ≤ ∏ _ ∈ range n, (2 : ℤ) ^ n := ?_\n    _ < k ! := ?_\n  · gcongr\n    · intro i hi\n      rw [mem_range] at hi\n      have : (2 : ℤ) ^ i ≤ (2 : ℤ) ^ n := by gcongr; norm_num\n      linarith\n    · apply sub_le_self\n      positivity\n  norm_cast\n  calc ∏ _ ∈ range n, 2 ^ n = 2 ^ (n * n) := by rw [prod_const, card_range, ← pow_mul]\n    _ < (∑ i ∈ range n, i)! := ?_\n    _ ≤ k ! := by gcongr\n  clear h h2\n  induction n, hn using Nat.le_induction with\n  | base => decide\n  | succ n' hn' IH =>\n    let A := ∑ i ∈ range n', i\n    have le_sum : ∑ i ∈ range 6, i ≤ A := by\n      apply sum_le_sum_of_subset\n      simpa using hn'\n    calc 2 ^ ((n' + 1) * (n' + 1))\n        ≤ 2 ^ (n' * n' + 4 * n') := by gcongr <;> linarith\n      _ = 2 ^ (n' * n') * (2 ^ 4) ^ n' := by rw [← pow_mul, ← pow_add]\n      _ < A ! * (2 ^ 4) ^ n' := by gcongr\n      _ = A ! * (15 + 1) ^ n' := rfl\n      _ ≤ A ! * (A + 1) ^ n' := by gcongr; exact le_sum\n      _ ≤ (A + n')! := factorial_mul_pow_le_factorial\n      _ = (∑ i ∈ range (n' + 1), i)! := by rw [sum_range_succ]\n\nend Imo2019Q4\n\nset_option linter.flexible false in -- TODO: fix non-terminal simp",
    ),

    # imo2020_q2 — Mathlib Archive/Imo/Imo2020Q2.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2020_q2",
        statement="open Real in theorem imo2020_q2 (a b c d : ℝ) (hd0 : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a) (h1 : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 := by",
        difficulty="imo",
        description="The real numbers `a`, `b`, `c`, `d` are such that `a ≥ b ≥ c ≥ d > 0` and `a + b + c + d = 1`.",
        tags=['imo', 'imo2020', 'real', 'inequality'],
        source="Mathlib Archive/Imo/Imo2020Q2.lean",
        reference_proof="  have hp : a ^ a * b ^ b * c ^ c * d ^ d ≤ a * a + b * b + c * c + d * d := by\n    refine geom_mean_le_arith_mean4_weighted ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h1 <;> linarith\n  calc\n    (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d =\n        (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) := by ac_rfl\n    _ ≤ (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d) := by gcongr; linarith\n    _ = (a + 2 * b + 3 * c + 4 * d) * a ^ 2 + (a + 2 * b + 3 * c + 4 * d) * b ^ 2\n        + (a + 2 * b + 3 * c + 4 * d) * c ^ 2 + (a + 2 * b + 3 * c + 4 * d) * d ^ 2 := by ring\n    _ ≤ (a + 3 * b + 3 * c + 3 * d) * a ^ 2 + (3 * a + b + 3 * c + 3 * d) * b ^ 2\n        + (3 * a + 3 * b + c + 3 * d) * c ^ 2 + (3 * a + 3 * b + 3 * c + d) * d ^ 2 := by\n        gcongr ?_ * _ + ?_ * _ + ?_ * _ + ?_ * _ <;> linarith\n    _ < (a + 3 * b + 3 * c + 3 * d) * a ^ 2 + (3 * a + b + 3 * c + 3 * d) * b ^ 2\n        + (3 * a + 3 * b + c + 3 * d) * c ^ 2 + (3 * a + 3 * b + 3 * c + d) * d ^ 2\n        + (6 * a * b * c + 6 * a * b * d + 6 * a * c * d + 6 * b * c * d) :=\n        (lt_add_of_pos_right _ (by apply_rules [add_pos, mul_pos, zero_lt_one] <;> linarith))\n    _ = (a + b + c + d) ^ 3 := by ring\n    _ = 1 := by simp [h1]",
        reference_preamble="/-\nCopyright (c) 2020 Joseph Myers. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Joseph Myers, Yury Kudryashov\n-/\n\n\n\n\nopen Real",
    ),

    # imo2021_q1 — Mathlib Archive/Imo/Imo2021Q1.lean
    # Statement and reference proof both verified in this harness
    # (scripts/verify_imo_candidates.py): the proof below closes to 0 goals.
    EvalProblem(
        name="imo2021_q1",
        statement="open Finset in theorem imo2021_q1 : ∀ n : ℕ, 100 ≤ n → ∀ A ⊆ Finset.Icc n (2 * n), (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ IsSquare (a + b)) ∨ ∃ a ∈ Finset.Icc n (2 * n) \\ A, ∃ b ∈ Finset.Icc n (2 * n) \\ A, a ≠ b ∧ IsSquare (a + b) := by",
        difficulty="imo",
        description="Let `n ≥ 100` be an integer. Ivan writes the numbers `n, n+1, ..., 2*n` each on different cards.",
        tags=['imo', 'imo2021', 'combinatorics', 'inequality'],
        source="Mathlib Archive/Imo/Imo2021Q1.lean",
        reference_proof="  intro n hn A hA\n  -- For each n ∈ ℕ such that 100 ≤ n, there exists a pairwise unequal triplet {a, b, c} ⊆ [n, 2n]\n  -- such that all pairwise sums are perfect squares. In practice, it will be easier to use\n  -- a finite set B ⊆ [n, 2n] such that all pairwise unequal pairs of B sum to a perfect square\n  -- noting that B has cardinality greater or equal to 3, by the explicit construction of the\n  -- triplet {a, b, c} before.\n  obtain ⟨B, hB, h₁, h₂⟩ := exists_finset_3_le_card_with_pairs_summing_to_squares hn\n  have hBsub : B ⊆ Finset.Icc n (2 * n) := by\n    intro c hcB; simpa only [Finset.mem_Icc] using h₂ c hcB\n  have hB' : 2 * 1 < #(B ∩ (Icc n (2 * n) \\ A) ∪ B ∩ A) := by\n    rwa [← inter_union_distrib_left, sdiff_union_self_eq_union, union_eq_left.2 hA,\n      inter_eq_left.2 hBsub, ← Nat.succ_le_iff]\n  -- Since B has cardinality greater or equal to 3, there must exist a subset C ⊆ B such that\n  -- for any A ⊆ [n, 2n], either C ⊆ A or C ⊆ [n, 2n] \\ A and C has cardinality greater\n  -- or equal to 2.\n  obtain ⟨C, hC, hCA⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hB'\n  rw [Finset.one_lt_card] at hC\n  rcases hC with ⟨a, ha, b, hb, hab⟩\n  simp only [Finset.subset_iff, Finset.mem_inter] at hCA\n  -- Now we split into the two cases C ⊆ [n, 2n] \\ A and C ⊆ A, which can be dealt with identically.\n  rcases hCA with hCA | hCA <;> [right; left] <;>\n    exact ⟨a, (hCA ha).2, b, (hCA hb).2, hab, h₁ a (hCA ha).1 b (hCA hb).1 hab⟩",
        reference_preamble="/-\nCopyright (c) 2021 Mantas Bakšys. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Mantas Bakšys\n-/\n\n\n\nopen Finset\n\nnamespace Imo2021Q1\n\n-- We will later make use of the fact that there exists `l : ℕ` such that\n-- `n ≤ 2 * l ^ 2 - 4 * l` and `2 * l ^ 2 + 4 * l ≤ 2 * n` for `n ≥ 100`.\nlemma exists_numbers_in_interval {n : ℕ} (hn : 100 ≤ n) :\n    ∃ l : ℕ, n + 4 * l ≤ 2 * l ^ 2 ∧ 2 * l ^ 2 + 4 * l ≤ 2 * n := by\n  have hn' : 1 ≤ Nat.sqrt (n + 1) := by\n    rw [Nat.le_sqrt]\n    apply Nat.le_add_left\n  have h₁ := Nat.sqrt_le' (n + 1)\n  have h₂ := Nat.succ_le_succ_sqrt' (n + 1)\n  have h₃ : 10 ≤ (n + 1).sqrt := by\n    rw [Nat.le_sqrt]\n    lia\n  rw [← Nat.sub_add_cancel hn'] at h₁ h₂ h₃\n  set l := (n + 1).sqrt - 1\n  refine ⟨l, ?_, ?_⟩\n  · calc n + 4 * l ≤ (l ^ 2 + 4 * l + 2) + 4 * l := by linarith only [h₂]\n      _ ≤ 2 * l ^ 2 := by nlinarith only [h₃]\n  · linarith only [h₁]\n\nlemma exists_triplet_summing_to_squares {n : ℕ} (hn : 100 ≤ n) :\n    ∃ a b c : ℕ, n ≤ a ∧ a < b ∧ b < c ∧ c ≤ 2 * n ∧\n      IsSquare (a + b) ∧ IsSquare (c + a) ∧ IsSquare (b + c) := by\n  obtain ⟨l, hl1, hl2⟩ := exists_numbers_in_interval hn\n  have hl : 1 < l := by contrapose! hl1; interval_cases l <;> linarith\n  have h₁ : 4 * l ≤ 2 * l ^ 2 := by lia\n  have h₂ : 1 ≤ 2 * l := by lia\n  refine ⟨2 * l ^ 2 - 4 * l, 2 * l ^ 2 + 1, 2 * l ^ 2 + 4 * l, ?_, ?_, ?_,\n    ⟨?_, ⟨2 * l - 1, ?_⟩, ⟨2 * l, ?_⟩, 2 * l + 1, ?_⟩⟩\n  all_goals zify [h₁, h₂]; linarith\n\n-- Since it will be more convenient to work with sets later on, we will translate the above claim\n-- to state that there always exists a set B ⊆ [n, 2n] of cardinality at least 3, such that each\n-- pair of pairwise unequal elements of B sums to a perfect square.\nlemma exists_finset_3_le_card_with_pairs_summing_to_squares {n : ℕ} (hn : 100 ≤ n) :\n    ∃ B : Finset ℕ,\n      2 * 1 + 1 ≤ #B ∧\n      (∀ a ∈ B, ∀ b ∈ B, a ≠ b → IsSquare (a + b)) ∧\n      ∀ c ∈ B, n ≤ c ∧ c ≤ 2 * n := by\n  obtain ⟨a, b, c, hna, hab, hbc, hcn, h₁, h₂, h₃⟩ := exists_triplet_summing_to_squares hn\n  refine ⟨{a, b, c}, ?_, ?_, ?_⟩\n  · suffices a ∉ {b, c} ∧ b ∉ {c} by\n      rw [Finset.card_insert_of_notMem this.1, Finset.card_insert_of_notMem this.2,\n        Finset.card_singleton]\n    grind\n  · intro x hx y hy hxy\n    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy\n    rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl) <;> grind\n  · grind\n\nend Imo2021Q1\n\nopen Imo2021Q1",
    ),
]
DIFFICULTIES: tuple[str, ...] = ("easy", "medium", "hard", "stretch", "imo")
PROBLEM_BY_NAME: dict[str, EvalProblem] = {p.name: p for p in PROBLEMS}


def select_problems(filter_str: str | None) -> list[EvalProblem]:
    """
    Parse a --problems filter string and return matching EvalProblems.

    Accepts a comma-separated list of difficulty tiers and/or problem names.
    Preserves the canonical ordering from PROBLEMS; no duplicates.

    Examples:
        None / ""          → all 20 problems
        "easy"             → all easy problems
        "easy,medium"      → easy + medium
        "add_zero"         → that one problem
        "easy,add_zero"    → easy tier (add_zero is already inside, not duplicated)

    Raises ValueError for unrecognised tokens.
    """
    if not filter_str:
        return list(PROBLEMS)

    tokens = [t.strip() for t in filter_str.split(",") if t.strip()]
    selected: list[EvalProblem] = []
    seen: set[str] = set()

    for token in tokens:
        if token in DIFFICULTIES:
            for p in PROBLEMS:
                if p.difficulty == token and p.name not in seen:
                    selected.append(p)
                    seen.add(p.name)
        elif token in PROBLEM_BY_NAME:
            p = PROBLEM_BY_NAME[token]
            if p.name not in seen:
                selected.append(p)
                seen.add(p.name)
        else:
            raise ValueError(
                f"Unknown filter token '{token}'. "
                f"Valid tiers: {', '.join(DIFFICULTIES)}. "
                f"Valid names: {', '.join(PROBLEM_BY_NAME)}."
            )

    return selected
