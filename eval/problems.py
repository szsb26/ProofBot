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
    difficulty: str   # "easy" | "medium" | "hard" | "stretch"
    description: str = ""   # natural-language statement of what's being proved
    tags: list[str] = field(default_factory=list)


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
    EvalProblem(
        name="tournament_champion",
        statement=(
            "theorem eval_tournament_champion "
            "{α : Type*} [Fintype α] [DecidableEq α] "
            "(beats : α → α → Prop) [DecidableRel beats] "
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
]

DIFFICULTIES: tuple[str, ...] = ("easy", "medium", "hard", "stretch")
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
