import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- A *board* is a finite multiset of natural numbers.  The full board discipline
(entries `≥ 1`, cardinality `2026`) is captured by the predicate `IsInitial`. -/
abbrev Board := Multiset ℕ

/-- An *initial board*: exactly `2026` entries, each strictly greater than `1`. -/
def IsInitial (B : Board) : Prop :=
  Multiset.card B = 2026 ∧ ∀ a ∈ B, 1 < a

/-- A single *move*: pick two entries `m, n` (from two distinct positions,
modelled as two separate elements of the multiset) both `> 1`, remove them and
insert `gcd(m, n)` and `lcm(m, n) / gcd(m, n)`.  Using `m ::ₘ n ::ₘ s` for the
source board automatically encodes that the two chosen positions are distinct
(they are two separate multiset elements, whose *values* may coincide). -/
def Move (B B' : Board) : Prop :=
  ∃ (m n : ℕ) (s : Board), 1 < m ∧ 1 < n ∧
    B = m ::ₘ n ::ₘ s ∧
    B' = Nat.gcd m n ::ₘ (Nat.lcm m n / Nat.gcd m n) ::ₘ s

/-- A board is *terminal* when at most one entry is `> 1`, so no move is possible. -/
def IsTerminal (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) ≤ 1

/-- A board has a *unique large entry* when exactly one entry is `> 1`. -/
def HasUniqueLarge (B : Board) : Prop :=
  Multiset.card (B.filter (fun a => 1 < a)) = 1

/-- `Reachable B B'` : `B'` can be obtained from `B` by a finite sequence of moves
(the reflexive–transitive closure of `Move`).  A finite play from `B` to a
terminal board `B'` is precisely a witness of `Reachable B B'` with `IsTerminal B'`. -/
def Reachable (B B' : Board) : Prop := Relation.ReflTransGen Move B B'

/-- The exponent `g_p` for a prime `p` and board `B`: the `gcd` of the `p`-adic
valuations of the entries of `B`.  Since `gcd(a, 0) = a`, valuations equal to `0`
(entries not divisible by `p`) do not affect this gcd, so `gExp p B` is the gcd of
the *positive* `p`-adic valuations occurring in `B`. -/
noncomputable def gExp (p : ℕ) (B : Board) : ℕ :=
  (B.map (fun a => padicValNat p a)).gcd

/-- The claimed invariant terminal value
`M = ∏_{p ∣ ∏ B} p ^ gExp p B`, the product over all primes dividing some entry
of `B` of `p` raised to the gcd of the `p`-adic valuations. -/
noncomputable def Mval (B : Board) : ℕ :=
  ∏ p ∈ B.prod.primeFactors, p ^ gExp p B

/-- On ℕ, the `GCDMonoid` gcd used by `Multiset.gcd` is `Nat.gcd`. -/
theorem gcdMonoid_eq_natGcd (a b : ℕ) : GCDMonoid.gcd a b = Nat.gcd a b := rfl

/-- Valuation of a gcd is the min of the valuations. -/
theorem padicValNat_gcd {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
  have h := Nat.factorization_gcd (a := m) (b := n) hm hn
  have := congrArg (fun f => f p) h
  simp only [Finsupp.inf_apply] at this
  rw [← Nat.factorization_def _ hp, this, Nat.factorization_def _ hp,
    Nat.factorization_def _ hp]

/-- Valuation of an lcm is the max of the valuations. -/
theorem padicValNat_lcm {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n) = max (padicValNat p m) (padicValNat p n) := by
  have h := Nat.factorization_lcm (a := m) (b := n) hm hn
  have := congrArg (fun f => f p) h
  simp only [Finsupp.sup_apply] at this
  rw [← Nat.factorization_def _ hp, this, Nat.factorization_def _ hp,
    Nat.factorization_def _ hp]

/-- Valuation of `lcm/gcd` is `max - min = |a-b|`. -/
theorem padicValNat_lcm_div_gcd {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    padicValNat p (Nat.lcm m n / Nat.gcd m n)
      = max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  rw [padicValNat.div_of_dvd hdvd, padicValNat_lcm hp hm hn, padicValNat_gcd hp hm hn]

/-- Core arithmetic identity: `gcd a b = gcd (min a b) (max a b - min a b)`. -/
theorem natGcd_min_max_sub (a b : ℕ) :
    Nat.gcd a b = Nat.gcd (min a b) (max a b - min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h, Nat.gcd_comm a b, Nat.gcd_sub_self_right h,
      Nat.gcd_comm]
  · rw [min_eq_right h, max_eq_left h, Nat.gcd_sub_self_right h, Nat.gcd_comm]

/-- The key invariant: a single move preserves `gExp p`, for any prime `p`. -/
theorem gExp_move {p : ℕ} (hp : p.Prime) {B B' : Board} (h : Move B B') :
    gExp p B = gExp p B' := by
  obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := h
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hg0 : Nat.gcd m n ≠ 0 := Nat.gcd_ne_zero_left hm0
  have hl0 : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero hm0 hn0
  have hq0 : Nat.lcm m n / Nat.gcd m n ≠ 0 := by
    have hdvd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
    intro hcontra
    rw [Nat.div_eq_zero_iff] at hcontra
    rcases hcontra with hc | hc
    · exact hg0 hc
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hdvd) (not_le.mpr hc)
  simp only [gExp, hB, hB', Multiset.map_cons, Multiset.gcd_cons, gcdMonoid_eq_natGcd]
  set G := (Multiset.map (fun a => padicValNat p a) s).gcd with hG
  have hvg : padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) :=
    padicValNat_gcd hp hm0 hn0
  have hvq : padicValNat p (Nat.lcm m n / Nat.gcd m n)
      = max (padicValNat p m) (padicValNat p n) - min (padicValNat p m) (padicValNat p n) :=
    padicValNat_lcm_div_gcd hp hm0 hn0
  rw [hvg, hvq]
  -- goal: gcd (v m) (gcd (v n) G) = gcd (min) (gcd (max - min) G)
  set a := padicValNat p m
  set b := padicValNat p n
  rw [← Nat.gcd_assoc, ← Nat.gcd_assoc, ← natGcd_min_max_sub a b]

open scoped ArithmeticFunction

/-- Total number of prime factors with multiplicity over the board. -/
noncomputable def totalOmega (B : Board) : ℕ := (B.map (fun a => ArithmeticFunction.cardFactors a)).sum

/-- Number of entries `> 1`. -/
noncomputable def countLarge (B : Board) : ℕ := Multiset.card (B.filter (fun a => 1 < a))

theorem countLarge_cons (a : ℕ) (t : Board) :
    countLarge (a ::ₘ t) = (if 1 < a then 1 else 0) + countLarge t := by
  unfold countLarge
  rw [Multiset.filter_cons]
  by_cases h : 1 < a <;> simp [h, Multiset.card_add, add_comm]

theorem totalOmega_cons (a : ℕ) (t : Board) :
    totalOmega (a ::ₘ t) = ArithmeticFunction.cardFactors a + totalOmega t := by
  unfold totalOmega
  rw [Multiset.map_cons, Multiset.sum_cons]

/-- `Ω` is additive on products of nonzero naturals. -/
theorem cardFactors_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ArithmeticFunction.cardFactors (a * b)
      = ArithmeticFunction.cardFactors a + ArithmeticFunction.cardFactors b := by
  simp only [ArithmeticFunction.cardFactors_apply]
  rw [(Nat.perm_primeFactorsList_mul ha hb).length_eq, List.length_append]

/-- The measure that strictly decreases on each move. -/
noncomputable def mu (B : Board) : ℕ := totalOmega B * 2027 + countLarge B

/-- A single move strictly decreases `mu`, provided the board card is `≤ 2026`
(so that `countLarge` stays `< 2027`). -/
theorem mu_move {B B' : Board} (h : Move B B') (hcard : Multiset.card B' ≤ 2026) :
    mu B' < mu B := by
  obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := h
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hg0 : Nat.gcd m n ≠ 0 := Nat.gcd_ne_zero_left hm0
  have hl0 : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero hm0 hn0
  have hdvd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  have hq0 : Nat.lcm m n / Nat.gcd m n ≠ 0 := by
    intro hcontra
    rw [Nat.div_eq_zero_iff] at hcontra
    rcases hcontra with hc | hc
    · exact hg0 hc
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hdvd) (not_le.mpr hc)
  -- Ω relation: totalOmega B' + Ω(gcd) = totalOmega B
  have hlcmeq : Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    Nat.mul_div_cancel' hdvd
  have hmn : m * n = Nat.gcd m n * Nat.lcm m n := (Nat.gcd_mul_lcm m n).symm
  have homm : ArithmeticFunction.cardFactors m + ArithmeticFunction.cardFactors n
      = ArithmeticFunction.cardFactors (Nat.gcd m n) + ArithmeticFunction.cardFactors (Nat.lcm m n) := by
    rw [← cardFactors_mul hm0 hn0, hmn, cardFactors_mul hg0 hl0]
  have hlcmsplit : ArithmeticFunction.cardFactors (Nat.lcm m n)
      = ArithmeticFunction.cardFactors (Nat.gcd m n)
        + ArithmeticFunction.cardFactors (Nat.lcm m n / Nat.gcd m n) := by
    conv_lhs => rw [← hlcmeq]
    rw [cardFactors_mul hg0 hq0]
  have hTotal : totalOmega B' + ArithmeticFunction.cardFactors (Nat.gcd m n) = totalOmega B := by
    rw [hB, hB', totalOmega_cons, totalOmega_cons, totalOmega_cons, totalOmega_cons]
    omega
  -- countLarge relation
  have hcountB : countLarge B = 2 + countLarge s := by
    rw [hB, countLarge_cons, countLarge_cons]
    simp [hm, hn]
    omega
  have hcountB' : countLarge B'
      = (if 1 < Nat.gcd m n then 1 else 0) + (if 1 < Nat.lcm m n / Nat.gcd m n then 1 else 0)
        + countLarge s := by
    rw [hB', countLarge_cons, countLarge_cons]
    ring
  have hcB'bound : countLarge B' ≤ 2026 := le_trans (by
    unfold countLarge; exact Multiset.card_le_card (Multiset.filter_le _ _)) hcard
  rcases Nat.lt_or_ge 1 (Nat.gcd m n) with hgt | hle
  · -- gcd > 1 : Ω(gcd) ≥ 1
    have hOg : 1 ≤ ArithmeticFunction.cardFactors (Nat.gcd m n) :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hgt
    unfold mu
    omega
  · -- gcd = 1
    have hg1 : Nat.gcd m n = 1 := by omega
    have hOg0 : ArithmeticFunction.cardFactors (Nat.gcd m n) = 0 := by rw [hg1]; simp
    -- lcm/gcd = lcm = m*n > 1
    have : Nat.lcm m n / Nat.gcd m n = m * n := by
      rw [hg1, Nat.div_one]
      have : Nat.lcm m n = m * n := by
        have := Nat.gcd_mul_lcm m n; rw [hg1, one_mul] at this; omega
      exact this
    have hbig : 1 < Nat.lcm m n / Nat.gcd m n := by
      rw [this]; nlinarith
    have hnotgcd : ¬ (1 < Nat.gcd m n) := by omega
    unfold mu
    rw [hcountB', hcountB]
    simp only [hnotgcd, if_false, hbig, if_true]
    omega

/-- A move preserves the board's cardinality. -/
theorem card_move {B B' : Board} (h : Move B B') : Multiset.card B' = Multiset.card B := by
  obtain ⟨m, n, s, hm, hn, hB, hB'⟩ := h
  subst hB hB'
  simp [Multiset.card_cons]

/-- `gExp p` is invariant along a reachability chain (for prime `p`). -/
theorem gExp_reachable {p : ℕ} (hp : p.Prime) {B B' : Board} (h : Reachable B B') :
    gExp p B = gExp p B' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [ih, gExp_move hp hstep]

/-- The claimed value `Mval` is invariant along a reachability chain. -/
theorem card_reachable {B B' : Board} (h : Reachable B B') :
    Multiset.card B' = Multiset.card B := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [card_move hstep, ih]

/-- An initial board has a prime `p` with `gExp p B₀ ≠ 0`. -/
theorem exists_prime_gExp_pos (B₀ : Board) (hB₀ : IsInitial B₀) :
    ∃ p : ℕ, p.Prime ∧ gExp p B₀ ≠ 0 := by
  -- pick an entry a₀ > 1
  have : ∃ a₀, a₀ ∈ B₀ := by
    have hcard := hB₀.1
    rcases Multiset.exists_mem_of_ne_zero (s := B₀) (by
      intro h; rw [h] at hcard; simp at hcard) with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨a₀, ha₀⟩ := this
  have ha₀1 : 1 < a₀ := hB₀.2 a₀ ha₀
  obtain ⟨p, hp, hpa⟩ := (a₀).exists_prime_and_dvd (by omega : a₀ ≠ 1)
  refine ⟨p, hp, ?_⟩
  intro hzero
  rw [gExp, Multiset.gcd_eq_zero_iff] at hzero
  have : padicValNat p a₀ = 0 := by
    have := hzero (padicValNat p a₀) (Multiset.mem_map.mpr ⟨a₀, ha₀, rfl⟩)
    exact this
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : 1 ≤ padicValNat p a₀ := one_le_padicValNat_of_dvd (by omega : a₀ ≠ 0) hpa
  omega

/-- A move preserves positivity of all entries. -/
theorem pos_move {B B' : Board} (h : Move B B') (hB : ∀ a ∈ B, 0 < a) :
    ∀ a ∈ B', 0 < a := by
  obtain ⟨m, n, s, hm, hn, hBeq, hB'eq⟩ := h
  subst hB'eq
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hg0 : Nat.gcd m n ≠ 0 := Nat.gcd_ne_zero_left hm0
  have hl0 : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero hm0 hn0
  have hdvd : Nat.gcd m n ∣ Nat.lcm m n := (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  have hq0 : Nat.lcm m n / Nat.gcd m n ≠ 0 := by
    intro hcontra
    rw [Nat.div_eq_zero_iff] at hcontra
    rcases hcontra with hc | hc
    · exact hg0 hc
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hdvd) (not_le.mpr hc)
  intro a ha
  rw [Multiset.mem_cons, Multiset.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Nat.pos_of_ne_zero hg0
  · exact Nat.pos_of_ne_zero hq0
  · apply hB
    rw [hBeq]; simp [ha]

/-- Reachability preserves positivity of all entries. -/
theorem pos_reachable {B B' : Board} (h : Reachable B B') (hB : ∀ a ∈ B, 0 < a) :
    ∀ a ∈ B', 0 < a := by
  induction h with
  | refl => exact hB
  | tail _ hstep ih => exact pos_move hstep ih

/-- If some prime valuation gcd is nonzero, there is an entry `> 1`. -/
theorem exists_large_of_gExp {p : ℕ} (hp : p.Prime) {B : Board} (h : gExp p B ≠ 0) :
    ∃ a ∈ B, 1 < a := by
  rw [gExp, Ne, Multiset.gcd_eq_zero_iff] at h
  push_neg at h
  obtain ⟨x, hx, hxne⟩ := h
  rw [Multiset.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, ?_⟩
  by_contra hcon
  push_neg at hcon
  interval_cases a
  · simp at hxne
  · simp at hxne

/-- Product of a board with positive entries is positive. -/
theorem prod_ne_zero {B : Board} (hB : ∀ a ∈ B, 0 < a) : B.prod ≠ 0 := by
  have : 0 < B.prod := Multiset.prod_pos hB
  omega

/-- For a board with positive entries, the primes dividing the product are exactly
the primes with a nonzero valuation gcd. -/
theorem mem_primeFactors_iff_gExp {B : Board} (hB : ∀ a ∈ B, 0 < a) {p : ℕ} :
    p ∈ B.prod.primeFactors ↔ (p.Prime ∧ gExp p B ≠ 0) := by
  have hprod : B.prod ≠ 0 := prod_ne_zero hB
  rw [Nat.mem_primeFactors_of_ne_zero hprod]
  constructor
  · rintro ⟨hp, hdvd⟩
    refine ⟨hp, ?_⟩
    obtain ⟨a, ha, hpa⟩ := hp.prime.exists_mem_multiset_dvd hdvd
    have ha0 : a ≠ 0 := (hB a ha).ne'
    haveI : Fact p.Prime := ⟨hp⟩
    have hva : padicValNat p a ≠ 0 := (dvd_iff_padicValNat_ne_zero ha0).mp hpa
    rw [gExp, Ne, Multiset.gcd_eq_zero_iff]
    push_neg
    exact ⟨padicValNat p a, Multiset.mem_map.mpr ⟨a, ha, rfl⟩, hva⟩
  · rintro ⟨hp, hgexp⟩
    refine ⟨hp, ?_⟩
    rw [gExp, Ne, Multiset.gcd_eq_zero_iff] at hgexp
    push_neg at hgexp
    obtain ⟨x, hx, hxne⟩ := hgexp
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha0 : a ≠ 0 := (hB a ha).ne'
    haveI : Fact p.Prime := ⟨hp⟩
    have hpa : p ∣ a := (dvd_iff_padicValNat_ne_zero ha0).mpr hxne
    exact hpa.trans (Multiset.dvd_prod ha)

/-- `Mval` is invariant under a single move (both boards positive). -/
theorem Mval_move {B B' : Board} (h : Move B B')
    (hB : ∀ a ∈ B, 0 < a) (hB' : ∀ a ∈ B', 0 < a) : Mval B = Mval B' := by
  have hset : B.prod.primeFactors = B'.prod.primeFactors := by
    ext p
    rw [mem_primeFactors_iff_gExp hB, mem_primeFactors_iff_gExp hB']
    constructor
    · rintro ⟨hp, hg⟩; exact ⟨hp, by rw [← gExp_move hp h]; exact hg⟩
    · rintro ⟨hp, hg⟩; exact ⟨hp, by rw [gExp_move hp h]; exact hg⟩
  unfold Mval
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors_of_ne_zero (prod_ne_zero hB')).mp hp |>.1
  rw [gExp_move hpp h]

/-- `Mval` is invariant along a reachability chain (given positivity of the start). -/
theorem Mval_reachable {B B' : Board} (h : Reachable B B') (hB : ∀ a ∈ B, 0 < a) :
    Mval B = Mval B' := by
  induction h with
  | refl => rfl
  | @tail c d hbc hcd ih =>
    have hc : ∀ a ∈ c, 0 < a := pos_reachable hbc hB
    have hd : ∀ a ∈ d, 0 < a := pos_move hcd hc
    rw [ih, Mval_move hcd hc hd]

/-- The `gExp` of a board consisting of `M` and copies of `1`. -/
theorem gExp_ones {p M : ℕ} {s : Board} (hs : ∀ a ∈ s, a = 1) :
    gExp p (M ::ₘ s) = padicValNat p M := by
  unfold gExp
  rw [Multiset.map_cons, Multiset.gcd_cons, gcdMonoid_eq_natGcd]
  have : (s.map (fun a => padicValNat p a)).gcd = 0 := by
    rw [Multiset.gcd_eq_zero_iff]
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hs a ha]
    simp
  rw [this, Nat.gcd_zero_right]

/-- Terminal value equals `Mval` of the terminal board. -/
theorem Mval_terminal {B : Board} (hpos : ∀ a ∈ B, 0 < a) (hterm : IsTerminal B)
    {M : ℕ} (hM : 1 < M) (hMem : M ∈ B) : Mval B = M := by
  -- decompose B = M ::ₘ s, all of s are 1
  set s := B.erase M with hs_def
  have hBeq : B = M ::ₘ s := (Multiset.cons_erase hMem).symm
  have hsones : ∀ a ∈ s, a = 1 := by
    intro a ha
    have haB : a ∈ B := by rw [hBeq]; exact Multiset.mem_cons_of_mem ha
    have hapos : 0 < a := hpos a haB
    by_contra hne
    have ha1 : 1 < a := by omega
    -- then filter (1<·) B contains both M and a (distinct positions)
    have : 2 ≤ Multiset.card (B.filter (fun a => 1 < a)) := by
      rw [hBeq, Multiset.filter_cons_of_pos _ hM]
      rw [Multiset.card_cons]
      have hmem : a ∈ s.filter (fun a => 1 < a) := Multiset.mem_filter.mpr ⟨ha, ha1⟩
      have hge : 1 ≤ Multiset.card (s.filter (fun a => 1 < a)) := by
        rw [Nat.one_le_iff_ne_zero, Ne, Multiset.card_eq_zero]
        intro he; rw [he] at hmem; simp at hmem
      show 2 ≤ (Multiset.filter (fun a => 1 < a) s).card + 1
      omega
    unfold IsTerminal at hterm
    omega
  have hprodM : B.prod = M := by
    rw [hBeq, Multiset.prod_cons]
    have : s.prod = 1 := by
      rw [Multiset.prod_eq_one]
      exact hsones
    rw [this, mul_one]
  have hM0 : M ≠ 0 := by omega
  unfold Mval
  rw [hprodM]
  -- gExp p B = padicValNat p M = M.factorization p
  have hgexp : ∀ p ∈ M.primeFactors, gExp p B = M.factorization p := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors_of_ne_zero hM0).mp hp |>.1
    rw [hBeq, gExp_ones hsones, Nat.factorization_def _ hpp]
  rw [Finset.prod_congr rfl (fun p hp => by rw [hgexp p hp])]
  -- ∏ p ∈ M.primeFactors, p ^ (M.factorization p) = M
  rw [← Nat.prod_factorization_eq_prod_primeFactors (fun p e => p ^ e)]
  exact Nat.factorization_prod_pow_eq_self hM0

/-- **Statement (a), part 1 — termination.**  There is no infinite play starting
from an initial board `B₀`: no infinite sequence of boards can start at `B₀` and
have every consecutive pair related by a `Move`. -/
theorem statement_a_termination (B₀ : Board) (hB₀ : IsInitial B₀) :
    ¬ ∃ f : ℕ → Board, f 0 = B₀ ∧ ∀ k, Move (f k) (f (k + 1)) := by
  rintro ⟨f, hf0, hmove⟩
  -- card is 2026 for all k
  have hcard : ∀ k, Multiset.card (f k) = 2026 := by
    intro k
    induction k with
    | zero => rw [hf0]; exact hB₀.1
    | succ j ih => rw [card_move (hmove j)]; exact ih
  -- mu strictly decreases each step
  have hdec : ∀ k, mu (f (k + 1)) < mu (f k) := by
    intro k
    exact mu_move (hmove k) (le_of_eq (hcard (k + 1)))
  -- hence mu (f k) + k ≤ mu (f 0)
  have hbound : ∀ k, mu (f k) + k ≤ mu (f 0) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      have := hdec j
      omega
  have := hbound (mu (f 0) + 1)
  omega

/-- **Statement (a), part 2 — unique large entry.**  Any terminal board reachable
from an initial board `B₀` has exactly one entry `> 1`. -/
theorem statement_a_unique_large (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B') :
    HasUniqueLarge B' := by
  obtain ⟨p, hp, hpne⟩ := exists_prime_gExp_pos B₀ hB₀
  have hpne' : gExp p B' ≠ 0 := by rw [← gExp_reachable hp hreach]; exact hpne
  obtain ⟨a, ha, ha1⟩ := exists_large_of_gExp hp hpne'
  -- countLarge B' ≥ 1
  have hge : 1 ≤ Multiset.card (B'.filter (fun a => 1 < a)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Multiset.card_eq_zero]
    intro hempty
    have : a ∈ B'.filter (fun a => 1 < a) := Multiset.mem_filter.mpr ⟨ha, ha1⟩
    rw [hempty] at this
    simp at this
  unfold HasUniqueLarge
  unfold IsTerminal at hterm
  omega

/-- **Value of `M` (correctness of the explicit formula).**  For any terminal board
`B'` reachable from an initial board `B₀`, the unique entry `M > 1` of `B'` equals
the invariant `Mval B₀`. -/
theorem terminal_value_eq_Mval (B₀ : Board) (hB₀ : IsInitial B₀)
    (B' : Board) (hreach : Reachable B₀ B') (hterm : IsTerminal B')
    (M : ℕ) (hM : 1 < M) (hMem : M ∈ B') :
    M = Mval B₀ := by
  have hB₀pos : ∀ a ∈ B₀, 0 < a := fun a ha => by
    have := hB₀.2 a ha; omega
  have hB'pos : ∀ a ∈ B', 0 < a := pos_reachable hreach hB₀pos
  have h1 : Mval B₀ = Mval B' := Mval_reachable hreach hB₀pos
  have h2 : Mval B' = M := Mval_terminal hB'pos hterm hM hMem
  rw [h1, h2]

/-- The invariant terminal value is itself `> 1`, since all initial entries exceed
`1`. -/
theorem Mval_gt_one (B₀ : Board) (hB₀ : IsInitial B₀) : 1 < Mval B₀ := by
  have hB₀pos : ∀ a ∈ B₀, 0 < a := fun a ha => by
    have := hB₀.2 a ha; omega
  obtain ⟨p, hp, hpne⟩ := exists_prime_gExp_pos B₀ hB₀
  have hpmem : p ∈ B₀.prod.primeFactors := (mem_primeFactors_iff_gExp hB₀pos).mpr ⟨hp, hpne⟩
  -- the p-term is ≥ p ≥ 2, all other terms ≥ 1
  have hterm : 2 ≤ p ^ gExp p B₀ := by
    have hpge : 2 ≤ p := hp.two_le
    have hge1 : 1 ≤ gExp p B₀ := Nat.one_le_iff_ne_zero.mpr hpne
    calc 2 ≤ p := hpge
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ gExp p B₀ := Nat.pow_le_pow_right (by omega) hge1
  unfold Mval
  have hle : p ^ gExp p B₀ ≤ ∏ q ∈ B₀.prod.primeFactors, q ^ gExp q B₀ := by
    apply Finset.single_le_prod' (f := fun q => q ^ gExp q B₀)
    · intro q hq
      have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by have := hqp.pos; omega))
    · exact hpmem
  omega

/-- **Statement (b) — invariance of `M`.**  Any two terminal boards reachable from
the same initial board `B₀` have the same set of entries `> 1`; since (by (a)) each
has exactly one such entry, this says the terminal value `M` is the same for both. -/
theorem statement_b_invariance (B₀ : Board) (hB₀ : IsInitial B₀)
    (B₁ B₂ : Board) (h₁ : Reachable B₀ B₁) (h₂ : Reachable B₀ B₂)
    (t₁ : IsTerminal B₁) (t₂ : IsTerminal B₂) :
    ∀ M, (1 < M ∧ M ∈ B₁) ↔ (1 < M ∧ M ∈ B₂) := by
  have hB₀pos : ∀ a ∈ B₀, 0 < a := fun a ha => by
    have := hB₀.2 a ha; omega
  -- helper: a terminal reachable board contains a unique large entry equal to Mval B₀
  have key : ∀ B, Reachable B₀ B → IsTerminal B →
      ∀ M, (1 < M ∧ M ∈ B) ↔ (1 < M ∧ M = Mval B₀) := by
    intro B hreach hterm M
    constructor
    · rintro ⟨hM, hMem⟩
      exact ⟨hM, terminal_value_eq_Mval B₀ hB₀ B hreach hterm M hM hMem⟩
    · rintro ⟨hM, hMeq⟩
      refine ⟨hM, ?_⟩
      -- B has exactly one large entry; find it, it equals Mval B₀ = M
      obtain ⟨p, hp, hpne⟩ := exists_prime_gExp_pos B₀ hB₀
      have hpne' : gExp p B ≠ 0 := by rw [← gExp_reachable hp hreach]; exact hpne
      obtain ⟨a, ha, ha1⟩ := exists_large_of_gExp hp hpne'
      have hBpos : ∀ x ∈ B, 0 < x := pos_reachable hreach hB₀pos
      have haeq : a = Mval B₀ := terminal_value_eq_Mval B₀ hB₀ B hreach hterm a ha1 ha
      rw [hMeq, ← haeq]; exact ha
  intro M
  rw [key B₁ h₁ t₁ M, key B₂ h₂ t₂ M]
