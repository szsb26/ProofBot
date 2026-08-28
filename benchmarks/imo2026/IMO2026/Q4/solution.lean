import Mathlib

namespace TriangleGame

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`.

We pick an apex angle `α` and the two base angles `β, γ` (so `s = {α, β, γ}`), and a
cut parameter `x` in the open interval `(γ, 180 - β)`. The resulting two triangles
have angle multisets `L = {β, x, 180 - β - x}` and `R = {γ, 180 - x, x - γ}`.
Ranging over all `α, β, γ` with `s = {α, β, γ}` captures all three apex choices and
both assignments of the two base angles. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

/-- The set of triangles from which Mulan can force, in finitely many steps, a
triangle with an interior angle equal to `θ`, no matter how Shan-Yu discards.

This is the least predicate closed under:
* (`win`) if the current triangle already has an angle equal to `θ`, Mulan has won;
* (`move`) if Mulan can make a cut producing children `L` and `R` from *both* of
  which she wins (so whichever one Shan-Yu keeps, she still wins), then she wins
  from the current triangle.

Membership means Mulan wins in finitely many steps. -/
inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

/-- Mulan can guarantee victory for the value `θ`: from every valid starting
triangle she wins in finitely many steps regardless of Shan-Yu's play. -/
def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

/-! ## Structural helper lemmas -/

/-- Membership in the three-element multiset `{a, b, c}`. -/
theorem mem_triple {a b c y : ℝ} :
    y ∈ ({a, b, c} : Multiset ℝ) ↔ y = a ∨ y = b ∨ y = c := by
  simp [Multiset.insert_eq_cons]

/-- The sum of a three-element multiset `{a, b, c}` is `a + b + c`. -/
theorem sum_triple (a b c : ℝ) : ({a, b, c} : Multiset ℝ).sum = a + b + c := by
  simp [Multiset.insert_eq_cons]
  ring

/-- The cardinality of the three-element multiset `{a, b, c}` is `3`. -/
theorem card_triple (a b c : ℝ) : ({a, b, c} : Multiset ℝ).card = 3 := by
  simp [Multiset.insert_eq_cons, Multiset.sum_cons]

/-- **Lemma 2 (cut preserves validity).** An admissible cut of a valid triangle yields
two valid triangles. -/
theorem cut_preserves {s L R : Multiset ℝ} (hs : IsTriangle s) (hcut : IsCut s L R) :
    IsTriangle L ∧ IsTriangle R := by
  obtain ⟨α, β, γ, x, hs_eq, hγx, hxβ, hL, hR⟩ := hcut
  obtain ⟨hcard, hpos, hsum⟩ := hs
  rw [hs_eq] at hpos hsum
  rw [sum_triple] at hsum
  have hα : 0 < α := hpos α (by rw [mem_triple]; tauto)
  have hβ : 0 < β := hpos β (by rw [mem_triple]; tauto)
  have hγ : 0 < γ := hpos γ (by rw [mem_triple]; tauto)
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rw [hL]; exact card_triple _ _ _
    · intro y hy
      rw [hL, mem_triple] at hy
      rcases hy with h | h | h
      · rw [h]; exact hβ
      · rw [h]; linarith
      · rw [h]; linarith
    · rw [hL, sum_triple]; ring
  · refine ⟨?_, ?_, ?_⟩
    · rw [hR]; exact card_triple _ _ _
    · intro y hy
      rw [hR, mem_triple] at hy
      rcases hy with h | h | h
      · rw [h]; exact hγ
      · rw [h]; linarith
      · rw [h]; linarith
    · rw [hR, sum_triple]; ring

/-- Enumerate a triangle with a chosen apex angle `a ∈ s`. -/
theorem triangle_with_apex {s : Multiset ℝ} (hs : IsTriangle s) {a : ℝ} (ha : a ∈ s) :
    ∃ β γ : ℝ, s = {a, β, γ} := by
  obtain ⟨hcard, hpos, hsum⟩ := hs
  have herase : (s.erase a).card = 2 := by
    have := Multiset.card_erase_of_mem ha
    rw [this, hcard]; rfl
  obtain ⟨β, γ, hβγ⟩ := Multiset.card_eq_two.mp herase
  refine ⟨β, γ, ?_⟩
  have : s = a ::ₘ s.erase a := (Multiset.cons_erase ha).symm
  rw [this, hβγ]
  rfl

/-! ## Sufficiency (reverse direction) -/

/-- **Lemma 3 (a positive integer multiple of `θ` is a winning angle).**
If `θ > 0`, `IsTriangle s`, `1 ≤ k`, and `(k:ℝ)*θ ∈ s`, then `MulanWins θ s`. -/
theorem win_of_multiple (θ : ℝ) (hθ0 : 0 < θ) :
    ∀ k : ℕ, 1 ≤ k → ∀ s : Multiset ℝ, IsTriangle s → (k : ℝ) * θ ∈ s → MulanWins θ s := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro s hs hmem
    apply MulanWins.win
    simpa [HasAngle] using hmem
  | succ k hk ih =>
    intro s hs hmem
    -- apex a = (k+1)*θ
    set a : ℝ := ((k + 1 : ℕ) : ℝ) * θ with ha_def
    obtain ⟨β, γ, hs_eq⟩ := triangle_with_apex hs hmem
    -- extract validity facts
    have hs' := hs
    obtain ⟨hcard, hpos, hsum⟩ := hs
    rw [hs_eq] at hpos hsum
    rw [sum_triple] at hsum
    have hβ : 0 < β := hpos β (by rw [mem_triple]; tauto)
    have hγ : 0 < γ := hpos γ (by rw [mem_triple]; tauto)
    -- cut parameter x = γ + θ
    have hkθ : 0 < (k : ℝ) * θ := by positivity
    have hcast : a = (k : ℝ) * θ + θ := by
      rw [ha_def]; push_cast; ring
    -- admissibility
    have hγx : γ < γ + θ := by linarith
    have hxβ : γ + θ < 180 - β := by
      -- a + β + γ = 180 ⇒ 180 - β = γ + a = γ + kθ + θ
      have : (180 : ℝ) - β = γ + (k : ℝ) * θ + θ := by
        rw [hcast] at hsum; linarith
      rw [this]; linarith
    have hcut : IsCut s ({β, γ + θ, 180 - β - (γ + θ)}) ({γ, 180 - (γ + θ), (γ + θ) - γ}) := by
      refine ⟨a, β, γ, γ + θ, hs_eq, hγx, hxβ, rfl, rfl⟩
    apply MulanWins.move hcut
    · -- L wins: contains kθ.  180 - β - (γ+θ) = kθ
      obtain ⟨hLtri, _⟩ := cut_preserves hs' hcut
      apply ih _ hLtri
      have hval : (180 : ℝ) - β - (γ + θ) = (k : ℝ) * θ := by
        rw [hcast] at hsum; linarith
      rw [mem_triple]
      right; right; rw [hval]
    · -- R wins: contains θ = (γ+θ)-γ
      obtain ⟨_, hRtri⟩ := cut_preserves hs' hcut
      apply MulanWins.win
      show θ ∈ ({γ, 180 - (γ + θ), (γ + θ) - γ} : Multiset ℝ)
      rw [mem_triple]
      right; right; ring

/-- **Lemma 4 (integer interval lemma for three positive summands).**
If `r₁,r₂,r₃ > 0` sum to an integer `n ≥ 2`, and none of them is an integer, then
after reordering as `(α', β', γ')` there is `m : ℕ` with `1 ≤ m ≤ n-1` and
`γ' < m < γ' + α'`.

Stated concretely: there is a permutation of the three reals (given as an explicit
choice among the 3 assignments) — here we return the reordered triple and `m`. -/
theorem interval_lemma (r₁ r₂ r₃ : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (h1 : 0 < r₁) (h2 : 0 < r₂) (h3 : 0 < r₃)
    (hsum : r₁ + r₂ + r₃ = (n : ℝ))
    (hni : ∀ z : ℤ, r₁ ≠ (z : ℝ) ∧ r₂ ≠ (z : ℝ) ∧ r₃ ≠ (z : ℝ)) :
    ∃ (α' β' γ' : ℝ) (m : ℕ),
      ({α', β', γ'} : Multiset ℝ) = {r₁, r₂, r₃} ∧
      1 ≤ m ∧ m ≤ n - 1 ∧ (γ' : ℝ) < m ∧ (m : ℝ) < γ' + α' ∧
      α' + β' + γ' = (n : ℝ) := by
  -- core1: assignment where α' = a > 1, γ' = c, β' = b. Uses m = ⌊c⌋ + 1.
  have core1 : ∀ a b c : ℝ, ({a, b, c} : Multiset ℝ) = {r₁, r₂, r₃} →
      1 < a → 0 < b → 0 < c → a + b + c = (n : ℝ) →
      ∃ (α' β' γ' : ℝ) (m : ℕ),
        ({α', β', γ'} : Multiset ℝ) = {r₁, r₂, r₃} ∧
        1 ≤ m ∧ m ≤ n - 1 ∧ (γ' : ℝ) < m ∧ (m : ℝ) < γ' + α' ∧
        α' + β' + γ' = (n : ℝ) := by
    intro a b c hperm ha hb hc hsum'
    have h0 : 0 ≤ ⌊c⌋ := Int.floor_nonneg.mpr (le_of_lt hc)
    have htn : ((⌊c⌋ + 1).toNat : ℝ) = (⌊c⌋ : ℝ) + 1 := by
      have : ((⌊c⌋ + 1).toNat : ℤ) = ⌊c⌋ + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have hlt1 : (c : ℝ) < (⌊c⌋ : ℝ) + 1 := Int.lt_floor_add_one c
    have hle : (⌊c⌋ : ℝ) ≤ c := Int.floor_le c
    refine ⟨a, b, c, (⌊c⌋ + 1).toNat, hperm, ?_, ?_, ?_, ?_, hsum'⟩
    · omega
    · -- m ≤ n - 1 : show (m:ℝ) < n then m < n
      have hmlt : ((⌊c⌋ + 1).toNat : ℝ) < (n : ℝ) := by
        rw [htn]; linarith
      have : (⌊c⌋ + 1).toNat < n := by exact_mod_cast hmlt
      omega
    · rw [htn]; linarith
    · rw [htn]; linarith
  -- core2: assignment where α'=a, γ'=c with a+c>1 and c<1, β'=b. Uses m=1.
  have core2 : ∀ a b c : ℝ, ({a, b, c} : Multiset ℝ) = {r₁, r₂, r₃} →
      c < 1 → 1 < a + c → a + b + c = (n : ℝ) →
      ∃ (α' β' γ' : ℝ) (m : ℕ),
        ({α', β', γ'} : Multiset ℝ) = {r₁, r₂, r₃} ∧
        1 ≤ m ∧ m ≤ n - 1 ∧ (γ' : ℝ) < m ∧ (m : ℝ) < γ' + α' ∧
        α' + β' + γ' = (n : ℝ) := by
    intro a b c hperm hc1 hac hsum'
    refine ⟨a, b, c, 1, hperm, le_refl 1, ?_, ?_, ?_, hsum'⟩
    · omega
    · push_cast; linarith
    · push_cast; linarith
  -- permutation equalities
  have p123 : ({r₁, r₂, r₃} : Multiset ℝ) = {r₁, r₂, r₃} := rfl
  have p213 : ({r₂, r₁, r₃} : Multiset ℝ) = {r₁, r₂, r₃} := by
    change (↑[r₂, r₁, r₃] : Multiset ℝ) = ↑[r₁, r₂, r₃]
    rw [Multiset.coe_eq_coe]; exact List.Perm.swap r₁ r₂ _
  have p321 : ({r₃, r₂, r₁} : Multiset ℝ) = {r₁, r₂, r₃} := by
    change (↑[r₃, r₂, r₁] : Multiset ℝ) = ↑[r₁, r₂, r₃]
    rw [Multiset.coe_eq_coe]
    exact List.reverse_perm [r₁, r₂, r₃]
  have p132 : ({r₁, r₃, r₂} : Multiset ℝ) = {r₁, r₂, r₃} := by
    change (↑[r₁, r₃, r₂] : Multiset ℝ) = ↑[r₁, r₂, r₃]
    rw [Multiset.coe_eq_coe]; exact (List.Perm.swap r₂ r₃ _).cons r₁

  -- Case analysis: some rᵢ > 1, or all ≤ 1
  by_cases hc1 : 1 < r₁
  · exact core1 r₁ r₂ r₃ p123 hc1 h2 h3 hsum
  · by_cases hc2 : 1 < r₂
    · -- α'=r₂, β'=r₁ (or r₃), γ'=r₃; use perm {r₂,r₁,r₃}
      exact core1 r₂ r₁ r₃ p213 hc2 h1 h3 (by linarith)
    · by_cases hc3 : 1 < r₃
      · exact core1 r₃ r₂ r₁ p321 hc3 h2 h1 (by linarith)
      · -- all ≤ 1; none is integer so all < 1 (and > 0)
        push_neg at hc1 hc2 hc3
        -- since none is an integer and 0 < rᵢ ≤ 1, rᵢ ≠ 1, so rᵢ < 1
        have hne1 : r₁ ≠ 1 := by have := (hni 1).1; simpa using this
        have hne2 : r₂ ≠ 1 := by have := (hni 1).2.1; simpa using this
        have hne3 : r₃ ≠ 1 := by have := (hni 1).2.2; simpa using this
        have hr1 : r₁ < 1 := lt_of_le_of_ne hc1 hne1
        have hr2 : r₂ < 1 := lt_of_le_of_ne hc2 hne2
        have hr3 : r₃ < 1 := lt_of_le_of_ne hc3 hne3
        -- sum = n ≥ 2, so some pair sums > 1
        have hnge : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        -- pick pair with sum > 1: r₁+r₂ or r₁+r₃ or r₂+r₃
        by_cases hp : 1 < r₁ + r₂
        · exact core2 r₁ r₃ r₂ p132 hr2 (by linarith) (by linarith)
        · by_cases hq : 1 < r₁ + r₃
          · exact core2 r₁ r₂ r₃ p123 hr3 (by linarith) hsum
          · -- then r₂ + r₃ > 1 (else all pairs ≤1 ⇒ 2n ≤ 3)
            push_neg at hp hq
            have hpr : 1 < r₂ + r₃ := by nlinarith [hsum, hnge]
            exact core2 r₂ r₁ r₃ p213 hr3 (by linarith) (by linarith)

/-- **Lemma 5 (every valid triangle is winning when `180 = n·θ`).**
If `θ > 0`, `n ≥ 2`, and `180 = (n:ℝ)*θ`, then every valid triangle is winning. -/
theorem all_win_of_divides (θ : ℝ) (hθ0 : 0 < θ) (n : ℕ) (hn : 2 ≤ n)
    (hdvd : (180 : ℝ) = (n : ℝ) * θ) :
    ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s := by
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  intro s hs
  obtain ⟨hcard, hpos, hsum⟩ := hs
  have hs' : IsTriangle s := ⟨hcard, hpos, hsum⟩
  obtain ⟨a, b, c, hs_eq⟩ := Multiset.card_eq_three.mp hcard
  have ha : 0 < a := hpos a (by rw [hs_eq, mem_triple]; tauto)
  have hb : 0 < b := hpos b (by rw [hs_eq, mem_triple]; tauto)
  have hc : 0 < c := hpos c (by rw [hs_eq, mem_triple]; tauto)
  have habc : a + b + c = 180 := by rw [hs_eq, sum_triple] at hsum; exact hsum
  -- Case A: some angle is an integer multiple of θ
  by_cases hcaseA : ∃ v ∈ s, ∃ z : ℤ, v = (z : ℝ) * θ
  · obtain ⟨v, hvmem, z, hveq⟩ := hcaseA
    have hvpos : 0 < v := hpos v hvmem
    have hzpos : 0 < z := by
      have : 0 < (z : ℝ) * θ := by rw [← hveq]; exact hvpos
      have hzr : 0 < (z : ℝ) := by
        by_contra hle; push_neg at hle; nlinarith [this, hθ0, hle]
      exact_mod_cast hzr
    have hk : (z.toNat : ℝ) * θ ∈ s := by
      have : (z.toNat : ℝ) = (z : ℝ) := by
        have := Int.toNat_of_nonneg (le_of_lt hzpos); exact_mod_cast this
      rw [this, ← hveq]; exact hvmem
    exact win_of_multiple θ hθ0 z.toNat (by omega) s hs' hk
  · -- Case B: no angle is a multiple of θ
    push_neg at hcaseA
    -- normalize
    set ra := a / θ with hra
    set rb := b / θ with hrb
    set rc := c / θ with hrc
    have hra_pos : 0 < ra := by rw [hra]; positivity
    have hrb_pos : 0 < rb := by rw [hrb]; positivity
    have hrc_pos : 0 < rc := by rw [hrc]; positivity
    -- sum = n
    have hn0 : (n : ℝ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hsum_r : ra + rb + rc = (n : ℝ) := by
      rw [hra, hrb, hrc]
      field_simp
      -- (a + b + c) = n * θ  and a+b+c = 180 = n*θ
      rw [habc]; linarith [hdvd]
    -- none is an integer
    have hni : ∀ z : ℤ, ra ≠ (z : ℝ) ∧ rb ≠ (z : ℝ) ∧ rc ≠ (z : ℝ) := by
      intro z
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        exact hcaseA a (by rw [hs_eq, mem_triple]; tauto) z (by rw [hra] at heq; field_simp at heq; linarith [heq])
      · intro heq
        exact hcaseA b (by rw [hs_eq, mem_triple]; tauto) z (by rw [hrb] at heq; field_simp at heq; linarith [heq])
      · intro heq
        exact hcaseA c (by rw [hs_eq, mem_triple]; tauto) z (by rw [hrc] at heq; field_simp at heq; linarith [heq])
    obtain ⟨α', β', γ', m, hperm, hm1, hmn, hγm, hmγα, hsabc⟩ :=
      interval_lemma ra rb rc n hn hra_pos hrb_pos hrc_pos hsum_r hni
    -- actual angles
    set α := α' * θ with hα
    set β := β' * θ with hβ
    set γ := γ' * θ with hγ
    -- s = {α, β, γ}
    have hs_eq2 : s = {α, β, γ} := by
      rw [hs_eq]
      -- {a,b,c} = map (·*θ) {ra,rb,rc}, and {α,β,γ} = map (·*θ) {α',β',γ'}
      have hmapL : ({a, b, c} : Multiset ℝ) = Multiset.map (· * θ) {ra, rb, rc} := by
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
        rw [hra, hrb, hrc]
        congr 1
        · field_simp
        congr 1
        · field_simp
        congr 1
        · field_simp
      have hmapR : ({α, β, γ} : Multiset ℝ) = Multiset.map (· * θ) {α', β', γ'} := by
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
        rw [hα, hβ, hγ]
      rw [hmapL, hmapR, hperm]
    -- sum α+β+γ = 180
    have hsumαβγ : α + β + γ = 180 := by
      rw [hα, hβ, hγ]
      have : (α' + β' + γ') * θ = (n : ℝ) * θ := by rw [hsabc]
      rw [hdvd]; nlinarith [this]
    -- cut parameter x = m*θ
    have hγx : γ < (m : ℝ) * θ := by rw [hγ]; nlinarith [hγm, hθ0]
    have hxβ : (m : ℝ) * θ < 180 - β := by
      -- m < γ'+α' ⇒ mθ < (γ'+α')θ = γ+α = 180-β
      rw [hβ]
      have h1 : (m : ℝ) * θ < (γ' + α') * θ := by nlinarith [hmγα, hθ0]
      have h2 : (γ' + α') * θ = 180 - β' * θ := by
        have : γ + α = 180 - β := by rw [hα, hβ, hγ] at *; linarith [hsumαβγ]
        rw [hγ, hα] at this; nlinarith [this]
      linarith [h1, h2]
    have hcut : IsCut s {β, (m : ℝ) * θ, 180 - β - (m : ℝ) * θ}
        {γ, 180 - (m : ℝ) * θ, (m : ℝ) * θ - γ} :=
      ⟨α, β, γ, (m : ℝ) * θ, hs_eq2, hγx, hxβ, rfl, rfl⟩
    apply MulanWins.move hcut
    · -- L wins: contains mθ = (m:ℝ)*θ, m ≥ 1
      obtain ⟨hLtri, _⟩ := cut_preserves hs' hcut
      apply win_of_multiple θ hθ0 m hm1 _ hLtri
      rw [mem_triple]; right; left; rfl
    · -- R wins: contains 180 - mθ = (n-m)θ, n-m ≥ 1
      obtain ⟨_, hRtri⟩ := cut_preserves hs' hcut
      apply win_of_multiple θ hθ0 (n - m) (by omega) _ hRtri
      rw [mem_triple]; right; left
      -- 180 - mθ = (n-m)*θ
      have hnm : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
        have : m ≤ n := by omega
        push_cast [Nat.cast_sub this]; ring
      rw [hnm]
      rw [hdvd]; ring

/-! ## Necessity (forward direction) -/

/-- A triangle is *safe* for `θ` when none of its angles is an integer multiple
of `θ`. -/
def Safe (θ : ℝ) (s : Multiset ℝ) : Prop :=
  ∀ a ∈ s, ∀ z : ℤ, a ≠ (z : ℝ) * θ

/-- **Lemma 6 (a cut of a safe triangle has a safe child).**
Assume `(*)`: `180` is not an integer multiple of `θ`. If `s` is a valid safe
triangle and `IsCut s L R`, then `L` is safe or `R` is safe. -/
theorem safe_child (θ : ℝ) (hθ0 : 0 < θ)
    (hstar : ∀ z : ℤ, (180 : ℝ) ≠ (z : ℝ) * θ)
    {s L R : Multiset ℝ} (hs : IsTriangle s) (hsafe : Safe θ s)
    (hcut : IsCut s L R) :
    Safe θ L ∨ Safe θ R := by
  obtain ⟨α, β, γ, x, hs_eq, hγx, hxβ, hL, hR⟩ := hcut
  obtain ⟨hcard, hpos, hsum⟩ := hs
  have hsum' : α + β + γ = 180 := by
    rw [hs_eq, sum_triple] at hsum; exact hsum
  -- parent angles are not multiples
  have hαsafe : ∀ z : ℤ, α ≠ (z : ℝ) * θ := hsafe α (by rw [hs_eq, mem_triple]; tauto)
  have hβsafe : ∀ z : ℤ, β ≠ (z : ℝ) * θ := hsafe β (by rw [hs_eq, mem_triple]; tauto)
  have hγsafe : ∀ z : ℤ, γ ≠ (z : ℝ) * θ := hsafe γ (by rw [hs_eq, mem_triple]; tauto)
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnL, hnR⟩ := hcon
  -- unfold not-safe to find offending elements
  simp only [Safe, not_forall] at hnL hnR
  obtain ⟨aL, haLmem, zL, haLeq⟩ := hnL
  obtain ⟨aR, haRmem, zR, haReq⟩ := hnR
  push_neg at haLeq haReq
  -- aL is x or 180-β-x (β is safe)
  rw [hL, mem_triple] at haLmem
  rw [hR, mem_triple] at haRmem
  rcases haLmem with h | h | h
  · exact hβsafe zL (h ▸ haLeq)
  all_goals rcases haRmem with h' | h' | h'
  -- Case aL = x
  · exact hγsafe zR (h' ▸ haReq)   -- aR = γ
  · -- aL = x = zL θ, aR = 180 - x = zR θ ⇒ 180 = (zL+zR)θ
    rw [h] at haLeq; rw [h'] at haReq
    apply hstar (zL + zR)
    push_cast; linarith [haLeq, haReq]
  · -- aL = x = zL θ, aR = x - γ = zR θ ⇒ γ = (zL - zR)θ
    rw [h] at haLeq; rw [h'] at haReq
    apply hγsafe (zL - zR)
    push_cast; linarith [haLeq, haReq]
  -- Case aL = 180 - β - x
  · exact hγsafe zR (h' ▸ haReq)   -- aR = γ
  · -- aL = 180-β-x = zL θ, aR = 180-x = zR θ ⇒ β = (zR - zL)θ
    rw [h] at haLeq; rw [h'] at haReq
    apply hβsafe (zR - zL)
    push_cast; linarith [haLeq, haReq]
  · -- aL = 180-β-x = zL θ, aR = x - γ = zR θ ⇒ 180-β-γ = (zL+zR)θ = α
    rw [h] at haLeq; rw [h'] at haReq
    apply hαsafe (zL + zR)
    push_cast; linarith [haLeq, haReq, hsum']

/-- **Lemma 7 (safe valid triangles are not winning).**
Under `(*)`, a valid safe triangle is never in `MulanWins`. -/
theorem safe_not_win (θ : ℝ) (hθ0 : 0 < θ)
    (hstar : ∀ z : ℤ, (180 : ℝ) ≠ (z : ℝ) * θ)
    {s : Multiset ℝ} (hs : IsTriangle s) (hsafe : Safe θ s) :
    ¬ MulanWins θ s := by
  -- Generalized claim: for any t with MulanWins, if t is a valid safe triangle, False.
  have key : ∀ t : Multiset ℝ, MulanWins θ t → IsTriangle t → Safe θ t → False := by
    intro t hwin
    induction hwin with
    | @win s h =>
      intro _ hsafe
      exact absurd (by push_cast; ring : θ = ((1 : ℤ) : ℝ) * θ) (hsafe θ h 1)
    | @move s L R hcut hL hR ihL ihR =>
      intro hs hsafe
      obtain ⟨hLtri, hRtri⟩ := cut_preserves hs hcut
      rcases safe_child θ hθ0 hstar hs hsafe hcut with hLsafe | hRsafe
      · exact ihL hLtri hLsafe
      · exact ihR hRtri hRsafe
  intro hwin
  exact key s hwin hs hsafe

/-- **Lemma 8 (equilateral counterexample).** Under `(*)`, the equilateral triangle
`{60,60,60}` is valid, safe, and hence not winning; so `MulanCanGuarantee θ` fails. -/
theorem equilateral_counterexample (θ : ℝ) (hθ0 : 0 < θ)
    (hstar : ∀ z : ℤ, (180 : ℝ) ≠ (z : ℝ) * θ) :
    ¬ MulanCanGuarantee θ := by
  intro hguar
  set e : Multiset ℝ := {60, 60, 60} with he
  have hetri : IsTriangle e := by
    refine ⟨?_, ?_, ?_⟩
    · rw [he]; exact card_triple _ _ _
    · intro y hy; rw [he, mem_triple] at hy; rcases hy with h | h | h <;> (rw [h]; norm_num)
    · rw [he, sum_triple]; norm_num
  have hesafe : Safe θ e := by
    intro a ha z heq
    rw [he, mem_triple] at ha
    have h60 : a = 60 := by rcases ha with h | h | h <;> exact h
    rw [h60] at heq
    -- 60 = z*θ ⇒ 180 = (3z)*θ
    apply hstar (3 * z)
    push_cast; linarith [heq]
  exact safe_not_win θ hθ0 hstar hetri hesafe (hguar e hetri)

/-! ## Assembling the main theorem -/

/-- **Main theorem.** For `0 < θ < 180`, Mulan can guarantee her victory in finitely
many steps, no matter how Shan-Yu plays, if and only if `θ = 180 / n` for some
integer `n ≥ 2`. -/
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  constructor
  · -- Forward (necessity): MulanCanGuarantee θ → ∃ n ≥ 2, θ = 180/n.
    intro hguar
    -- Step A: `180` IS an integer multiple of `θ`.
    -- If not (i.e. `(*)` holds), `equilateral_counterexample` contradicts `hguar`.
    -- So obtain `z : ℤ` with `180 = (z:ℝ)*θ`.
    have hmult : ∃ z : ℤ, (180 : ℝ) = (z : ℝ) * θ := by
      -- by_contra: push_neg gives `∀ z, 180 ≠ (z:ℝ)*θ = (*)`;
      -- then `equilateral_counterexample θ hθ0 (*)` contradicts `hguar`.
      by_contra h; push_neg at h; exact equilateral_counterexample θ hθ0 h hguar
    obtain ⟨z, hz⟩ := hmult
    -- Step B: `z > 0` (since `180 = z*θ`, `θ>0` ⇒ `z*θ>0` ⇒ `z>0`), so `z = (n:ℕ)`
    -- with `n ≥ 1`; `n ≠ 1` since `θ < 180` (n=1 ⇒ θ=180); hence `n ≥ 2`.
    -- Then `θ = 180/n` from `180 = n*θ`, `n ≠ 0`.
    have hzpos : 0 < z := by
      have hzθ : 0 < (z : ℝ) * θ := by rw [← hz]; norm_num
      have hzr : 0 < (z : ℝ) := by
        by_contra hle
        push_neg at hle
        nlinarith [hzθ, hθ0, hle]
      exact_mod_cast hzr
    have hz2 : 2 ≤ z := by
      by_contra hlt
      push_neg at hlt
      interval_cases z
      · -- z = 1: 180 = θ, contradiction
        simp at hz; linarith
    have htoNat : (z.toNat : ℝ) = (z : ℝ) := by
      have := Int.toNat_of_nonneg (le_of_lt hzpos)
      exact_mod_cast this
    refine ⟨z.toNat, ?_, ?_⟩
    · -- 2 ≤ z.toNat
      omega
    · -- θ = 180 / z.toNat
      rw [htoNat]
      have hzne : (z : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hzpos)
      field_simp
      linarith [hz]
  · -- Reverse (sufficiency): (∃ n ≥ 2, θ = 180/n) → MulanCanGuarantee θ.
    rintro ⟨n, hn, hθ⟩
    -- From `θ = 180/n` and `n ≥ 2` (so `(n:ℝ) ≠ 0`), get `180 = (n:ℝ)*θ`.
    -- Then `all_win_of_divides θ hθ0 n hn hdvd` gives `MulanCanGuarantee θ`.
    have hdvd : (180 : ℝ) = (n : ℝ) * θ := by
      have hn0 : (n : ℝ) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      rw [hθ]; field_simp
    exact all_win_of_divides θ hθ0 n hn hdvd

end TriangleGame
