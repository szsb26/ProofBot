import Mathlib

/-- The subtype of positive real numbers, representing `\mathbb{R}_{>0}`. -/
abbrev PositiveReal : Type := {x : ℝ // 0 < x}

/-- The two-sided inequality defining admissible functions on positive real numbers. -/
def IsAdmissible (f : PositiveReal → PositiveReal) : Prop :=
  ∀ x y : PositiveReal,
    Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ≥
        ((f x : ℝ) + (y : ℝ)) / 2 ∧
      ((f x : ℝ) + (y : ℝ)) / 2 ≥
        Real.sqrt ((x : ℝ) * (f y : ℝ))

/-- Squaring the two defining inequalities gives the polynomial bounds used in
all rigidity arguments. -/
lemma admissible_quadratic_bounds (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    (∀ x y : PositiveReal,
        4 * (x : ℝ) * (f y : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) ^ 2) ∧
      (∀ x y : PositiveReal,
        ((f x : ℝ) + (y : ℝ)) ^ 2 ≤ 2 * (x : ℝ) ^ 2 + 2 * (f y : ℝ) ^ 2) := by
  constructor
  · intro x y
    obtain ⟨hR, hL⟩ := hf x y
    have hx : (0 : ℝ) < (x : ℝ) := x.2
    have hy : (0 : ℝ) < (y : ℝ) := y.2
    have hfx : (0 : ℝ) < (f x : ℝ) := (f x).2
    have hfy : (0 : ℝ) < (f y : ℝ) := (f y).2
    have hb : (0 : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) / 2 := by positivity
    -- from hL: sqrt (x * f y) ≤ (f x + y)/2
    have hL' : Real.sqrt ((x : ℝ) * (f y : ℝ)) ≤ ((f x : ℝ) + (y : ℝ)) / 2 := hL
    have hsq : (x : ℝ) * (f y : ℝ) ≤ (((f x : ℝ) + (y : ℝ)) / 2) ^ 2 := by
      nlinarith [Real.sq_sqrt (le_of_lt (by positivity : (0:ℝ) < (x:ℝ) * (f y:ℝ))),
        Real.sqrt_nonneg ((x:ℝ)*(f y:ℝ)), hL', hb]
    nlinarith [hsq]
  · intro x y
    obtain ⟨hR, hL⟩ := hf x y
    have hx : (0 : ℝ) < (x : ℝ) := x.2
    have hy : (0 : ℝ) < (y : ℝ) := y.2
    have hfx : (0 : ℝ) < (f x : ℝ) := (f x).2
    have hfy : (0 : ℝ) < (f y : ℝ) := (f y).2
    have hb : (0 : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) / 2 := by positivity
    have hA : (0 : ℝ) ≤ (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) := by positivity
    have hR' : ((f x : ℝ) + (y : ℝ)) / 2 ≤ Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) := hR
    have := (Real.le_sqrt hb hA).mp hR'
    nlinarith [this]

/-- At points in the image of `f`, the upper and lower squared bounds are both
sharp enough to force one exact step of an arithmetic progression. -/
lemma admissible_key_step (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    ∀ y : PositiveReal, (f (f y) : ℝ) = 2 * (f y : ℝ) - (y : ℝ) := by
  intro y
  obtain ⟨hR, hL⟩ := admissible_quadratic_bounds f hf
  have h1 := hR (f y) y
  have h2 := hL (f y) y
  have hpos : (0 : ℝ) < (f (f y) : ℝ) + (y : ℝ) := by
    have := (f (f y)).2; have := y.2; linarith
  have hfy : (0 : ℝ) < (f y : ℝ) := (f y).2
  have heq : ((f (f y) : ℝ) + (y : ℝ) - 2 * (f y : ℝ)) *
      ((f (f y) : ℝ) + (y : ℝ) + 2 * (f y : ℝ)) = 0 := by nlinarith [h1, h2]
  have hne : (f (f y) : ℝ) + (y : ℝ) + 2 * (f y : ℝ) ≠ 0 := by positivity
  have := (mul_eq_zero.mp heq).resolve_right hne
  linarith

/-- The gap `g(x)=f x-x` is nonnegative.  Otherwise the forward orbit of `x`
would be an arithmetic progression with negative common difference, eventually
leaving the positive reals. -/
lemma admissible_gap_nonneg (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    ∀ x : PositiveReal, (x : ℝ) ≤ (f x : ℝ) := by
  intro x
  have hkey := admissible_key_step f hf
  by_contra hlt
  push_neg at hlt
  set a : ℝ := (f x : ℝ) - (x : ℝ) with ha
  have haneg : a < 0 := by simp only [ha]; linarith
  -- gap along the orbit is constant
  have hseq : ∀ n : ℕ, ((f^[n] x : PositiveReal) : ℝ) = (x : ℝ) + n * a := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      -- f^[k] x =: z, need f z - z = a
      -- prove gap invariance: f (f w) - f w = f w - w
      have hgap : ∀ m : ℕ, (f (f^[m] x) : ℝ) - (f^[m] x : ℝ) = a := by
        intro m
        induction m with
        | zero => simp [ha]
        | succ j ihj =>
          rw [Function.iterate_succ_apply']
          have := hkey (f^[j] x)
          rw [this]; ring_nf; linarith [ihj]
      have := hgap k
      rw [show ((f (f^[k] x) : ℝ)) = (f^[k] x : ℝ) + a by linarith [this]]
      rw [ih]; push_cast; ring
  -- choose n large so that x + n*a < 0
  obtain ⟨n, hn⟩ := exists_nat_gt ((x : ℝ) / (-a))
  have hpos : (0 : ℝ) < ((f^[n] x : PositiveReal) : ℝ) := (f^[n] x).2
  rw [hseq n] at hpos
  have : (x : ℝ) + n * a < 0 := by
    have hna : (n : ℝ) * (-a) > (x : ℝ) := by
      have hx : (0 : ℝ) < -a := by linarith
      rw [gt_iff_lt, ← div_lt_iff₀ hx] at *
      · linarith [hn]
    nlinarith [hna]
  linarith

/-- The forward orbit of any point is an arithmetic progression with common
difference `f z - z`. -/
lemma admissible_orbit (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    ∀ (z : PositiveReal) (n : ℕ),
      ((f^[n] z : PositiveReal) : ℝ) = (z : ℝ) + n * ((f z : ℝ) - (z : ℝ)) := by
  intro z
  have hkey := admissible_key_step f hf
  set a : ℝ := (f z : ℝ) - (z : ℝ) with ha
  have hgap : ∀ m : ℕ, (f (f^[m] z) : ℝ) - (f^[m] z : ℝ) = a := by
    intro m
    induction m with
    | zero => simp [ha]
    | succ j ihj =>
      rw [Function.iterate_succ_apply']
      have := hkey (f^[j] z)
      rw [this]; ring_nf; linarith [ihj]
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := hgap k
    rw [show ((f (f^[k] z) : ℝ)) = (f^[k] z : ℝ) + a by linarith [this]]
    rw [ih]; push_cast; ring

/-- Pure algebra step used in the positive-gap comparison. -/
lemma gap_algebra (a b X Y : ℝ) (ha0 : 0 ≤ a) (hbpos : 0 < b)
    (hAk' : (a - (X - Y))^2 + 4*X*(a-b) ≥ 0)
    (hBk' : 2*(b - (X - Y))^2 - (a - (X - Y))^2 + 4*X*(b-a) ≥ 0)
    (hd0 : 0 ≤ X - Y) (hd1 : X - Y < b) :
    4 * X * |a - b| ≤ (a+b)^2 + 2*b^2 := by
  rcases le_total a b with hab | hab
  · rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
    have hda : (a - (X - Y))^2 ≤ (a+b)^2 := by
      have h1 : -(a+b) ≤ a - (X - Y) := by linarith
      have h2 : a - (X - Y) ≤ a + b := by linarith
      nlinarith [h1, h2]
    nlinarith [hAk', hda]
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    have hdb : 2*(b - (X - Y))^2 ≤ 2*b^2 := by
      have h1 : -(b) ≤ b - (X - Y) := by linarith
      have h2 : b - (X - Y) ≤ b := by linarith
      nlinarith [h1, h2]
    nlinarith [hBk', hdb]

/-- If two gaps are strictly positive, then they are equal.

A useful route is to use `admissible_orbit` to get two arithmetic progressions
with fixed positive steps, then apply the defining quadratic inequalities to
nearby large orbit points.  The local estimate around an image point
`z = f y` is
`0 ≤ 4*z*(g x - g y) + ((x-z) + (g x-g y))^2 ≤ 2*(x-z)^2`,
which makes bounded-distance large comparisons force equality of the gaps. -/
lemma admissible_positive_gap_constant (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    ∀ x y : PositiveReal,
      0 < (f x : ℝ) - (x : ℝ) →
      0 < (f y : ℝ) - (y : ℝ) →
      (f x : ℝ) - (x : ℝ) = (f y : ℝ) - (y : ℝ) := by
  intro x0 y0 hax hby
  obtain ⟨hA, hB⟩ := admissible_quadratic_bounds f hf
  have horb := admissible_orbit f hf
  set a : ℝ := (f x0 : ℝ) - (x0 : ℝ) with ha
  set b : ℝ := (f y0 : ℝ) - (y0 : ℝ) with hb
  -- orbit values
  have hXval : ∀ m : ℕ, ((f^[m] x0 : PositiveReal) : ℝ) = (x0 : ℝ) + m * a := by
    intro m; have := horb x0 m; rw [← ha] at this; exact this
  have hYval : ∀ k : ℕ, ((f^[k] y0 : PositiveReal) : ℝ) = (y0 : ℝ) + k * b := by
    intro k; have := horb y0 k; rw [← hb] at this; exact this
  -- f at orbit points
  have hfXval : ∀ m : ℕ, ((f (f^[m] x0) : PositiveReal) : ℝ) = (x0 : ℝ) + (m+1) * a := by
    intro m
    have : ((f^[m+1] x0 : PositiveReal) : ℝ) = (x0 : ℝ) + (m+1) * a := by
      have := hXval (m+1); push_cast at this ⊢; linarith
    rw [Function.iterate_succ_apply'] at this; exact this
  have hfYval : ∀ k : ℕ, ((f (f^[k] y0) : PositiveReal) : ℝ) = (y0 : ℝ) + (k+1) * b := by
    intro k
    have : ((f^[k+1] y0 : PositiveReal) : ℝ) = (y0 : ℝ) + (k+1) * b := by
      have := hYval (k+1); push_cast at this ⊢; linarith
    rw [Function.iterate_succ_apply'] at this; exact this
  have keyA : ∀ m k : ℕ,
      4 * ((x0:ℝ) + m*a) * ((y0:ℝ) + (k+1)*b) ≤
        (((x0:ℝ) + (m+1)*a) + ((y0:ℝ) + k*b))^2 := by
    intro m k
    have := hA (f^[m] x0) (f^[k] y0)
    rw [hXval m, hfXval m, hYval k, hfYval k] at this
    convert this using 2 <;> ring
  have keyB : ∀ m k : ℕ,
      (((x0:ℝ) + (m+1)*a) + ((y0:ℝ) + k*b))^2 ≤
        2 * ((x0:ℝ) + m*a)^2 + 2 * ((y0:ℝ) + (k+1)*b)^2 := by
    intro m k
    have := hB (f^[m] x0) (f^[k] y0)
    rw [hXval m, hfXval m, hYval k, hfYval k] at this
    convert this using 2 <;> ring
  have hbpos : 0 < b := hby
  have hapos : 0 < a := hax
  have hx0 : (0:ℝ) < (x0:ℝ) := x0.2
  have hy0 : (0:ℝ) < (y0:ℝ) := y0.2
  -- For every n with Xv := x0 + n a ≥ y0, we can choose k so that
  -- Yv := y0 + k b satisfies Yv ≤ Xv < Yv + b.
  have hchoose : ∀ n : ℕ, (y0:ℝ) ≤ (x0:ℝ) + n*a →
      ∃ k : ℕ, (y0:ℝ) + k*b ≤ (x0:ℝ) + n*a ∧
               (x0:ℝ) + n*a < (y0:ℝ) + k*b + b := by
    intro n hn
    set t : ℝ := (x0:ℝ) + n*a - (y0:ℝ) with ht
    have htpos : 0 ≤ t := by simp only [ht]; linarith
    refine ⟨⌊t / b⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (by positivity : (0:ℝ) ≤ t / b)
      have h2 : (⌊t/b⌋₊ : ℝ) * b ≤ t := by
        rw [← le_div_iff₀ hbpos]; exact this
      simp only [ht] at h2; linarith
    · have := Nat.lt_floor_add_one (t / b)
      have h2 : t < (⌊t/b⌋₊ + 1 : ℝ) * b := by
        rw [← div_lt_iff₀ hbpos] at *
        · linarith [this]
      simp only [ht] at h2; nlinarith [h2]
  -- The bound C independent of n.
  set C : ℝ := (a+b)^2 + 2*b^2 with hC
  -- key growth contradiction: for every valid n, 4*(x0+n a)*|a-b| ≤ C.
  have hgrow : ∀ n : ℕ, (y0:ℝ) ≤ (x0:ℝ) + n*a →
      4 * ((x0:ℝ) + n*a) * |a - b| ≤ C := by
    intro n hn
    obtain ⟨k, hk1, hk2⟩ := hchoose n hn
    rw [hC]
    apply gap_algebra a b ((x0:ℝ) + n*a) ((y0:ℝ) + k*b) (le_of_lt hapos) hbpos
    · -- hAk'
      have hAk := keyA n k
      nlinarith [hAk]
    · -- hBk'
      have hBk := keyB n k
      nlinarith [hBk]
    · linarith
    · linarith
  -- now pick n large.
  by_contra hne
  have habs : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hne)
  -- need x0 + n a large. n ≥ (something)
  set M : ℝ := max ((y0:ℝ) - (x0:ℝ)) (C / (4*|a-b|) - (x0:ℝ)) with hM
  obtain ⟨n, hn⟩ := exists_nat_gt (M / a)
  have hna : (x0:ℝ) + n*a > (x0:ℝ) + M := by
    have h1 : M < (n:ℝ) * a := by
      rw [div_lt_iff₀ hapos] at hn; linarith [hn]
    linarith [h1]
  have hval1 : (y0:ℝ) ≤ (x0:ℝ) + n*a := by
    have := le_max_left ((y0:ℝ) - (x0:ℝ)) (C / (4*|a-b|) - (x0:ℝ))
    rw [← hM] at this; linarith [hna]
  have hbig : C / (4*|a-b|) < (x0:ℝ) + n*a := by
    have := le_max_right ((y0:ℝ) - (x0:ℝ)) (C / (4*|a-b|) - (x0:ℝ))
    rw [← hM] at this; linarith [hna]
  have hfinal := hgrow n hval1
  have h4 : 0 < 4 * |a - b| := by positivity
  rw [div_lt_iff₀ h4] at hbig
  nlinarith [hfinal, hbig]

/-- A zero gap cannot coexist with a positive gap.  Equivalently, if `f` fixes
one positive real, then it fixes every positive real.

This is the remaining endpoint case after the positive-gap comparison: combine
the sharp local estimate at fixed points with the preceding fact that all
positive gaps (if any) have one common value, and use connectedness/order of
`ℝ` to rule out a jump from gap `0` to that common positive value. -/
lemma admissible_zero_gap_forces_identity (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    ∀ x y : PositiveReal,
      (f x : ℝ) - (x : ℝ) = 0 →
      (f y : ℝ) - (y : ℝ) = 0 := by
  intro x0 y hx0
  obtain ⟨hA, hB⟩ := admissible_quadratic_bounds f hf
  have hge := admissible_gap_nonneg f hf
  by_contra hy
  -- y is a positive-gap point; set c to its gap
  have hypos : 0 < (f y : ℝ) - (y : ℝ) := lt_of_le_of_ne (by linarith [hge y]) (Ne.symm hy)
  set c : ℝ := (f y : ℝ) - (y : ℝ) with hc
  have hcpos : 0 < c := hypos
  -- classification: every point has gap 0 or gap c
  have hgapcl : ∀ q : PositiveReal, (f q : ℝ) - (q : ℝ) = 0 ∨ (f q : ℝ) - (q : ℝ) = c := by
    intro q
    rcases eq_or_lt_of_le (hge q) with h | h
    · left; linarith
    · right
      have : 0 < (f q : ℝ) - (q : ℝ) := by linarith
      exact admissible_positive_gap_constant f hf q y this hypos
  -- distance fact: fixed point p and c-point q satisfy 4 p c ≤ (p - q)^2
  have hdist : ∀ p q : PositiveReal, (f p : ℝ) - (p : ℝ) = 0 → (f q : ℝ) - (q : ℝ) = c →
      4 * (p : ℝ) * c ≤ ((p : ℝ) - (q : ℝ))^2 := by
    intro p q hp hq
    have hAk := hA p q
    have hfp : (f p : ℝ) = (p : ℝ) := by linarith
    have hfq : (f q : ℝ) = (q : ℝ) + c := by linarith
    rw [hfp, hfq] at hAk
    nlinarith [hAk]
  -- define the two open sets in ℝ
  set U : Set ℝ := {t : ℝ | ∃ h : 0 < t, (f ⟨t, h⟩ : ℝ) - (t : ℝ) = 0} with hU
  set V : Set ℝ := {t : ℝ | ∃ h : 0 < t, (f ⟨t, h⟩ : ℝ) - (t : ℝ) = c} with hV
  -- Ioi 0 ⊆ U ∪ V
  have hcover : Set.Ioi (0:ℝ) ⊆ U ∪ V := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    rcases hgapcl ⟨t, ht'⟩ with h | h
    · left; exact ⟨ht', h⟩
    · right; exact ⟨ht', h⟩
  -- U and V disjoint
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro t ⟨h1, hu⟩ ⟨h2, hv⟩
    -- same subtype element; gap can't be both 0 and c>0
    have he : (⟨t, h1⟩ : PositiveReal) = ⟨t, h2⟩ := rfl
    rw [he] at hu
    linarith [hu, hv]
  -- U open
  have hUopen : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro t ⟨ht, hfix⟩
    refine ⟨min ((t:ℝ)/2) (2 * Real.sqrt ((t:ℝ) * c)), by
      apply lt_min <;> positivity, ?_⟩
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hle2 : min ((t:ℝ)/2) (2 * Real.sqrt ((t:ℝ) * c)) ≤ 2 * Real.sqrt ((t:ℝ)*c) :=
      min_le_right _ _
    have hle1 : min ((t:ℝ)/2) (2 * Real.sqrt ((t:ℝ) * c)) ≤ (t:ℝ)/2 := min_le_left _ _
    have hsq : |s - t|^2 < 4 * (t:ℝ) * c := by
      have hrt : Real.sqrt ((t:ℝ)*c) ^ 2 = (t:ℝ)*c := Real.sq_sqrt (by positivity)
      have hlt : |s - t| < 2 * Real.sqrt ((t:ℝ)*c) := lt_of_lt_of_le hs hle2
      nlinarith [hlt, abs_nonneg (s - t), Real.sqrt_nonneg ((t:ℝ)*c), hrt]
    have hspos : 0 < s := by
      have : |s - t| < (t:ℝ)/2 := lt_of_lt_of_le hs hle1
      rw [abs_lt] at this
      linarith [this.1, ht]
    -- s is a fixed or c point
    rcases hgapcl ⟨s, hspos⟩ with h | h
    · exact ⟨hspos, h⟩
    · -- c-point s: distance to fixed t: 4 t c ≤ (t - s)^2, contradiction
      have hd := hdist ⟨t, ht⟩ ⟨s, hspos⟩ hfix h
      simp only at hd
      have : (s - t)^2 = |s - t|^2 := (sq_abs _).symm
      nlinarith [hd, hsq, this]
  -- V open
  have hVopen : IsOpen V := by
    rw [Metric.isOpen_iff]
    rintro t ⟨ht, hcpt⟩
    -- radius rho = min (t/2) (sqrt (t c))
    set rho : ℝ := min ((t:ℝ)/2) (Real.sqrt ((t:ℝ)*c)) with hrho
    have hrhopos : 0 < rho := by
      apply lt_min <;> positivity
    refine ⟨rho, hrhopos, ?_⟩
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hs2 : |s - t| < rho := hs
    have hst2 : (s - t)^2 < rho^2 := by
      have : (s-t)^2 = |s-t|^2 := (sq_abs _).symm
      rw [this]; nlinarith [hs2, abs_nonneg (s-t), hrhopos]
    have hspos : 0 < s := by
      have hle : rho ≤ (t:ℝ)/2 := min_le_left _ _
      nlinarith [hs2, ht, hle]
    rcases hgapcl ⟨s, hspos⟩ with h | h
    · -- fixed point s, but t is c-point: 4 s c ≤ (s - t)^2, contradiction
      have hd := hdist ⟨s, hspos⟩ ⟨t, ht⟩ h hcpt
      simp only at hd
      -- (s - t)^2 < rho^2 ≤ t c ≤ s c ... need 4 s c > (s-t)^2
      have hle2 : rho ≤ Real.sqrt ((t:ℝ)*c) := min_le_right _ _
      have hrt : Real.sqrt ((t:ℝ)*c) ^ 2 = (t:ℝ)*c := Real.sq_sqrt (by positivity)
      have hle1 : rho ≤ (t:ℝ)/2 := min_le_left _ _
      -- s ≥ t/2
      have hsge : (t:ℝ)/2 ≤ s := by nlinarith [hs2, hle1]
      have hrho2 : rho^2 ≤ (t:ℝ)*c := by nlinarith [hle2, hrhopos, hrt, Real.sqrt_nonneg ((t:ℝ)*c)]
      -- 4 s c ≥ 4 (t/2) c = 2 t c > t c ≥ rho^2 > (s-t)^2, but hd says 4 s c ≤ (s-t)^2
      have : ((s:ℝ) - (t:ℝ))^2 = (s - t)^2 := by norm_num
      nlinarith [hd, hst2, hrho2, hsge, hcpos]
    · exact ⟨hspos, h⟩
  -- Ioi 0 meets both U and V
  have hUmeet : (Set.Ioi (0:ℝ) ∩ U).Nonempty := by
    refine ⟨(x0 : ℝ), x0.2, ⟨x0.2, ?_⟩⟩
    have : (⟨(x0:ℝ), x0.2⟩ : PositiveReal) = x0 := by cases x0; rfl
    rw [this]; exact hx0
  have hVmeet : (Set.Ioi (0:ℝ) ∩ V).Nonempty := by
    refine ⟨(y : ℝ), y.2, ⟨y.2, ?_⟩⟩
    have he : (⟨(y:ℝ), y.2⟩ : PositiveReal) = y := by cases y; rfl
    rw [he]
  -- preconnected contradiction
  have hpre := isPreconnected_Ioi (a := (0:ℝ))
  rcases hpre.subset_or_subset hUopen hVopen hdisj hcover with hsub | hsub
  · obtain ⟨t, htv⟩ := hVmeet
    have := hsub htv.1
    exact (hdisj.ne_of_mem this htv.2) rfl
  · obtain ⟨t, htu⟩ := hUmeet
    have := hsub htu.1
    exact (hdisj.ne_of_mem htu.2 this) rfl

/-- The nonnegative gap `f x - x` is in fact independent of `x`. -/
lemma admissible_gap_constant (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    ∀ x y : PositiveReal, (f x : ℝ) - (x : ℝ) = (f y : ℝ) - (y : ℝ) := by
  intro x y
  have hge := admissible_gap_nonneg f hf
  by_cases hx0 : (f x : ℝ) - (x : ℝ) = 0
  · have hy0 := admissible_zero_gap_forces_identity f hf x y hx0
    linarith
  · by_cases hy0 : (f y : ℝ) - (y : ℝ) = 0
    · have hx0' := admissible_zero_gap_forces_identity f hf y x hy0
      linarith
    · have hx_nonneg : 0 ≤ (f x : ℝ) - (x : ℝ) := by linarith [hge x]
      have hy_nonneg : 0 ≤ (f y : ℝ) - (y : ℝ) := by linarith [hge y]
      have hxpos : 0 < (f x : ℝ) - (x : ℝ) := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
      have hypos : 0 < (f y : ℝ) - (y : ℝ) := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
      exact admissible_positive_gap_constant f hf x y hxpos hypos

/-- Every admissible function is an affine translate of the identity by a
nonnegative constant. -/
lemma admissible_has_affine_form (f : PositiveReal → PositiveReal) (hf : IsAdmissible f) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c := by
  let c : ℝ := (f ⟨1, by norm_num⟩ : ℝ) - 1
  have hconst := admissible_gap_constant f hf
  have hc : 0 ≤ c := by
    have hge := admissible_gap_nonneg f hf ⟨1, by norm_num⟩
    dsimp [c]
    linarith
  refine ⟨c, hc, ?_⟩
  intro x
  have hx := hconst x ⟨1, by norm_num⟩
  dsimp [c] at hx ⊢
  linarith

/-- Conversely, every nonnegative translate of the identity satisfies the
RMS-AM-GM chain in the definition. -/
lemma admissible_of_affine (f : PositiveReal → PositiveReal) (c : ℝ) (hc : 0 ≤ c)
    (hform : ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c) :
    IsAdmissible f := by
  intro x y
  have hx : (0 : ℝ) < (x : ℝ) := x.2
  have hy : (0 : ℝ) < (y : ℝ) := y.2
  have hfx : (f x : ℝ) = (x : ℝ) + c := hform x
  have hfy : (f y : ℝ) = (y : ℝ) + c := hform y
  have hb : (0 : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) / 2 := by
    rw [hfx]
    positivity
  have hA : (0 : ℝ) ≤ (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) := by
    positivity
  constructor
  · rw [ge_iff_le, Real.le_sqrt hb hA]
    rw [hfx, hfy]
    nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c)), hx.le, hy.le, hc]
  · rw [ge_iff_le, Real.sqrt_le_iff]
    refine ⟨hb, ?_⟩
    rw [hfx, hfy]
    nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c)), hx.le, hy.le, hc]

theorem main_theorem (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c := by
  constructor
  · intro hf
    exact admissible_has_affine_form f hf
  · rintro ⟨c, hc, hform⟩
    exact admissible_of_affine f c hc hform
