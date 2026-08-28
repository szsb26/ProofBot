import Mathlib
set_option backward.isDefEq.respectTransparency false

open EuclideanGeometry

-- We work in the Euclidean plane `ℝ²` with the standard `L²` (Euclidean) norm.
abbrev Plane := EuclideanSpace ℝ (Fin 2)


/-- A point `P` lies in the open interior of the triangle `X Y Z`: it is a
strictly convex combination `P = α • X + β • Y + γ • Z` with `α, β, γ > 0` and
`α + β + γ = 1`. -/
def InsideTriangle (X Y Z P : Plane) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P = α • X + β • Y + γ • Z

/-- A point `P` lies inside the (proper) angle at vertex `Y` spanned by the rays
`Y X` and `Y Z`: writing `P - Y = s • (X - Y) + t • (Z - Y)`, one has `s > 0`
and `t > 0`. -/
def InsideAngle (X Y Z P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P - Y = s • (X - Y) + t • (Z - Y)

/-- `O` is the circumcentre of triangle `A K L`: it is equidistant from the three
vertices. (For a nondegenerate triangle such a point exists and is unique.) -/
def IsCircumcentre (A K L O : Plane) : Prop :=
  dist O A = dist O K ∧ dist O A = dist O L

lemma inner_self_sub_self_sub (u v : Plane) :
  inner ℝ (u - v) (u - v) = inner ℝ u u - 2 * inner ℝ u v + inner ℝ v v := by
  simp only [inner_sub_left, inner_sub_right]
  have hcomm : inner ℝ v u = inner ℝ u v := real_inner_comm u v
  linarith

lemma circum_eq (A K O : Plane) (hOK : dist O A = dist O K) :
    2 * inner ℝ (O - A) (K - A) = inner ℝ (K - A) (K - A) := by
  have h1 : dist O A ^ 2 = dist O K ^ 2 := by rw [hOK]
  rw [dist_eq_norm, dist_eq_norm, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h1
  have H : (O - K) = (O - A) - (K - A) := by abel
  rw [H] at h1
  have H2 : inner ℝ ((O - A) - (K - A)) ((O - A) - (K - A)) = inner ℝ (O - A) (O - A) - 2 * inner ℝ (O - A) (K - A) + inner ℝ (K - A) (K - A) := inner_self_sub_self_sub (O - A) (K - A)
  rw [H2] at h1
  linarith

lemma hN_M_lem (A B C M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C) :
  N - M = (1/2:ℝ) • (C - B) := by
  have hM_sub : M - A = (1/2:ℝ) • (B - A) := by
    have h1 : M - A = (⅟2:ℝ) • (B - A) := by rw [hM, midpoint_sub_left]
    have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
    rwa [h2] at h1
  have hN_sub : N - A = (1/2:ℝ) • (C - A) := by
    have h1 : N - A = (⅟2:ℝ) • (C - A) := by rw [hN, midpoint_sub_left]
    have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
    rwa [h2] at h1
  have h3 : C - A - (B - A) = C - B := by abel
  calc N - M = (N - A) - (M - A) := by abel
    _ = (1/2:ℝ) • (C - A) - (1/2:ℝ) • (B - A) := by rw [hN_sub, hM_sub]
    _ = (1/2:ℝ) • (C - A - (B - A)) := by rw [← smul_sub]
    _ = (1/2:ℝ) • (C - B) := by rw [h3]

lemma hmid_lem (A B C M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C) :
  midpoint ℝ M N - A = (1/4:ℝ) • (C - A) + (1/4:ℝ) • (B - A) := by
  have hM_sub : M - A = (1/2:ℝ) • (B - A) := by
    have h1 : M - A = (⅟2:ℝ) • (B - A) := by rw [hM, midpoint_sub_left]
    have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
    rwa [h2] at h1
  have hN_sub : N - A = (1/2:ℝ) • (C - A) := by
    have h1 : N - A = (⅟2:ℝ) • (C - A) := by rw [hN, midpoint_sub_left]
    have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
    rwa [h2] at h1
  have h1 : midpoint ℝ M N - A = (1/2:ℝ) • (M - A) + (1/2:ℝ) • (N - A) := by
    have h1' : midpoint ℝ M N - A = (⅟2:ℝ) • (M - A) + (⅟2:ℝ) • (N - A) := by
      have : midpoint ℝ M N - A = midpoint ℝ M N -ᵥ A := rfl
      rw [this, midpoint_vsub]
      rfl
    have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
    rwa [h2] at h1'
  rw [h1, hM_sub, hN_sub]
  rw [smul_smul, smul_smul]
  have h2 : (1/2:ℝ) * (1/2:ℝ) = (1/4:ℝ) := by norm_num
  rw [h2]
  have : (1/4:ℝ) • (B - A) + (1/4:ℝ) • (C - A) = (1/4:ℝ) • (C - A) + (1/4:ℝ) • (B - A) := by abel
  rw [this]


lemma coords_exist (A B C K L : Plane) (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∃ x y z w : ℝ, K - A = x • (B - A) + y • (C - A) ∧ L - A = z • (B - A) + w • (C - A) := by
  have hd : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  have h_aff : AffineIndependent ℝ ![A, B, C] := affineIndependent_iff_not_collinear_set.mpr hABC
  have h_lin : LinearIndependent ℝ ![B - A, C - A] := by
    have h_lin' := affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] 0
    rw [h_lin'] at h_aff
    let e : Fin 2 ≃ {x : Fin 3 // x ≠ 0} :=
      ⟨fun i => if i = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩,
       fun x => if x.val = 1 then 0 else 1,
       by intro x; fin_cases x; rfl; rfl,
       by intro x; rcases x with ⟨x, hx⟩; revert hx; fin_cases x;
          · intro; contradiction
          · intro; rfl
          · intro; rfl⟩
    have h_comp := LinearIndependent.comp h_aff e e.injective
    have h_eq : (fun (i : Fin 2) => ![A, B, C] (e i).val -ᵥ ![A, B, C] 0) = ![B - A, C - A] := by
      ext i; fin_cases i <;> rfl
    have h_eq' : (fun (i : {x : Fin 3 // x ≠ 0}) => ![A, B, C] ↑i -ᵥ ![A, B, C] 0) ∘ (⇑e) = (fun (i : Fin 2) => ![A, B, C] (e i).val -ᵥ ![A, B, C] 0) := rfl
    rw [h_eq', h_eq] at h_comp
    exact h_comp

  let b := basisOfLinearIndependentOfCardEqFinrank h_lin (by
    show Fintype.card (Fin 2) = Module.finrank ℝ Plane
    rw [hd]; exact Fintype.card_fin 2)

  use b.repr (K - A) 0, b.repr (K - A) 1, b.repr (L - A) 0, b.repr (L - A) 1
  have h_sum_K := b.sum_repr (K - A)
  have h_sum_L := b.sum_repr (L - A)

  have hb_eq : ⇑b = ![B - A, C - A] := coe_basisOfLinearIndependentOfCardEqFinrank h_lin _

  have hK2 : ∑ i : Fin 2, b.repr (K - A) i • b i = b.repr (K - A) 0 • b 0 + b.repr (K - A) 1 • b 1 := by
    exact Fin.sum_univ_two (fun i => b.repr (K - A) i • b i)

  have hL2 : ∑ i : Fin 2, b.repr (L - A) i • b i = b.repr (L - A) 0 • b 0 + b.repr (L - A) 1 • b 1 := by
    exact Fin.sum_univ_two (fun i => b.repr (L - A) i • b i)

  rw [hK2] at h_sum_K
  rw [hL2] at h_sum_L

  have hb0 : b 0 = B - A := by
    calc b 0 = (⇑b) 0 := rfl
      _ = ![B - A, C - A] 0 := by rw [hb_eq]
      _ = B - A := rfl
  have hb1 : b 1 = C - A := by
    calc b 1 = (⇑b) 1 := rfl
      _ = ![B - A, C - A] 1 := by rw [hb_eq]
      _ = C - A := rfl

  rw [hb0, hb1] at h_sum_K h_sum_L
  exact ⟨h_sum_K.symm, h_sum_L.symm⟩

lemma coord_bounds (A B C K L M N : Plane) (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (x y z w : ℝ)
    (hK_coord : K - A = x • (B - A) + y • (C - A))
    (hL_coord : L - A = z • (B - A) + w • (C - A))
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L) :
    0 < x ∧ 0 < y ∧ x < 1 ∧ 0 < z ∧ 0 < w ∧ w < 1 ∧
    0 < w * (1 - x) - y * (1 - z) ∧
    0 < x * (1 - w) - z * (1 - y) := by
  have h_aff : AffineIndependent ℝ ![A, B, C] := affineIndependent_iff_not_collinear_set.mpr hABC
  have h_lin : LinearIndependent ℝ ![B - A, C - A] := by
    have h_lin' := affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] 0
    rw [h_lin'] at h_aff
    let e : Fin 2 ≃ {x : Fin 3 // x ≠ 0} :=
      ⟨fun i => if i = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩,
       fun x => if x.val = 1 then 0 else 1,
       by intro x; fin_cases x; rfl; rfl,
       by intro x; rcases x with ⟨x, hx⟩; revert hx; fin_cases x;
          · intro; contradiction
          · intro; rfl
          · intro; rfl⟩
    have h_comp := LinearIndependent.comp h_aff e e.injective
    have h_eq : (fun (i : Fin 2) => ![A, B, C] (e i).val -ᵥ ![A, B, C] 0) = ![B - A, C - A] := by
      ext i; fin_cases i <;> rfl
    have h_eq' : (fun (i : {x : Fin 3 // x ≠ 0}) => ![A, B, C] ↑i -ᵥ ![A, B, C] 0) ∘ (⇑e) = (fun (i : Fin 2) => ![A, B, C] (e i).val -ᵥ ![A, B, C] 0) := rfl
    rw [h_eq', h_eq] at h_comp
    exact h_comp

  have hk_bounds : 0 < x ∧ 0 < y ∧ x < 1 := by
    rcases hK with ⟨α, β, γ, hα, hβ, hγ, hsum, hK_eq⟩
    have hM_sub : M - A = (1/2:ℝ) • (B - A) := by
      have h1 : M - A = (⅟2:ℝ) • (B - A) := by rw [hM, midpoint_sub_left]
      have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
      rwa [h2] at h1
    have hK_sub : K - A = (α + β / 2) • (B - A) + γ • (C - A) := by
      calc K - A = α • B + β • M + γ • C - A := by rw [hK_eq]
        _ = α • B + β • M + γ • C - (α + β + γ) • A := by rw [hsum, one_smul]
        _ = α • B + β • M + γ • C - (α • A + β • A + γ • A) := by rw [add_smul, add_smul]
        _ = (α • B - α • A) + (β • M - β • A) + (γ • C - γ • A) := by module
        _ = α • (B - A) + β • (M - A) + γ • (C - A) := by rw [← smul_sub, ← smul_sub, ← smul_sub]
        _ = α • (B - A) + β • ((1/2:ℝ) • (B - A)) + γ • (C - A) := by rw [hM_sub]
        _ = (α + β / 2) • (B - A) + γ • (C - A) := by module
    have h_eq : (x - (α + β / 2)) • (B - A) + (y - γ) • (C - A) = 0 := by
      calc (x - (α + β / 2)) • (B - A) + (y - γ) • (C - A) = x • (B - A) + y • (C - A) - ((α + β / 2) • (B - A) + γ • (C - A)) := by module
        _ = K - A - (K - A) := by rw [← hK_coord, ← hK_sub]
        _ = 0 := by abel
    have h_sum : ∑ i : Fin 2, (![x - (α + β / 2), y - γ] i) • ![B - A, C - A] i = 0 := by
      have H : ∑ i : Fin 2, (![x - (α + β / 2), y - γ] i) • ![B - A, C - A] i = (x - (α + β / 2)) • (B - A) + (y - γ) • (C - A) := by
        exact Fin.sum_univ_two _
      rw [H, h_eq]
    have h_indep := Fintype.linearIndependent_iff.mp h_lin ![x - (α + β / 2), y - γ] h_sum
    have h_x : x - (α + β / 2) = 0 := h_indep 0
    have h_y : y - γ = 0 := h_indep 1
    exact ⟨by linarith, by linarith, by linarith⟩

  have hl_bounds : 0 < z ∧ 0 < w ∧ w < 1 := by
    rcases hL with ⟨α, β, γ, hα, hβ, hγ, hsum, hL_eq⟩
    have hN_sub : N - A = (1/2:ℝ) • (C - A) := by
      have h1 : N - A = (⅟2:ℝ) • (C - A) := by rw [hN, midpoint_sub_left]
      have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
      rwa [h2] at h1
    have hL_sub : L - A = α • (B - A) + (β / 2 + γ) • (C - A) := by
      calc L - A = α • B + β • N + γ • C - A := by rw [hL_eq]
        _ = α • B + β • N + γ • C - (α + β + γ) • A := by rw [hsum, one_smul]
        _ = α • B + β • N + γ • C - (α • A + β • A + γ • A) := by rw [add_smul, add_smul]
        _ = (α • B - α • A) + (β • N - β • A) + (γ • C - γ • A) := by module
        _ = α • (B - A) + β • (N - A) + γ • (C - A) := by rw [← smul_sub, ← smul_sub, ← smul_sub]
        _ = α • (B - A) + β • ((1/2:ℝ) • (C - A)) + γ • (C - A) := by rw [hN_sub]
        _ = α • (B - A) + (β / 2 + γ) • (C - A) := by module
    have h_eq : (z - α) • (B - A) + (w - (β / 2 + γ)) • (C - A) = 0 := by
      calc (z - α) • (B - A) + (w - (β / 2 + γ)) • (C - A) = z • (B - A) + w • (C - A) - (α • (B - A) + (β / 2 + γ) • (C - A)) := by module
        _ = L - A - (L - A) := by rw [← hL_coord, ← hL_sub]
        _ = 0 := by abel
    have h_sum : ∑ i : Fin 2, (![z - α, w - (β / 2 + γ)] i) • ![B - A, C - A] i = 0 := by
      have H : ∑ i : Fin 2, (![z - α, w - (β / 2 + γ)] i) • ![B - A, C - A] i = (z - α) • (B - A) + (w - (β / 2 + γ)) • (C - A) := by
        exact Fin.sum_univ_two _
      rw [H, h_eq]
    have h_indep := Fintype.linearIndependent_iff.mp h_lin ![z - α, w - (β / 2 + γ)] h_sum
    have h_z : z - α = 0 := h_indep 0
    have h_w : w - (β / 2 + γ) = 0 := h_indep 1
    exact ⟨by linarith, by linarith, by linarith⟩

  have h_k_angle : 0 < w * (1 - x) - y * (1 - z) := by
    rcases hKangle with ⟨s, t, hs, ht, hK_eq⟩
    have hKB : K - B = (x - 1) • (B - A) + y • (C - A) := by
      calc K - B = K - A - (B - A) := by abel
        _ = x • (B - A) + y • (C - A) - (B - A) := by rw [hK_coord]
        _ = (x - 1) • (B - A) + y • (C - A) := by module
    have hLB : L - B = (z - 1) • (B - A) + w • (C - A) := by
      calc L - B = L - A - (B - A) := by abel
        _ = z • (B - A) + w • (C - A) - (B - A) := by rw [hL_coord]
        _ = (z - 1) • (B - A) + w • (C - A) := by module
    have hAB : A - B = (-1:ℝ) • (B - A) := by
      calc A - B = -(B - A) := by abel
        _ = (-1:ℝ) • (B - A) := by module
    have h_sub : (x - 1) • (B - A) + y • (C - A) = (s * (z - 1) - t) • (B - A) + (s * w) • (C - A) := by
      calc (x - 1) • (B - A) + y • (C - A) = K - B := hKB.symm
        _ = s • (L - B) + t • (A - B) := hK_eq
        _ = s • ((z - 1) • (B - A) + w • (C - A)) + t • ((-1:ℝ) • (B - A)) := by rw [hLB, hAB]
        _ = (s * (z - 1) - t) • (B - A) + (s * w) • (C - A) := by module
    have h_eq : (x - 1 - (s * (z - 1) - t)) • (B - A) + (y - s * w) • (C - A) = 0 := by
      calc (x - 1 - (s * (z - 1) - t)) • (B - A) + (y - s * w) • (C - A) = (x - 1) • (B - A) + y • (C - A) - ((s * (z - 1) - t) • (B - A) + (s * w) • (C - A)) := by module
        _ = 0 := by rw [h_sub, sub_self]
    have h_sum : ∑ i : Fin 2, (![x - 1 - (s * (z - 1) - t), y - s * w] i) • ![B - A, C - A] i = 0 := by
      have H : ∑ i : Fin 2, (![x - 1 - (s * (z - 1) - t), y - s * w] i) • ![B - A, C - A] i = (x - 1 - (s * (z - 1) - t)) • (B - A) + (y - s * w) • (C - A) := by
        exact Fin.sum_univ_two _
      rw [H, h_eq]
    have h_indep := Fintype.linearIndependent_iff.mp h_lin ![x - 1 - (s * (z - 1) - t), y - s * w] h_sum
    have h_x_eq : x - 1 - (s * (z - 1) - t) = 0 := h_indep 0
    have h_y_eq : y - s * w = 0 := h_indep 1
    have hw : 0 < w := hl_bounds.2.1
    have H1 : y = s * w := by linarith
    have H2 : 1 - x = s * (1 - z) + t := by linarith
    calc w * (1 - x) - y * (1 - z) = w * (s * (1 - z) + t) - (s * w) * (1 - z) := by rw [H1, H2]
      _ = w * t := by ring
      _ > 0 := mul_pos hw ht

  have h_l_angle : 0 < x * (1 - w) - z * (1 - y) := by
    rcases hLangle with ⟨s, t, hs, ht, hL_eq⟩
    have hLC : L - C = z • (B - A) + (w - 1) • (C - A) := by
      calc L - C = L - A - (C - A) := by abel
        _ = z • (B - A) + w • (C - A) - (C - A) := by rw [hL_coord]
        _ = z • (B - A) + (w - 1) • (C - A) := by module
    have hKC : K - C = x • (B - A) + (y - 1) • (C - A) := by
      calc K - C = K - A - (C - A) := by abel
        _ = x • (B - A) + y • (C - A) - (C - A) := by rw [hK_coord]
        _ = x • (B - A) + (y - 1) • (C - A) := by module
    have hAC : A - C = (-1:ℝ) • (C - A) := by
      calc A - C = -(C - A) := by abel
        _ = (-1:ℝ) • (C - A) := by module
    have h_sub : z • (B - A) + (w - 1) • (C - A) = (t * x) • (B - A) + (-s + t * (y - 1)) • (C - A) := by
      calc z • (B - A) + (w - 1) • (C - A) = L - C := hLC.symm
        _ = s • (A - C) + t • (K - C) := hL_eq
        _ = s • ((-1:ℝ) • (C - A)) + t • (x • (B - A) + (y - 1) • (C - A)) := by rw [hKC, hAC]
        _ = (t * x) • (B - A) + (-s + t * (y - 1)) • (C - A) := by module
    have h_eq : (z - t * x) • (B - A) + (w - 1 - (-s + t * (y - 1))) • (C - A) = 0 := by
      calc (z - t * x) • (B - A) + (w - 1 - (-s + t * (y - 1))) • (C - A) = z • (B - A) + (w - 1) • (C - A) - ((t * x) • (B - A) + (-s + t * (y - 1)) • (C - A)) := by module
        _ = 0 := by rw [h_sub, sub_self]
    have h_sum : ∑ i : Fin 2, (![z - t * x, w - 1 - (-s + t * (y - 1))] i) • ![B - A, C - A] i = 0 := by
      have H : ∑ i : Fin 2, (![z - t * x, w - 1 - (-s + t * (y - 1))] i) • ![B - A, C - A] i = (z - t * x) • (B - A) + (w - 1 - (-s + t * (y - 1))) • (C - A) := by
        exact Fin.sum_univ_two _
      rw [H, h_eq]
    have h_indep := Fintype.linearIndependent_iff.mp h_lin ![z - t * x, w - 1 - (-s + t * (y - 1))] h_sum
    have h_z_eq : z - t * x = 0 := h_indep 0
    have h_w_eq : w - 1 - (-s + t * (y - 1)) = 0 := h_indep 1
    have hx : 0 < x := hk_bounds.1
    have H1 : z = t * x := by linarith
    have H2 : 1 - w = s + t * (1 - y) := by linarith
    calc x * (1 - w) - z * (1 - y) = x * (s + t * (1 - y)) - (t * x) * (1 - y) := by rw [H1, H2]
      _ = x * s := by ring
      _ > 0 := mul_pos hx hs

  exact ⟨hk_bounds.1, hk_bounds.2.1, hk_bounds.2.2, hl_bounds.1, hl_bounds.2.1, hl_bounds.2.2, h_k_angle, h_l_angle⟩

lemma det_nonzero (x y z w E F : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hx1 : x < 1)
    (hz : 0 < z) (hw : 0 < w) (hw1 : w < 1)
    (hE : E = w * (1 - x) - y * (1 - z)) (hE_pos : 0 < E)
    (hF : F = x * (1 - w) - z * (1 - y)) (hF_pos : 0 < F) :
    x * w - y * z ≠ 0 := by
  intro h
  have h1 : E = w - y := by
    calc E = w * (1 - x) - y * (1 - z) := hE
      _ = w - y - (x * w - y * z) := by ring
      _ = w - y := by rw [h]; ring
  have h2 : F = x - z := by
    calc F = x * (1 - w) - z * (1 - y) := hF
      _ = x - z - (x * w - y * z) := by ring
      _ = x - z := by rw [h]; ring
  nlinarith

lemma lin_indep_of_not_collinear (A B C : Plane) (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
  LinearIndependent ℝ ![B - A, C - A] := by
  have h_aff : AffineIndependent ℝ ![A, B, C] := affineIndependent_iff_not_collinear_set.mpr hABC
  have h_lin' := affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] 0
  rw [h_lin'] at h_aff
  let e : Fin 2 ≃ {x : Fin 3 // x ≠ 0} :=
    ⟨fun i => if i = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩,
     fun x => if x.val = 1 then 0 else 1,
     by intro x; fin_cases x; rfl; rfl,
     by intro x; rcases x with ⟨x, hx⟩; revert hx; fin_cases x;
        · intro; contradiction
        · intro; rfl
        · intro; rfl⟩
  have h_comp := LinearIndependent.comp h_aff e e.injective
  have h_eq : (fun (i : Fin 2) => ![A, B, C] (e i).val -ᵥ ![A, B, C] 0) = ![B - A, C - A] := by
    ext i; fin_cases i <;> rfl
  have h_eq' : (fun (i : {x : Fin 3 // x ≠ 0}) => ![A, B, C] ↑i -ᵥ ![A, B, C] 0) ∘ (⇑e) = (fun (i : Fin 2) => ![A, B, C] (e i).val -ᵥ ![A, B, C] 0) := rfl
  rw [h_eq', h_eq] at h_comp
  exact h_comp

lemma CS_strict (v1 v2 : Plane) (h_lin : LinearIndependent ℝ ![v1, v2]) :
  (inner ℝ v1 v2)^2 < inner ℝ v1 v1 * inner ℝ v2 v2 := by
  have hv1 : v1 ≠ 0 := by
    intro h
    have : ![v1, v2] 0 = 0 := h
    exact LinearIndependent.ne_zero 0 h_lin this
  have hv1_norm : 0 < inner ℝ v1 v1 := by
    have : ‖v1‖^2 = inner ℝ v1 v1 := real_inner_self_eq_norm_sq v1 |>.symm
    rw [← this]
    positivity
  let c := inner ℝ v2 v1 / inner ℝ v1 v1
  let w := v2 - c • v1
  have hw_ne : w ≠ 0 := by
    intro h
    have h_eq : v2 = c • v1 := by
      calc v2 = w + c • v1 := eq_add_of_sub_eq rfl
        _ = 0 + c • v1 := by rw [h]
        _ = c • v1 := zero_add _
    have h_sum : ∑ i : Fin 2, ![c, -1] i • ![v1, v2] i = 0 := by
      have : ∑ i : Fin 2, ![c, -1] i • ![v1, v2] i = c • v1 - v2 := by
        calc ∑ i : Fin 2, ![c, -1] i • ![v1, v2] i = c • v1 + (-1:ℝ) • v2 := Fin.sum_univ_two _
          _ = c • v1 - v2 := by module
      rw [this, h_eq, sub_self]
    have h_zero := Fintype.linearIndependent_iff.mp h_lin ![c, -1] h_sum
    have h_one : (-1:ℝ) = 0 := h_zero 1
    linarith
  have hw_norm : 0 < inner ℝ w w := by
    have : ‖w‖^2 = inner ℝ w w := real_inner_self_eq_norm_sq w |>.symm
    rw [← this]
    positivity
  have h_w_w : inner ℝ w w = inner ℝ v2 v2 - (inner ℝ v1 v2)^2 / inner ℝ v1 v1 := by
    dsimp [w, c]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ v2 v1 = inner ℝ v1 v2 := real_inner_comm _ _
    rw [hc]
    have hv1_ne : inner ℝ v1 v1 ≠ 0 := ne_of_gt hv1_norm
    calc inner ℝ v2 v2 - (inner ℝ v1 v2 / inner ℝ v1 v1) * inner ℝ v1 v2 - (inner ℝ v1 v2 / inner ℝ v1 v1) * (inner ℝ v1 v2 - (inner ℝ v1 v2 / inner ℝ v1 v1) * inner ℝ v1 v1)
      _ = inner ℝ v2 v2 - (inner ℝ v1 v2)^2 / inner ℝ v1 v1 - (inner ℝ v1 v2 / inner ℝ v1 v1) * (inner ℝ v1 v2 - inner ℝ v1 v2) := by
        congr 1
        · ring
        · congr 1
          rw [div_mul_cancel₀ _ hv1_ne]
      _ = inner ℝ v2 v2 - (inner ℝ v1 v2)^2 / inner ℝ v1 v1 := by ring
  have H : (inner ℝ v1 v2)^2 / inner ℝ v1 v1 < inner ℝ v2 v2 := by linarith [hw_norm, h_w_w]
  have H2 : (inner ℝ v1 v2)^2 < inner ℝ v1 v1 * inner ℝ v2 v2 := by
    have H3 := (div_lt_iff₀ hv1_norm).mp H
    calc (inner ℝ v1 v2)^2 < inner ℝ v2 v2 * inner ℝ v1 v1 := H3
      _ = inner ℝ v1 v1 * inner ℝ v2 v2 := mul_comm _ _
  exact H2

lemma cos_eq_implies (C1 C2 n1 n2 y z : ℝ) (hy : 0 < y) (hz : 0 < z)
  (hn1 : 0 < n1) (hn2 : 0 < n2)
  (h_cos : C1 / n1 = C2 / n2)
  (h_sq : (C1 * z)^2 = (C2 * y)^2) :
  C1 * z = C2 * y := by
  have hn1_ne : n1 ≠ 0 := by linarith
  have hn2_ne : n2 ≠ 0 := by linarith
  have h_sign2 : (C1 * z) * (C2 * y) = (C1 / n1)^2 * (n1 * z * n2 * y) := by
    calc (C1 * z) * (C2 * y) = (C1 / n1 * n1 * z) * (C2 / n2 * n2 * y) := by
          congr 1
          · have : C1 / n1 * n1 = C1 := div_mul_cancel₀ C1 hn1_ne
            rw [this]
          · have : C2 / n2 * n2 = C2 := div_mul_cancel₀ C2 hn2_ne
            rw [this]
      _ = (C1 / n1) * (C2 / n2) * (n1 * z * n2 * y) := by ring
      _ = (C1 / n1) * (C1 / n1) * (n1 * z * n2 * y) := by rw [h_cos]
      _ = (C1 / n1)^2 * (n1 * z * n2 * y) := by ring
  have h_pos : 0 ≤ (C1 * z) * (C2 * y) := by
    rw [h_sign2]
    have h1 : 0 ≤ (C1 / n1)^2 := sq_nonneg _
    have h2 : 0 ≤ n1 * z * n2 * y := by positivity
    exact mul_nonneg h1 h2
  have h_sq2 : (C1 * z - C2 * y) * (C1 * z + C2 * y) = 0 := by
    calc (C1 * z - C2 * y) * (C1 * z + C2 * y) = (C1 * z)^2 - (C2 * y)^2 := by ring
      _ = 0 := by rw [h_sq, sub_self]
  cases mul_eq_zero.mp h_sq2 with
  | inl h => linarith
  | inr h =>
    have : C1 * z = - (C2 * y) := by linarith
    have h_neg : (C1 * z) * (C2 * y) = - (C2 * y)^2 := by
      calc (C1 * z) * (C2 * y) = - (C2 * y) * (C2 * y) := by rw [this]
        _ = - (C2 * y)^2 := by ring
    have h_sq_nonneg : 0 ≤ (C2 * y)^2 := sq_nonneg _
    have h_zero : (C2 * y)^2 = 0 := by linarith
    have h_zero2 : C2 * y = 0 := sq_eq_zero_iff.mp h_zero
    linarith

lemma norm_pos_lem (A B C K L : Plane) (x y z w : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hy : 0 < y) (hz : 0 < z)
    (hK_coord : K - A = x • (B - A) + y • (C - A))
    (hL_coord : L - A = z • (B - A) + w • (C - A)) :
    0 < ‖K - B‖ ∧ 0 < ‖A - B‖ ∧ 0 < ‖L - C‖ ∧ 0 < ‖A - C‖ := by
  have h_lin : LinearIndependent ℝ ![B - A, C - A] := lin_indep_of_not_collinear A B C hABC
  have hAB_ne : B - A ≠ 0 := by
    intro h
    have : ![B - A, C - A] 0 = 0 := h
    exact LinearIndependent.ne_zero 0 h_lin this
  have hAC_ne : C - A ≠ 0 := by
    intro h
    have : ![B - A, C - A] 1 = 0 := h
    exact LinearIndependent.ne_zero 1 h_lin this

  have hv1 : 0 < ‖A - B‖ := by
    have : A - B = -(B - A) := by abel
    rw [this, norm_neg]
    exact norm_pos_iff.mpr hAB_ne
  have hv2 : 0 < ‖A - C‖ := by
    have : A - C = -(C - A) := by abel
    rw [this, norm_neg]
    exact norm_pos_iff.mpr hAC_ne

  have hu1 : 0 < ‖K - B‖ := by
    have hKB : K - B = (x - 1) • (B - A) + y • (C - A) := by
      calc K - B = K - A - (B - A) := by abel
        _ = x • (B - A) + y • (C - A) - (B - A) := by rw [hK_coord]
        _ = (x - 1) • (B - A) + y • (C - A) := by module
    have h_ne : K - B ≠ 0 := by
      intro h
      rw [hKB] at h
      have h_sum : ∑ i : Fin 2, (![x - 1, y] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![x - 1, y] i) • ![B - A, C - A] i = (x - 1) • (B - A) + y • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![x - 1, y] h_sum
      have h_y : y = 0 := h_indep 1
      linarith
    exact norm_pos_iff.mpr h_ne

  have hu2 : 0 < ‖L - C‖ := by
    have hLC : L - C = z • (B - A) + (w - 1) • (C - A) := by
      calc L - C = L - A - (C - A) := by abel
        _ = z • (B - A) + w • (C - A) - (C - A) := by rw [hL_coord]
        _ = z • (B - A) + (w - 1) • (C - A) := by module
    have h_ne : L - C ≠ 0 := by
      intro h
      rw [hLC] at h
      have h_sum : ∑ i : Fin 2, (![z, w - 1] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![z, w - 1] i) • ![B - A, C - A] i = z • (B - A) + (w - 1) • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![z, w - 1] h_sum
      have h_z : z = 0 := h_indep 0
      linarith
    exact norm_pos_iff.mpr h_ne

  exact ⟨hu1, hv1, hu2, hv2⟩

lemma angle_eq_to_c1 (A B C K L : Plane) (x y z w : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hy : 0 < y) (hz : 0 < z)
    (hK_coord : K - A = x • (B - A) + y • (C - A))
    (hL_coord : L - A = z • (B - A) + w • (C - A))
    (h1 : ∠ K B A = ∠ A C L) :
    inner ℝ (B - A) (B - A) * z * (1 - x) = inner ℝ (C - A) (C - A) * y * (1 - w) := by
  let a := inner ℝ (B - A) (B - A)
  let b := inner ℝ (C - A) (C - A)
  let g := inner ℝ (B - A) (C - A)
  let u1 := K - B
  let v1 := A - B
  let u2 := L - C
  let v2 := A - C
  have hnorm1 : inner ℝ u1 u1 * inner ℝ v1 v1 - (inner ℝ u1 v1)^2 = y^2 * (a * b - g^2) := by
    dsimp [u1, v1, a, b, g]
    have hKB : K - B = (x - 1) • (B - A) + y • (C - A) := by
      calc K - B = K - A - (B - A) := by abel
        _ = x • (B - A) + y • (C - A) - (B - A) := by rw [hK_coord]
        _ = (x - 1) • (B - A) + y • (C - A) := by module
    have hAB : A - B = -(B - A) := by abel
    rw [hKB, hAB]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring
  have hnorm2 : inner ℝ u2 u2 * inner ℝ v2 v2 - (inner ℝ u2 v2)^2 = z^2 * (a * b - g^2) := by
    dsimp [u2, v2, a, b, g]
    have hLC : L - C = z • (B - A) + (w - 1) • (C - A) := by
      calc L - C = L - A - (C - A) := by abel
        _ = z • (B - A) + w • (C - A) - (C - A) := by rw [hL_coord]
        _ = z • (B - A) + (w - 1) • (C - A) := by module
    have hAC : A - C = -(C - A) := by abel
    rw [hLC, hAC]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  have h_norm_pos := norm_pos_lem A B C K L x y z w hABC hy hz hK_coord hL_coord
  rcases h_norm_pos with ⟨hu1_pos, hv1_pos, hu2_pos, hv2_pos⟩

  have h_angle : Real.cos (InnerProductGeometry.angle u1 v1) = Real.cos (InnerProductGeometry.angle v2 u2) := by
    have h_Euclid : EuclideanGeometry.angle K B A = InnerProductGeometry.angle u1 v1 := rfl
    have h_Euclid2 : EuclideanGeometry.angle A C L = InnerProductGeometry.angle v2 u2 := rfl
    rw [← h_Euclid, ← h_Euclid2]
    rw [h1]

  have h_cos1 : Real.cos (InnerProductGeometry.angle u1 v1) = inner ℝ u1 v1 / (‖u1‖ * ‖v1‖) := InnerProductGeometry.cos_angle u1 v1
  have h_cos2 : Real.cos (InnerProductGeometry.angle v2 u2) = inner ℝ v2 u2 / (‖v2‖ * ‖u2‖) := InnerProductGeometry.cos_angle v2 u2
  rw [h_cos1, h_cos2] at h_angle
  have h_symm : inner ℝ v2 u2 = inner ℝ u2 v2 := real_inner_comm _ _
  rw [h_symm] at h_angle

  have h_sq_eq : (inner ℝ u1 v1 * z)^2 = (inner ℝ u2 v2 * y)^2 := by
    have h_div_eq : (inner ℝ u1 v1)^2 / (‖u1‖^2 * ‖v1‖^2) = (inner ℝ u2 v2)^2 / (‖u2‖^2 * ‖v2‖^2) := by
      calc (inner ℝ u1 v1)^2 / (‖u1‖^2 * ‖v1‖^2) = (inner ℝ u1 v1)^2 / (‖u1‖ * ‖v1‖)^2 := by
            congr 1
            exact (mul_pow ‖u1‖ ‖v1‖ 2).symm
        _ = (inner ℝ u1 v1 / (‖u1‖ * ‖v1‖))^2 := by rw [div_pow]
        _ = (inner ℝ u2 v2 / (‖v2‖ * ‖u2‖))^2 := by rw [h_angle]
        _ = (inner ℝ u2 v2)^2 / (‖v2‖ * ‖u2‖)^2 := by rw [div_pow]
        _ = (inner ℝ u2 v2)^2 / (‖v2‖^2 * ‖u2‖^2) := by
            congr 1
            exact mul_pow ‖v2‖ ‖u2‖ 2
        _ = (inner ℝ u2 v2)^2 / (‖u2‖^2 * ‖v2‖^2) := by
            have : ‖v2‖^2 * ‖u2‖^2 = ‖u2‖^2 * ‖v2‖^2 := by ring
            rw [this]
    have h_cross : (inner ℝ u1 v1)^2 * (‖u2‖^2 * ‖v2‖^2) = (inner ℝ u2 v2)^2 * (‖u1‖^2 * ‖v1‖^2) := by
      have hd1 : ‖u1‖^2 * ‖v1‖^2 ≠ 0 := by positivity
      have hd2 : ‖u2‖^2 * ‖v2‖^2 ≠ 0 := by positivity
      exact (div_eq_div_iff hd1 hd2).mp h_div_eq

    have h1_norm : ‖u1‖^2 * ‖v1‖^2 = (inner ℝ u1 v1)^2 + y^2 * (a * b - g^2) := by
      have h_u1 : ‖u1‖^2 = inner ℝ u1 u1 := real_inner_self_eq_norm_sq u1 |>.symm
      have h_v1 : ‖v1‖^2 = inner ℝ v1 v1 := real_inner_self_eq_norm_sq v1 |>.symm
      rw [h_u1, h_v1]
      linarith [hnorm1]
    have h2_norm : ‖u2‖^2 * ‖v2‖^2 = (inner ℝ u2 v2)^2 + z^2 * (a * b - g^2) := by
      have h_u2 : ‖u2‖^2 = inner ℝ u2 u2 := real_inner_self_eq_norm_sq u2 |>.symm
      have h_v2 : ‖v2‖^2 = inner ℝ v2 v2 := real_inner_self_eq_norm_sq v2 |>.symm
      rw [h_u2, h_v2]
      linarith [hnorm2]

    have h3 : (inner ℝ u1 v1)^2 * ((inner ℝ u2 v2)^2 + z^2 * (a * b - g^2)) = (inner ℝ u2 v2)^2 * ((inner ℝ u1 v1)^2 + y^2 * (a * b - g^2)) := by
      rw [h1_norm, h2_norm] at h_cross
      exact h_cross

    have h4 : (inner ℝ u1 v1)^2 * z^2 * (a * b - g^2) = (inner ℝ u2 v2)^2 * y^2 * (a * b - g^2) := by
      linarith [h3]

    have hD_pos : 0 < a * b - g^2 := by
      have h_lin : LinearIndependent ℝ ![B - A, C - A] := lin_indep_of_not_collinear A B C hABC
      have H_CS : (inner ℝ (B - A) (C - A))^2 < inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A) := CS_strict (B - A) (C - A) h_lin
      dsimp [a, b, g]
      linarith [H_CS]

    have hD_ne : a * b - g^2 ≠ 0 := by linarith
    have h5 : (inner ℝ u1 v1)^2 * z^2 = (inner ℝ u2 v2)^2 * y^2 := by
      have h_mul_eq : (a * b - g^2) * ((inner ℝ u1 v1)^2 * z^2) = (a * b - g^2) * ((inner ℝ u2 v2)^2 * y^2) := by linarith [h4]
      exact mul_left_cancel₀ hD_ne h_mul_eq
    calc (inner ℝ u1 v1 * z)^2 = (inner ℝ u1 v1)^2 * z^2 := mul_pow _ _ _
      _ = (inner ℝ u2 v2)^2 * y^2 := h5
      _ = (inner ℝ u2 v2 * y)^2 := (mul_pow _ _ _).symm

  have hn1_pos : 0 < ‖u1‖ * ‖v1‖ := mul_pos hu1_pos hv1_pos
  have hn2_pos : 0 < ‖v2‖ * ‖u2‖ := mul_pos hv2_pos hu2_pos

  have h_eq := cos_eq_implies (inner ℝ u1 v1) (inner ℝ u2 v2) (‖u1‖ * ‖v1‖) (‖v2‖ * ‖u2‖) y z hy hz hn1_pos hn2_pos h_angle h_sq_eq

  dsimp [u1, v1, u2, v2, a, b, g] at h_eq
  have hKB : K - B = (x - 1) • (B - A) + y • (C - A) := by
    calc K - B = K - A - (B - A) := by abel
      _ = x • (B - A) + y • (C - A) - (B - A) := by rw [hK_coord]
      _ = (x - 1) • (B - A) + y • (C - A) := by module
  have hAB : A - B = -(B - A) := by abel
  have hLC : L - C = z • (B - A) + (w - 1) • (C - A) := by
    calc L - C = L - A - (C - A) := by abel
      _ = z • (B - A) + w • (C - A) - (C - A) := by rw [hL_coord]
      _ = z • (B - A) + (w - 1) • (C - A) := by module
  have hAC : A - C = -(C - A) := by abel

  have h_LHS : inner ℝ (K - B) (A - B) = (1 - x) * a - y * g := by
    dsimp [a, g]
    rw [hKB, hAB]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  have h_RHS : inner ℝ (L - C) (A - C) = (1 - w) * b - z * g := by
    dsimp [b, g]
    rw [hLC, hAC]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (B - A) (C - A) = inner ℝ (C - A) (B - A) := real_inner_comm _ _
    rw [hc]
    ring

  rw [h_LHS, h_RHS] at h_eq

  calc inner ℝ (B - A) (B - A) * z * (1 - x) = a * z * (1 - x) := rfl
    _ = (1 - x) * a * z := by ring
    _ = ((1 - x) * a - y * g) * z + y * g * z := by ring
    _ = ((1 - w) * b - z * g) * y + y * g * z := by rw [h_eq]
    _ = (1 - w) * b * y := by ring
    _ = b * y * (1 - w) := by ring
    _ = inner ℝ (C - A) (C - A) * y * (1 - w) := rfl


lemma angle_eq_to_c2 (A B C K L N : Plane) (x y z w : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hz : 0 < z) (hE_pos : 0 < w * (1 - x) - y * (1 - z))
    (hN : N = midpoint ℝ A C)
    (hK_coord : K - A = x • (B - A) + y • (C - A))
    (hL_coord : L - A = z • (B - A) + w • (C - A))
    (h2 : ∠ L B K = ∠ L N C) :
    let a := inner ℝ (B - A) (B - A)
    let b := inner ℝ (C - A) (C - A)
    let g := inner ℝ (B - A) (C - A)
    let E := w * (1 - x) - y * (1 - z)
    2 * z * (a * x * z - a * x - a * z + a + b * w * y + g * w * x - g * w + g * y * z - g * y) = E * (2 * b * w - b + 2 * g * z) := by
  let a := inner ℝ (B - A) (B - A)
  let b := inner ℝ (C - A) (C - A)
  let g := inner ℝ (B - A) (C - A)
  let E := w * (1 - x) - y * (1 - z)
  let u1 := K - B
  let v1 := L - B
  let u2 := C - N
  let v2 := L - N
  have h_lin : LinearIndependent ℝ ![B - A, C - A] := lin_indep_of_not_collinear A B C hABC
  have hAC_ne : C - A ≠ 0 := by
    intro h
    have : ![B - A, C - A] 1 = 0 := h
    exact LinearIndependent.ne_zero 1 h_lin this

  have hKB : K - B = (x - 1) • (B - A) + y • (C - A) := by
    calc K - B = K - A - (B - A) := by abel
      _ = x • (B - A) + y • (C - A) - (B - A) := by rw [hK_coord]
      _ = (x - 1) • (B - A) + y • (C - A) := by module
  have hu1 : 0 < ‖u1‖ := by
    have h_ne : K - B ≠ 0 := by
      intro h
      rw [hKB] at h
      have h_sum : ∑ i : Fin 2, (![x - 1, y] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![x - 1, y] i) • ![B - A, C - A] i = (x - 1) • (B - A) + y • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![x - 1, y] h_sum
      have h_y : y = 0 := h_indep 1
      have h_x : x - 1 = 0 := h_indep 0
      have : w * (1 - x) - y * (1 - z) = 0 := by
        calc w * (1 - x) - y * (1 - z) = w * (-(x - 1)) - y * (1 - z) := by ring
          _ = w * (-0) - 0 * (1 - z) := by rw [h_x, h_y]
          _ = 0 := by ring
      linarith
    exact norm_pos_iff.mpr h_ne

  have hLB : L - B = (z - 1) • (B - A) + w • (C - A) := by
    calc L - B = L - A - (B - A) := by abel
      _ = z • (B - A) + w • (C - A) - (B - A) := by rw [hL_coord]
      _ = (z - 1) • (B - A) + w • (C - A) := by module
  have hv1 : 0 < ‖v1‖ := by
    have h_ne : L - B ≠ 0 := by
      intro h
      rw [hLB] at h
      have h_sum : ∑ i : Fin 2, (![z - 1, w] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![z - 1, w] i) • ![B - A, C - A] i = (z - 1) • (B - A) + w • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![z - 1, w] h_sum
      have h_z : z - 1 = 0 := h_indep 0
      have h_w : w = 0 := h_indep 1
      have : w * (1 - x) - y * (1 - z) = 0 := by
        calc w * (1 - x) - y * (1 - z) = w * (1 - x) - y * (-(z - 1)) := by ring
          _ = 0 * (1 - x) - y * (-0) := by rw [h_z, h_w]
          _ = 0 := by ring
      linarith
    exact norm_pos_iff.mpr h_ne

  have hN_sub : N - A = (1/2:ℝ) • (C - A) := by
    have h1 : N - A = (⅟2:ℝ) • (C - A) := by rw [hN, midpoint_sub_left]
    have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
    rwa [h2] at h1
  have hCN : C - N = (1/2:ℝ) • (C - A) := by
    calc C - N = C - A - (N - A) := by abel
      _ = (1:ℝ) • (C - A) - (1/2:ℝ) • (C - A) := by rw [hN_sub, one_smul]
      _ = (1/2:ℝ) • (C - A) := by module
  have hu2 : 0 < ‖u2‖ := by
    have h_ne : C - N ≠ 0 := by
      intro h
      rw [hCN] at h
      have : (1/2:ℝ) • (C - A) = 0 := h
      have h_c_ne_A : C - A = 0 := smul_eq_zero.mp this |>.resolve_left (by norm_num)
      exact hAC_ne h_c_ne_A
    exact norm_pos_iff.mpr h_ne

  have hLN : L - N = z • (B - A) + (w - 1/2) • (C - A) := by
    calc L - N = L - A - (N - A) := by abel
      _ = z • (B - A) + w • (C - A) - (1/2:ℝ) • (C - A) := by rw [hL_coord, hN_sub]
      _ = z • (B - A) + (w - 1/2) • (C - A) := by module
  have hv2 : 0 < ‖v2‖ := by
    have h_ne : L - N ≠ 0 := by
      intro h
      rw [hLN] at h
      have h_sum : ∑ i : Fin 2, (![z, w - 1/2] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![z, w - 1/2] i) • ![B - A, C - A] i = z • (B - A) + (w - 1/2) • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![z, w - 1/2] h_sum
      have h_z : z = 0 := h_indep 0
      linarith
    exact norm_pos_iff.mpr h_ne

  have hnorm1 : inner ℝ u1 u1 * inner ℝ v1 v1 - (inner ℝ u1 v1)^2 = E^2 * (a * b - g^2) := by
    dsimp [u1, v1, a, b, g, E]
    rw [hKB, hLB]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring
  have hnorm2 : inner ℝ u2 u2 * inner ℝ v2 v2 - (inner ℝ u2 v2)^2 = (z/2)^2 * (a * b - g^2) := by
    dsimp [u2, v2, a, b, g]
    rw [hCN, hLN]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  have h_angle : Real.cos (InnerProductGeometry.angle v1 u1) = Real.cos (InnerProductGeometry.angle v2 u2) := by
    have h_Euclid : EuclideanGeometry.angle L B K = InnerProductGeometry.angle v1 u1 := rfl
    have h_Euclid2 : EuclideanGeometry.angle L N C = InnerProductGeometry.angle v2 u2 := rfl
    rw [← h_Euclid, ← h_Euclid2]
    rw [h2]

  have h_cos1 : Real.cos (InnerProductGeometry.angle v1 u1) = inner ℝ v1 u1 / (‖v1‖ * ‖u1‖) := InnerProductGeometry.cos_angle v1 u1
  have h_cos2 : Real.cos (InnerProductGeometry.angle v2 u2) = inner ℝ v2 u2 / (‖v2‖ * ‖u2‖) := InnerProductGeometry.cos_angle v2 u2
  rw [h_cos1, h_cos2] at h_angle
  have h_symm1 : inner ℝ v1 u1 = inner ℝ u1 v1 := real_inner_comm _ _
  have h_symm2 : inner ℝ v2 u2 = inner ℝ u2 v2 := real_inner_comm _ _
  rw [h_symm1, h_symm2] at h_angle

  have h_sq_eq : (inner ℝ u1 v1 * (z / 2))^2 = (inner ℝ u2 v2 * E)^2 := by
    have h_div_eq : (inner ℝ u1 v1)^2 / (‖u1‖^2 * ‖v1‖^2) = (inner ℝ u2 v2)^2 / (‖u2‖^2 * ‖v2‖^2) := by
      calc (inner ℝ u1 v1)^2 / (‖u1‖^2 * ‖v1‖^2) = (inner ℝ u1 v1)^2 / (‖v1‖ * ‖u1‖)^2 := by
            congr 1
            have : ‖u1‖^2 * ‖v1‖^2 = ‖v1‖^2 * ‖u1‖^2 := by ring
            rw [this]
            exact (mul_pow ‖v1‖ ‖u1‖ 2).symm
        _ = (inner ℝ u1 v1 / (‖v1‖ * ‖u1‖))^2 := by rw [div_pow]
        _ = (inner ℝ u2 v2 / (‖v2‖ * ‖u2‖))^2 := by rw [h_angle]
        _ = (inner ℝ u2 v2)^2 / (‖v2‖ * ‖u2‖)^2 := by rw [div_pow]
        _ = (inner ℝ u2 v2)^2 / (‖v2‖^2 * ‖u2‖^2) := by
            congr 1
            exact mul_pow ‖v2‖ ‖u2‖ 2
        _ = (inner ℝ u2 v2)^2 / (‖u2‖^2 * ‖v2‖^2) := by
            have : ‖v2‖^2 * ‖u2‖^2 = ‖u2‖^2 * ‖v2‖^2 := by ring
            rw [this]
    have h_cross : (inner ℝ u1 v1)^2 * (‖u2‖^2 * ‖v2‖^2) = (inner ℝ u2 v2)^2 * (‖u1‖^2 * ‖v1‖^2) := by
      have hd1 : ‖u1‖^2 * ‖v1‖^2 ≠ 0 := by positivity
      have hd2 : ‖u2‖^2 * ‖v2‖^2 ≠ 0 := by positivity
      exact (div_eq_div_iff hd1 hd2).mp h_div_eq

    have h1_norm : ‖u1‖^2 * ‖v1‖^2 = (inner ℝ u1 v1)^2 + E^2 * (a * b - g^2) := by
      have h_u1 : ‖u1‖^2 = inner ℝ u1 u1 := real_inner_self_eq_norm_sq u1 |>.symm
      have h_v1 : ‖v1‖^2 = inner ℝ v1 v1 := real_inner_self_eq_norm_sq v1 |>.symm
      rw [h_u1, h_v1]
      linarith [hnorm1]
    have h2_norm : ‖u2‖^2 * ‖v2‖^2 = (inner ℝ u2 v2)^2 + (z/2)^2 * (a * b - g^2) := by
      have h_u2 : ‖u2‖^2 = inner ℝ u2 u2 := real_inner_self_eq_norm_sq u2 |>.symm
      have h_v2 : ‖v2‖^2 = inner ℝ v2 v2 := real_inner_self_eq_norm_sq v2 |>.symm
      rw [h_u2, h_v2]
      linarith [hnorm2]

    have h3 : (inner ℝ u1 v1)^2 * ((inner ℝ u2 v2)^2 + (z/2)^2 * (a * b - g^2)) = (inner ℝ u2 v2)^2 * ((inner ℝ u1 v1)^2 + E^2 * (a * b - g^2)) := by
      rw [h1_norm, h2_norm] at h_cross
      exact h_cross

    have h4 : (inner ℝ u1 v1)^2 * (z/2)^2 * (a * b - g^2) = (inner ℝ u2 v2)^2 * E^2 * (a * b - g^2) := by
      linarith [h3]

    have hD_pos : 0 < a * b - g^2 := by
      have H_CS : (inner ℝ (B - A) (C - A))^2 < inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A) := CS_strict (B - A) (C - A) h_lin
      dsimp [a, b, g]
      linarith [H_CS]

    have hD_ne : a * b - g^2 ≠ 0 := by linarith
    have h5 : (inner ℝ u1 v1)^2 * (z/2)^2 = (inner ℝ u2 v2)^2 * E^2 := by
      have h_mul_eq : (a * b - g^2) * ((inner ℝ u1 v1)^2 * (z/2)^2) = (a * b - g^2) * ((inner ℝ u2 v2)^2 * E^2) := by linarith [h4]
      exact mul_left_cancel₀ hD_ne h_mul_eq
    calc (inner ℝ u1 v1 * (z/2))^2 = (inner ℝ u1 v1)^2 * (z/2)^2 := mul_pow _ _ _
      _ = (inner ℝ u2 v2)^2 * E^2 := h5
      _ = (inner ℝ u2 v2 * E)^2 := (mul_pow _ _ _).symm

  have hn1_pos : 0 < ‖v1‖ * ‖u1‖ := mul_pos hv1 hu1
  have hn2_pos : 0 < ‖v2‖ * ‖u2‖ := mul_pos hv2 hu2
  have hE_pos_z2 : 0 < z / 2 := by linarith

  have h_eq := cos_eq_implies (inner ℝ u1 v1) (inner ℝ u2 v2) (‖v1‖ * ‖u1‖) (‖v2‖ * ‖u2‖) E (z / 2) hE_pos hE_pos_z2 hn1_pos hn2_pos h_angle h_sq_eq

  dsimp [u1, v1, u2, v2, a, b, g] at h_eq

  have h_LHS : inner ℝ (K - B) (L - B) = a * (x - 1) * (z - 1) + g * ((x - 1) * w + y * (z - 1)) + b * y * w := by
    dsimp [a, b, g]
    rw [hKB, hLB]
    simp only [inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  have h_RHS : inner ℝ (C - N) (L - N) = (1/2:ℝ) * (g * z + b * (w - 1/2)) := by
    dsimp [b, g]
    rw [hCN, hLN]
    simp only [inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  rw [h_LHS, h_RHS] at h_eq
  linarith

lemma angle_eq_to_c3 (A B C K L M : Plane) (x y z w : ℝ)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hy : 0 < y) (hF_pos : 0 < x * (1 - w) - z * (1 - y))
    (hM : M = midpoint ℝ A B)
    (hK_coord : K - A = x • (B - A) + y • (C - A))
    (hL_coord : L - A = z • (B - A) + w • (C - A))
    (h3 : ∠ L C K = ∠ B M K) :
    let a := inner ℝ (B - A) (B - A)
    let b := inner ℝ (C - A) (C - A)
    let g := inner ℝ (B - A) (C - A)
    let F := x * (1 - w) - z * (1 - y)
    2 * y * (a * x * z + b * w * y - b * w - b * y + b + g * w * x - g * x + g * y * z - g * z) = F * (2 * a * x - a + 2 * g * y) := by
  let a := inner ℝ (B - A) (B - A)
  let b := inner ℝ (C - A) (C - A)
  let g := inner ℝ (B - A) (C - A)
  let F := x * (1 - w) - z * (1 - y)
  let u1 := L - C
  let v1 := K - C
  let u2 := B - M
  let v2 := K - M

  have h_lin : LinearIndependent ℝ ![B - A, C - A] := lin_indep_of_not_collinear A B C hABC
  have hAB_ne : B - A ≠ 0 := by
    intro h
    have : ![B - A, C - A] 0 = 0 := h
    exact LinearIndependent.ne_zero 0 h_lin this

  have hLC : L - C = z • (B - A) + (w - 1) • (C - A) := by
    calc L - C = L - A - (C - A) := by abel
      _ = z • (B - A) + w • (C - A) - (C - A) := by rw [hL_coord]
      _ = z • (B - A) + (w - 1) • (C - A) := by module
  have hu1 : 0 < ‖u1‖ := by
    have h_ne : L - C ≠ 0 := by
      intro h
      rw [hLC] at h
      have h_sum : ∑ i : Fin 2, (![z, w - 1] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![z, w - 1] i) • ![B - A, C - A] i = z • (B - A) + (w - 1) • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![z, w - 1] h_sum
      have h_z : z = 0 := h_indep 0
      have h_w : w - 1 = 0 := h_indep 1
      have : x * (1 - w) - z * (1 - y) = 0 := by
        calc x * (1 - w) - z * (1 - y) = x * (-(w - 1)) - z * (1 - y) := by ring
          _ = x * (-0) - 0 * (1 - y) := by rw [h_w, h_z]
          _ = 0 := by ring
      linarith
    exact norm_pos_iff.mpr h_ne

  have hKC : K - C = x • (B - A) + (y - 1) • (C - A) := by
    calc K - C = K - A - (C - A) := by abel
      _ = x • (B - A) + y • (C - A) - (C - A) := by rw [hK_coord]
      _ = x • (B - A) + (y - 1) • (C - A) := by module
  have hv1 : 0 < ‖v1‖ := by
    have h_ne : K - C ≠ 0 := by
      intro h
      rw [hKC] at h
      have h_sum : ∑ i : Fin 2, (![x, y - 1] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![x, y - 1] i) • ![B - A, C - A] i = x • (B - A) + (y - 1) • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![x, y - 1] h_sum
      have h_x : x = 0 := h_indep 0
      have h_y : y - 1 = 0 := h_indep 1
      have : x * (1 - w) - z * (1 - y) = 0 := by
        calc x * (1 - w) - z * (1 - y) = x * (1 - w) - z * (-(y - 1)) := by ring
          _ = 0 * (1 - w) - z * (-0) := by rw [h_x, h_y]
          _ = 0 := by ring
      linarith
    exact norm_pos_iff.mpr h_ne

  have hM_sub : M - A = (1/2:ℝ) • (B - A) := by
    have h1 : M - A = (⅟2:ℝ) • (B - A) := by rw [hM, midpoint_sub_left]
    have h2 : (⅟2:ℝ) = (1/2:ℝ) := by norm_num
    rwa [h2] at h1
  have hBM : B - M = (1/2:ℝ) • (B - A) := by
    calc B - M = B - A - (M - A) := by abel
      _ = (1:ℝ) • (B - A) - (1/2:ℝ) • (B - A) := by rw [hM_sub, one_smul]
      _ = (1/2:ℝ) • (B - A) := by module
  have hu2 : 0 < ‖u2‖ := by
    have h_ne : B - M ≠ 0 := by
      intro h
      rw [hBM] at h
      have : (1/2:ℝ) • (B - A) = 0 := h
      have h_b_ne_A : B - A = 0 := smul_eq_zero.mp this |>.resolve_left (by norm_num)
      exact hAB_ne h_b_ne_A
    exact norm_pos_iff.mpr h_ne

  have hKM : K - M = (x - 1/2) • (B - A) + y • (C - A) := by
    calc K - M = K - A - (M - A) := by abel
      _ = x • (B - A) + y • (C - A) - (1/2:ℝ) • (B - A) := by rw [hK_coord, hM_sub]
      _ = (x - 1/2) • (B - A) + y • (C - A) := by module
  have hv2 : 0 < ‖v2‖ := by
    have h_ne : K - M ≠ 0 := by
      intro h
      rw [hKM] at h
      have h_sum : ∑ i : Fin 2, (![x - 1/2, y] i) • ![B - A, C - A] i = 0 := by
        have H : ∑ i : Fin 2, (![x - 1/2, y] i) • ![B - A, C - A] i = (x - 1/2) • (B - A) + y • (C - A) := Fin.sum_univ_two _
        rw [H, h]
      have h_indep := Fintype.linearIndependent_iff.mp h_lin ![x - 1/2, y] h_sum
      have h_y : y = 0 := h_indep 1
      linarith
    exact norm_pos_iff.mpr h_ne

  have hnorm1 : inner ℝ u1 u1 * inner ℝ v1 v1 - (inner ℝ u1 v1)^2 = F^2 * (a * b - g^2) := by
    dsimp [u1, v1, a, b, g, F]
    rw [hLC, hKC]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  have hnorm2 : inner ℝ u2 u2 * inner ℝ v2 v2 - (inner ℝ u2 v2)^2 = (y/2)^2 * (a * b - g^2) := by
    dsimp [u2, v2, a, b, g]
    rw [hBM, hKM]
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  have h_angle : Real.cos (InnerProductGeometry.angle u1 v1) = Real.cos (InnerProductGeometry.angle u2 v2) := by
    have h_Euclid : EuclideanGeometry.angle L C K = InnerProductGeometry.angle u1 v1 := rfl
    have h_Euclid2 : EuclideanGeometry.angle B M K = InnerProductGeometry.angle u2 v2 := rfl
    rw [← h_Euclid, ← h_Euclid2]
    rw [h3]

  have h_cos1 : Real.cos (InnerProductGeometry.angle u1 v1) = inner ℝ u1 v1 / (‖u1‖ * ‖v1‖) := InnerProductGeometry.cos_angle u1 v1
  have h_cos2 : Real.cos (InnerProductGeometry.angle u2 v2) = inner ℝ u2 v2 / (‖u2‖ * ‖v2‖) := InnerProductGeometry.cos_angle u2 v2
  rw [h_cos1, h_cos2] at h_angle

  have h_sq_eq : (inner ℝ u1 v1 * (y / 2))^2 = (inner ℝ u2 v2 * F)^2 := by
    have h_div_eq : (inner ℝ u1 v1)^2 / (‖u1‖^2 * ‖v1‖^2) = (inner ℝ u2 v2)^2 / (‖u2‖^2 * ‖v2‖^2) := by
      calc (inner ℝ u1 v1)^2 / (‖u1‖^2 * ‖v1‖^2) = (inner ℝ u1 v1)^2 / (‖u1‖ * ‖v1‖)^2 := by
            congr 1
            exact (mul_pow ‖u1‖ ‖v1‖ 2).symm
        _ = (inner ℝ u1 v1 / (‖u1‖ * ‖v1‖))^2 := by rw [div_pow]
        _ = (inner ℝ u2 v2 / (‖u2‖ * ‖v2‖))^2 := by rw [h_angle]
        _ = (inner ℝ u2 v2)^2 / (‖u2‖ * ‖v2‖)^2 := by rw [div_pow]
        _ = (inner ℝ u2 v2)^2 / (‖u2‖^2 * ‖v2‖^2) := by
            congr 1
            exact mul_pow ‖u2‖ ‖v2‖ 2
    have h_cross : (inner ℝ u1 v1)^2 * (‖u2‖^2 * ‖v2‖^2) = (inner ℝ u2 v2)^2 * (‖u1‖^2 * ‖v1‖^2) := by
      have hd1 : ‖u1‖^2 * ‖v1‖^2 ≠ 0 := by positivity
      have hd2 : ‖u2‖^2 * ‖v2‖^2 ≠ 0 := by positivity
      exact (div_eq_div_iff hd1 hd2).mp h_div_eq

    have h1_norm : ‖u1‖^2 * ‖v1‖^2 = (inner ℝ u1 v1)^2 + F^2 * (a * b - g^2) := by
      have h_u1 : ‖u1‖^2 = inner ℝ u1 u1 := real_inner_self_eq_norm_sq u1 |>.symm
      have h_v1 : ‖v1‖^2 = inner ℝ v1 v1 := real_inner_self_eq_norm_sq v1 |>.symm
      rw [h_u1, h_v1]
      linarith [hnorm1]
    have h2_norm : ‖u2‖^2 * ‖v2‖^2 = (inner ℝ u2 v2)^2 + (y/2)^2 * (a * b - g^2) := by
      have h_u2 : ‖u2‖^2 = inner ℝ u2 u2 := real_inner_self_eq_norm_sq u2 |>.symm
      have h_v2 : ‖v2‖^2 = inner ℝ v2 v2 := real_inner_self_eq_norm_sq v2 |>.symm
      rw [h_u2, h_v2]
      linarith [hnorm2]

    have h3 : (inner ℝ u1 v1)^2 * ((inner ℝ u2 v2)^2 + (y/2)^2 * (a * b - g^2)) = (inner ℝ u2 v2)^2 * ((inner ℝ u1 v1)^2 + F^2 * (a * b - g^2)) := by
      rw [h1_norm, h2_norm] at h_cross
      exact h_cross

    have h4 : (inner ℝ u1 v1)^2 * (y/2)^2 * (a * b - g^2) = (inner ℝ u2 v2)^2 * F^2 * (a * b - g^2) := by
      linarith [h3]

    have hD_pos : 0 < a * b - g^2 := by
      have H_CS : (inner ℝ (B - A) (C - A))^2 < inner ℝ (B - A) (B - A) * inner ℝ (C - A) (C - A) := CS_strict (B - A) (C - A) h_lin
      dsimp [a, b, g]
      linarith [H_CS]

    have hD_ne : a * b - g^2 ≠ 0 := by linarith
    have h5 : (inner ℝ u1 v1)^2 * (y/2)^2 = (inner ℝ u2 v2)^2 * F^2 := by
      have h_mul_eq : (a * b - g^2) * ((inner ℝ u1 v1)^2 * (y/2)^2) = (a * b - g^2) * ((inner ℝ u2 v2)^2 * F^2) := by linarith [h4]
      exact mul_left_cancel₀ hD_ne h_mul_eq
    calc (inner ℝ u1 v1 * (y/2))^2 = (inner ℝ u1 v1)^2 * (y/2)^2 := mul_pow _ _ _
      _ = (inner ℝ u2 v2)^2 * F^2 := h5
      _ = (inner ℝ u2 v2 * F)^2 := (mul_pow _ _ _).symm

  have hn1_pos : 0 < ‖u1‖ * ‖v1‖ := mul_pos hu1 hv1
  have hn2_pos : 0 < ‖u2‖ * ‖v2‖ := mul_pos hu2 hv2
  have hy_pos_y2 : 0 < y / 2 := by linarith

  have h_eq := cos_eq_implies (inner ℝ u1 v1) (inner ℝ u2 v2) (‖u1‖ * ‖v1‖) (‖u2‖ * ‖v2‖) F (y / 2) hF_pos hy_pos_y2 hn1_pos hn2_pos h_angle h_sq_eq

  dsimp [u1, v1, u2, v2, a, b, g] at h_eq

  have h_LHS : inner ℝ (L - C) (K - C) = a * x * z + g * ((y - 1) * z + x * (w - 1)) + b * (y - 1) * (w - 1) := by
    dsimp [a, b, g]
    rw [hLC, hKC]
    simp only [inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hc : inner ℝ (C - A) (B - A) = inner ℝ (B - A) (C - A) := real_inner_comm _ _
    rw [hc]
    ring

  have h_RHS : inner ℝ (B - M) (K - M) = (1/2:ℝ) * (a * (x - 1/2) + g * y) := by
    dsimp [a, g]
    rw [hBM, hKM]
    simp only [inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    ring

  rw [h_LHS, h_RHS] at h_eq
  linarith


lemma algebraic_identity (x y z w a b g : ℝ) :
  (x - 1) * (w - 1) * (2 * (-(w + z) * (a * x^2 + 2 * g * x * y + b * y^2) + (x + y) * (a * z^2 + 2 * g * z * w + b * w^2)) - (x * w - y * z) * (b - a)) =
      -(3 * w * x + 2 * w * y - w + 2 * x * z - x + y * z - y - z) * (a * z * (1 - x) - b * y * (1 - w))
      + (x + y) * (w - 1) * (2 * z * (a * x * z - a * x - a * z + a + b * w * y + g * w * x - g * w + g * y * z - g * y) - (w * (1 - x) - y * (1 - z)) * (2 * b * w - b + 2 * g * z))
      - (w + z) * (x - 1) * (2 * y * (a * x * z + b * w * y - b * w - b * y + b + g * w * x - g * x + g * y * z - g * z) - (x * (1 - w) - z * (1 - y)) * (2 * a * x - a + 2 * g * y)) := by
  ring

/-- IMO 2010 Problem 4: with the configuration described above, the circumcentre
`O` of triangle `AKL` satisfies `OM = ON`, where `M`, `N` are the midpoints of
`AB`, `AC`. -/
theorem main_theorem
    (A B C K L O : Plane)
    -- `ABC` is a nondegenerate triangle.
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    -- `M`, `N` are the midpoints of `AB`, `AC`.
    (M N : Plane) (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    -- `K` is inside triangle `BMC`; `L` is inside triangle `BNC`.
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    -- `K` inside angle `∠ L B A`; `L` inside angle `∠ A C K`.
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    -- The three angle equalities.
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    -- `O` is the circumcentre of triangle `AKL`.
    (hO : IsCircumcentre A K L O) :
    dist O M = dist O N := by
  -- It suffices to prove the squared distances agree.
  obtain ⟨hOK, hOL⟩ := hO
  -- Reduce to squared distances.
  have hsq : dist O M ^ 2 = dist O N ^ 2 := by
    suffices h : inner ℝ (O - midpoint ℝ M N) (N - M) = (0:ℝ) by
      have h1 : dist O M ^ 2 = inner ℝ (O - M) (O - M) := by rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
      have h2 : dist O N ^ 2 = inner ℝ (O - N) (O - N) := by rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
      rw [h1, h2]
      have H : inner ℝ (O - M) (O - M) - inner ℝ (O - N) (O - N) = 2 * inner ℝ (O - midpoint ℝ M N) (N - M) := by
        rw [midpoint_eq_smul_add]
        simp only [inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
          real_inner_comm M O, real_inner_comm N O, real_inner_comm N M, starRingEnd_apply, star_trivial, invOf_eq_inv]
        ring
      linarith
    suffices h : ∃ p q : ℝ, C - B = p • (K - A) + q • (L - A) ∧
      p * inner ℝ (K - A) (K - A) + q * inner ℝ (L - A) (L - A) = (inner ℝ (C - A) (C - A) - inner ℝ (B - A) (B - A)) / 2 by
      rcases h with ⟨p, q, hvec, hnorm⟩
      have hk : 2 * inner ℝ (O - A) (K - A) = inner ℝ (K - A) (K - A) := circum_eq A K O hOK
      have hl : 2 * inner ℝ (O - A) (L - A) = inner ℝ (L - A) (L - A) := circum_eq A L O hOL

      have H1 : inner ℝ (O - A) (C - B) = inner ℝ (O - A) (p • (K - A) + q • (L - A)) := by rw [hvec]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at H1

      have H2 : inner ℝ (O - A) (C - B) = (p * inner ℝ (K - A) (K - A) + q * inner ℝ (L - A) (L - A)) / 2 := by
        calc inner ℝ (O - A) (C - B) = p * inner ℝ (O - A) (K - A) + q * inner ℝ (O - A) (L - A) := H1
          _ = p * (inner ℝ (K - A) (K - A) / 2) + q * (inner ℝ (L - A) (L - A) / 2) := by
            congr 1
            · congr 1; linarith [hk]
            · congr 1; linarith [hl]
          _ = (p * inner ℝ (K - A) (K - A) + q * inner ℝ (L - A) (L - A)) / 2 := by ring

      have H3 : inner ℝ (O - A) (C - B) = (inner ℝ (C - A) (C - A) - inner ℝ (B - A) (B - A)) / 4 := by
        linarith [H2, hnorm]

      have hN_M : N - M = (1/2:ℝ) • (C - B) := hN_M_lem A B C M N hM hN

      have hmid : midpoint ℝ M N - A = (1/4:ℝ) • (C - A) + (1/4:ℝ) • (B - A) := hmid_lem A B C M N hM hN

      have h_target : inner ℝ (O - midpoint ℝ M N) (N - M) =
          inner ℝ ((O - A) - (midpoint ℝ M N - A)) (N - M) := by
        congr 1; abel

      rw [h_target]
      rw [inner_sub_left]
      rw [hN_M, real_inner_smul_right, real_inner_smul_right]

      have H4 : inner ℝ (midpoint ℝ M N - A) (C - B) = (1/4 : ℝ) * (inner ℝ (C - A) (C - A) - inner ℝ (B - A) (B - A)) := by
        rw [hmid]
        have Hcb : C - B = (C - A) - (B - A) := by abel
        rw [Hcb]
        simp only [inner_add_left, inner_sub_left, inner_sub_right, real_inner_smul_left]
        have hc1 : inner ℝ C A = inner ℝ A C := real_inner_comm A C
        have hc2 : inner ℝ B A = inner ℝ A B := real_inner_comm A B
        have hc3 : inner ℝ C B = inner ℝ B C := real_inner_comm B C
        have hc4 : inner ℝ (B - A) (C - A) = inner ℝ (C - A) (B - A) := real_inner_comm _ _
        linarith

      linarith [H3, H4]
    suffices h_coords : ∃ x y z w : ℝ,
        K - A = x • (B - A) + y • (C - A) ∧
        L - A = z • (B - A) + w • (C - A) ∧
        x * w - y * z ≠ 0 ∧
        2 * (-(w + z) * inner ℝ (K - A) (K - A) + (x + y) * inner ℝ (L - A) (L - A)) =
        (x * w - y * z) * (inner ℝ (C - A) (C - A) - inner ℝ (B - A) (B - A)) by
      rcases h_coords with ⟨x, y, z, w, hK_coord, hL_coord, hD, hpoly⟩
      let D := x * w - y * z
      have hDcomm : w * x - z * y ≠ 0 := by
        intro h_comm_eq
        apply hD
        calc x * w - y * z = w * x - z * y := by ring
          _ = 0 := h_comm_eq
      let p : ℝ := -(w + z) / D
      let q : ℝ := (x + y) / D
      refine ⟨p, q, ?_, ?_⟩
      · have hpB : p * x + q * z = -1 := by
          dsimp [p, q, D]
          field_simp [hDcomm]
          ring
        have hpC : p * y + q * w = 1 := by
          dsimp [p, q, D]
          field_simp [hDcomm]
          ring
        rw [hK_coord, hL_coord]
        calc
          C - B = (-1:ℝ) • (B - A) + (1:ℝ) • (C - A) := by module
          _ = (p * x + q * z) • (B - A) + (p * y + q * w) • (C - A) := by
            rw [hpB, hpC]
          _ = p • (x • (B - A) + y • (C - A)) +
              q • (z • (B - A) + w • (C - A)) := by
            module
      · dsimp [p, q, D]
        have hmain :
            (-(w + z) * inner ℝ (K - A) (K - A) +
                (x + y) * inner ℝ (L - A) (L - A)) /
              (x * w - y * z) =
            (inner ℝ (C - A) (C - A) - inner ℝ (B - A) (B - A)) / 2 := by
          field_simp [hD]
          nlinarith [hpoly]
        rw [← hmain]
        ring
    have h_coord_exist : ∃ x y z w : ℝ, K - A = x • (B - A) + y • (C - A) ∧ L - A = z • (B - A) + w • (C - A) := coords_exist A B C K L hABC
    rcases h_coord_exist with ⟨x, y, z, w, hK_coord, hL_coord⟩
    have h_bounds : 0 < x ∧ 0 < y ∧ x < 1 ∧ 0 < z ∧ 0 < w ∧ w < 1 ∧ 0 < w * (1 - x) - y * (1 - z) ∧ 0 < x * (1 - w) - z * (1 - y) := coord_bounds A B C K L M N hABC hM hN x y z w hK_coord hL_coord hK hL hKangle hLangle
    rcases h_bounds with ⟨hx, hy, hx1, hz, hw, hw1, hE_pos, hF_pos⟩
    let E := w * (1 - x) - y * (1 - z)
    let F := x * (1 - w) - z * (1 - y)
    have hD : x * w - y * z ≠ 0 := det_nonzero x y z w E F hx hy hx1 hz hw hw1 rfl hE_pos rfl hF_pos
    have hC1 : inner ℝ (B - A) (B - A) * z * (1 - x) = inner ℝ (C - A) (C - A) * y * (1 - w) := angle_eq_to_c1 A B C K L x y z w hABC hy hz hK_coord hL_coord h1
    have hC2 : 2 * z * (inner ℝ (B - A) (B - A) * x * z - inner ℝ (B - A) (B - A) * x - inner ℝ (B - A) (B - A) * z + inner ℝ (B - A) (B - A) + inner ℝ (C - A) (C - A) * w * y + inner ℝ (B - A) (C - A) * w * x - inner ℝ (B - A) (C - A) * w + inner ℝ (B - A) (C - A) * y * z - inner ℝ (B - A) (C - A) * y) = E * (2 * inner ℝ (C - A) (C - A) * w - inner ℝ (C - A) (C - A) + 2 * inner ℝ (B - A) (C - A) * z) := angle_eq_to_c2 A B C K L N x y z w hABC hz hE_pos hN hK_coord hL_coord h2
    have hC3 : 2 * y * (inner ℝ (B - A) (B - A) * x * z + inner ℝ (C - A) (C - A) * w * y - inner ℝ (C - A) (C - A) * w - inner ℝ (C - A) (C - A) * y + inner ℝ (C - A) (C - A) + inner ℝ (B - A) (C - A) * w * x - inner ℝ (B - A) (C - A) * x + inner ℝ (B - A) (C - A) * y * z - inner ℝ (B - A) (C - A) * z) = F * (2 * inner ℝ (B - A) (B - A) * x - inner ℝ (B - A) (B - A) + 2 * inner ℝ (B - A) (C - A) * y) := angle_eq_to_c3 A B C K L M x y z w hABC hy hF_pos hM hK_coord hL_coord h3

    let a := inner ℝ (B - A) (B - A)
    let b := inner ℝ (C - A) (C - A)
    let g := inner ℝ (B - A) (C - A)

    have h_normK : inner ℝ (K - A) (K - A) = a * x^2 + 2 * g * x * y + b * y^2 := by
      dsimp [a, b, g]
      rw [hK_coord]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm]
      ring

    have h_normL : inner ℝ (L - A) (L - A) = a * z^2 + 2 * g * z * w + b * w^2 := by
      dsimp [a, b, g]
      rw [hL_coord]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm]
      ring

    have h_alg : (x - 1) * (w - 1) * (2 * (-(w + z) * (a * x^2 + 2 * g * x * y + b * y^2) + (x + y) * (a * z^2 + 2 * g * z * w + b * w^2)) - (x * w - y * z) * (b - a)) = 0 := by
      calc
        _ = -(3 * w * x + 2 * w * y - w + 2 * x * z - x + y * z - y - z) * (a * z * (1 - x) - b * y * (1 - w))
            + (x + y) * (w - 1) * (2 * z * (a * x * z - a * x - a * z + a + b * w * y + g * w * x - g * w + g * y * z - g * y) - (w * (1 - x) - y * (1 - z)) * (2 * b * w - b + 2 * g * z))
            - (w + z) * (x - 1) * (2 * y * (a * x * z + b * w * y - b * w - b * y + b + g * w * x - g * x + g * y * z - g * z) - (x * (1 - w) - z * (1 - y)) * (2 * a * x - a + 2 * g * y)) := algebraic_identity x y z w a b g
        _ = 0 := by rw [hC1, hC2, hC3]; ring

    have h_poly : 2 * (-(w + z) * inner ℝ (K - A) (K - A) + (x + y) * inner ℝ (L - A) (L - A)) = (x * w - y * z) * (inner ℝ (C - A) (C - A) - inner ℝ (B - A) (B - A)) := by
      rw [h_normK, h_normL]
      have hw1_nz : w - 1 ≠ 0 := by linarith
      have hx1_nz : x - 1 ≠ 0 := by linarith
      have H1 : (x - 1) * (w - 1) ≠ 0 := mul_ne_zero hx1_nz hw1_nz
      have H2 : 2 * (-(w + z) * (a * x^2 + 2 * g * x * y + b * y^2) + (x + y) * (a * z^2 + 2 * g * z * w + b * w^2)) - (x * w - y * z) * (b - a) = 0 := by
        cases mul_eq_zero.mp h_alg with
        | inl h => exfalso; exact H1 h
        | inr h => exact h
      linarith [H2]

    exact ⟨x, y, z, w, hK_coord, hL_coord, hD, h_poly⟩
  have h1 : (0:ℝ) ≤ dist O M := dist_nonneg
  have h2 : (0:ℝ) ≤ dist O N := dist_nonneg
  nlinarith [hsq, h1, h2]
