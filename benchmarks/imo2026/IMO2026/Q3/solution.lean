import Mathlib

open scoped BigOperators

namespace LiuBangXiangYu

/-- The multiset of piece lengths obtained by cutting `[0,1]` at the points of a
finite set `S ⊆ (0,1)`.  We sort `S` ascending, prepend `0` and append `1`, and
take consecutive differences.  The result is a list of `|S| + 1` positive reals
summing to `1` (when `S ⊆ (0,1)`). -/
noncomputable def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

/-- The sum of the entries of a list `L` at the (0-indexed) even positions, after
sorting `L` in non-increasing order.  These are the entries in the `1`st, `3`rd,
`5`th, … positions of the sorted (decreasing) list, i.e. the pieces claimed by
the first mover under the greedy claiming rule. -/
noncomputable def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

/-- `L(A,B)`: Liu Bang's total length, given Liu Bang's marks `A` and Xiang Yu's
marks `B`. -/
noncomputable def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

/-- The set of admissible markings for a player: a finite subset of `(0,1)` of
size at most `n`.  We encode it as a `Finset ℝ` subject to the side conditions. -/
def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

/-- The value Liu Bang can guarantee.

`V n` is the supremum over Liu Bang's admissible markings `A` of the infimum,
over Xiang Yu's admissible markings `B` disjoint from `A`, of `L A B`. -/
noncomputable def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

/-- The claimed answer value `V(n) = 2^n / (2^(n+1) - 1)`. -/
noncomputable def answer (n : ℕ) : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)


/-- Alternating sum `l₀ - l₁ + l₂ - l₃ + …` of a list. -/
noncomputable def altSum (l : List ℝ) : ℝ :=
  (l.zipIdx.map (fun p => if p.2 % 2 = 0 then p.1 else -p.1)).sum

/-- Generic pair-list identity: twice the even-index subsum equals the total plus
the signed alternating sum.  Proved by induction on the list of pairs. -/
theorem twice_evenSum_gen (z : List (ℝ × ℕ)) :
    2 * ((z.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = (z.map (fun p => p.1)).sum
        + (z.map (fun p => if p.2 % 2 = 0 then p.1 else -p.1)).sum := by
  induction z with
  | nil => simp
  | cons a t ih =>
    by_cases h : a.2 % 2 = 0
    · simp only [List.filter_cons, h, decide_true, if_true, List.map_cons,
        List.sum_cons]
      linarith [ih]
    · simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, if_false,
        List.map_cons, List.sum_cons]
      linarith [ih]

/-- Twice the even-index subsum equals `sum + altSum`. -/
theorem twice_evenSum_eq_sum_add_alt (l : List ℝ) :
    2 * ((l.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = l.sum + altSum l := by
  have h := twice_evenSum_gen l.zipIdx
  rw [twice_evenSum_gen l.zipIdx]
  rw [List.zipIdx_map_fst]
  rfl

/-- Sum of even-indexed entries equals `(sum + altSum)/2` (over the given order). -/
theorem sum_even_eq_half_sum_add_alt (l : List ℝ) :
    ((l.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
      = (l.sum + altSum l) / 2 := by
  have h := twice_evenSum_eq_sum_add_alt l
  linarith

/-- `firstPlayerShare l = (S + Alt)/2` where `S`, `Alt` are of the descending sort. -/
theorem firstPlayerShare_eq_half_sum_add_alt (l : List ℝ) :
    firstPlayerShare l =
      ((l.mergeSort (· ≥ ·)).sum + altSum (l.mergeSort (· ≥ ·))) / 2 := by
  unfold firstPlayerShare
  exact sum_even_eq_half_sum_add_alt (l.mergeSort (· ≥ ·))


/-- Telescoping: the sum of consecutive differences of `a :: l` equals
`last - a`. -/
theorem zipWith_sub_sum_telescope (a : ℝ) (l : List ℝ) :
    (List.zipWith (fun x y => y - x) (a :: l) l).sum = (a :: l).getLastD a - a := by
  induction l generalizing a with
  | nil => simp
  | cons b t ih =>
    simp only [List.zipWith_cons_cons, List.sum_cons, ih b, List.getLastD_cons]
    ring

/-- The piece lengths of an admissible cut set sum to `1` (the total stick
length). -/
theorem pieceLengths_sum (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    (pieceLengths S).sum = 1 := by
  unfold pieceLengths
  simp only [List.cons_append, List.tail_cons]
  rw [zipWith_sub_sum_telescope]
  simp only [List.getLastD_cons, sub_zero]
  rw [List.getLastD_concat]

/-- There are `|S| + 1` pieces. -/
theorem pieceLengths_length (S : Finset ℝ) :
    (pieceLengths S).length = S.card + 1 := by
  unfold pieceLengths
  simp only [List.length_zipWith, List.length_tail, List.length_cons,
    List.length_append, List.length_nil, Finset.length_sort]
  omega

/-- For a `≤`-chain `l`, all consecutive differences `b - a` are nonnegative. -/
theorem chain'_zipWith_sub_nonneg :
    ∀ (l : List ℝ), List.IsChain (· ≤ ·) l →
      ∀ x ∈ List.zipWith (fun a b => b - a) l l.tail, 0 ≤ x := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a t ih =>
    intro hchain x hx
    cases t with
    | nil => simp at hx
    | cons b s =>
      simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at hx
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hrest⟩ := hchain
      rcases hx with h | h
      · rw [h]; linarith
      · exact ih hrest x (by simpa using h)

/-- Every piece length is nonnegative for an admissible cut set (the sorted
list `0 :: sort S ++ [1]` is monotone nondecreasing, so consecutive differences
are `≥ 0`). -/
theorem pieceLengths_nonneg (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1)
    (x : ℝ) (hx : x ∈ pieceLengths S) : 0 ≤ x := by
  have hchain : List.IsChain (· ≤ ·) ((0 :: (S.sort (· ≤ ·))) ++ [1]) := by
    -- membership facts
    have hmem : ∀ y ∈ S.sort (· ≤ ·), 0 ≤ y ∧ y ≤ 1 := by
      intro y hy
      rw [Finset.mem_sort] at hy
      have := hS (Finset.mem_coe.mpr hy)
      rw [Set.mem_Ioo] at this
      exact ⟨le_of_lt this.1, le_of_lt this.2⟩
    have hpair : List.Pairwise (· ≤ ·) (S.sort (· ≤ ·)) := Finset.pairwise_sort S _
    -- IsChain of the sort follows from Pairwise
    have hchsort : List.IsChain (· ≤ ·) (S.sort (· ≤ ·)) := by
      rw [List.isChain_iff_forall_rel_of_append_cons_cons]
      intro a b l₁ l₂ hl
      rw [hl] at hpair
      rw [List.pairwise_append] at hpair
      obtain ⟨_, hpr, _⟩ := hpair
      rw [List.pairwise_cons] at hpr
      exact hpr.1 b (by simp)
    -- 0 :: sort is a chain
    have hchcons : List.IsChain (· ≤ ·) (0 :: (S.sort (· ≤ ·))) := by
      apply hchsort.isChain_cons
      intro hne
      have := List.head_mem hne
      exact (hmem _ this).1
    -- append [1]
    rw [List.isChain_append]
    refine ⟨hchcons, List.isChain_singleton _, ?_⟩
    intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    -- x is the last element of 0 :: sort, hence a member of that list
    have hxmem : x ∈ (0 :: (S.sort (· ≤ ·))) := List.mem_of_mem_getLast? hx
    rw [List.mem_cons] at hxmem
    rcases hxmem with rfl | hxs
    · norm_num
    · exact (hmem x hxs).2
  have hmain := chain'_zipWith_sub_nonneg ((0 :: (S.sort (· ≤ ·))) ++ [1]) hchain
  apply hmain
  unfold pieceLengths at hx
  simpa using hx

/-- `firstPlayerShare` of a list of nonnegative reals is nonnegative and at most
the total sum of the list. -/
theorem firstPlayerShare_le_sum (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x) :
    0 ≤ firstPlayerShare l ∧ firstPlayerShare l ≤ l.sum := by
  unfold firstPlayerShare
  simp only
  set sorted := l.mergeSort (· ≥ ·) with hsorted
  -- all entries of sorted are ≥ 0 (perm of l)
  have hperm : sorted.Perm l := List.mergeSort_perm l _
  have hsortednn : ∀ y ∈ sorted, 0 ≤ y := fun y hy => hl y (hperm.mem_iff.mp hy)
  have hsortedsum : sorted.sum = l.sum := hperm.sum_eq
  -- selected list is a sublist of sorted
  have hsub : ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).Sublist sorted := by
    have h1 : (sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).Sublist sorted.zipIdx :=
      List.filter_sublist
    have h2 := h1.map (fun p => p.1)
    rwa [List.zipIdx_map_fst 0] at h2
  constructor
  · -- 0 ≤ subsum
    apply List.sum_nonneg
    intro y hy
    exact hsortednn y (hsub.subset hy)
  · -- subsum ≤ l.sum
    calc ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum
        ≤ sorted.sum := List.Sublist.sum_le_sum hsub hsortednn
      _ = l.sum := hsortedsum

theorem L_mem_Icc (A B : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (hB : ↑B ⊆ Set.Ioo (0 : ℝ) 1) :
    L A B ∈ Set.Icc (0 : ℝ) 1 := by
  have hAB : ↑(A ∪ B) ⊆ Set.Ioo (0 : ℝ) 1 := by
    rw [Finset.coe_union]
    exact Set.union_subset hA hB
  have hnn : ∀ x ∈ pieceLengths (A ∪ B), 0 ≤ x := pieceLengths_nonneg _ hAB
  have hsum : (pieceLengths (A ∪ B)).sum = 1 := pieceLengths_sum _ hAB
  have hshare := firstPlayerShare_le_sum (pieceLengths (A ∪ B)) hnn
  constructor
  · -- 0 ≤ L A B
    exact hshare.1
  · -- L A B ≤ 1
    calc L A B = firstPlayerShare (pieceLengths (A ∪ B)) := rfl
      _ ≤ (pieceLengths (A ∪ B)).sum := hshare.2
      _ = 1 := hsum

/-- Reduction of `L` to an alternating sum: `L A B = (1 + altSum sortedPieces)/2`
where `sortedPieces` is the descending sort of `pieceLengths (A ∪ B)`.  Combines
`firstPlayerShare_eq_half_sum_add_alt` with `pieceLengths_sum` (= 1). -/
theorem L_eq_half_one_add_alt (A B : Finset ℝ)
    (hAB : ↑(A ∪ B) ⊆ Set.Ioo (0 : ℝ) 1) :
    L A B = (1 + altSum ((pieceLengths (A ∪ B)).mergeSort (· ≥ ·))) / 2 := by
  unfold L
  rw [firstPlayerShare_eq_half_sum_add_alt]
  have hsum : (pieceLengths (A ∪ B)).sum = 1 := pieceLengths_sum _ hAB
  have hperm : ((pieceLengths (A ∪ B)).mergeSort (· ≥ ·)).sum
      = (pieceLengths (A ∪ B)).sum := (List.mergeSort_perm _ _).sum_eq
  rw [hperm, hsum]


/-- Liu Bang's optimal marking: partial sums giving pieces `2^{n-i}/D`.
`lowerA n = { (2^{n+1} - 2^{n+1-k})/(2^{n+1}-1) : 1 ≤ k ≤ n }`. -/
noncomputable def lowerA (n : ℕ) : Finset ℝ :=
  (Finset.Icc 1 n).image (fun k : ℕ =>
    ((2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n + 1 - k)) / ((2 : ℝ) ^ (n + 1) - 1))

/-- `lowerA n` has exactly `n` elements. -/
theorem lowerA_card (n : ℕ) : (lowerA n).card = n := by
  unfold lowerA
  rw [Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
    simp only at hab
    have hD : (0:ℝ) < (2:ℝ) ^ (n + 1) - 1 := by
      have : (1:ℝ) < (2:ℝ) ^ (n + 1) := by
        apply one_lt_pow₀ (by norm_num) (by omega)
      linarith
    have h2 : (2:ℝ) ^ (n + 1) - (2:ℝ) ^ (n + 1 - a) = (2:ℝ) ^ (n + 1) - (2:ℝ) ^ (n + 1 - b) := by
      have := hab
      field_simp at this
      linarith [this]
    have h3 : (2:ℝ) ^ (n + 1 - a) = (2:ℝ) ^ (n + 1 - b) := by linarith
    have h4 : n + 1 - a = n + 1 - b := by
      exact (pow_right_inj₀ (by norm_num) (by norm_num)).mp h3
    omega

/-- Every mark of `lowerA n` lies in `(0,1)`. -/
theorem lowerA_mem_Ioo (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ lowerA n) :
    x ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold lowerA at hx
  rw [Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_Icc] at hk
  have hD : (1:ℝ) < (2:ℝ) ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
  -- 2^{n+1-k} ≥ 2 since n+1-k ≥ 1 (k ≤ n)
  have hlow : (2:ℝ) ≤ (2:ℝ) ^ (n + 1 - k) := by
    calc (2:ℝ) = (2:ℝ) ^ 1 := by norm_num
    _ ≤ (2:ℝ) ^ (n + 1 - k) := by
        apply pow_le_pow_right₀ (by norm_num); omega
  -- 2^{n+1-k} < 2^{n+1} since n+1-k < n+1 (k ≥ 1)
  have hhi : (2:ℝ) ^ (n + 1 - k) < (2:ℝ) ^ (n + 1) := by
    apply pow_lt_pow_right₀ (by norm_num); omega
  have hpos : (0:ℝ) < (2:ℝ) ^ (n + 1 - k) := by positivity
  constructor
  · apply div_pos <;> linarith
  · rw [div_lt_one (by linarith)]
    linarith

/-- The unscaled dyadic list `[2^n, 2^{n-1}, …, 2, 1]` (length `n+1`). -/
noncomputable def dyadicList (n : ℕ) : List ℝ :=
  (List.range (n + 1)).map (fun i => (2 : ℝ) ^ (n - i))

/-- `Q` is obtained from `dyadicList n` by at most `n` cuts (each replacing one
piece `s` by two nonnegative pieces summing to `s`).  We phrase it as: there is
a chain of at most `n` single-cut steps from `dyadicList n` to `Q`.  A single cut
step relates multisets. -/
inductive RefinesByAtMostNCuts : List ℝ → ℕ → List ℝ → Prop
  /-- No cuts: `Q` is a permutation of the base list. -/
  | base {base Q : List ℝ} (h : Q.Perm base) : RefinesByAtMostNCuts base 0 Q
  /-- Spend a cut budget without cutting. -/
  | skip {base Q : List ℝ} {k : ℕ} (h : RefinesByAtMostNCuts base k Q) :
      RefinesByAtMostNCuts base (k + 1) Q
  /-- Cut: replace one occurrence of `s = s₁ + s₂` (both ≥ 0) by `s₁, s₂`. -/
  | cut {base Q Q' : List ℝ} {k : ℕ} {s s₁ s₂ : ℝ}
      (hs : s = s₁ + s₂) (h1 : 0 ≤ s₁) (h2 : 0 ≤ s₂)
      (hstep : Q'.Perm (s₁ :: s₂ :: Q.erase s)) (hmem : s ∈ Q)
      (h : RefinesByAtMostNCuts base k Q) :
      RefinesByAtMostNCuts base (k + 1) Q'

/-- Cons recursion for `altSum`: prepending flips all later signs. -/
theorem altSum_cons (a : ℝ) (l : List ℝ) :
    altSum (a :: l) = a - altSum l := by
  unfold altSum
  rw [List.zipIdx_cons']
  simp only [List.map_cons, List.map_map, List.sum_cons, Nat.zero_mod,
    if_pos]
  have : (List.map ((fun p => if p.2 % 2 = 0 then p.1 else -p.1) ∘
      Prod.map id (fun x => x + 1)) l.zipIdx) =
      List.map (fun x => -x)
        (List.map (fun p => if p.2 % 2 = 0 then p.1 else -p.1) l.zipIdx) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, Prod.map_snd, id_eq, Prod.map_fst]
    by_cases h : p.2 % 2 = 0
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega), neg_neg]
  rw [this, ← List.sum_neg]
  ring

/-- `dyadicList (n+1) = 2^(n+1) :: dyadicList n`. -/
theorem dyadicList_succ (n : ℕ) :
    dyadicList (n + 1) = (2 : ℝ) ^ (n + 1) :: dyadicList n := by
  unfold dyadicList
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.sub_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  congr 1
  omega

/-- Invariant: `1 ≤ altSum (dyadicList n) ≤ 2^n` (preserved by the recursion
`f(n+1) = 2^(n+1) - f(n)`). -/
theorem altSum_dyadicList_bounds (n : ℕ) :
    1 ≤ altSum (dyadicList n) ∧ altSum (dyadicList n) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero =>
    -- dyadicList 0 = [1]
    unfold dyadicList
    simp [altSum]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [dyadicList_succ, altSum_cons]
    have hp : (0:ℝ) < (2:ℝ) ^ n := by positivity
    have hpow : (2:ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    constructor
    · -- 1 ≤ 2^(n+1) - altSum (dyadicList n)
      -- = 2*2^n - f(n) ≥ 2*2^n - 2^n = 2^n ≥ 1
      have h1 : (1:ℝ) ≤ (2:ℝ) ^ n := one_le_pow₀ (by norm_num)
      nlinarith [ih1, ih2]
    · -- 2^(n+1) - altSum (dyadicList n) ≤ 2^(n+1)
      nlinarith [ih1]

/-- Closed-form lower bound: `altSum (dyadicList n) ≥ 1` for the raw list. -/
theorem altSum_dyadicList_raw_ge_one (n : ℕ) :
    1 ≤ altSum (dyadicList n) := (altSum_dyadicList_bounds n).1

/-- The base dyadic list is already sorted in non-increasing order. -/
theorem dyadicList_pairwise_ge (n : ℕ) :
    List.Pairwise (· ≥ ·) (dyadicList n) := by
  unfold dyadicList
  rw [List.pairwise_map]
  have hlt : List.Pairwise (fun x1 x2 => x1 < x2) (List.range (n + 1)) :=
    List.pairwise_lt_range
  refine hlt.imp ?_
  intro a b hab
  -- a < b ⟹ 2^(n-a) ≥ 2^(n-b)
  show (2 : ℝ) ^ (n - a) ≥ (2 : ℝ) ^ (n - b)
  apply pow_le_pow_right₀ (by norm_num)
  omega

/-- The alternating sum of the base dyadic list is at least `1`. -/
theorem altSum_dyadicList_ge_one (n : ℕ) (hn : 0 < n) :
    1 ≤ altSum ((dyadicList n).mergeSort (· ≥ ·)) := by
  have hmr := List.mergeSort_eq_self (r := (· ≥ ·)) (dyadicList_pairwise_ge n)
  rw [hmr]
  exact altSum_dyadicList_raw_ge_one n


/-- Layer A: a piece remembering which original dyadic stick `2^exp` it was cut from. -/
structure LPiece (n : ℕ) where
  exp : Fin (n + 1)
  len : ℝ

noncomputable instance {n : ℕ} : DecidableEq (LPiece n) := Classical.decEq _

/-- Sum of lengths of all pieces with a given label. -/
noncomputable def labelSum {n : ℕ} (R : List (LPiece n)) (e : Fin (n + 1)) : ℝ :=
  ((R.filter (fun p => p.exp = e)).map (·.len)).sum

/-- The labelled version of `dyadicList n`: piece `i` has exponent `n-i` and length `2^(n-i)`. -/
noncomputable def labelledDyadicList (n : ℕ) : List (LPiece n) :=
  (List.range (n + 1)).map (fun i => { exp := ⟨n - i, by omega⟩, len := (2 : ℝ) ^ (n - i) })

/-- Cut one labelled piece `p` into two children of the same label with lengths `s₁, s₂`. -/
noncomputable def cutLabelledPiece {n : ℕ} (R : List (LPiece n)) (p : LPiece n) (s₁ s₂ : ℝ) :
    List (LPiece n) :=
  { exp := p.exp, len := s₁ } :: { exp := p.exp, len := s₂ } :: R.erase p

/-- The length-projection of the labelled dyadic list is a permutation of `dyadicList n`. -/
theorem labelledDyadicList_map_len_perm (n : ℕ) :
    ((labelledDyadicList n).map (·.len)).Perm (dyadicList n) := by
  unfold labelledDyadicList dyadicList
  rw [List.map_map]
  rfl

/-- `labelSum` is permutation-invariant. -/
theorem labelSum_eq_of_perm {n : ℕ} {R R' : List (LPiece n)} (h : R.Perm R')
    (e : Fin (n + 1)) : labelSum R e = labelSum R' e := by
  unfold labelSum
  exact ((h.filter _).map _).sum_eq

/-- Each label `e` appears exactly once in `labelledDyadicList n`, with length `2^e`. -/
theorem labelledDyadicList_labelSum (n : ℕ) (e : Fin (n + 1)) :
    labelSum (labelledDyadicList n) e = (2 : ℝ) ^ (e : ℕ) := by
  classical
  unfold labelSum labelledDyadicList
  rw [List.filter_map, List.map_map]
  have hk : (e : ℕ) ≤ n := by have := e.isLt; omega
  -- The filtered range: elements i with (⟨n-i,_⟩ = e), i.e. n - i = e.
  have hfilter : ((List.range (n + 1)).filter
      ((fun p : LPiece n => decide (p.exp = e)) ∘
        fun i => { exp := ⟨n - i, by omega⟩, len := (2 : ℝ) ^ (n - i) }))
      = [n - (e : ℕ)] := by
    have hcongr : ((List.range (n + 1)).filter
        ((fun p : LPiece n => decide (p.exp = e)) ∘
          fun i => { exp := ⟨n - i, by omega⟩, len := (2 : ℝ) ^ (n - i) }))
        = (List.range (n + 1)).filter (fun i => decide (i = n - (e : ℕ))) := by
      apply List.filter_congr
      intro i hi
      rw [List.mem_range] at hi
      simp only [Function.comp_apply, Fin.ext_iff]
      congr 1
      apply propext
      constructor
      · intro h; omega
      · intro h; omega
    rw [hcongr]
    rw [List.filter_eq]
    rw [List.count_range]
    rw [if_pos (by omega)]
    rfl
  rw [hfilter]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Function.comp_apply]
  congr 1
  omega

/-- Cutting a piece into two same-label children preserves every label sum. -/
theorem labelSum_cut_same_label {n : ℕ} {R : List (LPiece n)} {p : LPiece n}
    (hp : p ∈ R) (s₁ s₂ : ℝ) (hs : p.len = s₁ + s₂) (e : Fin (n + 1)) :
    labelSum (cutLabelledPiece R p s₁ s₂) e = labelSum R e := by
  classical
  have hR : R.Perm (p :: R.erase p) := List.perm_cons_erase hp
  rw [labelSum_eq_of_perm hR e]
  unfold labelSum cutLabelledPiece
  simp only [List.filter_cons]
  by_cases h : p.exp = e
  · rw [if_pos (by simp [h]), if_pos (by simp [h]), if_pos (by simp [h])]
    simp only [List.map_cons, List.sum_cons]
    rw [hs]; ring
  · rw [if_neg (by simp [h]), if_neg (by simp [h]), if_neg (by simp [h])]

/-- The length-projection of a cut is the corresponding real cut permutation. -/
theorem map_len_cutLabelledPiece_perm {n : ℕ} {R : List (LPiece n)} {p : LPiece n}
    (hp : p ∈ R) (s₁ s₂ : ℝ) :
    ((cutLabelledPiece R p s₁ s₂).map (·.len)).Perm
      (s₁ :: s₂ :: (R.map (·.len)).erase p.len) := by
  classical
  unfold cutLabelledPiece
  simp only [List.map_cons]
  refine (List.Perm.cons _ (List.Perm.cons _ ?_))
  -- remains: ((R.erase p).map (·.len)).Perm ((R.map (·.len)).erase p.len)
  set f : LPiece n → ℝ := (·.len) with hf
  -- R ~ p :: R.erase p
  have h1 : R.Perm (p :: R.erase p) := List.perm_cons_erase hp
  -- map it
  have h2 : (R.map f).Perm (f p :: (R.erase p).map f) := by
    have := h1.map f
    simpa using this
  -- (R.map f) ~ f p :: (R.map f).erase (f p)
  have hmem : f p ∈ R.map f := List.mem_map.mpr ⟨p, hp, rfl⟩
  have h3 : (R.map f).Perm (f p :: (R.map f).erase (f p)) := List.perm_cons_erase hmem
  -- Combine: f p :: (R.erase p).map f ~ f p :: (R.map f).erase (f p)
  have h4 : (f p :: (R.erase p).map f).Perm (f p :: (R.map f).erase (f p)) :=
    h2.symm.trans h3
  exact (List.Perm.cons_inv h4)

/-- Given a permutation between `R`'s length-projection and `Q`, any member of `Q`
comes from a labelled piece in `R`. -/
theorem exists_lpiece_of_len_mem_of_perm {n : ℕ} {R : List (LPiece n)} {Q : List ℝ}
    {s : ℝ} (hperm : (R.map (·.len)).Perm Q) (hmem : s ∈ Q) : ∃ p ∈ R, p.len = s := by
  have : s ∈ R.map (·.len) := hperm.mem_iff.mpr hmem
  rw [List.mem_map] at this
  obtain ⟨p, hp, hpl⟩ := this
  exact ⟨p, hp, hpl⟩

/-- Layer D helper: sum of the first `r` powers of two. -/
theorem sum_powers_two_lt (r : ℕ) :
    (∑ i ∈ Finset.range r, (2 : ℤ) ^ i) = (2 : ℤ) ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ, ih]; ring

/-- Layer D: a nonzero `±1/0`-signed dyadic sum has absolute value at least `1`. -/
theorem one_le_abs_signed_sum_powers_two {n : ℕ} (χ : Fin (n + 1) → ℤ)
    (hcoeff : ∀ e, χ e = -1 ∨ χ e = 0 ∨ χ e = 1) (hnz : ∃ e, χ e ≠ 0) :
    1 ≤ |∑ e : Fin (n + 1), χ e * (2 : ℤ) ^ (e : ℕ)| := by
  classical
  -- S = set of indices where χ is nonzero
  set S : Finset (Fin (n + 1)) := Finset.univ.filter (fun e => χ e ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨e, he⟩ := hnz
    exact ⟨e, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ e, he⟩⟩
  -- r = max index with χ r ≠ 0
  set r : Fin (n + 1) := S.max' hSne with hr
  have hrmem : r ∈ S := S.max'_mem hSne
  have hrnz : χ r ≠ 0 := by
    have := hrmem; rw [hS, Finset.mem_filter] at this; exact this.2
  -- for e > r, χ e = 0
  have hzero : ∀ e : Fin (n + 1), (r : ℕ) < (e : ℕ) → χ e = 0 := by
    intro e he
    by_contra hne
    have : e ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ e, hne⟩
    have := S.le_max' e this
    -- r = max', so e ≤ r, contradiction with r < e
    have : (e : ℕ) ≤ (r : ℕ) := by exact_mod_cast (Fin.le_def.mp this)
    omega
  -- Split the sum: term at r plus the rest
  -- The rest = ∑ over e ≠ r. For e > r it's 0; for e < r bounded by 2^e.
  -- Define the full sum T
  set T : ℤ := ∑ e : Fin (n + 1), χ e * (2 : ℤ) ^ (e : ℕ) with hT
  -- Isolate the r term
  have hsplit : T = χ r * (2 : ℤ) ^ (r : ℕ)
      + ∑ e ∈ Finset.univ.erase r, χ e * (2 : ℤ) ^ (e : ℕ) := by
    rw [hT, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r)]
  -- Bound the rest
  set R : ℤ := ∑ e ∈ Finset.univ.erase r, χ e * (2 : ℤ) ^ (e : ℕ) with hR
  -- |R| ≤ ∑_{e < r} 2^e = 2^r - 1
  have hRbound : |R| ≤ (2 : ℤ) ^ (r : ℕ) - 1 := by
    -- |R| ≤ ∑ |χ e * 2^e|
    calc |R| ≤ ∑ e ∈ Finset.univ.erase r, |χ e * (2 : ℤ) ^ (e : ℕ)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Finset.univ.erase r,
            (if (e : ℕ) < (r : ℕ) then (2 : ℤ) ^ (e : ℕ) else 0) := by
            apply Finset.sum_le_sum
            intro e he
            rw [Finset.mem_erase] at he
            have hene : e ≠ r := he.1
            -- e ≠ r; either e < r or e > r
            rcases lt_trichotomy (e : ℕ) (r : ℕ) with hlt | heq | hgt
            · rw [if_pos hlt]
              rw [abs_mul]
              have hp : |(2 : ℤ) ^ (e : ℕ)| = (2 : ℤ) ^ (e : ℕ) := by
                rw [abs_of_nonneg]; positivity
              rw [hp]
              have hc : |χ e| ≤ 1 := by
                rcases hcoeff e with h | h | h <;> rw [h] <;> norm_num
              nlinarith [pow_nonneg (by norm_num : (0:ℤ) ≤ 2) (e:ℕ)]
            · exfalso; apply hene; exact Fin.ext heq
            · rw [if_neg (by omega)]
              rw [hzero e hgt]; simp
      _ ≤ ∑ e : Fin (n + 1),
            (if (e : ℕ) < (r : ℕ) then (2 : ℤ) ^ (e : ℕ) else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro e _ _
            split <;> positivity
      _ = ∑ e ∈ Finset.range (n + 1),
            (if e < (r : ℕ) then (2 : ℤ) ^ e else 0) := by
            rw [Fin.sum_univ_eq_sum_range (fun e => if e < (r : ℕ) then (2 : ℤ) ^ e else 0)]
      _ = ∑ e ∈ Finset.range (r : ℕ), (2 : ℤ) ^ e := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
            congr 1
            ext e
            simp only [Finset.mem_filter, Finset.mem_range]
            constructor
            · rintro ⟨_, h⟩; exact h
            · intro h
              have : (r : ℕ) < n + 1 := r.2
              exact ⟨by omega, h⟩
      _ = (2 : ℤ) ^ (r : ℕ) - 1 := sum_powers_two_lt _
  -- |χ r| = 1
  have hcr : |χ r| = 1 := by
    rcases hcoeff r with h | h | h
    · rw [h]; norm_num
    · exact absurd h hrnz
    · rw [h]; norm_num
  -- reverse triangle inequality
  have hterm : |χ r * (2 : ℤ) ^ (r : ℕ)| = (2 : ℤ) ^ (r : ℕ) := by
    rw [abs_mul, hcr, one_mul, abs_of_nonneg]; positivity
  rw [hsplit]
  have hrev : |χ r * (2 : ℤ) ^ (r : ℕ)| - |R| ≤ |χ r * (2 : ℤ) ^ (r : ℕ) + R| := by
    have h := abs_sub_abs_le_abs_sub (χ r * (2 : ℤ) ^ (r : ℕ)) (-R)
    have h2 : χ r * (2 : ℤ) ^ (r : ℕ) - -R = χ r * (2 : ℤ) ^ (r : ℕ) + R := by ring
    rw [h2, abs_neg] at h
    linarith
  rw [hterm] at hrev
  linarith [hRbound, hrev]

/-- Layer D (real cast). -/
theorem one_le_abs_signed_sum_powers_two_real {n : ℕ} (χ : Fin (n + 1) → ℤ)
    (hcoeff : ∀ e, χ e = -1 ∨ χ e = 0 ∨ χ e = 1) (hnz : ∃ e, χ e ≠ 0) :
    (1 : ℝ) ≤ |∑ e : Fin (n + 1), (χ e : ℝ) * (2 : ℝ) ^ (e : ℕ)| := by
  have hint := one_le_abs_signed_sum_powers_two χ hcoeff hnz
  have hcast : (∑ e : Fin (n + 1), (χ e : ℝ) * (2 : ℝ) ^ (e : ℕ))
      = ((∑ e : Fin (n + 1), χ e * (2 : ℤ) ^ (e : ℕ) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hcast, ← Int.cast_abs]
  have h1 : (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
  rw [h1]
  exact_mod_cast hint

/-- Layer B: the adjacent defect of a list (pair up `[0,1],[2,3],…`, trailing singleton). -/
noncomputable def adjacentDefect : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: y :: t => |x - y| + adjacentDefect t

/-- For a sorted-descending list of nonnegatives, adjacent defect equals `altSum`. -/
theorem adjacentDefect_eq_altSum_of_sorted_nonneg (l : List ℝ)
    (hge : List.Pairwise (· ≥ ·) l) (hnn : ∀ x ∈ l, 0 ≤ x) :
    adjacentDefect l = altSum l := by
  induction l using adjacentDefect.induct with
  | case1 =>
    simp [adjacentDefect, altSum]
  | case2 x =>
    -- singleton
    simp only [adjacentDefect]
    have : altSum [x] = x := by simp [altSum]
    rw [this]
  | case3 x y t ih =>
    -- x :: y :: t
    simp only [adjacentDefect]
    have hxy : x ≥ y := by
      rw [List.pairwise_cons] at hge
      exact hge.1 y (by simp)
    have hge' : List.Pairwise (· ≥ ·) t := by
      rw [List.pairwise_cons, List.pairwise_cons] at hge
      exact hge.2.2
    have hnn' : ∀ z ∈ t, 0 ≤ z := fun z hz => hnn z (by simp [hz])
    rw [ih hge' hnn']
    rw [altSum_cons, altSum_cons]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
    ring


/-- **Layer A.** Any `≤ k`-cut refinement of `dyadicList n` lifts to a labelled
list `R` whose length-projection is a permutation of `Q`, all lengths `≥ 0`,
every label sum is `2^e`, and `R.length ≤ (n+1) + k`. -/
theorem exists_labelled_refinement (n k : ℕ) (Q : List ℝ)
    (hQ : RefinesByAtMostNCuts (dyadicList n) k Q) :
    ∃ R : List (LPiece n), (R.map (·.len)).Perm Q ∧ (∀ p ∈ R, 0 ≤ p.len)
      ∧ (∀ e : Fin (n + 1), labelSum R e = (2 : ℝ) ^ (e : ℕ))
      ∧ R.length ≤ (n + 1) + k := by
  induction hQ with
  | base h =>
      refine ⟨labelledDyadicList n, ?_, ?_, ?_, ?_⟩
      · exact (labelledDyadicList_map_len_perm n).trans h.symm
      · intro p hp
        unfold labelledDyadicList at hp
        rw [List.mem_map] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        positivity
      · exact labelledDyadicList_labelSum n
      · simp [labelledDyadicList, List.length_map, List.length_range]
  | skip h ih =>
      obtain ⟨R, hperm, hnn, hlab, hlen⟩ := ih
      exact ⟨R, hperm, hnn, hlab, by omega⟩
  | cut hs h1 h2 hstep hmem h ih =>
      rename_i s s₁ s₂
      obtain ⟨R, hperm, hnn, hlab, hlen⟩ := ih
      obtain ⟨p, hp, hpl⟩ := exists_lpiece_of_len_mem_of_perm hperm hmem
      refine ⟨cutLabelledPiece R p s₁ s₂, ?_, ?_, ?_, ?_⟩
      · rename_i Qpre _ _
        have hmp := map_len_cutLabelledPiece_perm hp s₁ s₂
        have herase : ((R.map (·.len)).erase p.len).Perm (Qpre.erase s) := by
          rw [hpl]; exact hperm.erase _
        have hchain : ((cutLabelledPiece R p s₁ s₂).map (·.len)).Perm
            (s₁ :: s₂ :: Qpre.erase s) :=
          hmp.trans ((herase.cons _).cons _)
        exact hchain.trans hstep.symm
      · intro q hq
        simp only [cutLabelledPiece, List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact h1
        · exact h2
        · exact hnn q (List.mem_of_mem_erase hq)
      · intro e
        rw [labelSum_cut_same_label hp s₁ s₂ (by rw [hpl, hs]) e]
        exact hlab e
      · unfold cutLabelledPiece
        simp only [List.length_cons]
        have hlener : (R.erase p).length = R.length - 1 := List.length_erase_of_mem hp
        have hRpos : 1 ≤ R.length := List.length_pos_of_mem hp
        omega


/-- A pairing of a labelled list `R`: a list of disjoint pairs plus an optional
leftover singleton, together forming a permutation of `R`. -/
structure LPairing (n : ℕ) (R : List (LPiece n)) where
  pairs : List (LPiece n × LPiece n)
  single : Option (LPiece n)
  perm : ((pairs.flatMap (fun p => [p.1, p.2])) ++ single.toList).Perm R

/-- The defect (matching cost) of a pairing. -/
noncomputable def LPairing.defect {n : ℕ} {R : List (LPiece n)} (C : LPairing n R) : ℝ :=
  (C.pairs.map (fun p => |p.1.len - p.2.len|)).sum
    + (C.single.toList.map (·.len)).sum

/-- Length count for a pairing. -/
theorem LPairing_length_eq {n : ℕ} {R : List (LPiece n)} (C : LPairing n R) :
    R.length = 2 * C.pairs.length + C.single.toList.length := by
  have h := C.perm.length_eq.symm
  have hmap : (C.pairs.map (fun a : LPiece n × LPiece n => [a.1, a.2].length))
      = C.pairs.map (fun _ => 2) := by
    apply List.map_congr_left; intro a _; rfl
  simp only [List.length_append, List.length_flatMap, hmap,
    List.map_const', List.sum_replicate, smul_eq_mul] at h
  omega

/-- If `R` is short, the pairing has `≤ n` pairs. -/
theorem LPairing_pairs_length_le_n {n : ℕ} {R : List (LPiece n)} (C : LPairing n R)
    (hRlen : R.length ≤ 2 * n + 1) : C.pairs.length ≤ n := by
  have := LPairing_length_eq C; omega

/-- Lift `R` so its length-projection is exactly `Q` sorted descending. -/
theorem exists_labelled_list_with_sorted_lengths {n : ℕ} {R : List (LPiece n)} {Q : List ℝ}
    (hperm : (R.map (·.len)).Perm Q) :
    ∃ R' : List (LPiece n), R'.Perm R ∧ R'.map (·.len) = Q.mergeSort (· ≥ ·) := by
  classical
  set S : List ℝ := Q.mergeSort (· ≥ ·) with hSdef
  have hSQ : S.Perm Q := List.mergeSort_perm Q _
  have hRS : (R.map (·.len)).Perm S := hperm.trans hSQ.symm
  have hgen : ∀ (t : List ℝ) (l : List (LPiece n)), (l.map (·.len)).Perm t →
      ∃ l' : List (LPiece n), l'.Perm l ∧ l'.map (·.len) = t := by
    intro t
    induction t with
    | nil =>
      intro l h
      have hmap : l.map (·.len) = [] := List.Perm.eq_nil h
      have hl : l = [] := List.map_eq_nil_iff.mp hmap
      refine ⟨([] : List (LPiece n)), ?_, ?_⟩
      · rw [hl]
      · simp
    | cons a t ih =>
      intro l h
      have ha : a ∈ l.map (·.len) := h.mem_iff.mpr (by simp)
      rw [List.mem_map] at ha
      obtain ⟨p, hp, hpa⟩ := ha
      have hcons : l.Perm (p :: l.erase p) := List.perm_cons_erase hp
      have h2 : ((p :: l.erase p).map (·.len)).Perm (a :: t) := (hcons.map _).symm.trans h
      simp only [List.map_cons] at h2
      rw [hpa] at h2
      have h3 : ((l.erase p).map (·.len)).Perm t := List.Perm.cons_inv h2
      obtain ⟨l', hl'perm, hl'map⟩ := ih (l.erase p) h3
      refine ⟨p :: l', ?_, ?_⟩
      · exact (List.Perm.cons p hl'perm).trans hcons.symm
      · simp only [List.map_cons, hl'map, hpa]
  obtain ⟨R', hp, hm⟩ := hgen S R hRS
  exact ⟨R', hp, hm⟩

/-- The adjacent pairing of `R`: `R[0],R[1] ; R[2],R[3] ; …`, singleton if odd. -/
noncomputable def adjacentLPairing {n : ℕ} : (R : List (LPiece n)) → LPairing n R
  | [] => ⟨[], none, by simp⟩
  | [x] => ⟨[], some x, by simp⟩
  | x :: y :: t =>
      let C := adjacentLPairing t
      ⟨(x, y) :: C.pairs, C.single, by
        have h := C.perm
        simp only [List.flatMap_cons, List.cons_append,
          List.nil_append] at *
        exact (h.cons y).cons x⟩

/-- The adjacent pairing's defect equals `altSum` of the sorted lengths. -/
theorem adjacent_defect_eq_altSum {n : ℕ} {R : List (LPiece n)} {Q : List ℝ}
    (hmap : R.map (·.len) = Q.mergeSort (· ≥ ·))
    (hge : List.Pairwise (· ≥ ·) (Q.mergeSort (· ≥ ·)))
    (hnn : ∀ x ∈ Q.mergeSort (· ≥ ·), 0 ≤ x) :
    (adjacentLPairing R).defect = altSum (Q.mergeSort (· ≥ ·)) := by
  have hkey : ∀ (S : List (LPiece n)),
      (adjacentLPairing S).defect = adjacentDefect (S.map (·.len)) := by
    intro S
    induction S using adjacentLPairing.induct with
    | case1 => simp [adjacentLPairing, LPairing.defect, adjacentDefect]
    | case2 x => simp [adjacentLPairing, LPairing.defect, adjacentDefect]
    | case3 x y t ih =>
        simp only [adjacentLPairing, LPairing.defect, List.map_cons,
          List.sum_cons] at *
        rw [adjacentDefect]
        rw [← ih]
        ring
  rw [hkey R, hmap]
  exact adjacentDefect_eq_altSum_of_sorted_nonneg _ hge hnn


/-- Edge list on `Fin N`. -/
abbrev EdgeList (N : ℕ) := List (Fin N × Fin N)

/-- Degree of a vertex `v` in an edge list: number of endpoints equal to `v`. -/
def edgeDegree {N : ℕ} (E : EdgeList N) (v : Fin N) : ℕ :=
  (E.filter (fun e => e.1 = v)).length + (E.filter (fun e => e.2 = v)).length

/-- Handshake lemma: the sum of degrees is twice the number of edges. -/
theorem sum_edgeDegree {N : ℕ} (E : EdgeList N) :
    (∑ v : Fin N, edgeDegree E v) = 2 * E.length := by
  classical
  have key : ∀ (f : Fin N × Fin N → Fin N) (L : List (Fin N × Fin N)),
      (∑ v : Fin N, (L.filter (fun e => decide (f e = v))).length) = L.length := by
    intro f L
    induction L with
    | nil => simp
    | cons e t ih =>
      have hstep : ∀ v : Fin N,
          ((e :: t).filter (fun x => decide (f x = v))).length
            = (if f e = v then 1 else 0) + (t.filter (fun x => decide (f x = v))).length := by
        intro v
        rw [List.filter_cons]
        by_cases h : f e = v
        · rw [if_pos (by simp [h]), if_pos h]
          simp [Nat.add_comm]
        · rw [if_neg (by simp [h]), if_neg h]
          simp
      simp only [hstep]
      rw [Finset.sum_add_distrib, ih]
      have hsum : (∑ v : Fin N, (if f e = v then (1 : ℕ) else 0)) = 1 := by
        rw [Finset.sum_ite_eq Finset.univ (f e) (fun _ => (1 : ℕ))]
        rw [if_pos (Finset.mem_univ _)]
      rw [hsum, List.length_cons]
      ring
  unfold edgeDegree
  rw [Finset.sum_add_distrib]
  rw [key Prod.fst E, key Prod.snd E]
  ring

/-- With fewer edges than vertices, some vertex has degree at most `1`. -/
theorem exists_low_degree {N : ℕ} (hN : 0 < N) (E : EdgeList N) (hE : E.length < N) :
    ∃ v : Fin N, edgeDegree E v ≤ 1 := by
  classical
  by_contra h
  push_neg at h
  have h2 : ∀ v : Fin N, 2 ≤ edgeDegree E v := by
    intro v; have := h v; omega
  have hsumle : (∑ v : Fin N, (2 : ℕ)) ≤ ∑ v : Fin N, edgeDegree E v :=
    Finset.sum_le_sum (fun v _ => h2 v)
  rw [sum_edgeDegree] at hsumle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_comm] at hsumle
  omega

/-- Sum of degrees over an active set `S` containing all edge endpoints equals
`2 * E.length`. -/
theorem sum_edgeDegree_over_finset {N : ℕ} (S : Finset (Fin N)) (E : EdgeList N)
    (hmem : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) :
    (∑ v ∈ S, edgeDegree E v) = 2 * E.length := by
  classical
  rw [← sum_edgeDegree E]
  apply Finset.sum_subset (Finset.subset_univ S)
  intro v _ hvS
  -- v ∉ S ⟹ edgeDegree E v = 0: no edge endpoint equals v
  unfold edgeDegree
  have h1 : E.filter (fun e => e.1 = v) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hev
    simp only [decide_eq_true_eq] at hev
    have := (hmem e he).1
    rw [hev] at this; exact hvS this
  have h2 : E.filter (fun e => e.2 = v) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hev
    simp only [decide_eq_true_eq] at hev
    have := (hmem e he).2
    rw [hev] at this; exact hvS this
  rw [h1, h2]; simp

/-- With fewer edges than active vertices, some active vertex has degree `≤ 1`. -/
theorem exists_low_degree_in_finset {N : ℕ} (S : Finset (Fin N)) (E : EdgeList N)
    (hmem : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (hE : E.length < S.card) :
    ∃ v ∈ S, edgeDegree E v ≤ 1 := by
  classical
  by_contra h
  push_neg at h
  have h2 : ∀ v ∈ S, 2 ≤ edgeDegree E v := by
    intro v hv; have := h v hv; omega
  have hsumle : (∑ v ∈ S, (2 : ℕ)) ≤ ∑ v ∈ S, edgeDegree E v :=
    Finset.sum_le_sum h2
  rw [sum_edgeDegree_over_finset S E hmem] at hsumle
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] at hsumle
  omega

/-- Finset-parametrized signed coloring: over the active vertex set `S`, with all
edge endpoints in `S` and fewer edges than active vertices, there is a signed
coloring supported on `S`, nonzero somewhere on `S`, respecting every edge. Proved
by strong induction on `S.card` deleting a low-degree vertex. -/
theorem signed_coloring_on_finset {N : ℕ} (S : Finset (Fin N)) (E : EdgeList N)
    (hmem : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (hSne : S.Nonempty)
    (hE : E.length < S.card) :
    ∃ χ : Fin N → ℤ,
      (∀ v, v ∉ S → χ v = 0) ∧
      (∃ v ∈ S, χ v ≠ 0) ∧ (∀ v, χ v = -1 ∨ χ v = 0 ∨ χ v = 1) ∧
      (∀ e ∈ E, χ e.1 = 0 ↔ χ e.2 = 0) ∧
      (∀ e ∈ E, χ e.1 ≠ 0 → χ e.1 + χ e.2 = 0) := by
  classical
  suffices H : ∀ m (S : Finset (Fin N)) (E : EdgeList N), S.card = m →
      (∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) → S.Nonempty → E.length < S.card →
      ∃ χ : Fin N → ℤ,
        (∀ v, v ∉ S → χ v = 0) ∧
        (∃ v ∈ S, χ v ≠ 0) ∧ (∀ v, χ v = -1 ∨ χ v = 0 ∨ χ v = 1) ∧
        (∀ e ∈ E, χ e.1 = 0 ↔ χ e.2 = 0) ∧
        (∀ e ∈ E, χ e.1 ≠ 0 → χ e.1 + χ e.2 = 0) by
    exact H S.card S E rfl hmem hSne hE
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro S E hcard hmem hSne hE
    -- Step 1: low degree vertex
    obtain ⟨v, hvS, hvdeg⟩ := exists_low_degree_in_finset S E hmem hE
    -- E' keeps edges not touching v
    set E' : EdgeList N := E.filter (fun e => decide (e.1 ≠ v ∧ e.2 ≠ v)) with hE'def
    -- membership for E'
    have hmem' : ∀ e ∈ E', e.1 ∈ S \ {v} ∧ e.2 ∈ S \ {v} := by
      intro e he
      rw [hE'def, List.mem_filter] at he
      obtain ⟨heE, hcond⟩ := he
      simp only [decide_eq_true_eq] at hcond
      obtain ⟨h1, h2⟩ := hcond
      obtain ⟨hs1, hs2⟩ := hmem e heE
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hs1, h1⟩
      · rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hs2, h2⟩
    -- degree = length of filter (·.1=v) + length of filter (·.2=v)
    -- case split on degree
    have hdeg_cases : edgeDegree E v = 0 ∨ edgeDegree E v = 1 := by omega
    rcases hdeg_cases with hd0 | hd1
    · -- CASE A: degree 0
      -- both filter lists empty
      unfold edgeDegree at hd0
      have hf1 : (E.filter (fun e => e.1 = v)).length = 0 := by omega
      have hf2 : (E.filter (fun e => e.2 = v)).length = 0 := by omega
      have hnoedge : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v := by
        intro e he
        constructor
        · intro h1
          have : e ∈ E.filter (fun e => e.1 = v) := by
            rw [List.mem_filter]; exact ⟨he, by simp [h1]⟩
          rw [List.length_eq_zero_iff] at hf1
          rw [hf1] at this; simp at this
        · intro h2
          have : e ∈ E.filter (fun e => e.2 = v) := by
            rw [List.mem_filter]; exact ⟨he, by simp [h2]⟩
          rw [List.length_eq_zero_iff] at hf2
          rw [hf2] at this; simp at this
      refine ⟨fun u => if u = v then (1 : ℤ) else 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        simp only
        rw [if_neg]
        intro huv; subst huv; exact hu hvS
      · exact ⟨v, hvS, by simp⟩
      · intro u; simp only; by_cases h : u = v
        · rw [if_pos h]; right; right; rfl
        · rw [if_neg h]; right; left; rfl
      · intro e he
        obtain ⟨h1, h2⟩ := hnoedge e he
        simp only
        rw [if_neg h1, if_neg h2]
      · intro e he hne
        obtain ⟨h1, _⟩ := hnoedge e he
        simp only at hne
        rw [if_neg h1] at hne; exact absurd rfl hne
    · -- CASE B: degree 1
      unfold edgeDegree at hd1
      -- exactly one of the filters is a singleton, the other empty
      set F1 := E.filter (fun e => e.1 = v) with hF1
      set F2 := E.filter (fun e => e.2 = v) with hF2
      -- get an edge e0 touching v
      -- the touching edges filter
      have htouch : F1.length + F2.length = 1 := hd1
      -- there exists e0 in E with e0.1 = v ∨ e0.2 = v
      have hexe0 : ∃ e0 ∈ E, e0.1 = v ∨ e0.2 = v := by
        rcases Nat.eq_zero_or_pos F1.length with h1 | h1
        · -- F1 empty, F2 singleton
          have h2 : F2.length = 1 := by omega
          have : F2 ≠ [] := by
            intro h; rw [h] at h2; simp at h2
          obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil F2 this
          rw [hF2, List.mem_filter] at he0
          exact ⟨e0, he0.1, Or.inr (by simpa using he0.2)⟩
        · have : F1 ≠ [] := by
            intro h; rw [h] at h1; simp at h1
          obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil F1 this
          rw [hF1, List.mem_filter] at he0
          exact ⟨e0, he0.1, Or.inl (by simpa using he0.2)⟩
      obtain ⟨e0, he0E, he0v⟩ := hexe0
      -- neighbor w
      set w : Fin N := if e0.1 = v then e0.2 else e0.1 with hwdef
      -- w ≠ v
      have hwv : w ≠ v := by
        rw [hwdef]
        by_cases h : e0.1 = v
        · rw [if_pos h]
          intro he2
          -- both endpoints = v ⟹ degree ≥ 2
          have hin1 : e0 ∈ F1 := by rw [hF1, List.mem_filter]; exact ⟨he0E, by simp [h]⟩
          have hin2 : e0 ∈ F2 := by rw [hF2, List.mem_filter]; exact ⟨he0E, by simp [he2]⟩
          have hl1 : 1 ≤ F1.length := List.length_pos_of_mem hin1
          have hl2 : 1 ≤ F2.length := List.length_pos_of_mem hin2
          omega
        · rw [if_neg h]; exact h
      -- w ∈ S
      have hwS : w ∈ S := by
        rw [hwdef]
        by_cases h : e0.1 = v
        · rw [if_pos h]; exact (hmem e0 he0E).2
        · rw [if_neg h]; exact (hmem e0 he0E).1
      have hwSm : w ∈ S \ {v} := by
        rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hwS, hwv⟩
      -- the unique neighbor property
      have hneigh1 : ∀ e ∈ E, e.1 = v → e.2 = w := by
        intro e he he1
        -- e ∈ F1
        have hin : e ∈ F1 := by rw [hF1, List.mem_filter]; exact ⟨he, by simp [he1]⟩
        -- F1 has length 1 (since F2.length ≥ 0, and total = 1 with F1 nonempty)
        have hF1pos : 1 ≤ F1.length := List.length_pos_of_mem hin
        have hF1one : F1.length = 1 := by omega
        have hF2zero : F2.length = 0 := by omega
        -- e0 also touches v; determine e0's structure
        -- Since F1 has exactly one element, e = the unique element.
        -- Also determine that e0 ∈ F1 (since e0.1 = v because F2 empty).
        have he0F2 : e0 ∉ F2 := by
          rw [List.length_eq_zero_iff] at hF2zero
          rw [hF2zero]; simp
        have he01 : e0.1 = v := by
          rcases he0v with h | h
          · exact h
          · exfalso; apply he0F2; rw [hF2, List.mem_filter]; exact ⟨he0E, by simp [h]⟩
        have hin0 : e0 ∈ F1 := by rw [hF1, List.mem_filter]; exact ⟨he0E, by simp [he01]⟩
        -- F1 singleton ⟹ e = e0
        have : e = e0 := by
          have hlen := hF1one
          -- both e, e0 ∈ F1, length 1
          obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
          rw [ha] at hin hin0
          simp only [List.mem_singleton] at hin hin0
          rw [hin, hin0]
        rw [this, hwdef, if_pos he01]
      have hneigh2 : ∀ e ∈ E, e.2 = v → e.1 = w := by
        intro e he he2
        have hin : e ∈ F2 := by rw [hF2, List.mem_filter]; exact ⟨he, by simp [he2]⟩
        have hF2pos : 1 ≤ F2.length := List.length_pos_of_mem hin
        have hF2one : F2.length = 1 := by omega
        have hF1zero : F1.length = 0 := by omega
        have he0F1 : e0 ∉ F1 := by
          rw [List.length_eq_zero_iff] at hF1zero
          rw [hF1zero]; simp
        have he02 : e0.2 = v := by
          rcases he0v with h | h
          · exfalso; apply he0F1; rw [hF1, List.mem_filter]; exact ⟨he0E, by simp [h]⟩
          · exact h
        -- e0.1 ≠ v? If e0.1 = v then e0 ∈ F1 contra
        have he01ne : e0.1 ≠ v := by
          intro h; apply he0F1; rw [hF1, List.mem_filter]; exact ⟨he0E, by simp [h]⟩
        have hin0 : e0 ∈ F2 := by rw [hF2, List.mem_filter]; exact ⟨he0E, by simp [he02]⟩
        have : e = e0 := by
          obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hF2one
          rw [ha] at hin hin0
          simp only [List.mem_singleton] at hin hin0
          rw [hin, hin0]
        rw [this, hwdef, if_neg he01ne]
      -- E'.length < E.length: e0 ∉ E'
      have he0notE' : e0 ∉ E' := by
        rw [hE'def, List.mem_filter]
        intro ⟨_, hcond⟩
        simp only [decide_eq_true_eq] at hcond
        rcases he0v with h | h
        · exact hcond.1 h
        · exact hcond.2 h
      have hE'sub : E'.Sublist E := by rw [hE'def]; exact List.filter_sublist
      have hE'lt : E'.length < E.length := by
        rcases lt_or_eq_of_le (List.Sublist.length_le hE'sub) with h | h
        · exact h
        · exfalso
          -- if equal, E'.length = E.length ⟹ E' = E as sublist ⟹ e0 ∈ E'
          have : E' = E := List.Sublist.eq_of_length hE'sub h
          rw [this] at he0notE'
          exact he0notE' he0E
      -- card of S \ {v}
      have hcardS : (S \ {v}).card = S.card - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hvS]
      have hSvne : (S \ {v}).Nonempty := ⟨w, hwSm⟩
      have hlen' : E'.length < (S \ {v}).card := by
        rw [hcardS]; omega
      -- apply IH
      have hcardlt : (S \ {v}).card < m := by rw [hcardS, ← hcard]; omega
      obtain ⟨χ', hsupp', hnz', hcoeff', hzero', hopp'⟩ :=
        IH (S \ {v}).card hcardlt (S \ {v}) E' rfl hmem' hSvne hlen'
      -- define χ
      refine ⟨Function.update χ' v (-(χ' w)), ?_, ?_, ?_, ?_, ?_⟩
      · -- support
        intro u hu
        have huv : u ≠ v := by intro h; subst h; exact hu hvS
        rw [Function.update_of_ne huv]
        apply hsupp'
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        push_neg; intro h; exact absurd h hu
      · -- nonzero
        obtain ⟨u, huS, hune⟩ := hnz'
        have huv : u ≠ v := by
          rw [Finset.mem_sdiff, Finset.mem_singleton] at huS
          exact huS.2
        refine ⟨u, ?_, ?_⟩
        · rw [Finset.mem_sdiff, Finset.mem_singleton] at huS; exact huS.1
        · rw [Function.update_of_ne huv]; exact hune
      · -- coeff
        intro u
        by_cases h : u = v
        · rw [h, Function.update_self]
          rcases hcoeff' w with hc | hc | hc
          · rw [hc]; right; right; norm_num
          · rw [hc]; right; left; norm_num
          · rw [hc]; left; norm_num
        · rw [Function.update_of_ne h]; exact hcoeff' u
      · -- both-zero
        intro e he
        by_cases hin : e ∈ E'
        · -- e in E': endpoints ≠ v
          have hcond := hin
          rw [hE'def, List.mem_filter] at hcond
          simp only [decide_eq_true_eq] at hcond
          obtain ⟨_, h1, h2⟩ := hcond
          rw [Function.update_of_ne h1, Function.update_of_ne h2]
          exact hzero' e hin
        · -- e touches v
          have htouchv : e.1 = v ∨ e.2 = v := by
            by_contra hc
            push_neg at hc
            apply hin
            rw [hE'def, List.mem_filter]
            exact ⟨he, by simp [hc.1, hc.2]⟩
          rcases htouchv with h1 | h2
          · -- e.1 = v, e.2 = w
            have he2w : e.2 = w := hneigh1 e he h1
            rw [h1, he2w, Function.update_self, Function.update_of_ne hwv]
            constructor
            · intro h; simp only [neg_eq_zero] at h; exact h
            · intro h; rw [h]; simp
          · -- e.2 = v, e.1 = w
            have he1w : e.1 = w := hneigh2 e he h2
            rw [h2, he1w, Function.update_self, Function.update_of_ne hwv]
            constructor
            · intro h; rw [h]; simp
            · intro h; simp only [neg_eq_zero] at h; exact h
      · -- opposite
        intro e he hne1
        by_cases hin : e ∈ E'
        · have hcond := hin
          rw [hE'def, List.mem_filter] at hcond
          simp only [decide_eq_true_eq] at hcond
          obtain ⟨_, h1, h2⟩ := hcond
          rw [Function.update_of_ne h1, Function.update_of_ne h2]
          rw [Function.update_of_ne h1] at hne1
          exact hopp' e hin hne1
        · have htouchv : e.1 = v ∨ e.2 = v := by
            by_contra hc
            push_neg at hc
            apply hin
            rw [hE'def, List.mem_filter]
            exact ⟨he, by simp [hc.1, hc.2]⟩
          rcases htouchv with h1 | h2
          · have he2w : e.2 = w := hneigh1 e he h1
            rw [h1, he2w, Function.update_self, Function.update_of_ne hwv]
            ring
          · have he1w : e.1 = w := hneigh2 e he h2
            rw [h2, he1w, Function.update_self, Function.update_of_ne hwv]
            ring

/-- **Layer C.** A graph with fewer edges than vertices has a nonempty component
that can be two-colored by `χ : Fin N → ℤ` valued in `{-1,0,1}`, nonzero
somewhere, with no edge leaving the colored set, and opposite colors across each
colored edge. -/
theorem exists_signed_tree_component {N : ℕ} (hN : 0 < N) (E : EdgeList N)
    (hE : E.length < N) :
    ∃ χ : Fin N → ℤ,
      (∃ v, χ v ≠ 0) ∧ (∀ v, χ v = -1 ∨ χ v = 0 ∨ χ v = 1) ∧
      (∀ e ∈ E, χ e.1 = 0 ↔ χ e.2 = 0) ∧
      (∀ e ∈ E, χ e.1 ≠ 0 → χ e.1 + χ e.2 = 0) := by
  obtain ⟨χ, _, hnz, hcoeff, hz, hopp⟩ :=
    signed_coloring_on_finset (Finset.univ : Finset (Fin N)) E
      (fun e _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
      (by simpa [Finset.card_univ, Fintype.card_fin] using hE)
  exact ⟨χ, ⟨hnz.choose, hnz.choose_spec.2⟩, hcoeff, hz, hopp⟩


/-- **Layer E (inequality).** The absolute signed length-sum over `R` is at most
the pairing defect, when the sign function respects the pairing structure. -/
theorem abs_signed_sum_over_R_le_pairing_defect {n : ℕ} {R : List (LPiece n)}
    (C : LPairing n R) (χ : Fin (n + 1) → ℤ)
    (hcoeff : ∀ e, χ e = -1 ∨ χ e = 0 ∨ χ e = 1)
    (hz : ∀ p ∈ C.pairs, χ p.1.exp = 0 ↔ χ p.2.exp = 0)
    (hopp : ∀ p ∈ C.pairs, χ p.1.exp ≠ 0 → χ p.1.exp + χ p.2.exp = 0)
    (hnn : ∀ p ∈ R, 0 ≤ p.len) :
    |(R.map (fun p => (χ p.exp : ℝ) * p.len)).sum| ≤ C.defect := by
  classical
  set g : LPiece n → ℝ := fun p => (χ p.exp : ℝ) * p.len with hg
  set Lst : List (LPiece n) :=
    (C.pairs.flatMap (fun p => [p.1, p.2])) ++ C.single.toList with hLst
  -- Step 1: sum over R equals sum over the pairing list (permutation invariance)
  have hsum_eq : (R.map g).sum = (Lst.map g).sum := (C.perm.map g).sum_eq.symm
  -- Step 3: flatten the pairs part
  have hflat : ((C.pairs.flatMap (fun p => [p.1, p.2])).map g).sum
      = (C.pairs.map (fun p => g p.1 + g p.2)).sum := by
    induction C.pairs with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, ih]
      ring
  have habs : ∀ {ι : Type} (l : List ι) (f : ι → ℝ),
      |(l.map f).sum| ≤ (l.map (fun x => |f x|)).sum := by
    intro ι l f
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      calc |f a + (t.map f).sum| ≤ |f a| + |(t.map f).sum| := abs_add_le _ _
        _ ≤ |f a| + (t.map (fun x => |f x|)).sum := by linarith [ih]
  -- membership: elements of single.toList are in R
  have hsingle_mem : ∀ p ∈ C.single.toList, p ∈ R := by
    intro p hp
    exact C.perm.mem_iff.mp (by
      rw [List.mem_append]; exact Or.inr hp)
  -- termwise bound for pairs
  have hpairbound : ∀ p ∈ C.pairs, |g p.1 + g p.2| ≤ |p.1.len - p.2.len| := by
    intro p hp
    rcases eq_or_ne (χ p.1.exp) 0 with h0 | hne
    · -- both zero
      have h0' : χ p.2.exp = 0 := (hz p hp).mp h0
      have hz0 : g p.1 + g p.2 = 0 := by
        simp only [hg, h0, h0', Int.cast_zero, zero_mul, add_zero]
      rw [hz0, abs_zero]
      exact abs_nonneg _
    · -- opposite nonzero
      have hopp' := hopp p hp hne
      have h2 : χ p.2.exp = -χ p.1.exp := by linarith
      have hval : g p.1 + g p.2 = (χ p.1.exp : ℝ) * (p.1.len - p.2.len) := by
        simp only [hg, h2, Int.cast_neg]
        ring
      rw [hval, abs_mul]
      have hc1 : |(χ p.1.exp : ℝ)| = 1 := by
        rcases hcoeff p.1.exp with h | h | h
        · rw [h]; norm_num
        · exact absurd h hne
        · rw [h]; norm_num
      rw [hc1, one_mul]
  -- termwise bound for singles
  have hsinglebound : ∀ p ∈ C.single.toList, |g p| ≤ p.len := by
    intro p hp
    have hpR : p ∈ R := hsingle_mem p hp
    have hpnn : 0 ≤ p.len := hnn p hpR
    have hc : |(χ p.exp : ℝ)| ≤ 1 := by
      rcases hcoeff p.exp with h | h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
      · rw [h]; norm_num
    simp only [hg, abs_mul]
    calc |(χ p.exp : ℝ)| * |p.len| ≤ 1 * |p.len| := by
          gcongr
      _ = p.len := by rw [one_mul, abs_of_nonneg hpnn]
  -- Now the calc chain
  calc |(R.map g).sum|
      = |(C.pairs.map (fun p => g p.1 + g p.2)).sum
          + (C.single.toList.map g).sum| := by
        rw [hsum_eq, hLst, List.map_append, List.sum_append, hflat]
    _ ≤ (C.pairs.map (fun p => |g p.1 + g p.2|)).sum
          + (C.single.toList.map (fun p => |g p|)).sum := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        · exact habs C.pairs (fun p => g p.1 + g p.2)
        · exact habs C.single.toList g
    _ ≤ (C.pairs.map (fun p => |p.1.len - p.2.len|)).sum
          + (C.single.toList.map (·.len)).sum := by
        gcongr
        · exact List.sum_le_sum hpairbound
        · exact List.sum_le_sum hsinglebound
    _ = C.defect := rfl

/-- **Layer E (equality).** The signed length-sum over `R`, grouped by label,
equals the signed dyadic sum. -/
theorem signed_sum_over_R_eq_signed_dyadic_sum {n : ℕ} {R : List (LPiece n)}
    (hsum : ∀ e : Fin (n + 1), labelSum R e = (2 : ℝ) ^ (e : ℕ)) (χ : Fin (n + 1) → ℤ) :
    (R.map (fun p => (χ p.exp : ℝ) * p.len)).sum
      = ∑ e : Fin (n + 1), (χ e : ℝ) * (2 : ℝ) ^ (e : ℕ) := by
  classical
  have key : ∀ (S : List (LPiece n)),
      (S.map (fun p => (χ p.exp : ℝ) * p.len)).sum
        = ∑ e : Fin (n + 1), (χ e : ℝ) * labelSum S e := by
    intro S
    induction S with
    | nil => simp [labelSum]
    | cons p S ih =>
      have hls : ∀ e, labelSum (p :: S) e
          = (if p.exp = e then p.len else 0) + labelSum S e := by
        intro e
        unfold labelSum
        simp only [List.filter_cons]
        by_cases h : p.exp = e
        · rw [if_pos (by simp [h]), if_pos h]
          simp only [List.map_cons, List.sum_cons]
        · rw [if_neg (by simp [h]), if_neg h]
          simp
      simp only [List.map_cons, List.sum_cons, ih]
      have hrw : (∑ e, (χ e : ℝ) * labelSum (p :: S) e)
          = ∑ e, ((χ e : ℝ) * (if p.exp = e then p.len else 0)
            + (χ e : ℝ) * labelSum S e) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [hls]; ring
      rw [hrw, Finset.sum_add_distrib]
      have hdiag : (∑ e, (χ e : ℝ) * (if p.exp = e then p.len else 0))
          = (χ p.exp : ℝ) * p.len := by
        rw [Finset.sum_eq_single p.exp]
        · rw [if_pos rfl]
        · intro b _ hb
          rw [if_neg (Ne.symm hb), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hdiag]
  rw [key R]
  apply Finset.sum_congr rfl
  intro e _
  rw [hsum e]

/-- **Layer E (assembly).** Every pairing defect of a labelled `≤n`-cut refinement
is at least `1`. -/
theorem LPairing.defect_ge_one {n : ℕ} {R : List (LPiece n)} (hn : 0 < n)
    (hRnn : ∀ p ∈ R, 0 ≤ p.len) (hRlen : R.length ≤ 2 * n + 1)
    (hsum : ∀ e : Fin (n + 1), labelSum R e = (2 : ℝ) ^ (e : ℕ))
    (C : LPairing n R) : 1 ≤ C.defect := by
  classical
  -- Edge list from the pairing (labels of matched pairs)
  set E : EdgeList (n + 1) := C.pairs.map (fun p => (p.1.exp, p.2.exp)) with hE
  have hElen : E.length < n + 1 := by
    rw [hE, List.length_map]
    have := LPairing_pairs_length_le_n C hRlen
    omega
  obtain ⟨χ, hnzχ, hcoeff, hzedge, hoppedge⟩ :=
    exists_signed_tree_component (by omega : 0 < n + 1) E hElen
  -- translate edge conditions to pair conditions
  have hz : ∀ p ∈ C.pairs, χ p.1.exp = 0 ↔ χ p.2.exp = 0 := by
    intro p hp
    have hmem : (p.1.exp, p.2.exp) ∈ E := by
      rw [hE, List.mem_map]; exact ⟨p, hp, rfl⟩
    exact hzedge _ hmem
  have hopp : ∀ p ∈ C.pairs, χ p.1.exp ≠ 0 → χ p.1.exp + χ p.2.exp = 0 := by
    intro p hp hne
    have hmem : (p.1.exp, p.2.exp) ∈ E := by
      rw [hE, List.mem_map]; exact ⟨p, hp, rfl⟩
    exact hoppedge _ hmem hne
  -- chain: 1 ≤ |signed dyadic| = |signed sum over R| ≤ defect
  have h1 : (1 : ℝ) ≤ |∑ e : Fin (n + 1), (χ e : ℝ) * (2 : ℝ) ^ (e : ℕ)| :=
    one_le_abs_signed_sum_powers_two_real χ hcoeff hnzχ
  have heq := signed_sum_over_R_eq_signed_dyadic_sum hsum χ
  have h2 : |(R.map (fun p => (χ p.exp : ℝ) * p.len)).sum| ≤ C.defect :=
    abs_signed_sum_over_R_le_pairing_defect C χ hcoeff hz hopp hRnn
  rw [heq] at h2
  linarith


/-- **THE BLOCKING THEOREM (dyadic-refinement extremal lemma).**  Any multiset
obtained from `dyadicList n` by at most `n` cuts has alternating sum `≥ 1`. -/
theorem dyadic_refinement_alt_ge_one (n : ℕ) (hn : 0 < n) (Q : List ℝ)
    (hQnn : ∀ x ∈ Q, 0 ≤ x) (hQ : RefinesByAtMostNCuts (dyadicList n) n Q) :
    1 ≤ altSum (Q.mergeSort (· ≥ ·)) := by
  classical
  obtain ⟨R, hRperm, hRnn, hRsum, hRlen⟩ := exists_labelled_refinement n n Q hQ
  obtain ⟨R', hR'perm, hR'map⟩ := exists_labelled_list_with_sorted_lengths hRperm
  -- transport facts to R'
  have hR'nn : ∀ p ∈ R', 0 ≤ p.len := by
    intro p hp; exact hRnn p (hR'perm.mem_iff.mp hp)
  have hR'len : R'.length ≤ 2 * n + 1 := by
    rw [hR'perm.length_eq]; omega
  have hR'sum : ∀ e : Fin (n + 1), labelSum R' e = (2 : ℝ) ^ (e : ℕ) := by
    intro e; rw [labelSum_eq_of_perm hR'perm e]; exact hRsum e
  -- sortedness / nonnegativity of the sorted list
  have hsortperm : (Q.mergeSort (· ≥ ·)).Perm Q := List.mergeSort_perm Q _
  have hge : List.Pairwise (· ≥ ·) (Q.mergeSort (· ≥ ·)) := by
    apply List.sorted_mergeSort'
  have hnn : ∀ x ∈ Q.mergeSort (· ≥ ·), 0 ≤ x := by
    intro x hx; exact hQnn x (hsortperm.mem_iff.mp hx)
  -- adjacent pairing of R' has defect ≥ 1
  have hdef1 : 1 ≤ (adjacentLPairing R').defect :=
    LPairing.defect_ge_one hn hR'nn hR'len hR'sum (adjacentLPairing R')
  -- and its defect = altSum
  have hdefeq : (adjacentLPairing R').defect = altSum (Q.mergeSort (· ≥ ·)) :=
    adjacent_defect_eq_altSum hR'map hge hnn
  rw [hdefeq] at hdef1
  exact hdef1


/-- Scaling a refinement by a positive constant `c` (multiply every entry). -/
theorem refines_smul {base Q : List ℝ} {k : ℕ} (c : ℝ) (hc : 0 < c)
    (h : RefinesByAtMostNCuts base k Q) :
    RefinesByAtMostNCuts (base.map (fun x => c * x)) k (Q.map (fun x => c * x)) := by
  have hinj : Function.Injective (fun x : ℝ => c * x) := by
    intro a b hab; simpa using mul_left_cancel₀ (ne_of_gt hc) hab
  induction h with
  | base hperm =>
      exact RefinesByAtMostNCuts.base (hperm.map _)
  | skip _ ih =>
      exact RefinesByAtMostNCuts.skip ih
  | cut hs h1 h2 hstep hmem hh ih =>
      rename_i s s₁ s₂
      refine RefinesByAtMostNCuts.cut (s := c * s) (s₁ := c * s₁) (s₂ := c * s₂)
        (by rw [hs]; ring) (mul_nonneg (le_of_lt hc) h1) (mul_nonneg (le_of_lt hc) h2)
        ?_ ?_ ih
      · -- Perm of mapped Q' with (c*s₁ :: c*s₂ :: (Q.map).erase (c*s))
        have hmapstep := hstep.map (fun x : ℝ => c * x)
        simp only [List.map_cons] at hmapstep
        rw [List.map_erase hinj] at hmapstep
        exact hmapstep
      · exact List.mem_map_of_mem hmem

/-- `altSum` is homogeneous of degree 1. -/
theorem altSum_smul (c : ℝ) (l : List ℝ) :
    altSum (l.map (fun x => c * x)) = c * altSum l := by
  induction l with
  | nil => simp [altSum]
  | cons a t ih =>
      rw [List.map_cons, altSum_cons, altSum_cons, ih]
      ring

/-- Descending mergeSort commutes with scaling by a nonnegative constant. -/
theorem mergeSort_map_smul (c : ℝ) (hc : 0 ≤ c) (l : List ℝ) :
    (l.map (fun x => c * x)).mergeSort (· ≥ ·)
      = (l.mergeSort (· ≥ ·)).map (fun x => c * x) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- c = 0 : both sides are lists of zeros of the same length
    subst hc0
    -- map (0 * ·) sends everything to 0
    have hmap : ∀ (t : List ℝ), t.map (fun x => (0:ℝ) * x) = List.replicate t.length 0 := by
      intro t
      induction t with
      | nil => simp
      | cons a s ih =>
          rw [List.map_cons, ih, zero_mul, List.length_cons, List.replicate_succ]
    rw [hmap l]
    rw [hmap (l.mergeSort (· ≥ ·))]
    rw [List.length_mergeSort]
    -- mergeSort of a replicate of zeros = replicate
    -- both sides now equal; use that replicate is sorted for ≥
    have hlen : (List.replicate l.length (0:ℝ)).mergeSort (· ≥ ·)
        = List.replicate l.length 0 := by
      apply List.mergeSort_eq_self
      apply List.pairwise_replicate.mpr
      right; exact le_refl 0
    rw [hlen]
  · -- c > 0 : use List.map_mergeSort
    symm
    apply List.map_mergeSort
    intro a _ b _
    simp only [decide_eq_decide, ge_iff_le]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h (le_of_lt hcpos)
    · intro h; exact le_of_mul_le_mul_left h hcpos

/-- Consecutive-difference list of `m` (as used in `pieceLengths`). -/
noncomputable def diffs (m : List ℝ) : List ℝ :=
  List.zipWith (fun a b => b - a) m m.tail

/-- `pieceLengths S = diffs (0 :: S.sort ++ [1])`. -/
theorem pieceLengths_eq_diffs (S : Finset ℝ) :
    pieceLengths S = diffs ((0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]) := rfl

/-- `diffs (x :: y :: t) = (y - x) :: diffs (y :: t)`. -/
theorem diffs_cons_cons (x y : ℝ) (t : List ℝ) :
    diffs (x :: y :: t) = (y - x) :: diffs (y :: t) := by
  simp only [diffs, List.tail_cons, List.zipWith_cons_cons]

/-- **Core list lemma (add-s form).** Insert `b` into a pairwise-`≤` list `m` in
the interior (head `< b < ` last), so `orderedInsert (≤) b m` splits one gap `s`
into `s₁ + s₂` (both `≥ 0`).  We state it with `s` appended on both sides to avoid
`List.erase` position bookkeeping. -/
theorem diffs_orderedInsert (b : ℝ) :
    ∀ (m : List ℝ), List.Pairwise (· ≤ ·) m → m ≠ [] →
      m.head! < b → b < m.getLast! →
      ∃ s s₁ s₂ : ℝ, s = s₁ + s₂ ∧ 0 ≤ s₁ ∧ 0 ≤ s₂ ∧ s ∈ diffs m ∧
        (s :: diffs (List.orderedInsert (· ≤ ·) b m)).Perm
          (s₁ :: s₂ :: diffs m) := by
  intro m
  induction m with
  | nil => intro _ h; exact absurd rfl h
  | cons x rest ih =>
    intro hpw _ hhead hlast
    have hxb : ¬ (b ≤ x) := by simp only [List.head!_cons] at hhead; linarith
    cases rest with
    | nil =>
      simp only [List.getLast!_eq_getLast?_getD, List.getLast?_singleton,
        Option.getD_some, List.head!_cons] at hlast hhead
      exfalso; linarith
    | cons y rest' =>
      rw [List.pairwise_cons] at hpw
      obtain ⟨hx_all, hpw_rest⟩ := hpw
      have hxy : x ≤ y := hx_all y (by simp)
      by_cases hby : b ≤ y
      · -- b lands between x and y
        refine ⟨y - x, b - x, y - b, by ring, by linarith, by linarith, ?_, ?_⟩
        · rw [diffs_cons_cons]; exact List.mem_cons_self
        · -- orderedInsert = x :: b :: y :: rest'
          rw [List.orderedInsert_cons]
          simp only [hxb, if_false]
          rw [List.orderedInsert_cons]
          simp only [hby, if_true]
          rw [diffs_cons_cons, diffs_cons_cons, diffs_cons_cons]
          -- goal: (y-x) :: (b-x) :: (y-b) :: diffs(y::rest')
          --   Perm  (b-x) :: (y-b) :: (y-x) :: diffs(y::rest')
          -- rotate head to position 3: a::b::c::L ~ b::c::a::L
          exact (List.Perm.swap (b - x) (y - x) ((y - b) :: diffs (y :: rest'))).trans
            ((List.Perm.swap (y - b) (y - x) (diffs (y :: rest'))).cons (b - x))
      · -- b > y: recurse
        push_neg at hby
        have hrne : (y :: rest') ≠ [] := by simp
        have hrhead : (y :: rest').head! < b := by simp only [List.head!_cons]; exact hby
        have hrlast : b < (y :: rest').getLast! := by
          have he : (x :: y :: rest').getLast! = (y :: rest').getLast! := by
            simp only [List.getLast!_eq_getLast?_getD, List.getLast?_cons_cons]
          rw [he] at hlast; exact hlast
        obtain ⟨s, s₁, s₂, hs, hs1, hs2, hsmem, hperm⟩ :=
          ih hpw_rest hrne hrhead hrlast
        refine ⟨s, s₁, s₂, hs, hs1, hs2, ?_, ?_⟩
        · rw [diffs_cons_cons]; exact List.mem_cons_of_mem _ hsmem
        · -- orderedInsert b (x :: y :: rest') = x :: orderedInsert b (y :: rest')
          rw [List.orderedInsert_cons]
          simp only [hxb, if_false]
          -- head of orderedInsert b (y::rest') is y (since ¬ b ≤ y)
          have hoi_head : (List.orderedInsert (· ≤ ·) b (y :: rest')).head? = some y := by
            rw [List.orderedInsert_cons]
            simp only [not_le.mpr hby, if_false, List.head?_cons]
          obtain ⟨u, hu⟩ : ∃ u, List.orderedInsert (· ≤ ·) b (y :: rest') = y :: u := by
            cases hoi : List.orderedInsert (· ≤ ·) b (y :: rest') with
            | nil => rw [hoi] at hoi_head; simp at hoi_head
            | cons z t =>
              rw [hoi] at hoi_head; simp only [List.head?_cons] at hoi_head
              obtain rfl : z = y := by simpa using hoi_head
              exact ⟨t, rfl⟩
          rw [hu, diffs_cons_cons, diffs_cons_cons]
          -- goal: s :: (y-x) :: diffs(y::u)  Perm  s₁ :: s₂ :: (y-x) :: diffs(y::rest')
          -- IH (via hu): s :: diffs(y::u)  Perm  s₁ :: s₂ :: diffs(y::rest')
          have hperm' : (s :: diffs (y :: u)).Perm (s₁ :: s₂ :: diffs (y :: rest')) := by
            rw [← hu]; exact hperm
          -- move (y-x): s :: (y-x) :: L ~ (y-x) :: s :: L ~ (y-x) :: (s₁::s₂::L')
          --   ~ s₁ :: s₂ :: (y-x) :: L'
          refine (List.Perm.swap (y - x) s (diffs (y :: u))).trans ?_
          refine (hperm'.cons (y - x)).trans ?_
          -- (y-x) :: s₁ :: s₂ :: L' ~ s₁ :: s₂ :: (y-x) :: L'  (rotate head to pos 3)
          exact (List.Perm.swap s₁ (y - x) (s₂ :: diffs (y :: rest'))).trans
            ((List.Perm.swap s₂ (y - x) (diffs (y :: rest'))).cons s₁)

/-- (I) The ascending sort of `insert b A` is `orderedInsert b (A.sort)`. -/
theorem sort_insert_eq_orderedInsert (A : Finset ℝ) (b : ℝ) (hbA : b ∉ A) :
    (insert b A).sort (· ≤ ·) = List.orderedInsert (· ≤ ·) b (A.sort (· ≤ ·)) := by
  classical
  -- both are Pairwise (≤) and both permutations of b :: A.sort; conclude by uniqueness
  have hAsort : List.Pairwise (· ≤ ·) (A.sort (· ≤ ·)) :=
    (Finset.sort_sorted_lt _).pairwise.imp le_of_lt
  -- LHS pairwise
  have hlhs_pw : List.Pairwise (· ≤ ·) ((insert b A).sort (· ≤ ·)) :=
    (Finset.sort_sorted_lt _).pairwise.imp le_of_lt
  -- RHS pairwise via Pairwise.orderedInsert
  have hrhs_pw : List.Pairwise (· ≤ ·) (List.orderedInsert (· ≤ ·) b (A.sort (· ≤ ·))) :=
    List.Pairwise.orderedInsert b (A.sort (· ≤ ·)) hAsort
  -- both perms of b :: A.sort
  have hlhs_perm : ((insert b A).sort (· ≤ ·)).Perm (b :: A.sort (· ≤ ·)) := by
    apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).mpr
    · intro x
      rw [Finset.mem_sort, List.mem_cons, Finset.mem_insert, Finset.mem_sort]
    · rw [List.nodup_cons]
      exact ⟨by rw [Finset.mem_sort]; exact hbA, Finset.sort_nodup _ _⟩
  have hrhs_perm : (List.orderedInsert (· ≤ ·) b (A.sort (· ≤ ·))).Perm (b :: A.sort (· ≤ ·)) :=
    List.perm_orderedInsert (· ≤ ·) b (A.sort (· ≤ ·))
  have hperm : ((insert b A).sort (· ≤ ·)).Perm
      (List.orderedInsert (· ≤ ·) b (A.sort (· ≤ ·))) :=
    hlhs_perm.trans hrhs_perm.symm
  refine List.Perm.eq_of_pairwise ?_ hlhs_pw hrhs_pw hperm
  intro a b _ _ hab hba
  exact le_antisymm hab hba

/-- Insertion of `b` commutes with appending `[1]` when `b < 1`. -/
theorem orderedInsert_append_one (l : List ℝ) (b : ℝ) (hb1 : b < 1) :
    List.orderedInsert (· ≤ ·) b l ++ [1]
      = List.orderedInsert (· ≤ ·) b (l ++ [1]) := by
  induction l with
  | nil =>
    simp [List.orderedInsert, le_of_lt hb1]
  | cons x t ih =>
    rw [List.cons_append, List.orderedInsert_cons, List.orderedInsert_cons]
    by_cases hbx : b ≤ x
    · rw [if_pos hbx, if_pos hbx]; rfl
    · rw [if_neg hbx, if_neg hbx, List.cons_append, ih]

/-- (II) Insertion commutes with the `0 :: · ++ [1]` augmentation when `0 < b < 1`. -/
theorem augmented_orderedInsert (l : List ℝ) (b : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) :
    (0 : ℝ) :: List.orderedInsert (· ≤ ·) b l ++ [1]
      = List.orderedInsert (· ≤ ·) b ((0 : ℝ) :: l ++ [1]) := by
  -- RHS: orderedInsert into (0 :: (l ++ [1])); head is 0, ¬ b ≤ 0, so skip 0
  have hrhs : List.orderedInsert (· ≤ ·) b ((0 : ℝ) :: l ++ [1])
      = (0 : ℝ) :: List.orderedInsert (· ≤ ·) b (l ++ [1]) := by
    rw [List.cons_append, List.orderedInsert_cons, if_neg (by simp; linarith)]
  rw [hrhs, List.cons_append, orderedInsert_append_one l b hb1]

/-- **Single-point cut (Proposition A).** Adding one new interior mark `b ∉ A`,
`b ∈ (0,1)`, turns `pieceLengths A` into a single cut. -/
theorem pieceLengths_insert_single_cut (A : Finset ℝ) (b : ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hbA : b ∉ A) :
    ∃ s s₁ s₂ : ℝ, s = s₁ + s₂ ∧ 0 ≤ s₁ ∧ 0 ≤ s₂ ∧ s ∈ pieceLengths A ∧
      (pieceLengths (insert b A)).Perm (s₁ :: s₂ :: (pieceLengths A).erase s) := by
  classical
  rw [Set.mem_Ioo] at hb
  obtain ⟨hb0, hb1⟩ := hb
  -- The augmented list m = 0 :: A.sort ++ [1]
  set m : List ℝ := (0 : ℝ) :: (A.sort (· ≤ ·)) ++ [1] with hm
  -- pieceLengths A = diffs m
  have hplA : pieceLengths A = diffs m := rfl
  -- pieceLengths (insert b A) = diffs (orderedInsert b m)
  have hplins : pieceLengths (insert b A) = diffs (List.orderedInsert (· ≤ ·) b m) := by
    rw [pieceLengths_eq_diffs, sort_insert_eq_orderedInsert A b hbA, hm]
    rw [augmented_orderedInsert (A.sort (· ≤ ·)) b hb0 hb1]
  -- membership facts for A.sort
  have hmemA : ∀ y ∈ A.sort (· ≤ ·), 0 ≤ y ∧ y ≤ 1 := by
    intro y hy
    rw [Finset.mem_sort] at hy
    have := hA (Finset.mem_coe.mpr hy)
    rw [Set.mem_Ioo] at this
    exact ⟨le_of_lt this.1, le_of_lt this.2⟩
  -- m is Pairwise (≤)
  have hmpw : List.Pairwise (· ≤ ·) m := by
    rw [hm]
    have hAsort : List.Pairwise (· ≤ ·) (A.sort (· ≤ ·)) :=
      (Finset.sort_sorted_lt _).pairwise.imp le_of_lt
    rw [List.cons_append, List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact (hmemA z hz).1
      · norm_num
    · rw [List.pairwise_append]
      refine ⟨hAsort, by simp, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      exact (hmemA x hx).2
  -- m ≠ []
  have hmne : m ≠ [] := by rw [hm]; simp
  -- m.head! = 0 < b
  have hmhead : m.head! < b := by rw [hm]; simp only [List.cons_append, List.head!_cons]; exact hb0
  -- m.getLast! = 1 > b
  have hmlast : b < m.getLast! := by
    rw [hm]
    have : ((0 :: A.sort (· ≤ ·)) ++ [1]).getLast! = (1 : ℝ) := by
      rw [List.getLast!_eq_getLast?_getD, List.getLast?_concat]; rfl
    rw [this]; exact hb1
  -- apply the core lemma
  obtain ⟨s, s₁, s₂, hs, hs1, hs2, hsmem, hperm⟩ :=
    diffs_orderedInsert b m hmpw hmne hmhead hmlast
  refine ⟨s, s₁, s₂, hs, hs1, hs2, ?_, ?_⟩
  · rw [hplA]; exact hsmem
  · -- convert add-s Perm to erase form
    rw [hplins, hplA]
    -- hperm : s :: diffs (orderedInsert b m) ~ s₁ :: s₂ :: diffs m
    -- want : diffs (orderedInsert b m) ~ s₁ :: s₂ :: (diffs m).erase s
    -- diffs m ~ s :: (diffs m).erase s  (perm_cons_erase, s ∈ diffs m)
    have hce : (diffs m).Perm (s :: (diffs m).erase s) := List.perm_cons_erase hsmem
    -- s₁ :: s₂ :: diffs m ~ s₁ :: s₂ :: s :: (diffs m).erase s
    have h1 : (s₁ :: s₂ :: diffs m).Perm (s₁ :: s₂ :: s :: (diffs m).erase s) :=
      (hce.cons s₂).cons s₁
    -- s :: diffs(oi) ~ s :: s₁ :: s₂ :: (diffs m).erase s (move s to front on RHS)
    have h2 : (s :: diffs (List.orderedInsert (· ≤ ·) b m)).Perm
        (s :: s₁ :: s₂ :: (diffs m).erase s) := by
      refine hperm.trans (h1.trans ?_)
      -- s₁ :: s₂ :: s :: R ~ s :: s₁ :: s₂ :: R
      exact ((List.Perm.swap s s₂ ((diffs m).erase s)).cons s₁).trans
        (List.Perm.swap s s₁ (s₂ :: (diffs m).erase s))
    exact List.Perm.cons_inv h2

/-- **Bridge (Part II).** For disjoint `A, B ⊆ (0,1)`, `pieceLengths (A ∪ B)` is
a `B.card`-cut refinement of `pieceLengths A`. -/
theorem pieceLengths_union_refines (A B : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (hB : ↑B ⊆ Set.Ioo (0 : ℝ) 1)
    (hAB : Disjoint A B) :
    RefinesByAtMostNCuts (pieceLengths A) B.card (pieceLengths (A ∪ B)) := by
  classical
  induction B using Finset.induction with
  | empty =>
    -- A ∪ ∅ = A, card 0, base case (refl perm)
    rw [Finset.union_empty, Finset.card_empty]
    exact RefinesByAtMostNCuts.base (List.Perm.refl _)
  | @insert b B' hb ih =>
    -- hB : ↑(insert b B') ⊆ Ioo 0 1 ; derive sub-facts
    have hbmem : b ∈ Set.Ioo (0:ℝ) 1 := by
      apply hB; rw [Finset.coe_insert]; exact Set.mem_insert _ _
    have hB' : ↑B' ⊆ Set.Ioo (0:ℝ) 1 := by
      intro x hx
      apply hB
      rw [Finset.coe_insert]
      exact Set.mem_insert_of_mem _ hx
    -- Disjoint A B' from Disjoint A (insert b B')
    have hAB' : Disjoint A B' := by
      apply Finset.disjoint_of_subset_right (Finset.subset_insert b B') hAB
    -- b ∉ A: from Disjoint A (insert b B'), b ∈ insert b B'
    have hbA : b ∉ A := by
      intro hbA
      have : b ∈ A ∩ (insert b B') := by
        rw [Finset.mem_inter]; exact ⟨hbA, Finset.mem_insert_self b B'⟩
      rw [Finset.disjoint_iff_inter_eq_empty.mp hAB] at this
      simp at this
    -- b ∉ A ∪ B'
    have hbAB' : b ∉ A ∪ B' := by
      rw [Finset.mem_union]
      push_neg
      exact ⟨hbA, hb⟩
    -- A ∪ B' ⊆ Ioo 0 1
    have hAB'sub : ↑(A ∪ B') ⊆ Set.Ioo (0:ℝ) 1 := by
      rw [Finset.coe_union]; exact Set.union_subset hA hB'
    -- IH refinement
    have hih : RefinesByAtMostNCuts (pieceLengths A) B'.card (pieceLengths (A ∪ B')) :=
      ih hB' hAB'
    -- single cut adding b to A ∪ B'
    obtain ⟨s, s₁, s₂, hs, hs1, hs2, hsmem, hperm⟩ :=
      pieceLengths_insert_single_cut (A ∪ B') b hAB'sub hbmem hbAB'
    -- A ∪ insert b B' = insert b (A ∪ B')
    have hunion : A ∪ insert b B' = insert b (A ∪ B') := by
      rw [Finset.union_insert]
    -- card
    have hcard : (insert b B').card = B'.card + 1 :=
      Finset.card_insert_of_notMem hb
    rw [hcard, hunion]
    -- apply the cut constructor on top of IH
    exact RefinesByAtMostNCuts.cut hs hs1 hs2 hperm hsmem hih

/-- The mark function used to define `lowerA n`. -/
noncomputable def lowerMark (n : ℕ) (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n + 1 - k)) / ((2 : ℝ) ^ (n + 1) - 1)

/-- The mark function is strictly monotone on `Icc 1 n` (indeed on `Icc 1 (n+1)`). -/
theorem lowerMark_strictMonoOn (n : ℕ) :
    StrictMonoOn (lowerMark n) (Set.Icc 1 (n + 1)) := by
  have hD : (0:ℝ) < (2:ℝ) ^ (n + 1) - 1 := by
    have : (1:ℝ) < (2:ℝ) ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  intro a ha b hb hab
  simp only [Set.mem_Icc] at ha hb
  unfold lowerMark
  rw [div_lt_div_iff_of_pos_right hD]
  -- 2^(n+1) - 2^(n+1-a) < 2^(n+1) - 2^(n+1-b)  ⟺  2^(n+1-b) < 2^(n+1-a)
  have hexp : n + 1 - b < n + 1 - a := by omega
  have : (2:ℝ) ^ (n + 1 - b) < (2:ℝ) ^ (n + 1 - a) :=
    pow_lt_pow_right₀ (by norm_num) hexp
  linarith

/-- The ascending sort of `lowerA n` is the mapped ascending list of `Icc 1 n`. -/
theorem lowerA_sort (n : ℕ) :
    (lowerA n).sort (· ≤ ·) = ((Finset.Icc 1 n).sort (· ≤ ·)).map (lowerMark n) := by
  classical
  -- candidate sorted list
  set cand : List ℝ := ((Finset.Icc 1 n).sort (· ≤ ·)).map (lowerMark n) with hcand
  -- cand is sorted (≤)
  have hsmono : StrictMonoOn (lowerMark n) ↑(Finset.Icc 1 n) := by
    apply (lowerMark_strictMonoOn n).mono
    intro x hx
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx ⊢
    omega
  have hsortedIcc : List.Pairwise (· ≤ ·) ((Finset.Icc 1 n).sort (· ≤ ·)) :=
    (Finset.sort_sorted_lt _).pairwise.imp le_of_lt
  have hcandsorted : List.Pairwise (· ≤ ·) cand := by
    rw [hcand]
    rw [List.pairwise_map]
    -- need: Pairwise (fun a b => lowerMark n a ≤ lowerMark n b) on the sorted Icc
    have hpw : List.Pairwise (· ≤ ·) ((Finset.Icc 1 n).sort (· ≤ ·)) := hsortedIcc
    -- also need strict-in-order for distinct.  Use nodup + strictMonoOn.
    have hnd : ((Finset.Icc 1 n).sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
    -- Build pairwise using strict monotonicity: for a ≤ b in list, since nodup,
    -- either a = b (same index) or a < b as values.
    apply List.Pairwise.imp_of_mem ?_ hpw
    intro a b ha hb hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    · have haI : a ∈ Finset.Icc 1 n := by rwa [← Finset.mem_sort (· ≤ ·)]
      have hbI : b ∈ Finset.Icc 1 n := by rwa [← Finset.mem_sort (· ≤ ·)]
      exact le_of_lt (hsmono (by simpa using haI) (by simpa using hbI) hlt)
  -- cand is a permutation of (lowerA n).sort
  have hperm : cand.Perm ((lowerA n).sort (· ≤ ·)) := by
    apply (List.perm_ext_iff_of_nodup ?_ ?_).mpr
    · intro x
      constructor
      · intro hx
        rw [hcand, List.mem_map] at hx
        obtain ⟨k, hk, rfl⟩ := hx
        rw [Finset.mem_sort] at hk
        rw [Finset.mem_sort]
        unfold lowerA
        rw [Finset.mem_image]
        exact ⟨k, hk, rfl⟩
      · intro hx
        rw [Finset.mem_sort] at hx
        unfold lowerA at hx
        rw [Finset.mem_image] at hx
        obtain ⟨k, hk, rfl⟩ := hx
        rw [hcand, List.mem_map]
        exact ⟨k, by rw [Finset.mem_sort]; exact hk, rfl⟩
    · -- cand nodup
      rw [hcand]
      rw [List.nodup_map_iff_inj_on (Finset.sort_nodup _ _)]
      intro a ha b hb hab
      rw [Finset.mem_sort] at ha hb
      exact hsmono.injOn (by simpa using ha) (by simpa using hb) hab
    · exact Finset.sort_nodup _ _
  -- conclude by uniqueness of sorted permutations
  have hlowerAsorted : List.Pairwise (· ≤ ·) ((lowerA n).sort (· ≤ ·)) :=
    (Finset.sort_sorted_lt _).pairwise.imp le_of_lt
  refine (List.Perm.eq_of_pairwise ?_ hcandsorted hlowerAsorted hperm).symm
  intro a b _ _ hab hba
  exact le_antisymm hab hba

/-- `(Icc 1 n).sort = List.range' 1 n`. -/
theorem Icc_one_sort (n : ℕ) :
    (Finset.Icc 1 n).sort (· ≤ ·) = List.range' 1 n := by
  have hnd : (List.range' 1 n).Nodup := List.nodup_range'
  have hpw : (List.range' 1 n).Pairwise (· ≤ ·) := List.pairwise_le_range' 1
  have hkey := (List.toFinset_sort (· ≤ ·) hnd).mpr hpw
  have htf : (List.range' 1 n).toFinset = Finset.Icc 1 n := by
    ext x
    rw [List.mem_toFinset, List.mem_range', Finset.mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
  rw [htf] at hkey
  exact hkey

/-- Boundary value: `lowerMark n 0 = 0`. -/
theorem lowerMark_zero (n : ℕ) : lowerMark n 0 = 0 := by
  unfold lowerMark
  simp

/-- Boundary value: `lowerMark n (n+1) = 1`. -/
theorem lowerMark_top (n : ℕ) : lowerMark n (n + 1) = 1 := by
  unfold lowerMark
  have hD : (1:ℝ) < (2:ℝ) ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have h : n + 1 - (n + 1) = 0 := by omega
  rw [h]
  simp only [pow_zero]
  rw [div_self (by linarith)]

/-- Telescoping the consecutive differences of a mapped `range'`. -/
theorem zipWith_diff_map_range' (g : ℕ → ℝ) (s k : ℕ) :
    List.zipWith (fun a b => b - a) ((List.range' s (k + 1)).map g)
        (((List.range' s (k + 1)).map g).tail)
      = (List.range' s k).map (fun i => g (i + 1) - g i) := by
  induction k generalizing s with
  | zero =>
    simp [List.range'_succ, List.range'_zero]
  | succ k ih =>
    -- range' s (k+2) = s :: range' (s+1) (k+1)
    rw [List.range'_succ (s := s) (n := k + 1) (step := 1), List.map_cons]
    simp only [List.tail_cons]
    -- range' (s+1) (k+1) = (s+1) :: range' (s+2) k
    rw [List.range'_succ (s := s + 1) (n := k) (step := 1), List.map_cons]
    rw [List.zipWith_cons_cons]
    -- RHS: range' s (k+1) = s :: range' (s+1) k
    rw [List.range'_succ (s := s) (n := k) (step := 1), List.map_cons]
    -- head matches; tail is ih at (s+1)
    have hih := ih (s + 1)
    rw [List.range'_succ (s := s + 1) (n := k) (step := 1), List.map_cons] at hih
    simp only [List.tail_cons] at hih
    rw [hih]

/-- `pieceLengths (lowerA n)` is a permutation of the dyadic list scaled by `1/D`. -/
theorem pieceLengths_lowerA (n : ℕ) (hn : 0 < n) :
    (pieceLengths (lowerA n)).Perm
      ((dyadicList n).map (fun x => x / ((2 : ℝ) ^ (n + 1) - 1))) := by
  set D : ℝ := (2 : ℝ) ^ (n + 1) - 1 with hDdef
  have hD1 : (1:ℝ) < (2:ℝ) ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hDpos : (0:ℝ) < D := by rw [hDdef]; linarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  -- It suffices to prove the lists are EQUAL.
  suffices heq : pieceLengths (lowerA n)
      = (List.range (n + 1)).map (fun i => (2:ℝ) ^ (n - i) / D) by
    rw [heq]
    have hrhs : (dyadicList n).map (fun x => x / D)
        = (List.range (n + 1)).map (fun i => (2:ℝ) ^ (n - i) / D) := by
      unfold dyadicList
      rw [List.map_map]
      rfl
    rw [hrhs]
  -- The augmented list l = 0 :: (sorted marks) ++ [1] equals the map of
  -- lowerMark over range' 0 (n+2), using lowerMark n 0 = 0, lowerMark n (n+1)=1.
  have hlmap : (0:ℝ) :: (((Finset.Icc 1 n).sort (· ≤ ·)).map (lowerMark n)) ++ [1]
      = (List.range' 0 (n + 2)).map (lowerMark n) := by
    rw [Icc_one_sort]
    -- range' 0 (n+2) = 0 :: range' 1 (n+1)
    have hr0 : List.range' 0 (n + 2) = 0 :: List.range' 1 (n + 1) := by
      rw [List.range'_succ (s := 0) (n := n + 1) (step := 1)]
    -- range' 1 (n+1) = range' 1 n ++ [1+n]
    have hsplit : List.range' 1 (n + 1) = List.range' 1 n ++ [1 + n] :=
      List.range'_1_concat
    have htop : (1 + n : ℕ) = n + 1 := by omega
    rw [hr0, hsplit, List.map_cons, lowerMark_zero, List.map_append,
      List.map_cons, List.map_nil, htop, lowerMark_top]
    rfl
  -- Now compute pieceLengths.
  unfold pieceLengths
  rw [lowerA_sort]
  simp only [List.cons_append] at hlmap ⊢
  rw [hlmap]
  -- telescoping the consecutive differences
  rw [zipWith_diff_map_range' (lowerMark n) 0 (n + 1)]
  -- range' 0 (n+1) = range (n+1)
  rw [← List.range_eq_range']
  -- pointwise: lowerMark n (i+1) - lowerMark n i = 2^(n-i)/D for i ≤ n
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  unfold lowerMark
  rw [← hDdef]
  have h1 : n + 1 - (i + 1) = n - i := by omega
  have h2 : n + 1 - i = (n - i) + 1 := by omega
  rw [h1, h2]
  have hpow : (2:ℝ) ^ ((n - i) + 1) = 2 * 2 ^ (n - i) := by ring
  rw [hpow]
  field_simp
  ring

/-- Weaken the cut budget of a refinement. -/
theorem refines_mono {base Q : List ℝ} {k m : ℕ} (hkm : k ≤ m)
    (h : RefinesByAtMostNCuts base k Q) : RefinesByAtMostNCuts base m Q := by
  induction h generalizing m with
  | base hperm =>
      induction m with
      | zero => exact RefinesByAtMostNCuts.base hperm
      | succ m' ih2 => exact RefinesByAtMostNCuts.skip (ih2 (by omega))
  | skip _ ih =>
      rename_i k _
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact RefinesByAtMostNCuts.skip (ih (by omega))
  | cut hs h1 h2 hstep hmem hh ih =>
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact RefinesByAtMostNCuts.cut hs h1 h2 hstep hmem (ih (by omega))

/-- A refinement's base list may be replaced by any permutation of it. -/
theorem refines_of_perm_base {base base' Q : List ℝ} {k : ℕ}
    (hperm : base.Perm base') (h : RefinesByAtMostNCuts base' k Q) :
    RefinesByAtMostNCuts base k Q := by
  induction h generalizing base with
  | base hperm' => exact RefinesByAtMostNCuts.base (hperm'.trans hperm.symm)
  | skip _ ih => exact RefinesByAtMostNCuts.skip (ih hperm)
  | cut hs h1 h2 hstep hmem hh ih =>
      exact RefinesByAtMostNCuts.cut hs h1 h2 hstep hmem (ih hperm)

/-- A refinement's target list may be replaced by any permutation of it. -/
theorem refines_target_perm {base Q Q' : List ℝ} {k : ℕ}
    (hperm : Q.Perm Q') (h : RefinesByAtMostNCuts base k Q) :
    RefinesByAtMostNCuts base k Q' := by
  induction h generalizing Q' with
  | base hb => exact RefinesByAtMostNCuts.base (hperm.symm.trans hb)
  | skip _ ih => exact RefinesByAtMostNCuts.skip (ih hperm)
  | cut hs h1 h2 hstep hmem hh _ =>
      exact RefinesByAtMostNCuts.cut hs h1 h2 (hperm.symm.trans hstep) hmem hh

/-- Prepending the same element `a` to both base and target preserves a refinement
with the same cut budget. -/
theorem refines_cons {base Q : List ℝ} {k : ℕ} (a : ℝ)
    (h : RefinesByAtMostNCuts base k Q) :
    RefinesByAtMostNCuts (a :: base) k (a :: Q) := by
  induction h with
  | base hperm => exact RefinesByAtMostNCuts.base (hperm.cons a)
  | skip _ ih => exact RefinesByAtMostNCuts.skip ih
  | cut hs h1 h2 hstep hmem hh ih =>
      rename_i Qpre Qpost kk s s1 s2
      -- hmem : s ∈ Qpre ; hstep : Qpost.Perm (s1 :: s2 :: Qpre.erase s)
      -- ih : RefinesByAtMostNCuts (a :: base) kk (a :: Qpre)
      have hmem' : s ∈ a :: Qpre := List.mem_cons_of_mem a hmem
      have hkey : (a :: Qpre.erase s).Perm ((a :: Qpre).erase s) := by
        by_cases hae : a = s
        · rw [hae, List.erase_cons_head]
          exact (List.perm_cons_erase hmem).symm
        · rw [List.erase_cons_tail (by simpa using hae)]
      have hstep' : (a :: Qpost).Perm (s1 :: s2 :: (a :: Qpre).erase s) := by
        have h1' : (a :: Qpost).Perm (a :: s1 :: s2 :: Qpre.erase s) := hstep.cons a
        have e1 : (a :: s1 :: s2 :: Qpre.erase s).Perm (s1 :: a :: s2 :: Qpre.erase s) :=
          List.Perm.swap s1 a _
        have e2 : (s1 :: a :: s2 :: Qpre.erase s).Perm (s1 :: s2 :: a :: Qpre.erase s) :=
          (List.Perm.swap s2 a _).cons s1
        have h3' : (s1 :: s2 :: a :: Qpre.erase s).Perm (s1 :: s2 :: (a :: Qpre).erase s) :=
          (hkey.cons s2).cons s1
        exact ((h1'.trans e1).trans e2).trans h3'
      exact RefinesByAtMostNCuts.cut hs h1 h2 hstep' hmem' ih

/-- Composition (transitivity) of refinements: budgets add. -/
theorem refines_trans {base mid final : List ℝ} {k1 k2 : ℕ}
    (h1 : RefinesByAtMostNCuts base k1 mid)
    (h2 : RefinesByAtMostNCuts mid k2 final) :
    RefinesByAtMostNCuts base (k1 + k2) final := by
  induction h2 with
  | base hperm =>
      -- final.Perm mid, so base refines to final with budget k1
      have := refines_target_perm hperm.symm h1
      simpa using this
  | skip _ ih =>
      have := RefinesByAtMostNCuts.skip ih
      exact this
  | cut hs ha hb hstep hmem hh ih =>
      have := RefinesByAtMostNCuts.cut hs ha hb hstep hmem ih
      exact this


/-- **Lower bound.** Liu Bang has an admissible marking `A` such that for every
admissible marking `B` disjoint from `A`, his guaranteed share is at least
`2^n / (2^(n+1) - 1)`. -/
theorem lower_bound (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  refine ⟨lowerA n, ⟨?_, ?_⟩, ?_⟩
  · -- lowerA n ⊆ Ioo 0 1
    intro x hx
    exact lowerA_mem_Ioo n hn x (by simpa using hx)
  · -- card ≤ n
    rw [lowerA_card]
  · intro B hB hdisj
    obtain ⟨hBsub, hBcard⟩ := hB
    set D : ℝ := (2 : ℝ) ^ (n + 1) - 1 with hDdef
    have hD1 : (1 : ℝ) < (2 : ℝ) ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
    have hDpos : 0 < D := by rw [hDdef]; linarith
    have hAsub : ↑(lowerA n) ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx =>
      lowerA_mem_Ioo n hn x (by simpa using hx)
    have hABsub : ↑(lowerA n ∪ B) ⊆ Set.Ioo (0 : ℝ) 1 := by
      rw [Finset.coe_union]; exact Set.union_subset hAsub hBsub
    -- P = pieceLengths (A ∪ B)
    set P : List ℝ := pieceLengths (lowerA n ∪ B) with hPdef
    -- Reduce L to altSum
    have hLeq : L (lowerA n) B = (1 + altSum (P.mergeSort (· ≥ ·))) / 2 :=
      L_eq_half_one_add_alt _ _ hABsub
    -- Refinement of dyadicList scaled by 1/D
    have hrefP : RefinesByAtMostNCuts (pieceLengths (lowerA n)) B.card P :=
      pieceLengths_union_refines _ _ hAsub hBsub hdisj
    -- base perm to scaled dyadic list
    have hbaseperm : (pieceLengths (lowerA n)).Perm
        ((dyadicList n).map (fun x => x / D)) := pieceLengths_lowerA n hn
    -- rewrite x/D as (1/D)*x
    have hmapeq : (dyadicList n).map (fun x => x / D)
        = (dyadicList n).map (fun x => (1 / D) * x) := by
      apply List.map_congr_left; intro x _; field_simp
    rw [hmapeq] at hbaseperm
    -- P refines scaled base by B.card cuts
    have href1 : RefinesByAtMostNCuts ((dyadicList n).map (fun x => (1 / D) * x))
        B.card P := refines_of_perm_base hbaseperm.symm hrefP
    -- weaken budget to n
    have href2 : RefinesByAtMostNCuts ((dyadicList n).map (fun x => (1 / D) * x))
        n P := refines_mono hBcard href1
    -- scale by D
    have href3 : RefinesByAtMostNCuts
        (((dyadicList n).map (fun x => (1 / D) * x)).map (fun x => D * x)) n
        (P.map (fun x => D * x)) := refines_smul D hDpos href2
    -- the doubly-mapped base is dyadicList n
    have hbasesimp : ((dyadicList n).map (fun x => (1 / D) * x)).map (fun x => D * x)
        = dyadicList n := by
      rw [List.map_map]
      have : (fun x => D * x) ∘ (fun x => (1 / D) * x) = (id : ℝ → ℝ) := by
        funext x
        simp only [Function.comp_apply, id_eq]
        field_simp
      rw [this]; simp
    rw [hbasesimp] at href3
    -- nonnegativity of P.map (D*·)
    have hPnn : ∀ x ∈ P, 0 ≤ x := pieceLengths_nonneg _ hABsub
    have hPDnn : ∀ x ∈ P.map (fun x => D * x), 0 ≤ x := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact mul_nonneg (le_of_lt hDpos) (hPnn y hy)
    -- apply kernel
    have hkernel : 1 ≤ altSum ((P.map (fun x => D * x)).mergeSort (· ≥ ·)) :=
      dyadic_refinement_alt_ge_one n hn (P.map (fun x => D * x)) hPDnn href3
    -- mergeSort commutes with scaling
    rw [mergeSort_map_smul D (le_of_lt hDpos) P] at hkernel
    rw [altSum_smul D (P.mergeSort (· ≥ ·))] at hkernel
    -- so altSum(P.mergeSort) ≥ 1/D
    have haltge : 1 / D ≤ altSum (P.mergeSort (· ≥ ·)) := by
      rw [div_le_iff₀ hDpos]
      -- hkernel : 1 ≤ D * altSum ..
      nlinarith [hkernel]
    -- now the arithmetic: c ≤ (1 + Alt)/2, c = 2^n/D, and 2^n/D = (1 + 1/D)/2
    rw [hLeq]
    have hceq : (2 : ℝ) ^ n / D = (1 + 1 / D) / 2 := by
      rw [hDdef] at hDpos ⊢
      field_simp
      ring
    rw [hceq]
    have : (1 : ℝ) + 1 / D ≤ 1 + altSum (P.mergeSort (· ≥ ·)) := by linarith [haltge]
    linarith


/-- Layer 0: a pairing certificate of a plain list `l`. -/
structure PairingCert (l : List ℝ) where
  pairs   : List (ℝ × ℝ)
  singles : List ℝ
  perm    : ((pairs.flatMap (fun p => [p.1, p.2])) ++ singles).Perm l

/-- Defect (matching cost) of a plain pairing certificate. -/
noncomputable def PairingCert.defect {l : List ℝ} (C : PairingCert l) : ℝ :=
  (C.pairs.map (fun p => |p.1 - p.2|)).sum + C.singles.sum

/-- For a sorted-descending nonneg list, the tail's altSum is between `0` and the head. -/
theorem altSum_sorted_nonneg_bounds (q : List ℝ)
    (hge : List.Pairwise (· ≥ ·) q) (hnn : ∀ x ∈ q, 0 ≤ x) :
    0 ≤ altSum q ∧ altSum q ≤ q.headD 0 := by
  induction q using List.twoStepInduction with
  | nil =>
    simp [altSum]
  | singleton x =>
    have hx : altSum [x] = x := by simp [altSum]
    rw [hx]
    simp only [List.headD_cons]
    exact ⟨hnn x (by simp), le_refl x⟩
  | cons_cons x y t _ ih2 =>
    rw [altSum_cons]
    have hxy : x ≥ y := by
      rw [List.pairwise_cons] at hge
      exact hge.1 y (by simp)
    have hge' : List.Pairwise (· ≥ ·) (y :: t) := by
      rw [List.pairwise_cons] at hge
      exact hge.2
    have hnn' : ∀ z ∈ (y :: t), 0 ≤ z := fun z hz => hnn z (by simp [hz])
    obtain ⟨hlo, hhi⟩ := ih2 y hge' hnn'
    rw [List.headD_cons] at hhi
    refine ⟨?_, ?_⟩
    · linarith
    · rw [List.headD_cons]
      linarith

/-- Erasing an element preserves descending-pairwise. -/
theorem pairwise_ge_erase (q : List ℝ) (hge : List.Pairwise (· ≥ ·) q) (c : ℝ) :
    List.Pairwise (· ≥ ·) (q.erase c) :=
  hge.sublist (List.erase_sublist (a := c) (l := q))

/-- The cost of one certificate part (pair or single). -/
noncomputable def partCost (s : ℝ ⊕ (ℝ × ℝ)) : ℝ :=
  match s with
  | Sum.inl c => c
  | Sum.inr p => |p.1 - p.2|

/-- The list of elements a certificate part decodes to. -/
def partElts (s : ℝ ⊕ (ℝ × ℝ)) : List ℝ :=
  match s with
  | Sum.inl c => [c]
  | Sum.inr p => [p.1, p.2]

/-- Combined single-erase bound: for a sorted-desc nonneg list `R` and `b ∈ R`,
`b ≤ altSum R + altSum (R.erase b) ≤ 2 * R.headD 0 - b`.  Proved by a single
induction using BOTH parts of the IH (lower feeds upper and vice versa). -/
theorem altSum_erase_pair_bounds (R : List ℝ)
    (hge : List.Pairwise (· ≥ ·) R) (hnn : ∀ x ∈ R, 0 ≤ x)
    (b : ℝ) (hb : b ∈ R) :
    b ≤ altSum R + altSum (R.erase b) ∧
      altSum R + altSum (R.erase b) ≤ 2 * R.headD 0 - b := by
  induction R with
  | nil => simp at hb
  | cons y s ih =>
    have hge' : List.Pairwise (· ≥ ·) s := (List.pairwise_cons.mp hge).2
    have hnn' : ∀ x ∈ s, 0 ≤ x := fun x hx => hnn x (by simp [hx])
    by_cases hby : b = y
    · -- b is the head y
      subst hby
      rw [List.erase_cons_head, altSum_cons, List.headD_cons]
      constructor
      · linarith
      · linarith
    · -- b ≠ y, so b ∈ s
      have hbs : b ∈ s := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h hby
        · exact h
      rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact fun h => hby h.symm)]
      rw [altSum_cons, altSum_cons]
      have hyhead : s.headD 0 ≤ y := by
        cases s with
        | nil => simp at hbs
        | cons z t =>
          rw [List.headD_cons]
          exact (List.pairwise_cons.mp hge).1 z (by simp)
      obtain ⟨ihlo, ihhi⟩ := ih hge' hnn' hbs
      rw [List.headD_cons]
      constructor
      · -- b ≤ y - altSum s + (y - altSum (s.erase b)) = 2y - (altSum s + altSum (s.erase b))
        -- need altSum s + altSum (s.erase b) ≤ 2*s.headD 0 - b ≤ 2y - b
        nlinarith [ihhi, hyhead]
      · -- 2y - (altSum s + altSum (s.erase b)) ≤ 2y - b  ⟸ altSum s + altSum (s.erase b) ≥ b
        nlinarith [ihlo]

/-- Two-sided single peel: for sorted-desc nonneg `L` and `c ∈ L`,
`|altSum L - altSum (L.erase c)| ≤ c`, i.e. both signed differences are `≤ c`. -/
theorem altSum_erase_single_bounds (L : List ℝ)
    (hge : List.Pairwise (· ≥ ·) L) (hnn : ∀ x ∈ L, 0 ≤ x)
    (c : ℝ) (hc : c ∈ L) :
    altSum L - altSum (L.erase c) ≤ c ∧ altSum (L.erase c) - altSum L ≤ c := by
  induction L with
  | nil => simp at hc
  | cons x t ih =>
    have hge' : List.Pairwise (· ≥ ·) t := (List.pairwise_cons.mp hge).2
    have hnn' : ∀ z ∈ t, 0 ≤ z := fun z hz => hnn z (by simp [hz])
    by_cases hcx : c = x
    · subst hcx
      rw [List.erase_cons_head, altSum_cons]
      -- altSum(c::t) - altSum t = c - 2*altSum t ; other side = 2*altSum t - c
      obtain ⟨hlo, hhi⟩ := altSum_sorted_nonneg_bounds t hge' hnn'
      have hcnn : (0:ℝ) ≤ c := hnn c hc
      have hthead : t.headD 0 ≤ c := by
        cases t with
        | nil => simpa using hcnn
        | cons z w =>
          rw [List.headD_cons]
          exact (List.pairwise_cons.mp hge).1 z (by simp)
      constructor
      · linarith
      · linarith
    · have hct : c ∈ t := by
        rcases List.mem_cons.mp hc with h | h
        · exact absurd h hcx
        · exact h
      rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact fun h => hcx h.symm), altSum_cons, altSum_cons]
      obtain ⟨hlo, hhi⟩ := ih hge' hnn' hct
      constructor
      · linarith
      · linarith

/-- Peel a single certificate element `c` from `q`: `altSum q ≤ c + altSum (q.erase c)`. -/
theorem altSum_peel_single (q : List ℝ)
    (hge : List.Pairwise (· ≥ ·) q) (hnn : ∀ x ∈ q, 0 ≤ x)
    (c : ℝ) (hc : c ∈ q) :
    altSum q ≤ c + altSum (q.erase c) := by
  have h := (altSum_erase_single_bounds q hge hnn c hc).1
  linarith

/-- Two-sided pair-erase invariant assuming `a ≥ b`: the change to `altSum` from
erasing both `a` and `b` is bounded in absolute value by `a - b`. -/
theorem altSum_erase_two_ge (q : List ℝ)
    (hge : List.Pairwise (· ≥ ·) q) (hnn : ∀ x ∈ q, 0 ≤ x)
    (a b : ℝ) (hab : a ≥ b) (ha : a ∈ q) (hb : b ∈ q.erase a) :
    altSum q - altSum ((q.erase a).erase b) ≤ a - b ∧
      altSum ((q.erase a).erase b) - altSum q ≤ a - b := by
  induction q with
  | nil => simp at ha
  | cons x s ih =>
    have hge' : List.Pairwise (· ≥ ·) s := (List.pairwise_cons.mp hge).2
    have hnn' : ∀ z ∈ s, 0 ≤ z := fun z hz => hnn z (by simp [hz])
    by_cases hax : a = x
    · -- CASE a = x
      subst hax
      rw [List.erase_cons_head] at hb ⊢
      have hbs : b ∈ s := hb
      rw [altSum_cons]
      obtain ⟨hlo, hhi⟩ := altSum_erase_pair_bounds s hge' hnn' b hbs
      have hsh : s.headD 0 ≤ a := by
        cases s with
        | nil => simp at hbs
        | cons z t =>
          rw [List.headD_cons]
          exact (List.pairwise_cons.mp hge).1 z (by simp)
      constructor <;> nlinarith [hlo, hhi, hsh]
    · -- CASE a ≠ x
      have has : a ∈ s := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h hax
        · exact h
      have hxa : x ≥ a := (List.pairwise_cons.mp hge).1 a has
      have hbx : b ≠ x := by
        rintro rfl
        exact hax (le_antisymm hxa hab)
      have herasea : (x :: s).erase a = x :: s.erase a := by
        rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact fun h => hax h.symm)]
      rw [herasea] at hb ⊢
      have hbsa : b ∈ s.erase a := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h hbx
        · exact h
      rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact fun h => hbx h.symm)]
      rw [altSum_cons, altSum_cons]
      obtain ⟨ihlo, ihhi⟩ := ih hge' hnn' has hbsa
      constructor <;> linarith [ihlo, ihhi]

/-- Peel a pair `(a,b)` from `q`: `altSum q ≤ |a-b| + altSum ((q.erase a).erase b)`.
Uses `altSum_erase_two_ge` (WLOG `a ≥ b` via `List.erase_comm`). -/
theorem altSum_peel_pair (q : List ℝ)
    (hge : List.Pairwise (· ≥ ·) q) (hnn : ∀ x ∈ q, 0 ≤ x)
    (a b : ℝ) (ha : a ∈ q) (hb : b ∈ q.erase a) :
    altSum q ≤ |a - b| + altSum ((q.erase a).erase b) := by
  rcases le_total b a with hab | hab
  · -- a ≥ b
    have h := (altSum_erase_two_ge q hge hnn a b hab ha hb).1
    have : |a - b| = a - b := abs_of_nonneg (by linarith)
    rw [this]; linarith
  · -- b ≥ a, swap roles using erase_comm
    have hbq : b ∈ q := List.mem_of_mem_erase hb
    have haqb : a ∈ q.erase b := by
      by_cases hne : a = b
      · subst hne; exact hb
      · rw [List.mem_erase_of_ne hne]; exact ha
    have h := (altSum_erase_two_ge q hge hnn b a hab hbq haqb).1
    have hcomm : (q.erase b).erase a = (q.erase a).erase b := List.erase_comm b a
    rw [hcomm] at h
    have : |a - b| = b - a := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [this]; linarith

/-- Master peeling lemma: for a sorted-desc nonneg list `q` whose elements are
partitioned by `parts`, altSum is bounded by the total part cost. -/
theorem altSum_le_parts_cost :
    ∀ (parts : List (ℝ ⊕ (ℝ × ℝ))) (q : List ℝ),
      List.Pairwise (· ≥ ·) q → (∀ x ∈ q, 0 ≤ x) →
      (parts.flatMap partElts).Perm q →
      altSum q ≤ (parts.map partCost).sum := by
  intro parts
  induction parts with
  | nil =>
    intro q hge hnn hperm
    simp only [List.flatMap_nil] at hperm
    have : q = [] := hperm.symm.eq_nil
    subst this
    simp [altSum]
  | cons s rest ih =>
    intro q hge hnn hperm
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons] at *
    cases s with
    | inl c =>
      -- partElts (inl c) = [c]
      simp only [partElts, partCost, List.singleton_append] at *
      -- hperm : (c :: rest.flatMap partElts).Perm q
      have hcq : c ∈ q := hperm.mem_iff.mp (by simp)
      have hrest : (rest.flatMap partElts).Perm (q.erase c) := by
        have := (List.perm_cons_erase hcq)
        exact (List.Perm.cons_inv (hperm.trans this))
      have hqe_ge : List.Pairwise (· ≥ ·) (q.erase c) := pairwise_ge_erase q hge c
      have hqe_nn : ∀ x ∈ q.erase c, 0 ≤ x := fun x hx => hnn x (List.mem_of_mem_erase hx)
      have hpeel := altSum_peel_single q hge hnn c hcq
      have hih := ih (q.erase c) hqe_ge hqe_nn hrest
      linarith
    | inr p =>
      -- partElts (inr p) = [p.1, p.2]
      simp only [partElts, partCost] at *
      -- hperm : (p.1 :: p.2 :: rest.flatMap partElts).Perm q
      have hp1q : p.1 ∈ q := hperm.mem_iff.mp (by simp)
      have hrest1 : (p.2 :: rest.flatMap partElts).Perm (q.erase p.1) := by
        have := (List.perm_cons_erase hp1q)
        exact (List.Perm.cons_inv (hperm.trans this))
      have hp2qe : p.2 ∈ q.erase p.1 := hrest1.mem_iff.mp (by simp)
      have hrest : (rest.flatMap partElts).Perm ((q.erase p.1).erase p.2) := by
        have := (List.perm_cons_erase hp2qe)
        exact (List.Perm.cons_inv (hrest1.trans this))
      have hqe_ge : List.Pairwise (· ≥ ·) ((q.erase p.1).erase p.2) :=
        pairwise_ge_erase _ (pairwise_ge_erase q hge p.1) p.2
      have hqe_nn : ∀ x ∈ (q.erase p.1).erase p.2, 0 ≤ x := fun x hx =>
        hnn x (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
      have hpeel := altSum_peel_pair q hge hnn p.1 p.2 hp1q hp2qe
      have hih := ih ((q.erase p.1).erase p.2) hqe_ge hqe_nn hrest
      linarith

/-- U1 (uncrossing minimality): for a list of nonnegatives, `altSum` of the
descending sort is a lower bound for every pairing certificate's defect. -/
theorem altSum_sorted_le_pairingCert_defect (l : List ℝ)
    (hnn : ∀ x ∈ l, 0 ≤ x) (C : PairingCert l) :
    altSum (l.mergeSort (· ≥ ·)) ≤ C.defect := by
  classical
  set q := l.mergeSort (· ≥ ·) with hq
  have hqge : List.Pairwise (· ≥ ·) q := by rw [hq]; apply List.sorted_mergeSort'
  have hqperm : q.Perm l := by rw [hq]; exact List.mergeSort_perm l _
  have hqnn : ∀ x ∈ q, 0 ≤ x := fun x hx => hnn x (hqperm.mem_iff.mp hx)
  set parts : List (ℝ ⊕ (ℝ × ℝ)) := C.pairs.map Sum.inr ++ C.singles.map Sum.inl with hparts
  have hflatperm : (parts.flatMap partElts).Perm q := by
    rw [hparts]
    rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]
    have hpairs : (C.pairs.flatMap (fun a => partElts (Sum.inr a)))
        = C.pairs.flatMap (fun p => [p.1, p.2]) := by
      apply List.flatMap_congr
      intro p _; rfl
    have hsingles : (C.singles.flatMap (fun a => partElts (Sum.inl a))) = C.singles := by
      induction C.singles with
      | nil => simp
      | cons c t ih => simp only [List.flatMap_cons, ih]; rfl
    rw [hpairs, hsingles]
    exact (C.perm).trans hqperm.symm
  have hcost : (parts.map partCost).sum = C.defect := by
    rw [hparts]
    rw [List.map_append, List.sum_append, List.map_map, List.map_map]
    unfold PairingCert.defect
    have h1 : (C.pairs.map (partCost ∘ Sum.inr)) = C.pairs.map (fun p => |p.1 - p.2|) := by
      apply List.map_congr_left; intro p _; rfl
    have h2 : (C.singles.map (partCost ∘ Sum.inl)) = C.singles := by
      rw [show (partCost ∘ Sum.inl) = (fun c : ℝ => c) from by funext c; rfl]
      exact List.map_id _
    rw [h1, h2]
  have hmain := altSum_le_parts_cost parts q hqge hqnn hflatperm
  rw [hcost] at hmain
  exact hmain


/-- For a `<`-chain `l`, all consecutive differences `b - a` are positive. -/
theorem chain'_zipWith_sub_pos :
    ∀ (l : List ℝ), List.IsChain (· < ·) l →
      ∀ x ∈ List.zipWith (fun a b => b - a) l l.tail, 0 < x := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a t ih =>
    intro hchain x hx
    cases t with
    | nil => simp at hx
    | cons b s =>
      simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at hx
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hrest⟩ := hchain
      rcases hx with h | h
      · rw [h]; linarith
      · exact ih hrest x (by simpa using h)

/-- **(S0)** Every piece length of `A ⊆ (0,1)` is strictly positive. -/
theorem pieceLengths_pos (A : Finset ℝ) (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1)
    (x : ℝ) (hx : x ∈ pieceLengths A) : 0 < x := by
  have hchain : List.IsChain (· < ·) ((0 :: (A.sort (· ≤ ·))) ++ [1]) := by
    have hmem : ∀ y ∈ A.sort (· ≤ ·), 0 < y ∧ y < 1 := by
      intro y hy
      rw [Finset.mem_sort] at hy
      have := hA (Finset.mem_coe.mpr hy)
      rw [Set.mem_Ioo] at this
      exact this
    have hpair : List.Pairwise (· < ·) (A.sort (· ≤ ·)) := by
      have := Finset.sort_sorted_lt A
      exact this.pairwise
    have hchsort : List.IsChain (· < ·) (A.sort (· ≤ ·)) := by
      rw [List.isChain_iff_forall_rel_of_append_cons_cons]
      intro a b l₁ l₂ hl
      rw [hl] at hpair
      rw [List.pairwise_append] at hpair
      obtain ⟨_, hpr, _⟩ := hpair
      rw [List.pairwise_cons] at hpr
      exact hpr.1 b (by simp)
    have hchcons : List.IsChain (· < ·) (0 :: (A.sort (· ≤ ·))) := by
      apply hchsort.isChain_cons
      intro hne
      have := List.head_mem hne
      exact (hmem _ this).1
    rw [List.isChain_append]
    refine ⟨hchcons, List.isChain_singleton _, ?_⟩
    intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    have hxmem : x ∈ (0 :: (A.sort (· ≤ ·))) := List.mem_of_mem_getLast? hx
    rw [List.mem_cons] at hxmem
    rcases hxmem with rfl | hxs
    · norm_num
    · exact (hmem x hxs).2
  have hmain := chain'_zipWith_sub_pos ((0 :: (A.sort (· ≤ ·))) ++ [1]) hchain
  apply hmain
  unfold pieceLengths at hx
  simpa using hx

/-- **(S1a-helper)** In a `≤`-sorted list, between any two positions `i < j` there
is an adjacent gap not exceeding the full difference `xs[j] - xs[i]`. -/
theorem exists_adjacent_gap_le_of_sorted
    (xs : List ℝ) (hsorted : xs.Pairwise (· ≤ ·))
    (i j : ℕ) (hj : j < xs.length) (hij : i < j) :
    ∃ t : ℕ, t + 1 < xs.length ∧ i ≤ t ∧ t < j ∧
      xs.getD (t + 1) 0 - xs.getD t 0 ≤ xs.getD j 0 - xs.getD i 0 := by
  -- take t = i. Reduce to xs[i+1] ≤ xs[j] via sorted monotonicity.
  refine ⟨i, by omega, le_rfl, hij, ?_⟩
  have hi1 : i + 1 < xs.length := by omega
  rw [List.getD_eq_getElem xs 0 hi1, List.getD_eq_getElem xs 0 hj]
  have hle : xs[i + 1] ≤ xs[j] := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hij) with heq | hlt
    · exact le_of_eq (by have : i + 1 = j := heq; subst this; rfl)
    · exact (List.pairwise_iff_getElem.mp hsorted) (i + 1) j hi1 hj hlt
  linarith

/-- **(S1a)** Subset-sum minimum-gap lemma: for `m ≥ 1` positive weights `a`,
there are distinct subsets `U ≠ V` whose sum-difference `δ` satisfies both
`δ ≤ S/(2^m-1)` and `δ ≤ a_i` for every `i`. -/
theorem exists_subset_sum_gap_le {m : ℕ} (hm : 0 < m)
    (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ U V : Finset (Fin m), U ≠ V ∧
      |(∑ i ∈ U, a i) - (∑ i ∈ V, a i)| ≤ (∑ i : Fin m, a i) / ((2:ℝ)^m - 1) ∧
      ∀ i : Fin m, |(∑ i ∈ U, a i) - (∑ i ∈ V, a i)| ≤ a i := by
  classical
  set S : ℝ := ∑ i : Fin m, a i with hSdef
  have hmne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hSpos : 0 < S := by
    rw [hSdef]; apply Finset.sum_pos (fun i _ => ha i); exact Finset.univ_nonempty
  have hden : (0:ℝ) < (2:ℝ)^m - 1 := by
    have : (1:ℝ) < (2:ℝ)^m := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  set f : Finset (Fin m) → ℝ := fun U => ∑ i ∈ U, a i with hfdef
  have hf_range : ∀ U : Finset (Fin m), 0 ≤ f U ∧ f U ≤ S := by
    intro U
    refine ⟨?_, ?_⟩
    · apply Finset.sum_nonneg; intro i _; exact le_of_lt (ha i)
    · rw [hfdef, hSdef]; apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i _ _; exact le_of_lt (ha i)
  set P : Finset (Finset (Fin m) × Finset (Fin m)) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 ≠ p.2) with hPdef
  set g : Finset (Fin m) × Finset (Fin m) → ℝ := fun p => |f p.1 - f p.2| with hgdef
  have hne_univ_empty : (Finset.univ : Finset (Fin m)) ≠ ∅ := by
    simp only [ne_eq, Finset.univ_eq_empty_iff]
    rw [not_isEmpty_iff]; exact ⟨⟨0, hm⟩⟩
  have hPne : P.Nonempty := by
    refine ⟨(Finset.univ, ∅), ?_⟩
    rw [hPdef, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hne_univ_empty⟩
  obtain ⟨p₀, hp₀P, hp₀min⟩ := Finset.exists_min_image P g hPne
  rw [hPdef, Finset.mem_filter] at hp₀P
  obtain ⟨_, hp₀ne⟩ := hp₀P
  set U := p₀.1 with hU
  set V := p₀.2 with hV
  have hUV : U ≠ V := hp₀ne
  set δ : ℝ := g p₀ with hδ
  have hδval : δ = |f U - f V| := by rw [hδ, hgdef, hU, hV]
  have hδmin : ∀ U' V' : Finset (Fin m), U' ≠ V' → δ ≤ |f U' - f V'| := by
    intro U' V' hne'
    have hmemP : (U', V') ∈ P := by
      rw [hPdef, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hne'⟩
    exact hp₀min (U', V') hmemP
  refine ⟨U, V, hUV, ?_, ?_⟩
  · -- δ ≤ S/(2^m-1) via pigeonhole
    -- Box map into range (2^m - 1)
    set N : ℕ := 2^m - 1 with hN
    have hNpos : 0 < N := by
      rw [hN]
      have h1 : 2 ≤ 2^m := by
        calc 2 = 2^1 := by norm_num
          _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    set box : Finset (Fin m) → ℕ := fun U => min (N - 1) ⌊(f U) * N / S⌋₊ with hbox
    -- card of full subset finset
    have hcard : (Finset.range N).card < (Finset.univ : Finset (Finset (Fin m))).card := by
      rw [Finset.card_range, Finset.card_univ]
      simp only [Fintype.card_finset, Fintype.card_fin]
      rw [hN]; have : 1 ≤ 2^m := Nat.one_le_two_pow; omega
    have hmaps : Set.MapsTo box ↑(Finset.univ : Finset (Finset (Fin m))) ↑(Finset.range N) := by
      intro U _
      simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
      rw [hbox]; simp only; omega
    obtain ⟨U', _, V', _, hU'V', hbox_eq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    -- Both f U', f V' in [0,S], same box ⟹ |f U' - f V'| ≤ S/N
    have hgap : |f U' - f V'| ≤ S / N := by
      -- ⌊(f U)*N/S⌋₊ same after min with N-1
      -- Since f U ∈ [0,S], (f U)*N/S ∈ [0,N], so ⌊⌋₊ ∈ [0,N], min with N-1 caps at N-1
      -- Actually points in same box means their scaled floors (capped) agree ⟹ scaled values within 1
      -- Work with x := f U' * N / S, y := f V' * N / S in [0, N]
      set x := f U' * N / S with hx
      set y := f V' * N / S with hy
      have hxr : 0 ≤ x ∧ x ≤ (N:ℝ) := by
        obtain ⟨h0, h1⟩ := hf_range U'
        constructor
        · rw [hx]; positivity
        · rw [hx]; rw [div_le_iff₀ hSpos]
          have : f U' * N ≤ S * N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
          linarith
      have hyr : 0 ≤ y ∧ y ≤ (N:ℝ) := by
        obtain ⟨h0, h1⟩ := hf_range V'
        constructor
        · rw [hy]; positivity
        · rw [hy]; rw [div_le_iff₀ hSpos]
          have : f V' * N ≤ S * N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
          linarith
      -- box U' = box V' means min (N-1) ⌊x⌋₊ = min (N-1) ⌊y⌋₊
      rw [hbox] at hbox_eq
      simp only at hbox_eq
      -- Claim: |x - y| ≤ 1 (then divide)
      have hxy_close : |x - y| ≤ 1 := by
        set c := min (N - 1) ⌊x⌋₊ with hc
        -- x ≥ c (since c ≤ ⌊x⌋₊ ≤ x)
        have hcx_le : (c:ℝ) ≤ x := by
          have : (c:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.min_le_right _ _
          exact le_trans this (Nat.floor_le hxr.1)
        have hcy_le : (c:ℝ) ≤ y := by
          have hcm : c = min (N - 1) ⌊y⌋₊ := hbox_eq
          have h3 : (c:ℝ) ≤ (⌊y⌋₊ : ℝ) := by
            rw [hcm]; exact_mod_cast Nat.min_le_right _ _
          exact le_trans h3 (Nat.floor_le hyr.1)
        have hx_ub : x ≤ (c:ℝ) + 1 := by
          rcases le_or_gt (⌊x⌋₊) (N-1) with hle | hgt
          · have hceq : c = ⌊x⌋₊ := by rw [hc]; omega
            rw [hceq]
            have := Nat.lt_floor_add_one x
            linarith
          · -- ⌊x⌋₊ ≥ N, and x ≤ N ⟹ x = N. c = N - 1.
            have hceq : c = N - 1 := by rw [hc]; omega
            -- x ≤ N ≤ (N-1) + 1
            rw [hceq]
            push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
            linarith [hxr.2]
        have hbe : min (N - 1) ⌊x⌋₊ = min (N - 1) ⌊y⌋₊ := hbox_eq
        have hy_ub : y ≤ (c:ℝ) + 1 := by
          rcases le_or_gt (⌊y⌋₊) (N-1) with hle | hgt
          · have hceq : c = ⌊y⌋₊ := by rw [hc]; omega
            rw [hceq]
            have := Nat.lt_floor_add_one y
            linarith
          · have hceq : c = N - 1 := by rw [hc]; omega
            rw [hceq]
            push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
            linarith [hyr.2]
        rw [abs_le]; constructor <;> linarith
      -- Now |f U' - f V'| = |x - y| * S / N
      have hfx : f U' = x * S / N := by
        rw [hx]; field_simp
      have hfy : f V' = y * S / N := by
        rw [hy]; field_simp
      rw [hfx, hfy]
      have hNr : (0:ℝ) < N := by exact_mod_cast hNpos
      rw [show x * S / N - y * S / N = (x - y) * S / N by ring]
      rw [abs_div, abs_mul]
      rw [abs_of_pos hNr, abs_of_pos hSpos]
      rw [div_le_div_iff_of_pos_right hNr]
      calc |x - y| * S ≤ 1 * S := by nlinarith [hxy_close, hSpos]
        _ = S := by ring
    -- δ ≤ gap ≤ S/N. Need S/N ≤ S/(2^m-1). N = 2^m - 1 so equal.
    have hNeq : (N:ℝ) = (2:ℝ)^m - 1 := by
      rw [hN]; push_cast [Nat.cast_sub Nat.one_le_two_pow]; norm_num
    have hstep : δ ≤ |f U' - f V'| := hδmin U' V' hU'V'
    rw [hδval] at hstep
    calc |f U - f V| ≤ |f U' - f V'| := hstep
      _ ≤ S / N := hgap
      _ = S / ((2:ℝ)^m - 1) := by rw [hNeq]
  · intro i
    have h1 : δ ≤ |f {i} - f ∅| := by
      apply hδmin {i} ∅
      simp only [ne_eq, Finset.singleton_ne_empty, not_false_eq_true]
    have h2 : |f {i} - f ∅| = a i := by
      rw [hfdef]; simp only [Finset.sum_singleton, Finset.sum_empty, sub_zero]
      exact abs_of_pos (ha i)
    rw [hδval] at h1
    rw [h2] at h1; exact h1

/-- **(S1b)** Exact two-side matching: nonempty positive lists of equal sum admit
a common refinement `w`, each reachable by at most `u.length + v.length - 2`
cuts, with all parts positive. -/
theorem exists_exact_matching (u v : List ℝ)
    (hu : ∀ x ∈ u, 0 < x) (hv : ∀ x ∈ v, 0 < x)
    (hune : u ≠ []) (hvne : v ≠ []) (hsum : u.sum = v.sum) :
    ∃ (w : List ℝ),
      RefinesByAtMostNCuts u (u.length + v.length - 2) w ∧
      RefinesByAtMostNCuts v (u.length + v.length - 2) w ∧
      (∀ x ∈ w, 0 < x) ∧ w.length ≤ u.length + v.length - 1 := by
  -- Strong induction on N ≥ u.length + v.length.
  suffices H : ∀ N (u v : List ℝ), u.length + v.length ≤ N →
      (∀ x ∈ u, 0 < x) → (∀ x ∈ v, 0 < x) → u ≠ [] → v ≠ [] → u.sum = v.sum →
      ∃ (w : List ℝ),
        RefinesByAtMostNCuts u (u.length + v.length - 2) w ∧
        RefinesByAtMostNCuts v (u.length + v.length - 2) w ∧
        (∀ x ∈ w, 0 < x) ∧ w.length ≤ u.length + v.length - 1 by
    exact H (u.length + v.length) u v le_rfl hu hv hune hvne hsum
  intro N
  induction N with
  | zero =>
      intro u v hN _ _ hune _ _
      -- u.length ≥ 1, so u.length+v.length ≥ 1 > 0, contradiction
      exfalso
      have : 1 ≤ u.length := List.length_pos_of_ne_nil hune
      omega
  | succ M IH =>
      intro u v hN hu hv hune hvne hsum
      -- destructure u, v
      obtain ⟨u0, us, rfl⟩ : ∃ u0 us, u = u0 :: us := by
        cases u with
        | nil => exact absurd rfl hune
        | cons a t => exact ⟨a, t, rfl⟩
      obtain ⟨v0, vs, rfl⟩ : ∃ v0 vs, v = v0 :: vs := by
        cases v with
        | nil => exact absurd rfl hvne
        | cons a t => exact ⟨a, t, rfl⟩
      have hu0 : 0 < u0 := hu u0 (by simp)
      have hv0 : 0 < v0 := hv v0 (by simp)
      have huspos : ∀ x ∈ us, 0 < x := fun x hx => hu x (by simp [hx])
      have hvspos : ∀ x ∈ vs, 0 < x := fun x hx => hv x (by simp [hx])
      have hussum_nonneg : 0 ≤ us.sum := List.sum_nonneg (fun x hx => le_of_lt (huspos x hx))
      have hvssum_nonneg : 0 ≤ vs.sum := List.sum_nonneg (fun x hx => le_of_lt (hvspos x hx))
      have hsum' : u0 + us.sum = v0 + vs.sum := by simpa using hsum
      -- Trichotomy on u0 vs v0
      rcases lt_trichotomy u0 v0 with hlt | heq | hgt
      · -- u0 < v0 : cut v0 into u0 and (v0 - u0)
        set d : ℝ := v0 - u0 with hd
        have hdpos : 0 < d := by rw [hd]; linarith
        -- us ≠ [] : else u.sum = u0 < v0 ≤ v.sum
        have husne : us ≠ [] := by
          intro h; rw [h] at hsum'
          simp at hsum'
          -- u0 = v0 + vs.sum ≥ v0 > u0
          linarith [hvssum_nonneg, hsum']
        -- v' = u0 :: d :: vs ; v refines to it in 1 cut
        have hv'refines : RefinesByAtMostNCuts (v0 :: vs) 1 (u0 :: d :: vs) := by
          have hbase : RefinesByAtMostNCuts (v0 :: vs) 0 (v0 :: vs) :=
            RefinesByAtMostNCuts.base (List.Perm.refl _)
          have hmem : v0 ∈ (v0 :: vs) := by simp
          have hcut : RefinesByAtMostNCuts (v0 :: vs) 1 (u0 :: d :: (v0 :: vs).erase v0) :=
            RefinesByAtMostNCuts.cut (by rw [hd]; ring) (le_of_lt hu0) (le_of_lt hdpos)
              (List.Perm.refl _) hmem hbase
          simpa using hcut
        -- recurse on us and (d :: vs)
        have hdvspos : ∀ x ∈ (d :: vs), 0 < x := by
          intro x hx; rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hdpos
          · exact hvspos x hx
        have hdvsne : (d :: vs) ≠ [] := by simp
        have hsumrec : us.sum = (d :: vs).sum := by
          simp only [List.sum_cons]; rw [hd]; linarith
        have hmeasure : us.length + (d :: vs).length ≤ M := by
          simp only [List.length_cons] at hN ⊢
          omega
        obtain ⟨w, hwu, hwv, hwpos, hwlen⟩ := IH us (d :: vs) hmeasure huspos hdvspos husne hdvsne hsumrec
        refine ⟨u0 :: w, ?_, ?_, ?_, ?_⟩
        · -- u = u0 :: us refines to u0 :: w
          have hc := refines_cons u0 hwu
          apply refines_mono _ hc
          have hus1 : us.length ≥ 1 := List.length_pos_of_ne_nil husne
          simp only [List.length_cons] at *
          omega
        · -- v = v0 :: vs refines to u0 :: w
          have hc := refines_cons u0 hwv
          have hcomp := refines_trans hv'refines hc
          apply refines_mono _ hcomp
          have hus1 : us.length ≥ 1 := List.length_pos_of_ne_nil husne
          simp only [List.length_cons] at *
          omega
        · intro x hx; rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu0
          · exact hwpos x hx
        · -- length bound
          have hus1 : us.length ≥ 1 := List.length_pos_of_ne_nil husne
          simp only [List.length_cons] at hwlen ⊢
          omega
      · -- u0 = v0
        -- both tails empty or both nonempty
        by_cases husne : us = []
        · -- us = [] ⟹ vs = []
          have hvsempty : vs = [] := by
            rw [husne] at hsum'
            simp at hsum'
            -- u0 = v0 + vs.sum, u0 = v0 ⟹ vs.sum = 0 ⟹ vs = []
            have hvs0 : vs.sum = 0 := by rw [heq] at hsum'; linarith
            by_contra hne
            obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil vs hne
            have : 0 < vs.sum := List.sum_pos vs (fun x hx => hvspos x hx) hne
            linarith
          refine ⟨[u0], ?_, ?_, ?_, ?_⟩
          · rw [husne]; simp only [List.length_cons, List.length_nil]
            rw [hvsempty]; simp only [List.length_cons, List.length_nil]
            exact RefinesByAtMostNCuts.base (List.Perm.refl _)
          · rw [hvsempty]; simp only [List.length_cons, List.length_nil]
            rw [husne]; simp only [List.length_cons, List.length_nil]
            rw [heq]
            exact RefinesByAtMostNCuts.base (List.Perm.refl _)
          · intro x hx; simp only [List.mem_singleton] at hx; rw [hx]; exact hu0
          · -- length bound
            rw [husne, hvsempty]
            simp only [List.length_singleton, List.length_nil, List.length_cons, Nat.zero_add]
            -- 1 ≤ 1 + 1 - 1
            omega
        · -- us ≠ [] ⟹ vs ≠ []
          have hvsne : vs ≠ [] := by
            intro h; rw [h] at hsum'
            simp at hsum'
            -- v0 = u0 + us.sum, u0 = v0 ⟹ us.sum = 0 ⟹ us = []
            have hus0 : us.sum = 0 := by rw [heq] at hsum'; linarith
            apply husne
            by_contra hne
            have : 0 < us.sum := List.sum_pos us (fun x hx => huspos x hx) hne
            linarith
          have hsumrec : us.sum = vs.sum := by
            rw [heq] at hsum'; linarith
          have hmeasure : us.length + vs.length ≤ M := by
            simp only [List.length_cons] at hN; omega
          obtain ⟨w, hwu, hwv, hwpos, hwlen⟩ := IH us vs hmeasure huspos hvspos husne hvsne hsumrec
          refine ⟨u0 :: w, ?_, ?_, ?_, ?_⟩
          · have hc := refines_cons u0 hwu
            apply refines_mono _ hc
            simp only [List.length_cons] at *
            omega
          · have hc := refines_cons v0 hwv
            rw [show u0 = v0 from heq]
            apply refines_mono _ hc
            simp only [List.length_cons] at *
            omega
          · intro x hx; rw [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hu0
            · exact hwpos x hx
          · -- length bound
            have hus1 : us.length ≥ 1 := List.length_pos_of_ne_nil husne
            have hvs1 : vs.length ≥ 1 := List.length_pos_of_ne_nil hvsne
            simp only [List.length_cons] at hwlen ⊢
            omega
      · -- u0 > v0 : symmetric to first case, cut u0 into v0 and (u0 - v0)
        set d : ℝ := u0 - v0 with hd
        have hdpos : 0 < d := by rw [hd]; linarith
        have hvsne : vs ≠ [] := by
          intro h; rw [h] at hsum'
          simp at hsum'
          linarith [hussum_nonneg, hsum']
        have hu'refines : RefinesByAtMostNCuts (u0 :: us) 1 (v0 :: d :: us) := by
          have hbase : RefinesByAtMostNCuts (u0 :: us) 0 (u0 :: us) :=
            RefinesByAtMostNCuts.base (List.Perm.refl _)
          have hmem : u0 ∈ (u0 :: us) := by simp
          have hcut : RefinesByAtMostNCuts (u0 :: us) 1 (v0 :: d :: (u0 :: us).erase u0) :=
            RefinesByAtMostNCuts.cut (by rw [hd]; ring) (le_of_lt hv0) (le_of_lt hdpos)
              (List.Perm.refl _) hmem hbase
          simpa using hcut
        have hduspos : ∀ x ∈ (d :: us), 0 < x := by
          intro x hx; rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hdpos
          · exact huspos x hx
        have hdusne : (d :: us) ≠ [] := by simp
        have hsumrec : (d :: us).sum = vs.sum := by
          simp only [List.sum_cons]; rw [hd]; linarith
        have hmeasure : (d :: us).length + vs.length ≤ M := by
          simp only [List.length_cons] at hN ⊢
          omega
        obtain ⟨w, hwu, hwv, hwpos, hwlen⟩ := IH (d :: us) vs hmeasure hduspos hvspos hdusne hvsne hsumrec
        refine ⟨v0 :: w, ?_, ?_, ?_, ?_⟩
        · -- u = u0 :: us : u →1cut→ v0 :: d :: us = v0 :: (d::us) →budget→ v0 :: w
          have hc := refines_cons v0 hwu
          have hcomp := refines_trans hu'refines hc
          apply refines_mono _ hcomp
          have hvs1 : vs.length ≥ 1 := List.length_pos_of_ne_nil hvsne
          simp only [List.length_cons] at *
          omega
        · -- v = v0 :: vs refines to v0 :: w
          have hc := refines_cons v0 hwv
          apply refines_mono _ hc
          have hvs1 : vs.length ≥ 1 := List.length_pos_of_ne_nil hvsne
          simp only [List.length_cons] at *
          omega
        · intro x hx; rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hv0
          · exact hwpos x hx
        · -- length bound
          have hvs1 : vs.length ≥ 1 := List.length_pos_of_ne_nil hvsne
          simp only [List.length_cons] at hwlen ⊢
          omega

/-- Halving a whole list: `xs` refines (by `xs.length` cuts) to the list where
every element `x` is replaced by two copies of `x/2`. -/
theorem refines_halves (xs : List ℝ) (hnn : ∀ x ∈ xs, 0 ≤ x) :
    RefinesByAtMostNCuts xs xs.length (xs.flatMap (fun x => [x / 2, x / 2])) := by
  induction xs with
  | nil => simpa using RefinesByAtMostNCuts.base (List.Perm.refl ([] : List ℝ))
  | cons x t ih =>
    have hnn' : ∀ y ∈ t, 0 ≤ y := fun y hy => hnn y (by simp [hy])
    have hx0 : 0 ≤ x := hnn x (by simp)
    -- IH on tail, then prepend x, then cut x into x/2,x/2.
    have hih := ih hnn'
    have hcons : RefinesByAtMostNCuts (x :: t) t.length (x :: t.flatMap (fun x => [x / 2, x / 2])) :=
      refines_cons x hih
    -- cut x (head) into x/2, x/2
    have hmem : x ∈ (x :: t.flatMap (fun x => [x / 2, x / 2])) := by simp
    have hcut : RefinesByAtMostNCuts (x :: t) (t.length + 1)
        (x / 2 :: x / 2 :: (x :: t.flatMap (fun x => [x / 2, x / 2])).erase x) :=
      RefinesByAtMostNCuts.cut (by ring) (by linarith) (by linarith)
        (List.Perm.refl _) hmem hcons
    have herase : (x :: t.flatMap (fun x => [x / 2, x / 2])).erase x
        = t.flatMap (fun x => [x / 2, x / 2]) := List.erase_cons_head _ _
    rw [herase] at hcut
    have htarget : (x / 2 :: x / 2 :: t.flatMap (fun x => [x / 2, x / 2]))
        = (x :: t).flatMap (fun x => [x / 2, x / 2]) := by
      simp [List.flatMap_cons]
    rw [htarget] at hcut
    have hlen : t.length + 1 = (x :: t).length := by simp
    rw [hlen] at hcut
    exact hcut

/-- The pairing cost of a list of equal pairs `(x,x)` is zero. -/
theorem defect_equal_pairs (ps : List ℝ) :
    ((ps.map (fun x => (x, x))).map (fun p => |p.1 - p.2|)).sum = 0 := by
  induction ps with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons, sub_self, abs_zero, zero_add]
    exact ih

/-- **(H1a)** Sublist of `l = ofFn a` picked out by a Finset of indices via sorting. -/
noncomputable def subByIdx {m : ℕ} (a : Fin m → ℝ) (A : Finset (Fin m)) : List ℝ :=
  (A.sort (· ≤ ·)).map a

theorem subByIdx_length {m : ℕ} (a : Fin m → ℝ) (A : Finset (Fin m)) :
    (subByIdx a A).length = A.card := by
  unfold subByIdx
  rw [List.length_map, Finset.length_sort]

theorem subByIdx_sum {m : ℕ} (a : Fin m → ℝ) (A : Finset (Fin m)) :
    (subByIdx a A).sum = ∑ i ∈ A, a i := by
  unfold subByIdx
  have hperm : (A.sort (· ≤ ·)).Perm A.toList := Finset.sort_perm_toList A (· ≤ ·)
  rw [List.Perm.sum_eq (hperm.map a)]
  exact Finset.sum_map_toList A a

theorem subByIdx_pos {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (A : Finset (Fin m)) : ∀ x ∈ subByIdx a A, 0 < x := by
  intro x hx
  unfold subByIdx at hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ha i

theorem subByIdx_mem {m : ℕ} (a : Fin m → ℝ) (A : Finset (Fin m)) {x : ℝ}
    (hx : x ∈ subByIdx a A) : ∃ i, x = a i := by
  unfold subByIdx at hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨i, rfl⟩

/-- **(H1b)** Partition permutation: if `P,N,O` partition `univ`, then `ofFn a`
is a permutation of `subByIdx a P ++ subByIdx a N ++ subByIdx a O`. -/
theorem ofFn_perm_partition {m : ℕ} (a : Fin m → ℝ)
    (P N O : Finset (Fin m))
    (hunion : P ∪ N ∪ O = Finset.univ)
    (hPN : Disjoint P N) (hPO : Disjoint P O) (hNO : Disjoint N O) :
    (List.ofFn a).Perm (subByIdx a P ++ subByIdx a N ++ subByIdx a O) := by
  classical
  have hP : (subByIdx a P).Perm (P.toList.map a) :=
    (Finset.sort_perm_toList P (· ≤ ·)).map a
  have hN : (subByIdx a N).Perm (N.toList.map a) :=
    (Finset.sort_perm_toList N (· ≤ ·)).map a
  have hO : (subByIdx a O).Perm (O.toList.map a) :=
    (Finset.sort_perm_toList O (· ≤ ·)).map a
  have hRHS : (subByIdx a P ++ subByIdx a N ++ subByIdx a O).Perm
      ((P.toList.map a) ++ (N.toList.map a) ++ (O.toList.map a)) :=
    (hP.append hN).append hO
  have hcollapse : (P.toList.map a) ++ (N.toList.map a) ++ (O.toList.map a)
      = (P.toList ++ N.toList ++ O.toList).map a := by
    rw [List.map_append, List.map_append]
  have hval : (List.finRange m).Perm (P.toList ++ N.toList ++ O.toList) := by
    rw [← Multiset.coe_eq_coe]
    have hfr : (↑(List.finRange m) : Multiset (Fin m)) = (Finset.univ : Finset (Fin m)).val := by
      rw [Finset.val_univ_fin]
    rw [hfr]
    have hrhs : (↑(P.toList ++ N.toList ++ O.toList) : Multiset (Fin m))
        = P.val + N.val + O.val := by
      rw [← Multiset.coe_add, ← Multiset.coe_add, Finset.coe_toList,
        Finset.coe_toList, Finset.coe_toList]
    rw [hrhs]
    have hu : (Finset.univ : Finset (Fin m)).val = P.val + N.val + O.val := by
      have hPNO : Disjoint (P ∪ N) O := Finset.disjoint_union_left.mpr ⟨hPO, hNO⟩
      have hd1 : (P ∪ N).val = P.val + N.val := by
        rw [Finset.union_val, Multiset.add_eq_union_iff_disjoint.mpr]
        exact Finset.disjoint_val.mpr hPN
      have hd2 : ((P ∪ N) ∪ O).val = (P ∪ N).val + O.val := by
        rw [Finset.union_val, Multiset.add_eq_union_iff_disjoint.mpr]
        exact Finset.disjoint_val.mpr hPNO
      rw [← hunion, hd2, hd1]
    rw [hu]
  have hofFn : List.ofFn a = (List.finRange m).map a := List.ofFn_eq_map
  rw [hofFn]
  refine (hval.map a).trans ?_
  rw [← hcollapse]
  exact hRHS.symm

/-- **(H4)** `w ++ w` is a permutation of `w.flatMap (fun x => [x, x])`. -/
theorem perm_flatMap_pair_self (w : List ℝ) :
    (w.flatMap (fun x => [x, x])).Perm (w ++ w) := by
  induction w with
  | nil => simp
  | cons x t ih =>
    -- LHS = x :: x :: t.flatMap [·,·] ; RHS = (x::t)++(x::t) = x :: (t ++ x :: t)
    simp only [List.flatMap_cons, List.cons_append]
    -- goal: (x :: x :: t.flatMap ..).Perm (x :: t ++ x :: t)
    refine (List.Perm.cons x ?_)
    -- goal: (x :: t.flatMap ..).Perm (t ++ x :: t)
    refine (List.Perm.cons x ih).trans ?_
    -- goal: (x :: (t ++ t)).Perm (t ++ x :: t)
    exact (List.perm_middle (l₁ := t) (l₂ := t) (a := x)).symm

/-- A refinement's target is at least as long as its base (cuts only grow length). -/
theorem refines_length_ge {base Q : List ℝ} {k : ℕ}
    (h : RefinesByAtMostNCuts base k Q) : base.length ≤ Q.length := by
  induction h with
  | base hperm => rw [hperm.length_eq]
  | skip _ ih => exact ih
  | cut hs h1 h2 hstep hmem hh ih =>
      rename_i Qpre Qpost kk s s1 s2
      have hlen : Qpost.length = Qpre.length + 1 := by
        rw [hstep.length_eq]
        simp only [List.length_cons]
        rw [List.length_erase_of_mem hmem]
        have : 1 ≤ Qpre.length := List.length_pos_of_mem hmem
        omega
      omega

/-- Appending a fixed list `c` to both base and target on the right preserves a
refinement (same budget). -/
theorem refines_append_right {base Q : List ℝ} {k : ℕ} (c : List ℝ)
    (h : RefinesByAtMostNCuts base k Q) :
    RefinesByAtMostNCuts (base ++ c) k (Q ++ c) := by
  induction h with
  | base hperm => exact RefinesByAtMostNCuts.base (hperm.append_right c)
  | skip _ ih => exact RefinesByAtMostNCuts.skip ih
  | cut hs h1 h2 hstep hmem hh ih =>
      rename_i Qpre Qpost kk s s1 s2
      have hmem' : s ∈ Qpre ++ c := List.mem_append_left c hmem
      have herase : (Qpre ++ c).erase s = Qpre.erase s ++ c :=
        List.erase_append_left c hmem
      have hstep' : (Qpost ++ c).Perm (s1 :: s2 :: (Qpre ++ c).erase s) := by
        rw [herase]
        have := hstep.append_right c
        simpa only [List.cons_append] using this
      exact RefinesByAtMostNCuts.cut hs h1 h2 hstep' hmem' ih

/-- Appending a fixed list `c` to both base and target on the left preserves a
refinement (same budget). -/
theorem refines_append_left {base Q : List ℝ} {k : ℕ} (c : List ℝ)
    (h : RefinesByAtMostNCuts base k Q) :
    RefinesByAtMostNCuts (c ++ base) k (c ++ Q) := by
  induction c with
  | nil => simpa using h
  | cons a t ih => simpa using refines_cons a ih

/-- **(H2)** Appending refinements: budgets add. -/
theorem refines_append {b1 b2 Q1 Q2 : List ℝ} {k1 k2 : ℕ}
    (h1 : RefinesByAtMostNCuts b1 k1 Q1) (h2 : RefinesByAtMostNCuts b2 k2 Q2) :
    RefinesByAtMostNCuts (b1 ++ b2) (k1 + k2) (Q1 ++ Q2) := by
  have step1 : RefinesByAtMostNCuts (b1 ++ b2) k1 (Q1 ++ b2) :=
    refines_append_right b2 h1
  have step2 : RefinesByAtMostNCuts (Q1 ++ b2) k2 (Q1 ++ Q2) :=
    refines_append_left Q1 h2
  exact refines_trans step1 step2

/-- **(H3)** Budget tightening: a refinement can be re-derived using exactly
`Q.length - base.length` cuts. -/
theorem refines_tighten {base Q : List ℝ} {k : ℕ}
    (h : RefinesByAtMostNCuts base k Q) :
    RefinesByAtMostNCuts base (Q.length - base.length) Q := by
  induction h with
  | base hperm =>
      rename_i Q0
      have hlen : Q0.length = base.length := hperm.length_eq
      rw [hlen, Nat.sub_self]
      exact RefinesByAtMostNCuts.base hperm
  | skip _ ih => exact ih
  | cut hs h1 h2 hstep hmem hh ih =>
      rename_i Qpre Qpost kk s s1 s2
      have hlen : Qpost.length = Qpre.length + 1 := by
        rw [hstep.length_eq]
        simp only [List.length_cons]
        rw [List.length_erase_of_mem hmem]
        have : 1 ≤ Qpre.length := List.length_pos_of_mem hmem
        omega
      have hbase_le : base.length ≤ Qpre.length := refines_length_ge hh
      rw [hlen]
      have hbudget : Qpre.length + 1 - base.length = (Qpre.length - base.length) + 1 := by
        omega
      rw [hbudget]
      exact RefinesByAtMostNCuts.cut hs h1 h2 hstep hmem ih

/-- **(S1-core helper).** The subset-sum + matching construction, given a chosen
ordered partition `P` (heavy side, nonempty), `N` (light side) that are disjoint,
with `σ_N ≤ σ_P` and `δ := σ_P - σ_N ≤ a i` for every `i`. Produces the
equal-pairs-plus-singleton refinement of `l = List.ofFn a` with budget `k`. -/
theorem exists_equal_pairs_core {k : ℕ} {l : List ℝ} (hlen : l.length = k + 1)
    (a : Fin (k + 1) → ℝ) (hapos : ∀ i, 0 < a i) (hlofFn : l = List.ofFn a)
    (P N : Finset (Fin (k + 1)))
    (hPN : Disjoint P N)
    (hNP : (∑ i ∈ N, a i) ≤ (∑ i ∈ P, a i))
    (hPne : P ≠ ∅)
    (hδai : ∀ i, (∑ i ∈ P, a i) - (∑ i ∈ N, a i) ≤ a i) :
    ∃ (ps : List ℝ),
      RefinesByAtMostNCuts l k
        ((ps.flatMap (fun x => [x, x])) ++ [(∑ i ∈ P, a i) - (∑ i ∈ N, a i)]) := by
  classical
  set δ : ℝ := (∑ i ∈ P, a i) - (∑ i ∈ N, a i) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  -- Outside set and partition facts
  set O : Finset (Fin (k+1)) := Finset.univ \ (P ∪ N) with hO
  have hPO : Disjoint P O := by
    apply Finset.disjoint_left.mpr
    intro x hx hxO; rw [hO, Finset.mem_sdiff] at hxO
    exact hxO.2 (Finset.mem_union_left _ hx)
  have hNO : Disjoint N O := by
    apply Finset.disjoint_left.mpr
    intro x hx hxO; rw [hO, Finset.mem_sdiff] at hxO
    exact hxO.2 (Finset.mem_union_right _ hx)
  have hunion : P ∪ N ∪ O = Finset.univ := by
    rw [hO, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  -- The three sublists
  set Pb : List ℝ := subByIdx a P with hPb
  set Nb : List ℝ := subByIdx a N with hNb
  set Ob : List ℝ := subByIdx a O with hOb
  have hPblen : Pb.length = P.card := subByIdx_length a P
  have hNblen : Nb.length = N.card := subByIdx_length a N
  have hOblen : Ob.length = O.card := subByIdx_length a O
  have hPbsum : Pb.sum = ∑ i ∈ P, a i := subByIdx_sum a P
  have hNbsum : Nb.sum = ∑ i ∈ N, a i := subByIdx_sum a N
  have hPbpos : ∀ x ∈ Pb, 0 < x := subByIdx_pos a hapos P
  have hNbpos : ∀ x ∈ Nb, 0 < x := subByIdx_pos a hapos N
  have hObpos : ∀ x ∈ Ob, 0 < x := subByIdx_pos a hapos O
  have hObnn : ∀ x ∈ Ob, 0 ≤ x := fun x hx => le_of_lt (hObpos x hx)
  -- card facts
  have hcard : P.card + N.card + O.card = k + 1 := by
    have hPNO : Disjoint (P ∪ N) O := by
      rw [Finset.disjoint_union_left]; exact ⟨hPO, hNO⟩
    have h1 : (P ∪ N ∪ O).card = Fintype.card (Fin (k+1)) := by
      rw [hunion]; exact Finset.card_univ
    rw [Finset.card_union_of_disjoint hPNO, Finset.card_union_of_disjoint hPN] at h1
    simpa using h1
  -- l ~ Pb ++ Nb ++ Ob
  have hlperm : l.Perm (Pb ++ Nb ++ Ob) := by
    rw [hlofFn]
    exact ofFn_perm_partition a P N O hunion hPN hPO hNO
  -- P nonempty ⟹ Pb nonempty
  have hPcard : 0 < P.card := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hPne)
  have hPbne : Pb ≠ [] := by
    intro he; rw [he] at hPblen; simp at hPblen; omega
  -- head/tail of Pb
  obtain ⟨c, Pb', hPbcons⟩ := List.exists_cons_of_ne_nil hPbne
  have hc_pos : 0 < c := hPbpos c (by rw [hPbcons]; simp)
  -- δ ≤ c: c is a i0 for some i0 ∈ P, and δ ≤ a i0 ≤ c
  have hδc : δ ≤ c := by
    have hcmem : c ∈ Pb := by rw [hPbcons]; simp
    rw [hPb] at hcmem
    obtain ⟨i, rfl⟩ := subByIdx_mem a P hcmem
    exact hδai i
  have hcδ_nn : 0 ≤ c - δ := by linarith
  -- Define Pminus and refinement Pb → δ :: Pminus with 1 cut
  set Pminus : List ℝ := if c - δ = 0 then Pb' else (c - δ) :: Pb' with hPmdef
  have hPm_pos : ∀ x ∈ Pminus, 0 < x := by
    rw [hPmdef]; split
    · intro x hx; exact hPbpos x (by rw [hPbcons]; simp [hx])
    · rename_i hne
      intro x hx; simp only [List.mem_cons] at hx
      rcases hx with h | h
      · rw [h]; rcases lt_or_eq_of_le hcδ_nn with hlt | heq
        · exact hlt
        · exact absurd heq.symm hne
      · exact hPbpos x (by rw [hPbcons]; simp [h])
  have hPm_sum : Pminus.sum = Pb.sum - δ := by
    rw [hPmdef, hPbcons]; split
    · rename_i he; simp only [List.sum_cons]; linarith
    · simp only [List.sum_cons]; ring
  have hPmlen : Pminus.length ≤ Pb.length := by
    rw [hPmdef, hPbcons]; split
    · simp
    · simp
  -- refinement Pb → δ :: Pminus with budget 1
  have hPref : RefinesByAtMostNCuts Pb 1 (δ :: Pminus) := by
    rw [hPmdef]
    by_cases hce : c - δ = 0
    · simp only [hce, if_pos]
      -- δ = c, δ :: Pb' = c :: Pb' = Pb (perm), budget 0 then mono to 1
      have hδeqc : δ = c := by linarith [sub_eq_zero.mp hce]
      have hb : RefinesByAtMostNCuts Pb 0 (δ :: Pb') := by
        apply RefinesByAtMostNCuts.base
        rw [hδeqc, ← hPbcons]
      exact refines_mono (by omega) hb
    · simp only [hce, if_neg, if_false]
      -- cut c = δ + (c - δ) in Pb = c :: Pb'
      have hb0 : RefinesByAtMostNCuts Pb 0 Pb := RefinesByAtMostNCuts.base (List.Perm.refl _)
      have hmem : c ∈ Pb := by rw [hPbcons]; simp
      have hstep : (δ :: (c - δ) :: Pb').Perm (δ :: (c - δ) :: Pb.erase c) := by
        rw [hPbcons, List.erase_cons_head]
      have := RefinesByAtMostNCuts.cut (s := c) (s₁ := δ) (s₂ := c - δ)
        (by ring) hδ0 hcδ_nn hstep hmem hb0
      simpa using this
  -- Ob halves and its map form
  set Oh : List ℝ := Ob.flatMap (fun x => [x / 2, x / 2]) with hOh
  set Ohalf : List ℝ := Ob.map (fun x => x / 2) with hOhalf
  have hOh_map : Ohalf.flatMap (fun x => [x, x]) = Oh := by
    rw [hOhalf, hOh, List.flatMap_map]
  have hObhalves : RefinesByAtMostNCuts Ob Ob.length Oh := refines_halves Ob hObnn
  -- The construction produces w with Pminus → w and Nb → w at some budgets, and w.length ≤ Pminus.length + N.card - 1 (or 0).
  -- We build the refinement of (Pb ++ Nb ++ Ob) into Z = (δ :: w) ++ w ++ Oh, then transport.
  -- Key: produce w, hwPm : Refines Pminus _ w, hwN : Refines Nb _ w, hwlen : w.length ≤ P.card + N.card - 1
  obtain ⟨w, hwPm, hwN, hwpos, hwlen⟩ :
      ∃ w : List ℝ, (∃ b, RefinesByAtMostNCuts Pminus b w) ∧
        (∃ b, RefinesByAtMostNCuts Nb b w) ∧ (∀ x ∈ w, 0 < x) ∧
        w.length ≤ P.card + N.card - 1 := by
    by_cases hNe : N = ∅
    · -- N = ∅: σ_N = 0, δ = σ_P, Pminus.sum = 0, so Pminus = [], w = []
      refine ⟨[], ⟨0, ?_⟩, ⟨0, ?_⟩, by simp, ?_⟩
      · -- Pminus refines to []: Pminus is empty
        have hσN : (∑ i ∈ N, a i) = 0 := by rw [hNe]; simp
        have hδσP : δ = ∑ i ∈ P, a i := by rw [hδ, hσN]; ring
        have hPmsum0 : Pminus.sum = 0 := by
          rw [hPm_sum, hPbsum, hδσP]; ring
        have hPmnil : Pminus = [] := by
          by_contra hne
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil Pminus hne
          have : 0 < Pminus.sum := by
            have := List.sum_pos Pminus (fun x hx => hPm_pos x hx) hne
            exact this
          linarith
        rw [hPmnil]; exact RefinesByAtMostNCuts.base (List.Perm.refl _)
      · have hNbnil : Nb = [] := by
          rw [hNb, hNe]; unfold subByIdx; simp
        rw [hNbnil]; exact RefinesByAtMostNCuts.base (List.Perm.refl _)
      · simp
    · -- N ≠ ∅: matching
      have hNbne : Nb ≠ [] := by
        intro he; rw [hNb] at he
        have : (subByIdx a N).length = 0 := by rw [he]; simp
        rw [subByIdx_length] at this
        have : N.card = 0 := this
        exact hNe (Finset.card_eq_zero.mp this)
      -- Pminus.sum = σ_N > 0 so Pminus ≠ []
      have hσNpos : 0 < ∑ i ∈ N, a i := by
        obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty hNe
        exact Finset.sum_pos (fun i _ => hapos i) ⟨j, hj⟩
      have hPmsumN : Pminus.sum = ∑ i ∈ N, a i := by
        rw [hPm_sum, hPbsum, hδ]; ring
      have hPmne : Pminus ≠ [] := by
        intro he; rw [he] at hPmsumN; simp at hPmsumN; linarith
      have hsumeq : Pminus.sum = Nb.sum := by rw [hPmsumN, hNbsum]
      obtain ⟨w, hw1, hw2, hwpos, hwlen0⟩ :=
        exists_exact_matching Pminus Nb hPm_pos hNbpos hPmne hNbne hsumeq
      refine ⟨w, ⟨_, hw1⟩, ⟨_, hw2⟩, hwpos, ?_⟩
      -- w.length ≤ Pminus.length + Nb.length - 1 ≤ P.card + N.card - 1
      have hle1 : Pminus.length + Nb.length - 1 ≤ P.card + N.card - 1 := by
        have : Pminus.length ≤ P.card := by rw [← hPblen]; exact hPmlen
        have hN : Nb.length = N.card := hNblen
        omega
      omega
  -- Now assemble.
  obtain ⟨bPm, hwPm'⟩ := hwPm
  obtain ⟨bN, hwN'⟩ := hwN
  -- Block1: Pb → δ :: w
  have hBlock1 : RefinesByAtMostNCuts Pb (1 + bPm) (δ :: w) :=
    refines_trans hPref (refines_cons δ hwPm')
  -- Block2: Nb → w
  have hBlock2 : RefinesByAtMostNCuts Nb bN w := hwN'
  -- Block3: Ob → Oh
  have hBlock3 : RefinesByAtMostNCuts Ob Ob.length Oh := hObhalves
  -- append Block1, Block2
  have hAB : RefinesByAtMostNCuts (Pb ++ Nb) ((1 + bPm) + bN) ((δ :: w) ++ w) :=
    refines_append hBlock1 hBlock2
  -- append with Block3
  have hABC : RefinesByAtMostNCuts (Pb ++ Nb ++ Ob) (((1 + bPm) + bN) + Ob.length)
      (((δ :: w) ++ w) ++ Oh) :=
    refines_append hAB hBlock3
  -- transport base to l
  have hL : RefinesByAtMostNCuts l (((1 + bPm) + bN) + Ob.length) (((δ :: w) ++ w) ++ Oh) :=
    refines_of_perm_base hlperm hABC
  -- Set ps and T
  set ps : List ℝ := w ++ Ohalf with hps
  set T : List ℝ := (ps.flatMap (fun x => [x, x])) ++ [δ] with hT
  -- Z ~ T
  have hZT : (((δ :: w) ++ w) ++ Oh).Perm T := by
    rw [hT, hps]
    -- T = (w ++ Ohalf).flatMap[x,x] ++ [δ] = w.flatMap[x,x] ++ Oh ++ [δ]
    have hTexp : (w ++ Ohalf).flatMap (fun x => [x, x]) ++ [δ]
        = w.flatMap (fun x => [x, x]) ++ Oh ++ [δ] := by
      rw [List.flatMap_append, hOh_map]
    rw [hTexp]
    -- Z = δ :: (w ++ w ++ Oh) ; goal: (δ :: w ++ w) ++ Oh ~ w.flatMap ++ Oh ++ [δ]
    have hww : (w ++ w).Perm (w.flatMap (fun x => [x, x])) := (perm_flatMap_pair_self w).symm
    have hstep1 : (((δ :: w) ++ w) ++ Oh) = δ :: ((w ++ w) ++ Oh) := by simp
    have hstep2 : (δ :: ((w ++ w) ++ Oh)).Perm (δ :: (w.flatMap (fun x => [x, x]) ++ Oh)) :=
      List.Perm.cons δ (hww.append_right Oh)
    have hstep3 : (δ :: (w.flatMap (fun x => [x, x]) ++ Oh)).Perm
        (w.flatMap (fun x => [x, x]) ++ Oh ++ [δ]) := by
      have := List.perm_append_singleton δ (w.flatMap (fun x => [x, x]) ++ Oh)
      simpa using this.symm
    rw [hstep1]
    exact hstep2.trans hstep3
  have hLT : RefinesByAtMostNCuts l (((1 + bPm) + bN) + Ob.length) T :=
    refines_target_perm hZT hL
  -- tighten
  have hTight : RefinesByAtMostNCuts l (T.length - l.length) T := refines_tighten hLT
  -- budget bound: T.length - l.length ≤ k
  have hTlen : T.length = 2 * (w.length + Ob.length) + 1 := by
    rw [hT, hps]
    have hfm : ((w ++ Ohalf).flatMap (fun x => [x, x])).length = 2 * (w ++ Ohalf).length := by
      induction (w ++ Ohalf) with
      | nil => simp
      | cons y t ih => simp [List.flatMap_cons, ih]; ring
    have hOhalflen : Ohalf.length = Ob.length := by rw [hOhalf]; simp
    simp only [List.length_append, List.length_cons, List.length_nil, hfm]
    rw [hOhalflen]
  have hbudget : T.length - l.length ≤ k := by
    rw [hTlen, hlen]
    have hOblen' : Ob.length = O.card := hOblen
    -- w.length + Ob.length ≤ k, since w.length ≤ P.card+N.card-1, Ob.length = O.card, sum = k
    have : w.length + Ob.length ≤ k := by
      rw [hOblen']
      have hPcard1 : 1 ≤ P.card := hPcard
      omega
    omega
  exact ⟨ps, refines_mono hbudget hTight⟩


/-- **(S1-core, list form).** From `k+1` positive reals one reaches, by `≤ k`
cuts, a list of the form `equal-pairs ++ [δ]` with `0 ≤ δ ≤ l.sum/(2^{k+1}-1)`. -/
theorem exists_equal_pairs_refinement (k : ℕ) (l : List ℝ)
    (hlen : l.length = k + 1) (hpos : ∀ x ∈ l, 0 < x) :
    ∃ (ps : List ℝ) (δ : ℝ), 0 ≤ δ ∧ δ ≤ l.sum / ((2:ℝ)^(k+1) - 1) ∧
      RefinesByAtMostNCuts l k ((ps.flatMap (fun x => [x, x])) ++ [δ]) := by
  classical
  set m := k + 1 with hm
  set a : Fin m → ℝ := fun i => l.get (Fin.cast hlen.symm i) with ha
  have hlofFn : l = List.ofFn a := by
    apply List.ext_get
    · rw [List.length_ofFn, hlen]
    · intro i h1 h2
      simp only [ha, List.get_ofFn]
      congr 1
  have hapos : ∀ i, 0 < a i := by
    intro i; rw [ha]; apply hpos; exact List.get_mem _ _
  have hmpos : 0 < m := by omega
  obtain ⟨U, V, hUV, hΔle, hΔai⟩ := exists_subset_sum_gap_le hmpos a hapos
  set S : ℝ := ∑ i : Fin m, a i with hSdef
  have hlsum : l.sum = S := by rw [hlofFn, hSdef, List.sum_ofFn]
  -- gap in terms of set-differences
  have hgap : (∑ i ∈ U, a i) - (∑ i ∈ V, a i) = (∑ i ∈ U \ V, a i) - (∑ i ∈ V \ U, a i) := by
    have e1 : (∑ i ∈ U, a i) = (∑ i ∈ U \ V, a i) + (∑ i ∈ U ∩ V, a i) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter U V), Finset.sdiff_union_inter]
    have e2 : (∑ i ∈ V, a i) = (∑ i ∈ V \ U, a i) + (∑ i ∈ V ∩ U, a i) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter V U), Finset.sdiff_union_inter]
    rw [e1, e2, Finset.inter_comm U V]; ring
  set p0 : Finset (Fin m) := U \ V with hp0
  set n0 : Finset (Fin m) := V \ U with hn0
  have hdisj : Disjoint p0 n0 := by
    rw [hp0, hn0]
    apply Finset.disjoint_left.mpr
    intro x hx hx2
    rw [Finset.mem_sdiff] at hx hx2
    exact hx.2 hx2.1
  have hpn_ne : ¬ (p0 = ∅ ∧ n0 = ∅) := by
    rintro ⟨he1, he2⟩
    apply hUV
    -- U \ V = ∅ and V \ U = ∅ ⟹ U = V
    have he1' : U \ V = ∅ := by rw [← hp0]; exact he1
    have he2' : V \ U = ∅ := by rw [← hn0]; exact he2
    apply Finset.Subset.antisymm
    · intro x hx; by_contra hxV
      have : x ∈ U \ V := Finset.mem_sdiff.mpr ⟨hx, hxV⟩
      rw [he1'] at this; exact absurd this (Finset.notMem_empty x)
    · intro x hx; by_contra hxU
      have : x ∈ V \ U := Finset.mem_sdiff.mpr ⟨hx, hxU⟩
      rw [he2'] at this; exact absurd this (Finset.notMem_empty x)
  have hΔeq : |(∑ i ∈ U, a i) - (∑ i ∈ V, a i)| = |(∑ i ∈ p0, a i) - (∑ i ∈ n0, a i)| := by
    rw [hgap]
  -- δ nonneg, bound, δ ≤ a i
  have hδle' : |(∑ i ∈ p0, a i) - (∑ i ∈ n0, a i)| ≤ S / ((2:ℝ)^m - 1) := by
    rw [← hΔeq]; rw [hSdef]; exact hΔle
  have hδai' : ∀ i, |(∑ i ∈ p0, a i) - (∑ i ∈ n0, a i)| ≤ a i := by
    intro i; rw [← hΔeq]; exact hΔai i
  -- Choose ordered P, N with σ_P ≥ σ_N
  rcases le_total (∑ i ∈ n0, a i) (∑ i ∈ p0, a i) with hle | hle
  · -- P = p0, N = n0
    have hPne : p0 ≠ ∅ := by
      intro he
      apply hpn_ne
      refine ⟨he, ?_⟩
      -- p0 = ∅ ⟹ σ_{p0}=0 ≥ σ_{n0} ≥ 0 ⟹ σ_{n0}=0 ⟹ n0 = ∅
      rw [he] at hle; simp at hle
      have hn0nn : 0 ≤ (∑ i ∈ n0, a i) := Finset.sum_nonneg (fun i _ => le_of_lt (hapos i))
      have : (∑ i ∈ n0, a i) = 0 := le_antisymm hle hn0nn
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty hne
      have hpos : 0 < (∑ i ∈ n0, a i) := Finset.sum_pos (fun i _ => hapos i) ⟨j, hj⟩
      linarith
    have hδai2 : ∀ i, (∑ i ∈ p0, a i) - (∑ i ∈ n0, a i) ≤ a i := by
      intro i
      have := hδai' i
      rw [abs_of_nonneg (by linarith)] at this
      exact this
    obtain ⟨ps, href⟩ := exists_equal_pairs_core hlen a hapos hlofFn p0 n0 hdisj hle hPne hδai2
    refine ⟨ps, (∑ i ∈ p0, a i) - (∑ i ∈ n0, a i), by linarith, ?_, href⟩
    rw [hlsum]
    have := hδle'
    rw [abs_of_nonneg (by linarith)] at this
    exact this
  · -- P = n0, N = p0
    have hPne : n0 ≠ ∅ := by
      intro he
      apply hpn_ne
      refine ⟨?_, he⟩
      rw [he] at hle; simp at hle
      have hp0nn : 0 ≤ (∑ i ∈ p0, a i) := Finset.sum_nonneg (fun i _ => le_of_lt (hapos i))
      have : (∑ i ∈ p0, a i) = 0 := le_antisymm hle hp0nn
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty hne
      have hpos : 0 < (∑ i ∈ p0, a i) := Finset.sum_pos (fun i _ => hapos i) ⟨j, hj⟩
      linarith
    have hδai2 : ∀ i, (∑ i ∈ n0, a i) - (∑ i ∈ p0, a i) ≤ a i := by
      intro i
      have := hδai' i
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at this
      exact this
    obtain ⟨ps, href⟩ := exists_equal_pairs_core hlen a hapos hlofFn n0 p0 hdisj.symm hle hPne hδai2
    refine ⟨ps, (∑ i ∈ n0, a i) - (∑ i ∈ p0, a i), by linarith, ?_, href⟩
    rw [hlsum]
    have := hδle'
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at this
    exact this

/-- **(S1)** Combinatorial core: `k+1` positive reals reach, by `≤ k` cuts, a
multiset with a pairing certificate of `≤ 1` singleton and defect
`≤ l.sum/(2^{k+1}-1)`. -/
theorem exists_equalized_refinement (k : ℕ) (l : List ℝ)
    (hlen : l.length = k + 1) (hpos : ∀ x ∈ l, 0 < x) :
    ∃ Q, RefinesByAtMostNCuts l k Q ∧
      ∃ C : PairingCert Q, C.singles.length ≤ 1 ∧
        C.defect ≤ l.sum / ((2:ℝ)^(k+1) - 1) := by
  obtain ⟨ps, δ, hδ0, hδle, href⟩ := exists_equal_pairs_refinement k l hlen hpos
  refine ⟨(ps.flatMap (fun x => [x, x])) ++ [δ], href, ?_⟩
  -- Build the pairing certificate: pairs = ps.map (x,x), singles = [δ].
  have hpermQ : (((ps.map (fun x => (x, x))).flatMap (fun p => [p.1, p.2])) ++ [δ]).Perm
      ((ps.flatMap (fun x => [x, x])) ++ [δ]) := by
    have hfm : (ps.map (fun x => (x, x))).flatMap (fun p => [p.1, p.2])
        = ps.flatMap (fun x => [x, x]) := by
      rw [List.flatMap_map]
    rw [hfm]
  refine ⟨⟨ps.map (fun x => (x, x)), [δ], hpermQ⟩, ?_, ?_⟩
  · simp
  · -- defect = 0 + δ = δ ≤ bound
    unfold PairingCert.defect
    simp only [defect_equal_pairs, List.sum_cons, List.sum_nil, add_zero, zero_add]
    exact hδle

theorem head_le_getLast_pw : ∀ (a : ℝ) (l : List ℝ),
    List.Pairwise (· < ·) (a :: l) → a ≤ (a :: l).getLast! := by
  intro a l
  induction l generalizing a with
  | nil => intro _; simp
  | cons z t ih =>
    intro hpw
    rw [List.pairwise_cons] at hpw
    obtain ⟨haz, hpwt⟩ := hpw
    have hazlt : a < z := haz z (by simp)
    have : (a :: z :: t).getLast! = (z :: t).getLast! := by
      simp [List.getLast!_cons_eq_getLastD]
    rw [this]
    have := ih z hpwt
    linarith

theorem diffs_orderedInsert_prescribed (s s₁ s₂ : ℝ)
    (hs : s = s₁ + s₂) (hs1 : 0 < s₁) (hs2 : 0 < s₂) :
    ∀ (m : List ℝ), List.Pairwise (· < ·) m → s ∈ diffs m →
      ∃ b : ℝ, m.head! < b ∧ b < m.getLast! ∧ b ∉ m ∧
        (diffs (List.orderedInsert (· ≤ ·) b m)).Perm
          (s₁ :: s₂ :: (diffs m).erase s) := by
  intro m
  induction m with
  | nil => intro _ hsmem; simp [diffs] at hsmem
  | cons x rest ih =>
    intro hpw hsmem
    cases rest with
    | nil => simp [diffs] at hsmem
    | cons y rest' =>
      rw [List.pairwise_cons] at hpw
      obtain ⟨hx_all, hpw_rest⟩ := hpw
      have hxy : x < y := hx_all y (by simp)
      rw [diffs_cons_cons] at hsmem
      rw [List.mem_cons] at hsmem
      have hlast_eq : (x :: y :: rest').getLast! = (y :: rest').getLast! := by
        simp [List.getLast!_cons_eq_getLastD]
      have hy_le_last : y ≤ (y :: rest').getLast! := head_le_getLast_pw y rest' hpw_rest
      by_cases hsx : s = y - x
      · -- b lands in the FIRST gap, b = x + s₁
        have hbx : x + s₁ < y := by rw [hsx] at hs; linarith
        refine ⟨x + s₁, ?_, ?_, ?_, ?_⟩
        · simp only [List.head!_cons]; linarith
        · rw [hlast_eq]; linarith
        · -- x + s₁ ∉ x :: y :: rest'
          simp only [List.mem_cons, not_or]
          refine ⟨by linarith, by linarith, ?_⟩
          intro hmem
          have hylt : y < x + s₁ := by
            rw [List.pairwise_cons] at hpw_rest
            exact hpw_rest.1 _ hmem
          linarith
        · -- perm: orderedInsert = x :: (x+s₁) :: y :: rest'
          have hoi : List.orderedInsert (· ≤ ·) (x + s₁) (x :: y :: rest')
              = x :: (x + s₁) :: y :: rest' := by
            rw [List.orderedInsert_cons, if_neg (by simp; linarith),
                List.orderedInsert_cons, if_pos (by linarith)]
          rw [hoi, diffs_cons_cons, diffs_cons_cons]
          -- (x+s₁ - x) :: (y - (x+s₁)) :: diffs (y::rest')
          have e1 : x + s₁ - x = s₁ := by ring
          have e2 : y - (x + s₁) = s₂ := by rw [hsx] at hs; linarith
          rw [e1, e2]
          -- RHS: (diffs (x::y::rest')).erase s = ((y-x)::diffs(y::rest')).erase s = diffs(y::rest')
          rw [diffs_cons_cons]
          have hers : ((y - x) :: diffs (y :: rest')).erase s = diffs (y :: rest') := by
            rw [← hsx]; exact List.erase_cons_head s (diffs (y :: rest'))
          rw [hers]
      · -- s ∈ diffs (y :: rest'), recurse
        have hsmem' : s ∈ diffs (y :: rest') := by
          rcases hsmem with h | h
          · exact absurd h hsx
          · exact h
        obtain ⟨b, hbhead, hblast, hbnotmem, hbperm⟩ := ih hpw_rest hsmem'
        simp only [List.head!_cons] at hbhead
        refine ⟨b, ?_, ?_, ?_, ?_⟩
        · simp only [List.head!_cons]; linarith
        · rw [hlast_eq]; exact hblast
        · simp only [List.mem_cons, not_or] at hbnotmem ⊢
          exact ⟨by linarith, hbnotmem.1, hbnotmem.2⟩
        · -- orderedInsert b (x::y::rest') = x :: orderedInsert b (y::rest')
          have hoi : List.orderedInsert (· ≤ ·) b (x :: y :: rest')
              = x :: List.orderedInsert (· ≤ ·) b (y :: rest') := by
            rw [List.orderedInsert_cons, if_neg (by simp; linarith)]
          rw [hoi]
          -- diffs (x :: orderedInsert b (y::rest'))
          -- head of orderedInsert b (y::rest') is y (since ¬ b ≤ y, b > y)
          have hoi_head : (List.orderedInsert (· ≤ ·) b (y :: rest')).head? = some y := by
            rw [List.orderedInsert_cons]
            simp only [not_le.mpr hbhead, if_false, List.head?_cons]
          obtain ⟨u, hu⟩ : ∃ u, List.orderedInsert (· ≤ ·) b (y :: rest') = y :: u := by
            cases hoi2 : List.orderedInsert (· ≤ ·) b (y :: rest') with
            | nil => rw [hoi2] at hoi_head; simp at hoi_head
            | cons z t =>
              rw [hoi2] at hoi_head; simp only [List.head?_cons] at hoi_head
              obtain rfl : z = y := by simpa using hoi_head
              exact ⟨t, rfl⟩
          rw [hu, diffs_cons_cons, diffs_cons_cons]
          -- goal: (y-x) :: diffs (y::u)  Perm  s₁ :: s₂ :: ((y-x)::diffs(y::rest')).erase s
          -- hbperm : diffs (orderedInsert b (y::rest')) ~ s₁ :: s₂ :: (diffs(y::rest')).erase s
          -- via hu: diffs (y::u) ~ s₁::s₂::(diffs(y::rest')).erase s
          have hbperm' : (diffs (y :: u)).Perm (s₁ :: s₂ :: (diffs (y :: rest')).erase s) := by
            rw [← hu]; exact hbperm
          -- erase on RHS: s ≠ y-x so peels tail
          have hers : ((y - x) :: diffs (y :: rest')).erase s
              = (y - x) :: (diffs (y :: rest')).erase s := by
            apply List.erase_cons_tail
            simp only [beq_iff_eq]
            intro h; exact hsx (by rw [← h])
          rw [hers]
          -- goal: (y-x) :: diffs(y::u) ~ s₁ :: s₂ :: (y-x) :: (diffs(y::rest')).erase s
          -- from hbperm' : diffs(y::u) ~ s₁::s₂::(diffs(y::rest')).erase s
          refine (hbperm'.cons (y - x)).trans ?_
          -- (y-x) :: s₁ :: s₂ :: L ~ s₁ :: s₂ :: (y-x) :: L
          exact (List.Perm.swap s₁ (y - x) (s₂ :: (diffs (y :: rest')).erase s)).trans
            ((List.Perm.swap s₂ (y - x) ((diffs (y :: rest')).erase s)).cons s₁)


/-- **(Lemma 2, prescribed cut).** Given a mark set `C ⊆ (0,1)`, a gap
`s ∈ pieceLengths C` and a *prescribed* positive split `s = s₁ + s₂` with
`s₁, s₂ > 0`, there is a new interior mark `b ∉ C` realizing exactly that split. -/
theorem pieceLengths_prescribed_cut (C : Finset ℝ)
    (hC : ↑C ⊆ Set.Ioo (0 : ℝ) 1) (s s₁ s₂ : ℝ)
    (hs : s = s₁ + s₂) (hs1 : 0 < s₁) (hs2 : 0 < s₂)
    (hsmem : s ∈ pieceLengths C) :
    ∃ b : ℝ, b ∈ Set.Ioo (0 : ℝ) 1 ∧ b ∉ C ∧
      (pieceLengths (insert b C)).Perm (s₁ :: s₂ :: (pieceLengths C).erase s) := by
  classical
  set m : List ℝ := (0 : ℝ) :: (C.sort (· ≤ ·)) ++ [1] with hm
  have hplC : pieceLengths C = diffs m := rfl
  have hmemC : ∀ y ∈ C.sort (· ≤ ·), 0 < y ∧ y < 1 := by
    intro y hy
    rw [Finset.mem_sort] at hy
    have := hC (Finset.mem_coe.mpr hy)
    rw [Set.mem_Ioo] at this
    exact this
  have hmpw : List.Pairwise (· < ·) m := by
    rw [hm]
    have hCsort : List.Pairwise (· < ·) (C.sort (· ≤ ·)) := (Finset.sort_sorted_lt _).pairwise
    rw [List.cons_append, List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact (hmemC z hz).1
      · norm_num
    · rw [List.pairwise_append]
      refine ⟨hCsort, by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      exact (hmemC a ha).2
  have hsmem' : s ∈ diffs m := by rw [← hplC]; exact hsmem
  obtain ⟨b, hbhead, hblast, hbnotmem, hbperm⟩ :=
    diffs_orderedInsert_prescribed s s₁ s₂ hs hs1 hs2 m hmpw hsmem'
  have hmhead : m.head! = 0 := by rw [hm]; simp only [List.cons_append, List.head!_cons]
  have hmlast : m.getLast! = 1 := by
    rw [hm]
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_concat]; rfl
  rw [hmhead] at hbhead
  rw [hmlast] at hblast
  have hbnotC : b ∉ C := by
    intro hbC
    apply hbnotmem
    rw [hm]
    have : b ∈ C.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact hbC
    rw [List.mem_append, List.mem_cons]
    exact Or.inl (Or.inr this)
  refine ⟨b, ⟨hbhead, hblast⟩, hbnotC, ?_⟩
  have hplins : pieceLengths (insert b C) = diffs (List.orderedInsert (· ≤ ·) b m) := by
    rw [pieceLengths_eq_diffs, sort_insert_eq_orderedInsert C b hbnotC, hm]
    rw [augmented_orderedInsert (C.sort (· ≤ ·)) b hbhead hblast]
  rw [hplins, hplC]
  exact hbperm

/-- **(S2)** Realize a cut-refinement of `pieceLengths A` as admissible disjoint
marks `B`. -/
theorem exists_marks_realizing_refinement (n : ℕ) (A : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : k ≤ n) (Q : List ℝ)
    (hQpos : ∀ x ∈ Q, 0 < x)
    (hQ : RefinesByAtMostNCuts (pieceLengths A) k Q) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      (pieceLengths (A ∪ B)).Perm Q := by
  -- Strengthened claim: B.card ≤ k, by induction on the derivation.
  suffices hClaim : ∀ (k : ℕ) (Q : List ℝ), (∀ x ∈ Q, 0 < x) →
      RefinesByAtMostNCuts (pieceLengths A) k Q →
      ∃ B : Finset ℝ, ↑B ⊆ Set.Ioo (0 : ℝ) 1 ∧ B.card ≤ k ∧ Disjoint A B ∧
        (pieceLengths (A ∪ B)).Perm Q by
    obtain ⟨B, hBsub, hBcard, hBdisj, hBperm⟩ := hClaim k Q hQpos hQ
    exact ⟨B, ⟨hBsub, le_trans hBcard hk⟩, hBdisj, hBperm⟩
  clear hQ hQpos hk k Q
  intro k Q hQpos hQ
  induction hQ with
  | @base Q hperm =>
    -- base = pieceLengths A ; hperm : Q.Perm (pieceLengths A)
    refine ⟨∅, by simp, by simp, by simp, ?_⟩
    rw [Finset.union_empty]
    exact hperm.symm
  | @skip Q k' h' ih =>
    obtain ⟨B, hBsub, hBcard, hBdisj, hBperm⟩ := ih hQpos
    exact ⟨B, hBsub, le_trans hBcard (Nat.le_succ k'), hBdisj, hBperm⟩
  | @cut Q₀ Q k' s s₁ s₂ hs h1 h2 hstep hmem h' ih =>
    -- Step 1: s₁, s₂ > 0 from positivity of Q
    have hs1pos : 0 < s₁ := hQpos s₁ (hstep.mem_iff.mpr (by simp))
    have hs2pos : 0 < s₂ := hQpos s₂ (hstep.mem_iff.mpr (by simp))
    -- Step 2: positivity of Q₀
    have hQ0pos : ∀ x ∈ Q₀, 0 < x := by
      intro t ht
      by_cases hts : t = s
      · rw [hts, hs]; linarith
      · have : t ∈ Q₀.erase s := List.mem_erase_of_ne hts |>.mpr ht
        exact hQpos t (hstep.mem_iff.mpr (by simp [this]))
    -- Step 3: IH on parent
    obtain ⟨C, hCsub, hCcard, hCdisj, hCperm⟩ := ih hQ0pos
    -- D = A ∪ C
    have hDsub : ↑(A ∪ C) ⊆ Set.Ioo (0 : ℝ) 1 := by
      rw [Finset.coe_union]; exact Set.union_subset hA hCsub
    -- Step 4: s ∈ pieceLengths D
    have hsmemD : s ∈ pieceLengths (A ∪ C) := hCperm.mem_iff.mpr hmem
    -- Step 5: realize the prescribed cut
    obtain ⟨b, hbIoo, hbD, hbperm⟩ :=
      pieceLengths_prescribed_cut (A ∪ C) hDsub s s₁ s₂ hs hs1pos hs2pos hsmemD
    -- b ∉ A and b ∉ C
    have hbnotA : b ∉ A := fun h => hbD (Finset.mem_union_left _ h)
    have hbnotC : b ∉ C := fun h => hbD (Finset.mem_union_right _ h)
    refine ⟨insert b C, ?_, ?_, ?_, ?_⟩
    · -- interior
      rw [Finset.coe_insert]
      exact Set.insert_subset hbIoo hCsub
    · -- cardinality
      rw [Finset.card_insert_of_notMem hbnotC]
      omega
    · -- disjoint A (insert b C)
      rw [Finset.disjoint_insert_right]
      exact ⟨hbnotA, hCdisj⟩
    · -- permutation
      -- A ∪ insert b C = insert b (A ∪ C)
      have hAB : A ∪ insert b C = insert b (A ∪ C) := by
        rw [Finset.union_insert]
      rw [hAB]
      -- pieceLengths (insert b (A∪C)) ~ s₁::s₂::(pieceLengths (A∪C)).erase s
      refine hbperm.trans ?_
      -- (pieceLengths (A∪C)).erase s ~ Q₀.erase s
      have heraseperm : ((pieceLengths (A ∪ C)).erase s).Perm (Q₀.erase s) :=
        hCperm.erase s
      -- prepend s₁, s₂
      refine ((heraseperm.cons s₂).cons s₁).trans ?_
      -- s₁::s₂::Q₀.erase s ~ Q  (symm of hstep)
      exact hstep.symm

/-- **(S3-arith)** The answer equals `(1 + 1/(2^{n+1}-1))/2`. -/
theorem answer_eq_half_one_add_inv (n : ℕ) :
    (2:ℝ)^n / ((2:ℝ)^(n+1) - 1) = (1 + 1 / ((2:ℝ)^(n+1) - 1)) / 2 := by
  have hpos : (0:ℝ) < (2:ℝ)^(n+1) - 1 := by
    have : (1:ℝ) < (2:ℝ)^(n+1) := by
      apply one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hne : (2:ℝ)^(n+1) - 1 ≠ 0 := ne_of_gt hpos
  field_simp
  ring

/-- Layer 5: a single piece `s` splits (with `parts.length - 1` cuts) into any
list `parts` of positive reals summing to `s`. -/
theorem refines_single_to_parts (s : ℝ) (parts : List ℝ)
    (hpos : ∀ x ∈ parts, 0 < x) (hsum : parts.sum = s) (hne : parts ≠ []) :
    RefinesByAtMostNCuts [s] (parts.length - 1) parts := by
  have helper : ∀ (parts : List ℝ), (∀ x ∈ parts, 0 < x) → parts ≠ [] →
      ∀ (base Q : List ℝ) (k : ℕ) (t : ℝ),
        RefinesByAtMostNCuts base k Q → t ∈ Q → parts.sum = t →
        ∃ Q', Q'.Perm (parts ++ Q.erase t) ∧
          RefinesByAtMostNCuts base (k + (parts.length - 1)) Q' := by
    intro parts
    induction parts with
    | nil => intro _ hne; exact absurd rfl hne
    | cons x rest ih =>
      intro hpos _ base Q k t hQ hmem hsum
      cases rest with
      | nil =>
        -- singleton: x = t
        have hxt : x = t := by simpa using hsum
        refine ⟨Q, ?_, ?_⟩
        · -- Q ~ [x] ++ Q.erase t = x :: Q.erase t = t :: Q.erase t
          rw [hxt]
          simpa using (List.perm_cons_erase hmem)
        · simpa using hQ
      | cons y ys =>
        set rSum := (y :: ys).sum with hrSum
        have hxrs : t = x + rSum := by
          rw [← hsum]; simp [hrSum]
        have hx0 : (0:ℝ) ≤ x := le_of_lt (hpos x (by simp))
        have hrs0 : (0:ℝ) ≤ rSum := by
          rw [hrSum]
          apply List.sum_nonneg
          intro z hz; exact le_of_lt (hpos z (List.mem_cons_of_mem x hz))
        -- First cut: base-context Q → x :: rSum :: Q.erase t
        have hcut : RefinesByAtMostNCuts base (k + 1) (x :: rSum :: Q.erase t) :=
          RefinesByAtMostNCuts.cut hxrs hx0 hrs0 (List.Perm.refl _) hmem hQ
        -- rSum ∈ new target
        have hmem2 : rSum ∈ (x :: rSum :: Q.erase t) := by simp
        -- rest positive
        have hrestpos : ∀ z ∈ (y :: ys), 0 < z := fun z hz => hpos z (List.mem_cons_of_mem x hz)
        have hrestne : (y :: ys) ≠ [] := by simp
        -- IH on rest inside the new target
        obtain ⟨Q', hQ'perm, hQ'ref⟩ :=
          ih hrestpos hrestne base (x :: rSum :: Q.erase t) (k + 1) rSum hcut hmem2 hrSum.symm
        -- erase fact: (x :: rSum :: Q.erase t).erase rSum ~ x :: Q.erase t
        have herase : ((x :: rSum :: Q.erase t).erase rSum).Perm (x :: Q.erase t) := by
          by_cases hxr : x = rSum
          · -- erase removes the head x (which equals rSum)
            rw [← hxr, List.erase_cons_head]
          · rw [List.erase_cons_tail (by simpa using hxr), List.erase_cons_head]
        refine ⟨Q', ?_, ?_⟩
        · -- Q'.Perm ((x :: (y :: ys)) ++ Q.erase t)
          have h1 : ((y :: ys) ++ (x :: rSum :: Q.erase t).erase rSum).Perm
              ((y :: ys) ++ (x :: Q.erase t)) := herase.append_left (y :: ys)
          have h2 : Q'.Perm ((y :: ys) ++ (x :: Q.erase t)) := hQ'perm.trans h1
          have h3 : ((y :: ys) ++ (x :: Q.erase t)).Perm ((x :: (y :: ys)) ++ Q.erase t) := by
            have hA : ((y :: ys) ++ (x :: Q.erase t)).Perm ((x :: Q.erase t) ++ (y :: ys)) :=
              List.perm_append_comm
            have hB : ((x :: Q.erase t) ++ (y :: ys)).Perm (x :: ((y :: ys) ++ Q.erase t)) := by
              simp only [List.cons_append]
              exact List.Perm.cons x (List.perm_append_comm)
            have hC : (x :: ((y :: ys) ++ Q.erase t)) = ((x :: (y :: ys)) ++ Q.erase t) := by
              simp
            rw [← hC]
            exact hA.trans hB
          exact h2.trans h3
        · -- budget rewrite
          have hbudget : k + 1 + ((y :: ys).length - 1) = k + ((x :: (y :: ys)).length - 1) := by
            simp only [List.length_cons]
            omega
          rw [hbudget] at hQ'ref
          exact hQ'ref
  -- apply the helper with base = Q = [s], t = s, k = 0
  obtain ⟨Q', hperm, href⟩ := helper parts hpos hne [s] [s] 0 s
    (RefinesByAtMostNCuts.base (List.Perm.refl _)) (by simp) hsum
  simp only [List.erase_cons_head, List.append_nil, zero_add] at hperm href
  exact refines_target_perm hperm href

/-- **Lemma A.** A refinement preserves the total sum. -/
theorem refines_sum_eq {base Q : List ℝ} {k : ℕ}
    (h : RefinesByAtMostNCuts base k Q) : Q.sum = base.sum := by
  induction h with
  | base hperm => exact hperm.sum_eq
  | skip _ ih => exact ih
  | cut hs h1 h2 hstep hmem hh ih =>
      rename_i Q0 Q' _ s s1 s2
      rw [hstep.sum_eq]
      simp only [List.sum_cons]
      have hse : s + (Q0.erase s).sum = Q0.sum := List.sum_erase hmem
      rw [show s1 + (s2 + (Q0.erase s).sum) = s + (Q0.erase s).sum by rw [hs]; ring, hse]
      exact ih

/-- **Lemma B.** A refinement of a nonnegative list is nonnegative. -/
theorem refines_nonneg {base Q : List ℝ} {k : ℕ}
    (hbase : ∀ x ∈ base, 0 ≤ x)
    (h : RefinesByAtMostNCuts base k Q) : ∀ x ∈ Q, 0 ≤ x := by
  induction h with
  | base hperm => intro x hx; exact hbase x (hperm.mem_iff.mp hx)
  | skip _ ih => exact ih
  | cut hs h1 h2 hstep hmem hh ih =>
      rename_i Q0 Q' _ s s1 s2
      intro x hx
      have hx' : x ∈ (s1 :: s2 :: Q0.erase s) := hstep.mem_iff.mp hx
      simp only [List.mem_cons] at hx'
      rcases hx' with rfl | rfl | hx'
      · exact h1
      · exact h2
      · exact ih x (List.mem_of_mem_erase hx')

/-- **Lemma C.** Removing a zero-entry from a refinement of a strictly positive
base list keeps it a refinement with the same budget. -/
theorem refines_erase_zero {base Q : List ℝ} {k : ℕ}
    (hbase : ∀ x ∈ base, 0 < x)
    (h : RefinesByAtMostNCuts base k Q) (hz : (0:ℝ) ∈ Q) :
    RefinesByAtMostNCuts base k (Q.erase 0) := by
  induction h with
  | base hperm =>
      -- 0 ∈ Q → 0 ∈ base, contradicting strict positivity of base
      exact absurd (hbase 0 (hperm.mem_iff.mp hz)) (lt_irrefl 0)
  | skip _ ih =>
      exact RefinesByAtMostNCuts.skip (ih hz)
  | @cut Q0 Q' k' s s1 s2 hs h1 h2 hstep hmem hh ih =>
      -- hz : 0 ∈ Q', hstep : Q'.Perm (s1 :: s2 :: Q0.erase s), hmem : s ∈ Q0
      by_cases hs1 : s1 = 0
      · -- degenerate cut: s1 = 0, so s = s2, cut is spurious
        subst hs1
        have hseq : s = s2 := by rw [hs]; ring
        subst hseq
        -- Q'.erase 0 ~ s :: Q0.erase s ~ Q0
        have hperm0 : (Q'.erase 0).Perm (s :: Q0.erase s) := by
          have := hstep.erase (0:ℝ)
          simpa using this
        have hpermQ0 : (s :: Q0.erase s).Perm Q0 := (List.perm_cons_erase hmem).symm
        exact refines_target_perm ((hperm0.trans hpermQ0).symm)
          (RefinesByAtMostNCuts.skip hh)
      · by_cases hs2 : s2 = 0
        · -- degenerate cut: s2 = 0, so s = s1
          subst hs2
          have hseq : s = s1 := by rw [hs]; ring
          subst hseq
          have hperm0 : (Q'.erase 0).Perm (s :: Q0.erase s) := by
            have hpe := hstep.erase (0:ℝ)
            -- (s :: 0 :: Q0.erase s).erase 0 = s :: Q0.erase s  (s ≠ 0)
            have hsne : s ≠ 0 := hs1
            have : (s :: (0:ℝ) :: Q0.erase s).erase 0 = s :: Q0.erase s := by
              rw [List.erase_cons_tail (by exact fun hh => hsne (by simpa using hh.symm)),
                  List.erase_cons_head]
            rw [this] at hpe
            exact hpe
          have hpermQ0 : (s :: Q0.erase s).Perm Q0 := (List.perm_cons_erase hmem).symm
          exact refines_target_perm ((hperm0.trans hpermQ0).symm)
            (RefinesByAtMostNCuts.skip hh)
        · -- generic cut: s1 ≠ 0, s2 ≠ 0, so the 0 comes from Q0.erase s ⟹ 0 ∈ Q0
          have h0mem : (0:ℝ) ∈ (s1 :: s2 :: Q0.erase s) := hstep.mem_iff.mp hz
          have h0inerase : (0:ℝ) ∈ Q0.erase s := by
            simp only [List.mem_cons] at h0mem
            rcases h0mem with h | h | h
            · exact absurd h.symm hs1
            · exact absurd h.symm hs2
            · exact h
          have h0Q0 : (0:ℝ) ∈ Q0 := List.mem_of_mem_erase h0inerase
          have hsne0 : s ≠ 0 := by
            intro he; rw [he] at hs; have : s1 = 0 ∧ s2 = 0 := by constructor <;> nlinarith
            exact hs1 this.1
          -- apply IH: Refines base k' (Q0.erase 0)
          have hih := ih h0Q0
          -- reconstruct the cut on Q0.erase 0
          have hmem' : s ∈ Q0.erase 0 := List.mem_erase_of_ne hsne0 |>.mpr hmem
          -- new step perm : (Q'.erase 0).Perm (s1 :: s2 :: (Q0.erase 0).erase s)
          have hcomm : (Q0.erase s).erase 0 = (Q0.erase 0).erase s := List.erase_comm s 0
          have hstep' : (Q'.erase 0).Perm (s1 :: s2 :: (Q0.erase 0).erase s) := by
            have hpe : (Q'.erase 0).Perm ((s1 :: s2 :: Q0.erase s).erase 0) := hstep.erase 0
            have herase_cons : (s1 :: s2 :: Q0.erase s).erase 0
                = s1 :: s2 :: (Q0.erase s).erase 0 := by
              rw [List.erase_cons_tail, List.erase_cons_tail]
              · exact fun h => hs2 (by simpa using h.symm)
              · exact fun h => hs1 (by simpa using h.symm)
            rw [herase_cons, hcomm] at hpe
            exact hpe
          exact RefinesByAtMostNCuts.cut hs h1 h2 hstep' hmem' hih

/-- **P2.** Filtering out the zero-entries of a refinement of a strictly positive
base list keeps it a refinement with the same budget. -/
theorem refines_filter_pos {base Q : List ℝ} {k : ℕ}
    (hbase : ∀ x ∈ base, 0 < x)
    (h : RefinesByAtMostNCuts base k Q) :
    RefinesByAtMostNCuts base k (Q.filter (fun x => decide (x ≠ 0))) := by
  -- Induct on a length bound; each step erases one zero.
  suffices H : ∀ (m : ℕ) (Q : List ℝ), Q.length ≤ m →
      RefinesByAtMostNCuts base k Q →
      RefinesByAtMostNCuts base k (Q.filter (fun x => decide (x ≠ 0))) by
    exact H Q.length Q (le_refl _) h
  clear h Q
  intro m
  induction m with
  | zero =>
      intro Q hlen h
      -- Q = [], filter [] = []
      have : Q = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this; simpa using h
  | succ m ih =>
      intro Q hlen h
      by_cases hz : (0:ℝ) ∈ Q
      · -- erase the zero, recurse; filter unchanged
        have herz : RefinesByAtMostNCuts base k (Q.erase 0) := refines_erase_zero hbase h hz
        have hlen' : (Q.erase 0).length ≤ m := by
          have he : (Q.erase 0).length = Q.length - 1 := List.length_erase_of_mem hz
          have hpos : 1 ≤ Q.length := List.length_pos_of_mem hz
          omega
        have hfil : (Q.erase 0).filter (fun x => decide (x ≠ 0))
            = Q.filter (fun x => decide (x ≠ 0)) := by
          -- 0 ∉ filter (·≠0) Q, so erasing 0 from it is a no-op; and erase_filter swaps.
          have h0notin : (0:ℝ) ∉ Q.filter (fun x => decide (x ≠ 0)) := by
            intro hmem
            rw [List.mem_filter] at hmem
            simp at hmem
          rw [← List.erase_filter, List.erase_of_not_mem h0notin]
        rw [← hfil]
        exact ih (Q.erase 0) hlen' herz
      · -- no zeros: filter keeps everything
        have hall : ∀ x ∈ Q, decide (x ≠ 0) = true := by
          intro x hx
          have : x ≠ 0 := fun he => hz (he ▸ hx)
          simp [this]
        have : Q.filter (fun x => decide (x ≠ 0)) = Q := List.filter_eq_self.mpr hall
        rw [this]; exact h

/-- **Lemma D-perm.** The descending-`altSum` depends only on the multiset. -/
theorem altSum_mergeSort_perm {l l' : List ℝ} (h : l.Perm l') :
    altSum (l.mergeSort (· ≥ ·)) = altSum (l'.mergeSort (· ≥ ·)) := by
  have heq : l.mergeSort (· ≥ ·) = l'.mergeSort (· ≥ ·) := by
    apply List.Perm.eq_of_pairwise (le := (· ≥ ·))
    · intro a b _ _ hab hba; exact le_antisymm hba hab
    · exact List.sorted_mergeSort' _ _
    · exact List.sorted_mergeSort' _ _
    · exact (List.mergeSort_perm l _).trans (h.trans (List.mergeSort_perm l' _).symm)
  rw [heq]

/-- A list all of whose entries are zero has `altSum = 0`. -/
theorem altSum_all_zero (z : List ℝ) (hz : ∀ x ∈ z, x = (0:ℝ)) :
    altSum z = 0 := by
  induction z with
  | nil => simp [altSum]
  | cons a t ih =>
      rw [altSum_cons, hz a (by simp), ih (fun x hx => hz x (by simp [hx]))]; ring

/-- Appending a block of zeros does not change `altSum`. -/
theorem altSum_append_zeros (m z : List ℝ) (hz : ∀ x ∈ z, x = (0:ℝ)) :
    altSum (m ++ z) = altSum m := by
  induction m with
  | nil => simp [altSum]; exact altSum_all_zero z hz
  | cons a m' ih =>
      rw [List.cons_append, altSum_cons, altSum_cons, ih]

/-- **Lemma D.** Filtering out zeros from a nonnegative list does not change its
descending-`altSum`. -/
theorem altSum_filter_ne_zero (l : List ℝ) (hnn : ∀ x ∈ l, 0 ≤ x) :
    altSum ((l.filter (fun x => decide (x ≠ 0))).mergeSort (· ≥ ·))
      = altSum (l.mergeSort (· ≥ ·)) := by
  set f := l.filter (fun x => decide (x ≠ 0)) with hf
  set z := l.filter (fun x => !decide (x ≠ 0)) with hz
  have hfpos : ∀ x ∈ f, 0 < x := by
    intro x hx
    rw [hf, List.mem_filter] at hx
    have hxne : x ≠ 0 := by simpa using hx.2
    exact lt_of_le_of_ne (hnn x hx.1) (Ne.symm hxne)
  have hzzero : ∀ x ∈ z, x = (0:ℝ) := by
    intro x hx
    rw [hz, List.mem_filter] at hx
    have : ¬ (x ≠ 0) := by simpa using hx.2
    simpa using this
  have hperm : (f ++ z).Perm l := List.filter_append_perm _ _
  have hstep1 : altSum (l.mergeSort (· ≥ ·)) = altSum ((f ++ z).mergeSort (· ≥ ·)) :=
    (altSum_mergeSort_perm hperm).symm
  have hsortf : List.Pairwise (· ≥ ·) (f.mergeSort (· ≥ ·)) :=
    List.sorted_mergeSort' (· ≥ ·) f
  have hzpair : List.Pairwise (· ≥ ·) z := by
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    rw [hzzero a ha, hzzero b hb]
  have hcross : ∀ a ∈ f.mergeSort (· ≥ ·), ∀ b ∈ z, a ≥ b := by
    intro a ha b hb
    have haf : a ∈ f := (List.mergeSort_perm f _).mem_iff.mp ha
    rw [hzzero b hb]
    exact le_of_lt (hfpos a haf)
  have hpairwise : List.Pairwise (· ≥ ·) (f.mergeSort (· ≥ ·) ++ z) := by
    rw [List.pairwise_append]
    exact ⟨hsortf, hzpair, hcross⟩
  have heq : (f ++ z).mergeSort (· ≥ ·) = f.mergeSort (· ≥ ·) ++ z := by
    apply List.Perm.eq_of_pairwise (le := (· ≥ ·))
    · intro a b _ _ hab hba; exact le_antisymm hba hab
    · exact List.sorted_mergeSort' (· ≥ ·) (f ++ z)
    · exact hpairwise
    · refine (List.mergeSort_perm (f ++ z) _).trans ?_
      exact (List.mergeSort_perm f _).symm.append_right z
  rw [hstep1, heq, altSum_append_zeros _ _ hzzero]

/-- Helper: given a strictly-positive refinement `Q` of `pieceLengths A` by at
most `k ≤ n` cuts whose descending `altSum` is `≤ c`, Xiang Yu obtains an
admissible disjoint `B` with `L A B ≤ (1 + c)/2`. -/
theorem upper_bound_from_altSum_le (n : ℕ) (A : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : k ≤ n) (Q : List ℝ)
    (hQpos : ∀ x ∈ Q, 0 < x)
    (hQref : RefinesByAtMostNCuts (pieceLengths A) k Q)
    (c : ℝ) (hbound : altSum (Q.mergeSort (· ≥ ·)) ≤ c) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧ L A B ≤ (1 + c) / 2 := by
  obtain ⟨B, hBadm, hBdisj, hBperm⟩ :=
    exists_marks_realizing_refinement n A hA k hk Q hQpos hQref
  refine ⟨B, hBadm, hBdisj, ?_⟩
  have hAB : ↑(A ∪ B) ⊆ Set.Ioo (0 : ℝ) 1 := by
    rw [Finset.coe_union]; exact Set.union_subset hA hBadm.1
  rw [L_eq_half_one_add_alt A B hAB]
  have halteq : altSum ((pieceLengths (A ∪ B)).mergeSort (· ≥ ·))
      = altSum (Q.mergeSort (· ≥ ·)) := altSum_mergeSort_perm hBperm
  rw [halteq]
  have : altSum (Q.mergeSort (· ≥ ·)) ≤ c := hbound
  linarith

/-- **Upper bound / optimality.** For every admissible marking `A` of Liu Bang,
Xiang Yu has an admissible marking `B` disjoint from `A` with
`L A B ≤ 2^n / (2^(n+1) - 1)`, so Liu Bang cannot guarantee more. -/
theorem upper_bound (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  intro A hAadm
  obtain ⟨hAsub, hAcard⟩ := hAadm
  set k := A.card with hkdef
  have hk : k ≤ n := hAcard
  -- base = pieceLengths A
  set base := pieceLengths A with hbasedef
  have hbaselen : base.length = k + 1 := by rw [hbasedef, pieceLengths_length]
  have hbasepos : ∀ x ∈ base, 0 < x := fun x hx => pieceLengths_pos A hAsub x hx
  have hbasenn : ∀ x ∈ base, 0 ≤ x := fun x hx => le_of_lt (hbasepos x hx)
  have hbasesum : base.sum = 1 := pieceLengths_sum A hAsub
  have hDpos : (0:ℝ) < (2:ℝ)^(n+1) - 1 := by
    have : (1:ℝ) < (2:ℝ)^(n+1) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  -- get the equal-pairs refinement
  obtain ⟨ps, δ, hδ0, hδle, href⟩ := exists_equal_pairs_refinement k base hbaselen hbasepos
  -- ps and δ nonneg via refinement nonneg
  have hQ0nn : ∀ x ∈ (ps.flatMap (fun x => [x, x])) ++ [δ], 0 ≤ x :=
    refines_nonneg hbasenn href
  have hpsnn : ∀ x ∈ ps, 0 ≤ x := by
    intro x hx
    apply hQ0nn
    apply List.mem_append_left
    rw [List.mem_flatMap]; exact ⟨x, hx, by simp⟩
  by_cases hkn : k = n
  · -- CASE k = n: use Q₀ = (ps.flatMap[x,x]) ++ [δ], defect ≤ 1/(2^(n+1)-1)
    subst hkn
    set Q₀ := (ps.flatMap (fun x => [x, x])) ++ [δ] with hQ0def
    -- pairing certificate on Q₀ with defect δ
    have hpermQ : (((ps.map (fun x => (x, x))).flatMap (fun p => [p.1, p.2])) ++ [δ]).Perm Q₀ := by
      have hfm : (ps.map (fun x => (x, x))).flatMap (fun p => [p.1, p.2])
          = ps.flatMap (fun x => [x, x]) := by rw [List.flatMap_map]
      rw [hfm]
    set C₀ : PairingCert Q₀ := ⟨ps.map (fun x => (x, x)), [δ], hpermQ⟩ with hC0def
    have hC0def_eq : C₀.defect = δ := by
      unfold PairingCert.defect
      simp only [hC0def, defect_equal_pairs, List.sum_cons, List.sum_nil, add_zero, zero_add]
    -- altSum bound: altSum(sort Q₀) ≤ defect = δ ≤ base.sum/(2^(k+1)-1) = 1/(2^(n+1)-1)
    have hQ0nn' : ∀ x ∈ Q₀, 0 ≤ x := hQ0nn
    have haltle : altSum (Q₀.mergeSort (· ≥ ·)) ≤ δ := by
      have := altSum_sorted_le_pairingCert_defect Q₀ hQ0nn' C₀
      rw [hC0def_eq] at this; exact this
    have hδbound : δ ≤ 1 / ((2:ℝ)^(k+1) - 1) := by
      rw [hbasesum] at hδle; simpa using hδle
    -- filter zeros
    set Q := Q₀.filter (fun x => decide (x ≠ 0)) with hQdef
    have hQref : RefinesByAtMostNCuts base k Q := refines_filter_pos hbasepos href
    have hQpos : ∀ x ∈ Q, 0 < x := by
      intro x hx
      rw [hQdef, List.mem_filter] at hx
      have hxne : x ≠ 0 := by simpa using hx.2
      exact lt_of_le_of_ne (hQ0nn' x hx.1) (Ne.symm hxne)
    have haltQeq : altSum (Q.mergeSort (· ≥ ·)) = altSum (Q₀.mergeSort (· ≥ ·)) :=
      altSum_filter_ne_zero Q₀ hQ0nn'
    -- c = 1/(2^(k+1)-1)
    have hcbound : altSum (Q.mergeSort (· ≥ ·)) ≤ 1 / ((2:ℝ)^(k+1) - 1) := by
      rw [haltQeq]; linarith [haltle, hδbound]
    obtain ⟨B, hBadm, hBdisj, hBle⟩ :=
      upper_bound_from_altSum_le k A hAsub k (le_refl k) Q hQpos hQref
        (1 / ((2:ℝ)^(k+1) - 1)) hcbound
    refine ⟨B, hBadm, hBdisj, ?_⟩
    calc L A B ≤ (1 + 1 / ((2:ℝ)^(k+1) - 1)) / 2 := hBle
      _ = (2:ℝ)^k / ((2:ℝ)^(k+1) - 1) := (answer_eq_half_one_add_inv k).symm
  · -- CASE k < n: split δ into δ/2, δ/2 → fully paired → defect 0 → altSum 0 → L = 1/2
    have hklt : k < n := lt_of_le_of_ne hk hkn
    -- Q₁ = (ps.flatMap[x,x]) ++ [δ/2, δ/2]
    set Q₁ := (ps.flatMap (fun x => [x, x])) ++ [δ/2, δ/2] with hQ1def
    -- refinement: cut δ (the last element of Q₀) into δ/2, δ/2
    have hδmem : δ ∈ (ps.flatMap (fun x => [x, x])) ++ [δ] := by
      apply List.mem_append_right; simp
    have hcut : RefinesByAtMostNCuts base (k + 1) Q₁ := by
      have hc := RefinesByAtMostNCuts.cut (base := base) (Q := (ps.flatMap (fun x => [x, x])) ++ [δ])
        (Q' := Q₁) (k := k) (s := δ) (s₁ := δ/2) (s₂ := δ/2)
        (by ring) (by linarith) (by linarith) ?_ hδmem href
      · exact hc
      · -- Q₁.Perm (δ/2 :: δ/2 :: ((ps.flatMap[x,x]) ++ [δ]).erase δ)
        set Q₀e := (ps.flatMap (fun x => [x, x])) ++ [δ] with hQ0d
        -- Q₀e.erase δ ~ ps.flatMap[x,x]
        have herasePerm : (Q₀e.erase δ).Perm (ps.flatMap (fun x => [x, x])) := by
          have h1 : Q₀e.Perm (δ :: Q₀e.erase δ) := List.perm_cons_erase hδmem
          have h2 : Q₀e.Perm (δ :: ps.flatMap (fun x => [x, x])) := by
            rw [hQ0d]
            exact (List.perm_append_comm.trans (by simp))
          have h3 : (δ :: Q₀e.erase δ).Perm (δ :: ps.flatMap (fun x => [x, x])) := h1.symm.trans h2
          exact List.Perm.cons_inv h3
        rw [hQ1def]
        -- Q₁ = ps.flatMap[x,x] ++ [δ/2, δ/2] ~ δ/2 :: δ/2 :: Q₀e.erase δ
        refine List.Perm.trans ?_ ((herasePerm.symm.cons (δ/2)).cons (δ/2))
        have h1 : ((ps.flatMap (fun x => [x, x])) ++ [δ/2, δ/2]).Perm
            ([δ/2, δ/2] ++ ps.flatMap (fun x => [x, x])) := List.perm_append_comm
        simpa using h1
    have hcut' : RefinesByAtMostNCuts base n Q₁ := refines_mono (by omega) hcut
    -- Q₁ nonneg
    have hQ1nn : ∀ x ∈ Q₁, 0 ≤ x := refines_nonneg hbasenn hcut'
    -- pairing certificate on Q₁ with defect 0
    have hpermQ1 : (((ps.map (fun x => (x, x)) ++ [(δ/2, δ/2)]).flatMap (fun p : ℝ × ℝ => [p.1, p.2])) ++ []).Perm Q₁ := by
      simp only [List.append_nil, List.flatMap_append]
      have hfm : (ps.map (fun x => (x, x))).flatMap (fun p => [p.1, p.2])
          = ps.flatMap (fun x => [x, x]) := by rw [List.flatMap_map]
      rw [hfm]
      simp [hQ1def, List.flatMap_cons]
    set C₁ : PairingCert Q₁ := ⟨ps.map (fun x => (x, x)) ++ [(δ/2, δ/2)], [], hpermQ1⟩ with hC1def
    have hC1defect : C₁.defect = 0 := by
      unfold PairingCert.defect
      simp only [hC1def, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, sub_self, abs_zero, add_zero, defect_equal_pairs, zero_add]
    have haltle0 : altSum (Q₁.mergeSort (· ≥ ·)) ≤ 0 := by
      have := altSum_sorted_le_pairingCert_defect Q₁ hQ1nn C₁
      rw [hC1defect] at this; exact this
    have haltge0 : 0 ≤ altSum (Q₁.mergeSort (· ≥ ·)) := by
      have hge : List.Pairwise (· ≥ ·) (Q₁.mergeSort (· ≥ ·)) := List.sorted_mergeSort' _ _
      have hnn : ∀ x ∈ Q₁.mergeSort (· ≥ ·), 0 ≤ x := by
        intro x hx
        exact hQ1nn x ((List.mergeSort_perm Q₁ _).mem_iff.mp hx)
      exact (altSum_sorted_nonneg_bounds _ hge hnn).1
    have halt0 : altSum (Q₁.mergeSort (· ≥ ·)) = 0 := le_antisymm haltle0 haltge0
    -- filter zeros from Q₁
    set Q := Q₁.filter (fun x => decide (x ≠ 0)) with hQdef
    have hQref : RefinesByAtMostNCuts base n Q := refines_filter_pos hbasepos hcut'
    have hQpos : ∀ x ∈ Q, 0 < x := by
      intro x hx
      rw [hQdef, List.mem_filter] at hx
      have hxne : x ≠ 0 := by simpa using hx.2
      exact lt_of_le_of_ne (hQ1nn x hx.1) (Ne.symm hxne)
    have haltQeq : altSum (Q.mergeSort (· ≥ ·)) = altSum (Q₁.mergeSort (· ≥ ·)) :=
      altSum_filter_ne_zero Q₁ hQ1nn
    have hcbound : altSum (Q.mergeSort (· ≥ ·)) ≤ 0 := by rw [haltQeq, halt0]
    obtain ⟨B, hBadm, hBdisj, hBle⟩ :=
      upper_bound_from_altSum_le n A hAsub n (le_refl n) Q hQpos hQref 0 hcbound
    refine ⟨B, hBadm, hBdisj, ?_⟩
    -- L A B ≤ (1+0)/2 = 1/2 ≤ 2^n/(2^(n+1)-1)
    have hhalf : (1 + (0:ℝ)) / 2 = 1/2 := by ring
    have hfge : (1:ℝ)/2 ≤ (2:ℝ)^n / ((2:ℝ)^(n+1) - 1) := by
      rw [le_div_iff₀ hDpos]
      have h2 : (2:ℝ)^(n+1) = 2 * 2^n := by ring
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) n]
    calc L A B ≤ (1 + (0:ℝ)) / 2 := hBle
      _ = 1/2 := hhalf
      _ ≤ (2:ℝ)^n / ((2:ℝ)^(n+1) - 1) := hfge

/-- For a fixed admissible `A`, the family `B ↦ L A B` over admissible disjoint
`B` is bounded below (by `0`), so the inner `⨅` is well-behaved. -/
theorem innerInf_bddBelow (n : ℕ) (A : {A : Finset ℝ // AdmissibleMark n A}) :
    BddBelow (Set.range (fun B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}
      => L A.1 B.1)) := by
  refine ⟨0, ?_⟩
  rw [mem_lowerBounds]
  rintro y ⟨B, rfl⟩
  exact (L_mem_Icc A.1 B.1 A.2.1 B.2.1.1).1

/-- The inner index type (Xiang Yu's admissible disjoint marks) is nonempty:
`B = ∅` is admissible and disjoint from any `A`. -/
instance innerNonempty (n : ℕ) (A : {A : Finset ℝ // AdmissibleMark n A}) :
    Nonempty {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} := by
  refine ⟨⟨∅, ?_, ?_⟩⟩
  · -- AdmissibleMark n ∅
    exact ⟨by simp, by simp⟩
  · -- Disjoint A.1 ∅
    exact disjoint_bot_right

/-- The outer family `A ↦ ⨅ B, L A B` is bounded above (by `1`), so the outer
`⨆` is well-behaved. -/
theorem outerSup_bddAbove (n : ℕ) :
    BddAbove (Set.range (fun A : {A : Finset ℝ // AdmissibleMark n A}
      => ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1)) := by
  refine ⟨1, ?_⟩
  rw [mem_upperBounds]
  rintro y ⟨A, rfl⟩
  refine ciInf_le_of_le (innerInf_bddBelow n A) ⟨∅, ⟨by simp, by simp⟩, disjoint_bot_right⟩ ?_
  exact (L_mem_Icc A.1 ∅ A.2.1 (by simp)).2

/-- The outer index type (Liu Bang's admissible marks) is nonempty (`A = ∅`). -/
instance outerNonempty (n : ℕ) : Nonempty {A : Finset ℝ // AdmissibleMark n A} :=
  ⟨⟨∅, by simp, by simp⟩⟩

/-- **Main statement.** For every positive integer `n`, Liu Bang's guaranteed
value equals `2^n / (2^(n+1) - 1)`. -/
theorem V_eq (n : ℕ) (hn : 0 < n) : V n = (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  set ans : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) with hans
  apply le_antisymm
  · -- V n ≤ ans
    apply ciSup_le
    intro A
    -- ⨅ B, L A.1 B.1 ≤ ans, via upper_bound at A
    obtain ⟨B₀, hB₀adm, hB₀disj, hB₀le⟩ := upper_bound n hn A.1 A.2
    have : (⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1)
        ≤ L A.1 B₀ := by
      exact ciInf_le_of_le (innerInf_bddBelow n A) ⟨B₀, hB₀adm, hB₀disj⟩ le_rfl
    exact this.trans hB₀le
  · -- ans ≤ V n
    obtain ⟨A₀, hA₀adm, hA₀⟩ := lower_bound n hn
    haveI : Nonempty {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A₀ B} :=
      ⟨⟨∅, ⟨by simp, by simp⟩, disjoint_bot_right⟩⟩
    -- ans ≤ ⨅ B, L A₀ B
    have hinf : ans ≤ ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A₀ B},
        L A₀ B.1 := by
      apply le_ciInf
      intro B
      exact hA₀ B.1 B.2.1 B.2.2
    -- ⨅ B, L A₀ B ≤ V n, at the outer point A₀
    have hle : (⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A₀ B}, L A₀ B.1)
        ≤ V n := by
      exact le_ciSup_of_le (outerSup_bddAbove n) ⟨A₀, hA₀adm⟩ le_rfl
    exact hinf.trans hle

end LiuBangXiangYu
