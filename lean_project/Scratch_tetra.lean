import Mathlib

theorem vertex_pair_lemma (x y1 y2 z1 z2 : ℝ)
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
  obtain ⟨M, hMAB, hMAC, hMAD, hMBC, hMBD, hMCD, hMeq⟩ :
      ∃ M : ℝ, AB ≤ M ∧ AC ≤ M ∧ AD ≤ M ∧ BC ≤ M ∧ BD ≤ M ∧ CD ≤ M ∧
        (AB = M ∨ AC = M ∨ AD = M ∨ BC = M ∨ BD = M ∨ CD = M) := by
    refine ⟨max AB (max AC (max AD (max BC (max BD CD)))), le_max_left _ _,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
    · rcases max_choice AB (max AC (max AD (max BC (max BD CD)))) with h | h
      · exact Or.inl h.symm
      rcases max_choice AC (max AD (max BC (max BD CD))) with h2 | h2
      · exact Or.inr (Or.inl (h.trans h2).symm)
      rcases max_choice AD (max BC (max BD CD)) with h3 | h3
      · exact Or.inr (Or.inr (Or.inl (h.trans (h2.trans h3)).symm))
      rcases max_choice BC (max BD CD) with h4 | h4
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h.trans (h2.trans (h3.trans h4))).symm)))
      rcases max_choice BD CD with h5 | h5
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.trans (h2.trans (h3.trans (h4.trans h5)))).symm))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.trans (h2.trans (h3.trans (h4.trans h5)))).symm))))
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
