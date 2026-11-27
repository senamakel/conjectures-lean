import Implications.SplitGraphTrees

/-!
Small combinatorial consequences of the row bounds used for split graphs.

The first lemma isolates the connectivity-one incidence restriction: every independent
vertex has a clique neighbour, every clique row has size at most two, and distinct rows
differ in at most one place. In that situation there are at most two independent vertices.
-/

namespace SplitGraphPath

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma subset_of_card_eq_two_of_symmDiff_le_one {s t : Finset V}
    (hs : s.card ≤ 2) (ht : t.card = 2)
    (hd : ((s \ t) ∪ (t \ s)).card ≤ 1) : s ⊆ t := by
  classical
  intro x hx
  by_contra hxt
  have hxs : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
  by_cases hts : t ⊆ s
  · have hxt' : x ∉ t := hxt
    have hxnot : x ∉ t := hxt'
    have hcard : (insert x t).card = 3 := by
      rw [Finset.card_insert_of_notMem hxnot, ht]
    have hsub : insert x t ⊆ s := Finset.insert_subset.mpr ⟨hx, hts⟩
    have : (insert x t).card ≤ s.card := Finset.card_le_card hsub
    omega
  · obtain ⟨y, hyt, hys⟩ := Finset.not_subset.mp hts
    have hysdiff : y ∈ t \ s := Finset.mem_sdiff.mpr ⟨hyt, hys⟩
    have hxy : x ≠ y := by
      intro heq
      subst y
      exact hys hxs.1
    have hxy' : y ∉ s \ t := by
      intro hy
      exact hys hy.1
    have hpair : ({x, y} : Finset V) ⊆ (s \ t) ∪ (t \ s) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ hxs
      · exact Finset.mem_union_right _ hysdiff
    have hpaircard : ({x, y} : Finset V).card = 2 := by simp [hxy]
    have := Finset.card_le_card hpair
    omega

private lemma eq_of_card_eq_one_of_symmDiff_le_one {s t : Finset V}
    (hs : s.card = 1) (ht : t.card = 1)
    (hd : ((s \ t) ∪ (t \ s)).card ≤ 1) : s = t := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxt
    have hxs : x ∈ s \ t := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
    by_cases hts : t ⊆ s
    · have hst : s = t := Finset.eq_of_subset_of_card_le hts (by omega)
      exact hxt (hst ▸ hx)
    · obtain ⟨y, hyt, hys⟩ := Finset.not_subset.mp hts
      have hysdiff : y ∈ t \ s := Finset.mem_sdiff.mpr ⟨hyt, hys⟩
      have hxy : x ≠ y := by
        intro heq
        subst y
        exact hys hxs.1
      have hpair : ({x, y} : Finset V) ⊆ (s \ t) ∪ (t \ s) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union_left _ hxs
        · exact Finset.mem_union_right _ hysdiff
      have hpaircard : ({x, y} : Finset V).card = 2 := by simp [hxy]
      have := Finset.card_le_card hpair
      omega
  · intro hx
    by_contra hxt
    have hxt' : x ∈ t \ s := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
    by_cases hst : s ⊆ t
    · have hts : t = s := Finset.eq_of_subset_of_card_le hst (by omega)
      exact hxt (hts ▸ hx)
    · obtain ⟨y, hys, hyt⟩ := Finset.not_subset.mp hst
      have hysdiff : y ∈ s \ t := Finset.mem_sdiff.mpr ⟨hys, hyt⟩
      have hxy : x ≠ y := by
        intro heq
        subst y
        exact hyt hxt'.1
      have hpair : ({x, y} : Finset V) ⊆ (s \ t) ∪ (t \ s) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union_right _ hxt'
        · exact Finset.mem_union_left _ hysdiff
      have hpaircard : ({x, y} : Finset V).card = 2 := by simp [hxy]
      have := Finset.card_le_card hpair
      omega

/-- In the connectivity-one row regime, the independent side has at most two vertices. -/
theorem independent_card_le_two_of_row_bounds
    (G : SimpleGraph V) (C I : Finset V)
    (hrow : ∀ c ∈ C, (row G I c).card ≤ 2)
    (hdiff : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → (rowDiff G I c d).card ≤ 1)
    (hcover : ∀ i ∈ I, ∃ c ∈ C, G.Adj c i) : I.card ≤ 2 := by
  classical
  by_cases htwo : ∃ c ∈ C, (row G I c).card = 2
  · obtain ⟨c₀, hc₀, hcard₀⟩ := htwo
    have hsub : ∀ c ∈ C, row G I c ⊆ row G I c₀ := by
      intro c hc
      by_cases hcc : c = c₀
      · subst c
        exact Finset.Subset.rfl
      · apply subset_of_card_eq_two_of_symmDiff_le_one (hrow c hc) hcard₀
        simpa [rowDiff, hcc, Finset.union_comm] using hdiff c hc c₀ hc₀ hcc
    have hI : I ⊆ row G I c₀ := by
      intro i hi
      obtain ⟨c, hc, hci⟩ := hcover i hi
      exact hsub c hc (Finset.mem_filter.mpr ⟨hi, hci.symm⟩)
    exact (Finset.card_le_card hI).trans (by omega)
  · have hsmall : ∀ c ∈ C, (row G I c).card ≤ 1 := by
      intro c hc
      have hle := hrow c hc
      by_contra h
      have : (row G I c).card = 2 := by omega
      exact htwo ⟨c, hc, this⟩
    by_cases hempty : I = ∅
    · simp [hempty]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨c₀, hc₀, hci₀⟩ := hcover i hi
      have hc₀row : (row G I c₀).card = 1 := by
        have hmem : i ∈ row G I c₀ := Finset.mem_filter.mpr ⟨hi, hci₀.symm⟩
        have : 0 < (row G I c₀).card := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
      have hsame : ∀ c ∈ C, row G I c = row G I c₀ := by
        intro c hc
        by_cases hcc : c = c₀
        · simpa [hcc]
        · by_cases hnon : (row G I c).card = 0
          · have hzero : row G I c = ∅ := Finset.card_eq_zero.mp hnon
            have hdiff' := hdiff c hc c₀ hc₀ hcc
            rw [hzero] at hdiff'
            simp [rowDiff, hzero] at hdiff'
            omega
          · have hone : (row G I c).card = 1 := by omega
            exact eq_of_card_eq_one_of_symmDiff_le_one hone hc₀row (by
              simpa [rowDiff, hcc, Finset.union_comm] using hdiff c hc c₀ hc₀ hcc)
      have hI : I ⊆ row G I c₀ := by
        intro j hj
        obtain ⟨c, hc, hcj⟩ := hcover j hj
        rw [← hsame c hc]
        exact Finset.mem_filter.mpr ⟨hj, hcj.symm⟩
      exact (Finset.card_le_card hI).trans (by omega)

end SplitGraphPath

#print axioms SplitGraphPath.independent_card_le_two_of_row_bounds
