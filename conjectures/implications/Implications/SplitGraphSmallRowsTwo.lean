import Implications.SplitGraphSmallRows
import Implications.SplitGraphSmallRowsPath

/-!
The case with exactly two selected clique rows of size two.
-/

namespace SplitGraphSmallRowsTwo

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem two_rows_intersect_of_symmDiff_card_le_two
    (s t : Finset V) (hs : s.card = 2) (ht : t.card = 2)
    (hd : (s \ t ∪ t \ s).card ≤ 2) : ∃ x, x ∈ s ∧ x ∈ t := by
  classical
  by_contra hn
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      exact False.elim (hn ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)
    · simp
  have hEq : s ∪ t = s \ t ∪ t \ s := by
    rw [← Finset.symmDiff_eq_union hdis, Finset.symmDiff_def]
  have hunion : (s ∪ t).card = 4 := by
    rw [Finset.card_union_of_disjoint hdis, hs, ht]
  have hlarge : (s \ t ∪ t \ s).card = 4 := by rw [← hEq]; exact hunion
  omega

/-- Two size-two rows under the symmetric-difference bound share a label. -/
theorem two_original_rows_intersect
    (G : SimpleGraph V) (I : Finset V) (c d : V)
    (hc : (row G I c).card = 2) (hd : (row G I d).card = 2)
    (hdiff : (rowDiff G I c d).card ≤ 2) :
    ∃ i, i ∈ row G I c ∧ i ∈ row G I d := by
  exact two_rows_intersect_of_symmDiff_card_le_two _ _ hc hd (by simpa [rowDiff] using hdiff)

/-- The common label gives the only two possibilities: equal rows, or one
shared label and one private label on each side. -/
theorem two_original_rows_shape
    (G : SimpleGraph V) (I : Finset V) (c d : V)
    (hc : (row G I c).card = 2) (hd : (row G I d).card = 2)
    (hdiff : (rowDiff G I c d).card ≤ 2) :
    (row G I c = row G I d) ∨
      ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        row G I c = {u, v} ∧ row G I d = {u, w} := by
  classical
  obtain ⟨u, huC, huD⟩ := two_original_rows_intersect G I c d hc hd hdiff
  obtain ⟨x, y, hxy, hCeq⟩ := Finset.card_eq_two.mp hc
  have huxy : u = x ∨ u = y := by
    rw [hCeq] at huC
    simpa using huC
  rcases huxy with hux | huy
  · obtain ⟨r, s, hrs, hDeq⟩ := Finset.card_eq_two.mp hd
    have hur : u = r ∨ u = s := by rw [hDeq] at huD; simpa using huD
    rcases hur with hur | hus
    · subst x r
      by_cases heq : y = s
      · left
        rw [hCeq, hDeq]
        simp [heq]
      · right
        refine ⟨u, y, s, ?_, ?_, ?_, hCeq, ?_⟩
        · intro h
          subst y
          exact hxy rfl
        · intro h
          subst s
          exact hrs rfl
        · intro h
          subst s
          exact heq rfl
        · rw [hDeq]
          simp [hur]
    · subst x s
      by_cases heq : y = r
      · left
        rw [hCeq, hDeq]
        simp [heq, Finset.pair_comm]
      · right
        refine ⟨u, y, r, ?_, ?_, ?_, hCeq, ?_⟩
        · intro h
          subst y
          exact hxy rfl
        · intro h
          subst r
          exact hrs rfl
        · exact heq
        · rw [hDeq]
          simp [Finset.pair_comm, hus]
  · subst y
    obtain ⟨r, s, hrs, hDeq⟩ := Finset.card_eq_two.mp hd
    have hur : u = r ∨ u = s := by rw [hDeq] at huD; simpa using huD
    rcases hur with hur | hus
    · subst y r
      by_cases heq : x = s
      · left
        rw [hCeq, hDeq]
        simp [heq, Finset.pair_comm]
      · right
        refine ⟨u, x, s, ?_, ?_, ?_, ?_, ?_⟩
        · intro h
          subst x
          exact hxy rfl
        · intro h
          subst s
          exact hrs rfl
        · exact heq.symm
        · rw [hCeq]
          simp [Finset.pair_comm]
        · rw [hDeq]
          simp [hus]
    · subst y s
      by_cases heq : x = r
      · left
        rw [hCeq, hDeq]
        simp [heq]
      · right
        refine ⟨u, x, r, ?_, ?_, ?_, ?_, ?_⟩
        · intro h
          subst x
          exact hxy rfl
        · intro h
          subst r
          exact hrs rfl
        · exact heq.symm
        · rw [hCeq]
          simp
        · rw [hDeq]
          simp [hus, Finset.pair_comm]

end SplitGraphSmallRowsTwo

#print axioms SplitGraphSmallRowsTwo.two_original_rows_intersect
