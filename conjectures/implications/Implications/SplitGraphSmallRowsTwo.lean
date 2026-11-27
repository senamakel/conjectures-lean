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
  have hcEraseCard : ((row G I c).erase u).card = 1 := by
    rw [Finset.card_erase_of_mem huC, hc]
  have hdEraseCard : ((row G I d).erase u).card = 1 := by
    rw [Finset.card_erase_of_mem huD, hd]
  obtain ⟨v, hvErase⟩ := Finset.card_eq_one.mp hcEraseCard
  obtain ⟨w, hwErase⟩ := Finset.card_eq_one.mp hdEraseCard
  have hCeq : row G I c = {u, v} := by
    ext x
    by_cases hxu : x = u
    · subst x
      simp [huC]
    · have hx : x ∈ row G I c ↔ x ∈ (row G I c).erase u := by
        simp [Finset.mem_erase, hxu]
      rw [hx, hvErase]
      simp [hxu]
  have hDeq : row G I d = {u, w} := by
    ext x
    by_cases hxu : x = u
    · subst x
      simp [huD]
    · have hx : x ∈ row G I d ↔ x ∈ (row G I d).erase u := by
        simp [Finset.mem_erase, hxu]
      rw [hx, hwErase]
      simp [hxu]
  have huv : u ≠ v := by
    have hvMem : v ∈ (row G I c).erase u := by rw [hvErase]; simp
    have hvNe : v ≠ u := (Finset.mem_erase.mp hvMem).1
    exact fun h => hvNe h.symm
  have huw : u ≠ w := by
    have hwMem : w ∈ (row G I d).erase u := by rw [hwErase]; simp
    have hwNe : w ≠ u := (Finset.mem_erase.mp hwMem).1
    exact fun h => hwNe h.symm
  by_cases hvw : v = w
  · left
    rw [hCeq, hDeq, hvw]
  · right
    exact ⟨u, v, w, huv, huw, hvw, hCeq, hDeq⟩

end SplitGraphSmallRowsTwo

#print axioms SplitGraphSmallRowsTwo.two_original_rows_intersect
