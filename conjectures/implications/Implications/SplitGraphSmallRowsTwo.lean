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

end SplitGraphSmallRowsTwo

#print axioms SplitGraphSmallRowsTwo.two_original_rows_intersect
