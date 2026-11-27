import Mathlib

/-!
Small set-theoretic facts for the degree-two row case in the WOWII 199 split-graph argument.
-/

namespace SplitGraphComponents

/-- Two rows of size two whose symmetric difference has size at most two must intersect. -/
theorem twoRows_intersect_of_symmDiff_card_le_two
    {α : Type*} [DecidableEq α] (s t : Finset α)
    (hs : s.card = 2) (ht : t.card = 2)
    (h : (s \ t ∪ t \ s).card ≤ 2) : (s ∩ t).Nonempty := by
  by_contra hst
  have hdis : Disjoint s t := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.not_nonempty_iff_eq_empty.mp hst
  have hEq : s ∪ t = s \ t ∪ t \ s := by
    rw [← Finset.symmDiff_eq_union hdis, Finset.symmDiff_def]
  have hcard : (s \ t ∪ t \ s).card = 4 := by
    rw [← hEq, Finset.card_union_of_disjoint hdis, hs, ht]
  omega

end SplitGraphComponents
