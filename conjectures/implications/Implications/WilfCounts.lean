import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

/-!
# Recovering exact occurrence counts from marked occurrence counts

The upper-cone counts of a finite family of occurrence sets determine its exact
counts, with one contribution for each index in the family.
-/

namespace Implications.WilfCounts

open scoped BigOperators

variable {α ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [Fintype κ]

/-- The number of indices whose occurrence set contains all prescribed marks. -/
noncomputable def markedCount (occ : ι → Finset α) (marks : Finset α) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => marks ⊆ occ i).card

/-- The number of indices whose occurrence set is exactly the prescribed set. -/
def exactCount (occ : ι → Finset α) (marks : Finset α) : ℕ :=
  (Finset.univ.filter fun i => occ i = marks).card

private theorem markedCount_eq_sum (occ : ι → Finset α) (marks : Finset α) :
    markedCount occ marks =
      ∑ s ∈ Finset.univ.filter (marks ⊆ ·), exactCount occ s := by
  classical
  have maps : (↑(Finset.univ.filter fun i => marks ⊆ occ i) : Set ι).MapsTo occ
      (Finset.univ.filter (marks ⊆ ·) : Finset (Finset α)) := by
    intro i hi
    simpa using hi
  unfold markedCount
  rw [Finset.card_eq_sum_card_fiberwise maps]
  apply Finset.sum_congr rfl
  intro s hs
  have hsm : marks ⊆ s := (Finset.mem_filter.mp hs).2
  unfold exactCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun hi => hi.symm ▸ hsm

/-- Equality of all marked counts forces equality of all exact occurrence counts. -/
theorem exactCount_eq_of_markedCount_eq (left : ι → Finset α) (right : κ → Finset α)
    (h : ∀ s, markedCount left s = markedCount right s) (marks : Finset α) :
    exactCount left marks = exactCount right marks := by
  classical
  have htotal := h marks
  rw [markedCount_eq_sum, markedCount_eq_sum] at htotal
  let upper := Finset.univ.filter (marks ⊆ ·)
  have hm : marks ∈ upper := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.rfl⟩
  change (∑ s ∈ upper, exactCount left s) = ∑ s ∈ upper, exactCount right s at htotal
  rw [← Finset.sum_erase_add _ _ hm, ← Finset.sum_erase_add _ _ hm] at htotal
  have herase : (∑ s ∈ upper.erase marks, exactCount left s) =
      ∑ s ∈ upper.erase marks, exactCount right s := by
    apply Finset.sum_congr rfl
    intro s hs
    have hsub : marks ⊆ s := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hs)).2
    have hstrict : marks ⊂ s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, (Finset.ne_of_mem_erase hs).symm⟩
    exact exactCount_eq_of_markedCount_eq left right h s
  omega
termination_by Fintype.card α - marks.card
decreasing_by
  have hlt := Finset.card_lt_card hstrict
  have hle := Finset.card_le_univ s
  omega

end Implications.WilfCounts
