import Mathlib

/-!
Set-theoretic constraints for connectivity two in the WOWII 199 split-graph argument.
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

private theorem card_row_difference {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A \ B ∪ B \ A).card = (A \ B).card + (B \ A).card := by
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1

/-- A row containing a vertex outside a three-element row contains exactly
two vertices of the three-element row and exactly one outside it. -/
theorem tripleRow_outside_counts
    {α : Type*} [DecidableEq α] (A B : Finset α)
    (hA : A.card = 3) (hB : B.card ≤ 3)
    (hd : (A \ B ∪ B \ A).card ≤ 2)
    (hout : (B \ A).Nonempty) :
    (A ∩ B).card = 2 ∧ (B \ A).card = 1 := by
  rw [card_row_difference] at hd
  have ha := Finset.card_sdiff_add_card_inter A B
  have hb := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hb
  have hp := Finset.card_pos.mpr hout
  omega

/-- Rows containing distinct outside vertices attach to the same pair in
the three-element row. -/
theorem tripleRow_outside_attachments_eq
    {α : Type*} [DecidableEq α] (A B D : Finset α) {b d : α}
    (hA : A.card = 3) (hB : B.card ≤ 3) (hD : D.card ≤ 3)
    (hAB : (A \ B ∪ B \ A).card ≤ 2)
    (hAD : (A \ D ∪ D \ A).card ≤ 2)
    (hBD : (B \ D ∪ D \ B).card ≤ 2)
    (hb : b ∈ B \ A) (hd : d ∈ D \ A) (hne : b ≠ d) :
    A ∩ B = A ∩ D := by
  obtain ⟨hBi, hBo⟩ := tripleRow_outside_counts A B hA hB hAB ⟨b, hb⟩
  obtain ⟨hDi, hDo⟩ := tripleRow_outside_counts A D hA hD hAD ⟨d, hd⟩
  have hbD : b ∉ D := fun h =>
    hne (Finset.card_le_one.mp hDo.le (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hb).2⟩) hd)
  have hdB : d ∉ B := fun h =>
    hne (Finset.card_le_one.mp hBo.le hb (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hd).2⟩))
  have hbDiff : b ∈ B \ D := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hb).1, hbD⟩
  have hdDiff : d ∈ D \ B := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hd).1, hdB⟩
  rw [card_row_difference] at hBD
  have hpos := Finset.card_pos.mpr ⟨d, hdDiff⟩
  have hsmall : (B \ D).card ≤ 1 := by omega
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (by rw [hBi, hDi])
  obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
  refine Finset.mem_inter.mpr ⟨hxA, ?_⟩
  by_contra hxd
  have hxb := Finset.card_le_one.mp hsmall (Finset.mem_sdiff.mpr ⟨hxB, hxd⟩) hbDiff
  exact (Finset.mem_sdiff.mp hb).2 (hxb ▸ hxA)

end SplitGraphComponents

#print axioms SplitGraphComponents.tripleRow_outside_counts
#print axioms SplitGraphComponents.tripleRow_outside_attachments_eq
