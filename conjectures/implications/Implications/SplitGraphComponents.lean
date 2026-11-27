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
    hne (Finset.card_le_one_iff.mp hDo.le (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hb).2⟩) hd)
  have hdB : d ∉ B := fun h =>
    hne (Finset.card_le_one_iff.mp hBo.le hb (Finset.mem_sdiff.mpr ⟨h, (Finset.mem_sdiff.mp hd).2⟩))
  have hbDiff : b ∈ B \ D := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hb).1, hbD⟩
  have hdDiff : d ∈ D \ B := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hd).1, hdB⟩
  rw [card_row_difference] at hBD
  have hpos := Finset.card_pos.mpr ⟨d, hdDiff⟩
  have hsmall : (B \ D).card ≤ 1 := by omega
  refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (by rw [hBi, hDi])
  obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
  refine Finset.mem_inter.mpr ⟨hxA, ?_⟩
  by_contra hxd
  have hxb := Finset.card_le_one_iff.mp hsmall (Finset.mem_sdiff.mpr ⟨hxB, hxd⟩) hbDiff
  exact (Finset.mem_sdiff.mp hb).2 (hxb ▸ hxA)

/-- If two distinct outside vertices occur, every row meeting the outside
attaches to one common pair in the three-element row. -/
theorem tripleRow_common_outside_pair
    {α : Type*} [DecidableEq α] (A : Finset α) (R : Finset (Finset α))
    (hA : A.card = 3) (hAR : A ∈ R)
    (hsize : ∀ B ∈ R, B.card ≤ 3)
    (hdiff : ∀ B ∈ R, ∀ D ∈ R, (B \ D ∪ D \ B).card ≤ 2)
    {B D : Finset α} (hBR : B ∈ R) (hDR : D ∈ R) {b d : α}
    (hb : b ∈ B \ A) (hd : d ∈ D \ A) (hne : b ≠ d) :
    ∃ P : Finset α, P ⊆ A ∧ P.card = 2 ∧
      ∀ T ∈ R, (T \ A).Nonempty → A ∩ T = P := by
  have hBD : A ∩ B = A ∩ D :=
    tripleRow_outside_attachments_eq A B D hA (hsize B hBR) (hsize D hDR)
      (hdiff A hAR B hBR) (hdiff A hAR D hDR) (hdiff B hBR D hDR) hb hd hne
  refine ⟨A ∩ B, Finset.inter_subset_left,
    (tripleRow_outside_counts A B hA (hsize B hBR) (hdiff A hAR B hBR) ⟨b, hb⟩).1, ?_⟩
  rintro T hTR ⟨t, ht⟩
  by_cases htb : t = b
  · have htd : t ≠ d := htb ▸ hne
    exact (tripleRow_outside_attachments_eq A T D hA (hsize T hTR) (hsize D hDR)
      (hdiff A hAR T hTR) (hdiff A hAR D hDR) (hdiff T hTR D hDR) ht hd htd).trans hBD.symm
  · exact tripleRow_outside_attachments_eq A T B hA (hsize T hTR) (hsize B hBR)
      (hdiff A hAR T hTR) (hdiff A hAR B hBR) (hdiff T hTR B hBR) ht hb htb

/-- The third vertex of a triple row occurs only in copies of the full triple
when at least two distinct outsiders occur in the row family. -/
theorem tripleRow_third_forces_full_row
    {α : Type*} [DecidableEq α] (A : Finset α) (R : Finset (Finset α))
    (hA : A.card = 3) (hAR : A ∈ R)
    (hsize : ∀ B ∈ R, B.card ≤ 3)
    (hdiff : ∀ B ∈ R, ∀ D ∈ R, (B \ D ∪ D \ B).card ≤ 2)
    {B D T : Finset α} (hBR : B ∈ R) (hDR : D ∈ R) (hTR : T ∈ R)
    {b d x : α} (hb : b ∈ B \ A) (hd : d ∈ D \ A) (hne : b ≠ d)
    (hx : x ∈ A \ B) (hxT : x ∈ T) :
    T = A := by
  obtain ⟨P, hPA, hPsize, hcommon⟩ :=
    tripleRow_common_outside_pair A R hA hAR hsize hdiff hBR hDR hb hd hne
  have hBP : A ∩ B = P := hcommon B hBR ⟨b, hb⟩
  have hxA := (Finset.mem_sdiff.mp hx).1
  have hxB := (Finset.mem_sdiff.mp hx).2
  have hTsub : T ⊆ A := by
    intro y hy
    by_contra hyA
    have hTP := hcommon T hTR ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyA⟩⟩
    have hxP : x ∈ P := hTP ▸ Finset.mem_inter.mpr ⟨hxA, hxT⟩
    exact hxB (Finset.mem_inter.mp (hBP.symm ▸ hxP)).2
  have hbA := (Finset.mem_sdiff.mp hb).2
  have hbDiff : b ∈ B \ T :=
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hb).1, fun h => hbA (hTsub h)⟩
  have hxDiff : x ∈ T \ B := Finset.mem_sdiff.mpr ⟨hxT, hxB⟩
  have hpos := Finset.card_pos.mpr ⟨x, hxDiff⟩
  have hBT := hdiff B hBR T hTR
  rw [card_row_difference] at hBT
  have hsmall : (B \ T).card ≤ 1 := by omega
  have hPT : P ⊆ T := by
    intro y hy
    by_contra hyT
    have hmem := Finset.mem_inter.mp (hBP.symm ▸ hy)
    have hyb := Finset.card_le_one_iff.mp hsmall
      (Finset.mem_sdiff.mpr ⟨hmem.2, hyT⟩) hbDiff
    exact hbA (hyb ▸ hmem.1)
  have hxP : x ∉ P := fun h => hxB (Finset.mem_inter.mp (hBP.symm ▸ h)).2
  have hinsT : insert x P ⊆ T := Finset.insert_subset hxT hPT
  have hcard := Finset.card_le_card hinsT
  rw [Finset.card_insert_of_notMem hxP, hPsize] at hcard
  exact Finset.eq_of_subset_of_card_le hTsub (by omega)

end SplitGraphComponents

#print axioms SplitGraphComponents.tripleRow_outside_counts
#print axioms SplitGraphComponents.tripleRow_outside_attachments_eq
#print axioms SplitGraphComponents.tripleRow_common_outside_pair
#print axioms SplitGraphComponents.tripleRow_third_forces_full_row
