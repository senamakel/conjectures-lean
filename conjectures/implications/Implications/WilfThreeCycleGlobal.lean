import Mathlib.GroupTheory.Perm.ViaEmbedding
import Implications.WilfThreeCycleOrder
import Implications.WilfPatternSwap

/-! Geometry of simultaneous three-position cycles in marked length-eight windows. -/

namespace Implications.WilfThreeCycleGlobal

open WilfMarked WilfTwoWindowOrder WilfThreeCycleOrder

private def windowEmbedding {n : ℕ} (s : ℕ) (hs : s + 7 < n) : Fin 8 ↪ Fin n where
  toFun i := ⟨s + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change s + i.val = s + j.val at hv
    omega

private noncomputable def component {n : ℕ} (m : Equiv.Perm (Fin 8)) (s : ℕ) :
    Equiv.Perm (Fin n) :=
  if hs : s + 7 < n then m.viaEmbedding (windowEmbedding s hs) else Equiv.refl _

private theorem component_apply {n : ℕ} (m : Equiv.Perm (Fin 8)) {s : ℕ}
    (hs : s + 7 < n) (i : Fin 8) :
    component m s (windowEmbedding s hs i) = windowEmbedding s hs (m i) := by
  rw [component, dif_pos hs, Equiv.Perm.viaEmbedding_apply]

private theorem mem_component_support {n : ℕ} (m : Equiv.Perm (Fin 8)) {s : ℕ}
    (hs : s + 7 < n) (x : Fin n) :
    x ∈ (component m s).support ↔ ∃ i : Fin 8, m i ≠ i ∧ windowEmbedding s hs i = x := by
  classical
  rw [Equiv.Perm.mem_support]
  constructor
  · intro h
    by_cases hx : x ∈ Set.range (windowEmbedding s hs)
    · obtain ⟨i, rfl⟩ := hx
      rw [component_apply m hs] at h
      exact ⟨i, fun e => h (congrArg (windowEmbedding s hs) e), rfl⟩
    · rw [component, dif_pos hs, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx] at h
      exact (h rfl).elim
  · rintro ⟨i, h, rfl⟩
    rw [component_apply m hs]
    exact fun e => h ((windowEmbedding s hs).injective e)

/-- Every pair of distinct starts has gap five or at least seven. -/
def SeparatedStarts (marks : Finset ℕ) : Prop :=
  ∀ s ∈ marks, ∀ t ∈ marks, s < t → t - s = 5 ∨ 7 ≤ t - s

private theorem separated_of_occurrences {n : ℕ} (π : Equiv.Perm (Fin n))
    (p : Fin 8 → Fin 8)
    (hover : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (marks : Finset ℕ) (hmark : ∀ s ∈ marks, ContainsAt π s p) :
    SeparatedStarts marks := by
  intro s hs t ht hst
  by_cases hd : t - s < 8
  · have hov := same_pattern_overlap_compatible π p s t (hmark s hs) (hmark t ht) hst hd
    rcases hover (t - s) (by omega) hd hov with h | h
    · exact Or.inl h
    · exact Or.inr h.ge
  · exact Or.inr (by omega)

/-- A moved position from a different marked window reaches the current window
only at offset six, from offset one of the window starting five places later. -/
theorem crossing_offsets (marks : Finset ℕ) (hsep : SeparatedStarts marks)
    {s t : ℕ} (hs : s ∈ marks) (ht : t ∈ marks) (hst : s ≠ t)
    {i j : Fin 8} (hj : j = 1 ∨ j = 3 ∨ j = 4)
    (hindex : s + i.val = t + j.val) :
    t = s + 5 ∧ i = 6 ∧ j = 1 := by
  have hi8 := i.isLt
  have hrange : 1 ≤ j.val ∧ j.val ≤ 4 := by
    rcases hj with rfl | rfl | rfl <;> decide
  rcases lt_or_gt_of_ne hst with hst | hts
  · have ht5 : t = s + 5 := by
      rcases hsep s hs t ht hst with h | h <;> omega
    have hj1 : j = 1 := by
      rcases hj with rfl | rfl | rfl
      · rfl
      · change s + i.val = t + 3 at hindex
        omega
      · change s + i.val = t + 4 at hindex
        omega
    refine ⟨ht5, Fin.ext ?_, hj1⟩
    rw [hj1] at hindex
    change s + i.val = t + 1 at hindex
    change i.val = 6
    omega
  · exfalso
    rcases hsep t ht s hs hts with h | h <;> omega

private theorem components_disjoint {n : ℕ} (m : Equiv.Perm (Fin 8))
    (hm : ∀ i : Fin 8, m i ≠ i ↔ i = 1 ∨ i = 3 ∨ i = 4)
    (marks : Finset ℕ) (hb : ∀ s ∈ marks, s + 7 < n) (hsep : SeparatedStarts marks) :
    (marks : Set ℕ).Pairwise
      (fun s t => Equiv.Perm.Disjoint (component m s : Equiv.Perm (Fin n)) (component m t)) := by
  intro s hs t ht hst
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨i, hi, he⟩ := (mem_component_support m (hb s hs) x).mp hx
  obtain ⟨j, hj, he'⟩ := (mem_component_support m (hb t ht) x).mp hx'
  have hindex := congrArg Fin.val (he.trans he'.symm)
  change s + i.val = t + j.val at hindex
  obtain ⟨_, rfl, _⟩ := crossing_offsets marks hsep hs ht hst ((hm j).mp hj) hindex
  simpa using (hm 6).mp hi

#print axioms crossing_offsets

end Implications.WilfThreeCycleGlobal
