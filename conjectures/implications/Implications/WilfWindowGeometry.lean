import Implications.WilfDisjointPermutations

/-! Reusable support geometry for local permutations on marked length-eight windows. -/

namespace Implications.WilfWindowGeometry

open WilfDisjointPermutations

/-- The support of a permutation lifted into a window is the image of its local support. -/
theorem liftWindow_support_image {n : ℕ} (s : ℕ) (hs : s + 8 ≤ n)
    (m : Equiv.Perm (Fin 8)) :
    (liftWindow s hs m).support = m.support.image (windowEmbedding s hs) := by
  classical
  ext x
  rw [Equiv.Perm.mem_support, Finset.mem_image]
  constructor
  · intro hx
    have hnot : x ∈ Set.range (windowEmbedding s hs) := by
      by_contra hnot
      exact hx (Equiv.Perm.viaEmbedding_apply_of_notMem m (windowEmbedding s hs) x hnot)
    obtain ⟨i, rfl⟩ := hnot
    refine ⟨i, ?_, rfl⟩
    rw [Equiv.Perm.mem_support]
    intro hfix
    apply hx
    rw [liftWindow_apply]
    exact congrArg (windowEmbedding s hs) hfix
  · rintro ⟨i, hi, rfl⟩
    rw [Equiv.Perm.mem_support] at hi
    intro hfix
    apply hi
    apply (windowEmbedding s hs).injective
    rw [liftWindow_apply] at hfix
    exact hfix

/-- A family of length-eight starts is separated according to its allowed overlap shifts.
Every pair is either disjoint as windows or has a gap listed in `shifts`. -/
def SeparatedBy (marks shifts : Finset ℕ) : Prop :=
  ∀ s ∈ marks, ∀ t ∈ marks, s < t → 8 ≤ t - s ∨ t - s ∈ shifts

/-- When every allowed overlap shift is at least four, a marked window has at most
one later marked window that overlaps it. -/
theorem unique_overlapping_successor (marks shifts : Finset ℕ)
    (hsep : SeparatedBy marks shifts)
    (hgap : ∀ d ∈ shifts, 4 ≤ d)
    {s t u : ℕ} (hs : s ∈ marks) (ht : t ∈ marks) (hu : u ∈ marks)
    (hst : s < t) (hsu : s < u) (htt : t - s < 8) (htu : u - s < 8) :
    t = u := by
  have hstGap : 4 ≤ t - s := by
    rcases hsep s hs t ht hst with hfar | hd
    · omega
    · exact hgap (t - s) hd
  have hsuGap : 4 ≤ u - s := by
    rcases hsep s hs u hu hsu with hfar | hd
    · omega
    · exact hgap (u - s) hd
  rcases lt_trichotomy t u with h | h | h
  · omega
  · exact h
  · omega

/-- If local moved offsets never meet their translates at an allowed gap, the lifted
permutations at all marked windows have pairwise-disjoint supports. -/
theorem lifted_windows_pairwise_disjoint {n : ℕ} (marks shifts : Finset ℕ)
    (m : Equiv.Perm (Fin 8))
    (hb : ∀ s ∈ marks, s + 8 ≤ n)
    (hsep : SeparatedBy marks shifts)
    (htranslate : ∀ d ∈ shifts, ∀ i j : Fin 8,
      i ∈ m.support → j ∈ m.support → i.val ≠ d + j.val) :
    ∀ s (hs : s ∈ marks), ∀ t (ht : t ∈ marks), s ≠ t →
      Equiv.Perm.Disjoint (liftWindow s (hb s hs) m)
        (liftWindow t (hb t ht) m) := by
  have hordered {s t : ℕ} (hs : s ∈ marks) (ht : t ∈ marks) (hst : s < t) :
      Equiv.Perm.Disjoint (liftWindow s (hb s hs) m) (liftWindow t (hb t ht) m) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    rw [liftWindow_support_image] at hx hx'
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx'
    have hindex := congrArg Fin.val (hix.trans hjx.symm)
    change s + i.val = t + j.val at hindex
    rcases hsep s hs t ht hst with hfar | hd
    · have hi8 := i.isLt
      have hj8 := j.isLt
      omega
    · exact htranslate (t - s) hd i j hi hj (by omega)
  intro s hs t ht hst
  rcases lt_or_gt_of_ne hst with h | h
  · exact hordered hs ht h
  · exact (hordered ht hs h).symm

#print axioms liftWindow_support_image
#print axioms unique_overlapping_successor
#print axioms lifted_windows_pairwise_disjoint

end Implications.WilfWindowGeometry
