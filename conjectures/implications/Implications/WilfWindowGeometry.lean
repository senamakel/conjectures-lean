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
  · rcases hsep t ht u hu h with hfar | hd
    · omega
    · have htuGap := hgap (u - t) hd
      omega
  · exact h
  · rcases hsep u hu t ht h with hfar | hd
    · omega
    · have hutGap := hgap (t - u) hd
      omega

/-- The corresponding uniqueness statement for an earlier overlapping window. -/
theorem unique_overlapping_predecessor (marks shifts : Finset ℕ)
    (hsep : SeparatedBy marks shifts)
    (hgap : ∀ d ∈ shifts, 4 ≤ d)
    {s t u : ℕ} (hs : s ∈ marks) (ht : t ∈ marks) (hu : u ∈ marks)
    (hst : t < s) (hus : u < s) (htt : s - t < 8) (htu : s - u < 8) :
    t = u := by
  have hstGap : 4 ≤ s - t := by
    rcases hsep t ht s hs hst with hfar | hd
    · omega
    · exact hgap (s - t) hd
  have husGap : 4 ≤ s - u := by
    rcases hsep u hu s hs hus with hfar | hd
    · omega
    · exact hgap (s - u) hd
  rcases lt_trichotomy t u with h | h | h
  · rcases hsep t ht u hu h with hfar | hd
    · omega
    · have htuGap := hgap (u - t) hd
      omega
  · exact h
  · rcases hsep u hu t ht h with hfar | hd
    · omega
    · have hutGap := hgap (t - u) hd
      omega

/-- If a summand based at another marked start moves a point of the central window,
its start is an allowed overlap shift immediately before or after the central start. -/
theorem moved_position_has_overlapping_neighbor (marks shifts : Finset ℕ)
    (hsep : SeparatedBy marks shifts)
    {s t : ℕ} (hs : s ∈ marks) (ht : t ∈ marks) (hst : s ≠ t)
    (i j : Fin 8)
    (hcoord : s + i.val = t + j.val) :
    (t < s ∧ s - t ∈ shifts ∧ s - t < 8) ∨
      (s < t ∧ t - s ∈ shifts ∧ t - s < 8) := by
  have hi8 := i.isLt
  have hj8 := j.isLt
  rcases lt_or_gt_of_ne hst with hst' | hts
  · rcases hsep s hs t ht hst' with hfar | hd
    · omega
    · exact Or.inr ⟨hst', hd, by omega⟩
  · rcases hsep t ht s hs hts with hfar | hd
    · omega
    · exact Or.inl ⟨hts, hd, by omega⟩

private abbrev MarkedStart (marks : Finset ℕ) := {t : ℕ // t ∈ marks}

private noncomputable def markedComponent {n : ℕ} (marks : Finset ℕ)
    (m : Equiv.Perm (Fin 8)) (hb : ∀ s ∈ marks, s + 8 ≤ n) (t : MarkedStart marks) :
    Equiv.Perm (Fin n) :=
  liftWindow t.val (hb t.val t.property) m

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

private theorem markedComponents_disjoint {n : ℕ} (marks shifts : Finset ℕ)
    (m : Equiv.Perm (Fin 8)) (hb : ∀ s ∈ marks, s + 8 ≤ n)
    (hsep : SeparatedBy marks shifts)
    (htranslate : ∀ d ∈ shifts, ∀ i j : Fin 8,
      i ∈ m.support → j ∈ m.support → i.val ≠ d + j.val) :
    ((Finset.univ : Finset (MarkedStart marks)) : Set (MarkedStart marks)).Pairwise
      (fun s t => Equiv.Perm.Disjoint
        (markedComponent marks m hb s) (markedComponent marks m hb t)) := by
  have hpair := lifted_windows_pairwise_disjoint marks shifts m hb hsep htranslate
  intro s _ t _ hst
  apply hpair s.val s.property t.val t.property
  intro h
  apply hst
  exact Subtype.ext h

/-- Two distinct marked starts cannot both move the same point under their lifted
local permutations, under the translated-support separation hypothesis. -/
theorem lifted_support_mover_unique {n : ℕ} (marks shifts : Finset ℕ)
    (m : Equiv.Perm (Fin 8)) (hb : ∀ s ∈ marks, s + 8 ≤ n)
    (hsep : SeparatedBy marks shifts)
    (htranslate : ∀ d ∈ shifts, ∀ i j : Fin 8,
      i ∈ m.support → j ∈ m.support → i.val ≠ d + j.val)
    {s t : ℕ} (hs : s ∈ marks) (ht : t ∈ marks) (hst : s ≠ t)
    {x : Fin n} (hx₁ : x ∈ (liftWindow s (hb s hs) m).support)
    (hx₂ : x ∈ (liftWindow t (hb t ht) m).support) : False := by
  have hdisj := lifted_windows_pairwise_disjoint marks shifts m hb hsep htranslate
    s hs t ht hst
  rw [Equiv.Perm.disjoint_iff_disjoint_support] at hdisj
  exact (Finset.disjoint_left.mp hdisj) hx₁ hx₂

/-- At a point moved by one marked-window summand, the global assembled permutation
acts exactly as that summand. -/
theorem assemble_apply_of_lifted_support {n : ℕ} (marks shifts : Finset ℕ)
    (m : Equiv.Perm (Fin 8)) (hb : ∀ s ∈ marks, s + 8 ≤ n)
    (hsep : SeparatedBy marks shifts)
    (htranslate : ∀ d ∈ shifts, ∀ i j : Fin 8,
      i ∈ m.support → j ∈ m.support → i.val ≠ d + j.val)
    {t : ℕ} (ht : t ∈ marks) {x : Fin n}
    (hx : x ∈ (liftWindow t (hb t ht) m).support) :
    WilfDisjointPermutations.assemble (Finset.univ : Finset (MarkedStart marks))
      (markedComponent marks m hb)
      (markedComponents_disjoint marks shifts m hb hsep htranslate) x =
        liftWindow t (hb t ht) m x := by
  exact WilfDisjointPermutations.assemble_apply_of_mem_support
    (Finset.univ : Finset (MarkedStart marks)) (markedComponent marks m hb)
    (markedComponents_disjoint marks shifts m hb hsep htranslate)
    (i := ⟨t, ht⟩) (Finset.mem_univ _) hx

/-- If no marked-window summand moves a point, the assembled permutation fixes it. -/
theorem assemble_apply_of_no_lifted_support {n : ℕ} (marks shifts : Finset ℕ)
    (m : Equiv.Perm (Fin 8)) (hb : ∀ s ∈ marks, s + 8 ≤ n)
    (hsep : SeparatedBy marks shifts)
    (htranslate : ∀ d ∈ shifts, ∀ i j : Fin 8,
      i ∈ m.support → j ∈ m.support → i.val ≠ d + j.val)
    {x : Fin n} (hx : ∀ t (ht : t ∈ marks),
      x ∉ (liftWindow t (hb t ht) m).support) :
    WilfDisjointPermutations.assemble (Finset.univ : Finset (MarkedStart marks))
      (markedComponent marks m hb)
      (markedComponents_disjoint marks shifts m hb hsep htranslate) x = x := by
  exact WilfDisjointPermutations.assemble_apply_of_forall_fixes
    (Finset.univ : Finset (MarkedStart marks)) (markedComponent marks m hb)
    (markedComponents_disjoint marks shifts m hb hsep htranslate) (by
      intro t _
      exact Equiv.Perm.notMem_support.mp (hx t.val t.property))

#print axioms liftWindow_support_image
#print axioms unique_overlapping_successor
#print axioms unique_overlapping_predecessor
#print axioms moved_position_has_overlapping_neighbor
#print axioms lifted_windows_pairwise_disjoint
#print axioms lifted_support_mover_unique
#print axioms assemble_apply_of_lifted_support
#print axioms assemble_apply_of_no_lifted_support

end Implications.WilfWindowGeometry
