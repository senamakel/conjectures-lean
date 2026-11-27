import Implications.WilfDisjointPermutations
import Implications.WilfThreeCycleOrder
import Implications.WilfPatternSwap

/-! Geometry of simultaneous three-position cycles in marked length-eight windows. -/

namespace Implications.WilfThreeCycleGlobal

open WilfMarked WilfTwoWindowOrder WilfThreeCycleOrder

/-- The middle pattern in archive block 41, obtained by swapping entries at positions one and
three of `23145786`. -/
def pattern24135786 : Fin 8 → Fin 8 := ![1, 3, 0, 2, 4, 6, 7, 5]

/-- The position transposition relating the first and middle patterns of block 41. -/
def swap13 : Equiv.Perm (Fin 8) := Equiv.swap 1 3

private abbrev windowEmbedding {n : ℕ} (s : ℕ) (hs : s + 7 < n) : Fin 8 ↪ Fin n :=
  WilfDisjointPermutations.windowEmbedding s (by omega)

private noncomputable def component {n : ℕ} (m : Equiv.Perm (Fin 8)) (s : ℕ) :
    Equiv.Perm (Fin n) :=
  if hs : s + 7 < n then WilfDisjointPermutations.liftWindow s (by omega) m else Equiv.refl _

private theorem component_apply {n : ℕ} (m : Equiv.Perm (Fin 8)) {s : ℕ}
    (hs : s + 7 < n) (i : Fin 8) :
    component m s (windowEmbedding s hs i) = windowEmbedding s hs (m i) := by
  rw [component, dite_eq_left hs, WilfDisjointPermutations.liftWindow_apply]

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
    · rw [component, dite_eq_left hs] at h
      exact (h (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx)).elim
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
    (hm : ∀ i : Fin 8, m i ≠ i → i = 1 ∨ i = 3 ∨ i = 4)
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
  obtain ⟨_, rfl, _⟩ := crossing_offsets marks hsep hs ht hst (hm j hj) hindex
  rcases hm 6 hi with h | h | h <;> norm_num at h

private theorem assembled_on_window {n : ℕ} (m : Equiv.Perm (Fin 8))
    (hm : ∀ i : Fin 8, m i ≠ i → i = 1 ∨ i = 3 ∨ i = 4)
    (hm1 : m 1 ≠ 1)
    (marks : Finset ℕ) (hb : ∀ s ∈ marks, s + 7 < n) (hsep : SeparatedStarts marks)
    {s : ℕ} (hs : s ∈ marks) (i : Fin 8) :
    WilfDisjointPermutations.assemble marks (component m) (components_disjoint m hm marks hb hsep)
        (windowEmbedding s (hb s hs) i) =
      if h : i = 6 ∧ s + 5 ∈ marks then
        windowEmbedding (s + 5) (hb _ h.2) (m 1)
      else windowEmbedding s (hb s hs) (m i) := by
  by_cases hnext : i = 6 ∧ s + 5 ∈ marks
  · rw [dite_eq_left hnext]
    have he : windowEmbedding (s + 5) (hb _ hnext.2) (1 : Fin 8) =
        windowEmbedding s (hb s hs) i := by
      apply Fin.ext
      change s + 5 + 1 = s + i.val
      rw [hnext.1]
      rfl
    rw [← he]
    rw [WilfDisjointPermutations.assemble_apply_of_mem_support _ _ _ hnext.2]
    · exact component_apply m (hb _ hnext.2) 1
      · exact (mem_component_support m (hb _ hnext.2) _).mpr ⟨1, hm1, rfl⟩
  · rw [dite_eq_right hnext]
    by_cases hmove : m i ≠ i
    · rw [WilfDisjointPermutations.assemble_apply_of_mem_support _ _ _ hs]
      · exact component_apply m (hb _ hs) i
      · exact (mem_component_support m (hb _ hs) _).mpr ⟨i, hmove, rfl⟩
    · rw [not_ne_iff.mp hmove]
      apply WilfDisjointPermutations.assemble_apply_of_forall_fixes
      intro t ht
      by_cases heq : t = s
      · subst t
        rw [component_apply m (hb _ hs), not_ne_iff.mp hmove]
      · by_contra! hbad
        have hmem := Equiv.Perm.mem_support.mpr hbad
        obtain ⟨j, hj, he⟩ := (mem_component_support m (hb _ ht) _).mp hmem
        have hindex := congrArg Fin.val he.symm
        change s + i.val = t + j.val at hindex
        obtain ⟨ht', hi, _⟩ := crossing_offsets marks hsep hs ht (Ne.symm heq) (hm j hj) hindex
        exact hnext ⟨hi, ht' ▸ ht⟩

private def Marked {n : ℕ} (marks : Finset ℕ) (p : Fin 8 → Fin 8)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ s ∈ marks, ContainsAt π s p

private noncomputable def moveMarked {n : ℕ} (marks : Finset ℕ) (p q : Fin 8 → Fin 8)
    (m : Equiv.Perm (Fin 8))
    (hm : ∀ i : Fin 8, m i ≠ i → i = 1 ∨ i = 3 ∨ i = 4)
    (hm1 : m 1 ≠ 1)
    (hover : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hq : p ∘ m = q)
    (hlocal : ∀ f : Fin 13 → Fin n, WindowOrder p f 0 → WindowOrder p f 5 →
      ∀ i j, f (overlapImage m i) < f (overlapImage m j) ↔ q i < q j)
    (π : {f : Equiv.Perm (Fin n) // Marked marks p f}) :
    {f : Equiv.Perm (Fin n) // Marked marks q f} := by
  let hb := marked_starts_bounded π.val p marks π.property
  let hsep := separated_of_occurrences π.val p hover marks π.property
  let g := WilfDisjointPermutations.assemble marks (component m)
    (components_disjoint m hm marks hb hsep)
  refine ⟨g.trans π.val, ?_⟩
  intro s hs
  have hfirst := π.property s hs
  refine ⟨hb s hs, ?_⟩
  intro i j
  change π.val (g (windowEmbedding s (hb s hs) i)) <
    π.val (g (windowEmbedding s (hb s hs) j)) ↔ q i < q j
  by_cases hnext : s + 5 ∈ marks
  · let f : Fin 13 → Fin n :=
      fun k => π.val ⟨s + k.val, by have := hb _ hnext; have := k.isLt; omega⟩
    have h0 : WindowOrder p f 0 := by
      obtain ⟨_, hpat⟩ := hfirst
      intro a b h
      simpa [f, position] using (hpat a b).mpr h
    have h5 : WindowOrder p f 5 := by
      obtain ⟨_, hpat⟩ := π.property (s + 5) hnext
      intro a b h
      simpa [f, position, Nat.add_assoc] using (hpat a b).mpr h
    have himage (k : Fin 8) :
        π.val (g (windowEmbedding s (hb s hs) k)) = f (overlapImage m k) := by
      change π.val (WilfDisjointPermutations.assemble marks (component m)
        (components_disjoint m hm marks hb hsep) (windowEmbedding s (hb s hs) k)) = _
      rw [assembled_on_window m hm hm1 marks hb hsep hs]
      by_cases hk : k = 6
      · rw [dite_eq_left ⟨hk, hnext⟩]
        congr 1
        apply Fin.ext
        simp [overlapImage, hk, WilfDisjointPermutations.windowEmbedding, position, Nat.add_assoc]
      · rw [dite_eq_right (fun h => hk h.1)]
        congr 1
        apply Fin.ext
        simp [overlapImage, hk, WilfDisjointPermutations.windowEmbedding, position]
        rfl
    rw [himage i, himage j]
    exact hlocal f h0 h5 i j
  · have hfix (k : Fin 8) : g (windowEmbedding s (hb s hs) k) =
        windowEmbedding s (hb s hs) (m k) := by
      change WilfDisjointPermutations.assemble marks (component m)
        (components_disjoint m hm marks hb hsep) (windowEmbedding s (hb s hs) k) = _
      rw [assembled_on_window m hm hm1 marks hb hsep hs, dite_eq_right (fun h => hnext h.2)]
    rw [hfix i, hfix j, ← hq]
    obtain ⟨_, hpat⟩ := hfirst
    exact hpat (m i) (m j)

private theorem moveMarked_injective {n : ℕ} (marks : Finset ℕ) (p q : Fin 8 → Fin 8)
    (m : Equiv.Perm (Fin 8))
    (hm : ∀ i : Fin 8, m i ≠ i → i = 1 ∨ i = 3 ∨ i = 4)
    (hm1 : m 1 ≠ 1)
    (hover : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hq : p ∘ m = q)
    (hlocal : ∀ f : Fin 13 → Fin n, WindowOrder p f 0 → WindowOrder p f 5 →
      ∀ i j, f (overlapImage m i) < f (overlapImage m j) ↔ q i < q j) :
    Function.Injective (moveMarked marks p q m hm hm1 hover hq hlocal) := by
  intro a b hab
  apply Subtype.ext
  let hb := marked_starts_bounded a.val p marks a.property
  let hs := separated_of_occurrences a.val p hover marks a.property
  let g := WilfDisjointPermutations.assemble marks (component m)
    (components_disjoint m hm marks hb hs)
  have he : g.trans a.val = g.trans b.val := congrArg Subtype.val hab
  apply Equiv.ext
  intro x
  have hx := congrArg (fun e : Equiv.Perm (Fin n) => e (g.symm x)) he
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hx

private theorem marked_iff_subset {n : ℕ} (p : Fin 8 → Fin 8)
    (chosen : Finset (Fin n)) (π : Equiv.Perm (Fin n)) :
    chosen ⊆ WilfPatternSwap.occurrenceSet p π ↔ Marked (chosen.image Fin.val) p π := by
  classical
  constructor
  · intro h s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_filter.mp (h hi)).2
  · intro h i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h i.val (Finset.mem_image_of_mem _ hi)⟩

/-- A marked-window bijection turns a local overlap certificate into exact count equality.

The moved points of `m` only need to lie among offsets `1`, `3`, and `4`; the separate
condition on offset `1` ensures that a later marked window supplies a nontrivial component
at the critical crossing point. -/
theorem exactOccurrenceCount_eq_of_markedSwap (n : ℕ) (marks : Finset (Fin n))
    (p q : Fin 8 → Fin 8) (m : Equiv.Perm (Fin 8))
    (hm : ∀ i : Fin 8, m i ≠ i → i = 1 ∨ i = 3 ∨ i = 4) (hm1 : m 1 ≠ 1)
    (hoverP : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hoverQ : ∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7)
    (hpq : p ∘ m = q) (hqp : q ∘ m.symm = p)
    (hlocal : ∀ f : Fin 13 → Fin n, WindowOrder p f 0 → WindowOrder p f 5 →
      ∀ i j, f (overlapImage m i) < f (overlapImage m j) ↔ q i < q j)
    (hlocalInv : ∀ f : Fin 13 → Fin n, WindowOrder q f 0 → WindowOrder q f 5 →
      ∀ i j, f (overlapImage m.symm i) < f (overlapImage m.symm j) ↔ p i < p j) :
    WilfCounts.exactCount (WilfPatternSwap.occurrenceSet p) marks =
      WilfCounts.exactCount (WilfPatternSwap.occurrenceSet q) marks := by
  classical
  apply WilfEquivalence.exactCount_eq_of_markedEquiv
  intro chosen
  let chosenNat := chosen.image Fin.val
  have hmInv : ∀ i : Fin 8, m.symm i ≠ i → i = 1 ∨ i = 3 ∨ i = 4 := by
    intro i hi
    apply hm i
    intro hfix
    apply hi
    have h := congrArg m.symm hfix
    simpa using h.symm
  have hm1Inv : m.symm 1 ≠ 1 := by
    intro hfix
    apply hm1
    have h := congrArg m hfix
    simpa using h.symm
  have hcount : Fintype.card {π : Equiv.Perm (Fin n) // Marked chosenNat p π} =
      Fintype.card {π : Equiv.Perm (Fin n) // Marked chosenNat q π} := by
    apply le_antisymm
    · apply Fintype.card_le_of_injective _
        (moveMarked_injective chosenNat p q m hm hm1 hoverP hpq hlocal)
      apply overlap_compatible_only_at_5_or_7_of_decide
      intro d hd hsmall
      exact hoverP d hd hsmall
    · apply Fintype.card_le_of_injective _
        (moveMarked_injective chosenNat q p m.symm hmInv hm1Inv hoverQ hqp hlocalInv)
      apply overlap_compatible_only_at_5_or_7_of_decide
      intro d hd hsmall
      exact hoverQ d hd hsmall
  exact (Equiv.subtypeEquivRight (marked_iff_subset p chosen)).trans
    ((Fintype.equivOfCardEq hcount).trans
      (Equiv.subtypeEquivRight (marked_iff_subset q chosen)).symm)

/-- The marked three-position cycle proves exact occurrence-count equality. -/
theorem exactOccurrenceCount_eq_23145786_25134786 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (WilfPatternSwap.occurrenceSet pattern23145786) marks =
      WilfCounts.exactCount (WilfPatternSwap.occurrenceSet pattern25134786) marks := by
  have hpq : pattern23145786 ∘ cycle = pattern25134786 := by funext i; fin_cases i <;> rfl
  have hqp : pattern25134786 ∘ cycle.symm = pattern23145786 := by funext i; fin_cases i <;> rfl
  apply exactOccurrenceCount_eq_of_markedSwap n marks pattern23145786 pattern25134786 cycle
  · intro i hi
    have hcycle : ∀ i : Fin 8, cycle i ≠ i ↔ i = 1 ∨ i = 3 ∨ i = 4 := by decide
    exact (hcycle i).mp hi
  · exact (by decide : cycle 1 ≠ 1)
  · intro d hd hsmall
    interval_cases d <;> decide
  · intro d hd hsmall
    interval_cases d <;> decide
  · exact hpq
  · exact hqp
  · exact overlap_order_23145786_25134786
  · exact overlap_order_25134786_23145786

private theorem overlap_order_23145786_24135786 {α : Type*} [Preorder α]
    (f : Fin 13 → α) (hf : WindowOrder pattern23145786 f 0)
    (hn : WindowOrder pattern23145786 f 5) (i j : Fin 8) :
    f (overlapImage swap13 i) < f (overlapImage swap13 j) ↔
      pattern24135786 i < pattern24135786 j := by
  have hpq : pattern23145786 ∘ swap13 = pattern24135786 := by
    funext k
    fin_cases k <;> rfl
  rw [← hpq]
  exact overlap_cycle_order pattern23145786 swap13 (by decide) (by decide)
    (by decide) (by decide) (by decide) f hf hn i j

private theorem overlap_order_24135786_23145786 {α : Type*} [Preorder α]
    (f : Fin 13 → α) (hf : WindowOrder pattern24135786 f 0)
    (hn : WindowOrder pattern24135786 f 5) (i j : Fin 8) :
    f (overlapImage swap13.symm i) < f (overlapImage swap13.symm j) ↔
      pattern23145786 i < pattern23145786 j := by
  have hqp : pattern24135786 ∘ swap13.symm = pattern23145786 := by
    funext k
    fin_cases k <;> rfl
  rw [← hqp]
  exact overlap_cycle_order pattern24135786 swap13.symm (by decide) (by decide)
    (by decide) (by decide) (by decide) f hf hn i j

/-- Swapping zero-based positions one and three preserves the exact occurrence count. -/
theorem exactOccurrenceCount_eq_23145786_24135786 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (WilfPatternSwap.occurrenceSet pattern23145786) marks =
      WilfCounts.exactCount (WilfPatternSwap.occurrenceSet pattern24135786) marks := by
  have hpq : pattern23145786 ∘ swap13 = pattern24135786 := by
    funext i
    fin_cases i <;> rfl
  have hqp : pattern24135786 ∘ swap13.symm = pattern23145786 := by
    funext i
    fin_cases i <;> rfl
  apply exactOccurrenceCount_eq_of_markedSwap n marks pattern23145786 pattern24135786 swap13
  · intro i hi
    have hm : ∀ i : Fin 8, swap13 i ≠ i → i = 1 ∨ i = 3 ∨ i = 4 := by decide
    exact hm i hi
  · by decide
  · intro d hd hsmall
    interval_cases d <;> decide
  · intro d hd hsmall
    interval_cases d <;> decide
  · exact hpq
  · exact hqp
  · exact overlap_order_23145786_24135786
  · exact overlap_order_24135786_23145786

/-- The first, middle, and last patterns in archive block 41 have equal exact counts. -/
theorem exactOccurrenceCount_eq_24135786_25134786 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (WilfPatternSwap.occurrenceSet pattern24135786) marks =
      WilfCounts.exactCount (WilfPatternSwap.occurrenceSet pattern25134786) marks := by
  exact (exactOccurrenceCount_eq_23145786_24135786 n marks).symm.trans
    (exactOccurrenceCount_eq_23145786_25134786 n marks)

#print axioms crossing_offsets
#print axioms exactOccurrenceCount_eq_of_markedSwap
#print axioms exactOccurrenceCount_eq_23145786_24135786
#print axioms exactOccurrenceCount_eq_24135786_25134786
#print axioms exactOccurrenceCount_eq_23145786_25134786

end Implications.WilfThreeCycleGlobal
