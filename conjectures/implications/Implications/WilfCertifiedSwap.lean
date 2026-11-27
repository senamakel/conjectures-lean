import Implications.WilfPatternSwap
import Implications.WilfTwoWindowOrder

/-! Exact marked occurrence counts from two-window order certificates. -/

namespace Implications.WilfCertifiedSwap

open WilfMarked WilfGlobalSwap WilfPatternSwap WilfTwoWindowOrder

/-- The ordered comparisons needed when a shift-five overlap changes the first entry. -/
def FirstOrderCertificate (p : Fin 8 → Fin 8) : Prop :=
  ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t + 12 < n),
    ContainsAt π t p → ContainsAt π (t + 5) p →
    ∀ j : Fin 8, j ≠ 0 →
    (π ⟨t + 3, by omega⟩ < π ⟨t + 5 + j.val, by have := j.isLt; omega⟩ ↔
      p 0 < p j)

private theorem first_comparison {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8) (hcert : FirstOrderCertificate p)
    (hπ : ∀ s ∈ marks, ContainsAt π s p) {s : ℕ} (hs : s ∈ marks)
    (j : Fin 8) (hj : j ≠ 0) :
    π (swapIndex marks hb hd (atOffset s (hb s hs) 0)) <
      π (atOffset s (hb s hs) j) ↔ p 0 < p j := by
  have hleft : ¬ IsLeft marks (atOffset s (hb s hs) 0) := by
    rintro ⟨t, ht, he⟩
    change s + 0 = t + 3 at he
    have hts : t < s := by omega
    have := hd t ht s hs hts
    omega
  by_cases hright : IsRight marks (atOffset s (hb s hs) 0)
  · obtain ⟨t, ht, he⟩ := hright
    change s + 0 = t + 5 at he
    have hst : s = t + 5 := by omega
    have hw₀ : swapIndex marks hb hd (atOffset s (hb s hs) 0) =
        atOffset t (hb t ht) 3 := by
      apply Fin.ext
      rw [swapIndex_val_right _ _ _ _ ⟨t, ht, he⟩]
      change (s + 0) - 2 = t + 3
      omega
    rw [hw₀]
    have hroom : t + 12 < n := by have := hb s hs; omega
    have hsecond : ContainsAt π (t + 5) p := hst ▸ hπ s hs
    simpa [atOffset, hst] using hcert π t hroom (hπ t ht) hsecond j hj
  · have hw₀ : swapIndex marks hb hd (atOffset s (hb s hs) 0) =
        atOffset s (hb s hs) 0 :=
      Fin.ext (swapIndex_val_other _ _ _ _ hleft hright)
    rw [hw₀]
    obtain ⟨_, hpattern⟩ := hπ s hs
    exact hpattern 0 j

private theorem containsAt_swapped_of_certificate {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8) (hinj : Function.Injective p)
    (hcert : FirstOrderCertificate p) (hπ : ∀ s ∈ marks, ContainsAt π s p)
    {s : ℕ} (hs : s ∈ marks) :
    ContainsAt ((swapPerm marks hb hd).trans π) s (p ∘ windowSwap) := by
  obtain ⟨_, hpattern⟩ := hπ s hs
  let m := atOffset s (hb s hs)
  let f := swapIndex marks hb hd
  have hnonfirst (i : Fin 8) (hi : i ≠ 0) : f (m i) = m (windowSwap i) :=
    swaps_nonfirst marks hb hd hs i hi
  have hswap₀ : windowSwap 0 = 0 := by decide
  have hcompare (i : Fin 8) (hi : i ≠ 0) :
      π (f (m 0)) < π (f (m i)) ↔ p 0 < p (windowSwap i) := by
    rw [hnonfirst i hi]
    have hother : windowSwap i ≠ 0 := by
      intro he
      exact hi (windowSwap_involutive.injective (he.trans hswap₀.symm))
    exact first_comparison marks hb hd π p hcert hπ hs (windowSwap i) hother
  refine ⟨hb s hs, ?_⟩
  intro i j
  change (π (f (m i)) < π (f (m j))) ↔ p (windowSwap i) < p (windowSwap j)
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp
    · rw [hswap₀]
      exact hcompare j hj
  · by_cases hj : j = 0
    · subst j
      rw [hswap₀]
      have hπne : π (f (m 0)) ≠ π (f (m i)) := by
        intro he
        have hm := (swapIndex_involutive marks hb hd).injective (π.injective he)
        have hv := congrArg Fin.val hm
        change s + 0 = s + i.val at hv
        exact hi (Fin.ext (by omega))
      have hpne : p 0 ≠ p (windowSwap i) := by
        intro he
        exact hi ((windowSwap_involutive.injective (hswap₀.trans (hinj he))).symm)
      constructor
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt fun hy =>
          (not_lt_of_gt h) ((hcompare i hi).mpr hy)) hpne.symm
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt fun hy =>
          (not_lt_of_gt h) ((hcompare i hi).mp hy)) hπne.symm
    · rw [hnonfirst i hi, hnonfirst j hj]
      exact hpattern _ _

private def OverlapSpacing (p : Fin 8 → Fin 8) : Prop :=
  ∀ d, 1 ≤ d → d < 5 → overlapCompatible p d = false

private theorem starts_separated {n : ℕ} (π : Equiv.Perm (Fin n))
    (p : Fin 8 → Fin 8) (hspace : OverlapSpacing p) (marks : Finset ℕ)
    (hπ : ∀ s ∈ marks, ContainsAt π s p) :
    ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t := by
  intro s hs t ht hst
  by_contra! hsmall
  have h := same_pattern_overlap_compatible π p s t (hπ s hs) (hπ t ht) hst (by omega)
  rw [hspace (t - s) (by omega) (by omega)] at h
  contradiction

private def Marked {n : ℕ} (p : Fin 8 → Fin 8) (marks : Finset ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ s ∈ marks, ContainsAt π s p

private noncomputable def certifiedSwap {n : ℕ} (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8) (hspace : OverlapSpacing p) (hinj : Function.Injective p)
    (hcert : FirstOrderCertificate p) (hswap : p ∘ windowSwap = q)
    (π : {f : Equiv.Perm (Fin n) // Marked p marks f}) :
    {f : Equiv.Perm (Fin n) // Marked q marks f} := by
  let hb := marked_starts_bounded π.val p marks π.property
  let hd := starts_separated π.val p hspace marks π.property
  refine ⟨(swapPerm marks hb hd).trans π.val, ?_⟩
  intro s hs
  rw [← hswap]
  exact containsAt_swapped_of_certificate marks hb hd π.val p hinj hcert π.property hs

private theorem certifiedSwap_twice {n : ℕ} (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8) (hspace : OverlapSpacing p) (hspaceQ : OverlapSpacing q)
    (hinj : Function.Injective p) (hinjQ : Function.Injective q)
    (hcert : FirstOrderCertificate p) (hcertQ : FirstOrderCertificate q)
    (hpq : p ∘ windowSwap = q) (hqp : q ∘ windowSwap = p)
    (π : {f : Equiv.Perm (Fin n) // Marked p marks f}) :
    certifiedSwap marks q p hspaceQ hinjQ hcertQ hqp
      (certifiedSwap marks p q hspace hinj hcert hpq π) = π := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact congrArg π.val
    (swapIndex_involutive marks (marked_starts_bounded π.val p marks π.property)
      (starts_separated π.val p hspace marks π.property) i)

private noncomputable def markedEquiv_of_certificate (n : ℕ) (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8) (hspace : OverlapSpacing p) (hspaceQ : OverlapSpacing q)
    (hinj : Function.Injective p) (hinjQ : Function.Injective q)
    (hcert : FirstOrderCertificate p) (hcertQ : FirstOrderCertificate q)
    (hpq : p ∘ windowSwap = q) (hqp : q ∘ windowSwap = p) :
    {f : Equiv.Perm (Fin n) // Marked p marks f} ≃
      {f : Equiv.Perm (Fin n) // Marked q marks f} where
  toFun := certifiedSwap marks p q hspace hinj hcert hpq
  invFun := certifiedSwap marks q p hspaceQ hinjQ hcertQ hqp
  left_inv := certifiedSwap_twice marks p q hspace hspaceQ hinj hinjQ hcert hcertQ hpq hqp
  right_inv := certifiedSwap_twice marks q p hspaceQ hspace hinjQ hinj hcertQ hcert hqp hpq

private theorem spacing_of_finite (p : Fin 8 → Fin 8)
    (h : ∀ d : Fin 5, 0 < d → overlapCompatible p d.val = false) :
    OverlapSpacing p := fun d hd hd' => h ⟨d, hd'⟩ hd

/-- Super-strong consecutive Wilf equivalence: every exact occurrence set
has the same multiplicity for 23157684 and 23167584. -/
theorem exactOccurrenceCount_eq_23157684_23167584 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pattern23157684) marks =
      WilfCounts.exactCount (occurrenceSet pattern23167584) marks := by
  apply WilfEquivalence.exactCount_eq_of_markedEquiv
  intro chosen
  exact (Equiv.subtypeEquivRight (subset_occurrenceSet_iff pattern23157684 chosen)).trans
    ((markedEquiv_of_certificate n (chosen.image Fin.val) pattern23157684 pattern23167584
      (spacing_of_finite _ (by decide)) (spacing_of_finite _ (by decide))
      (by decide) (by decide)
      (fun π t ht => replacement_order_of_occurrences π _ (Or.inl rfl) t ht)
      (fun π t ht => replacement_order_of_occurrences π _ (Or.inr rfl) t ht)
      (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl)).trans
    (Equiv.subtypeEquivRight (subset_occurrenceSet_iff pattern23167584 chosen)).symm)

#print axioms exactOccurrenceCount_eq_23157684_23167584

end Implications.WilfCertifiedSwap
