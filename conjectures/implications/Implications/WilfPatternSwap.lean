import Implications.WilfGlobalSwap
import Implications.WilfMarked
import Implications.WilfEquivalence

/-! The effect of simultaneous position swaps on occurrences in marked windows. -/

namespace Implications.WilfPatternSwap

open WilfMarked WilfGlobalSwap

private def atOffset {n : ℕ} (s : ℕ) (hs : s + 7 < n) (i : Fin 8) : Fin n :=
  ⟨s + i.val, by have := i.isLt; omega⟩

private def leftIndex (left : LeftOffset) : Fin 8 :=
  ⟨left.val, by have := left.property; omega⟩

/-- Exchange the requested left offset with offset five in one window. -/
def windowSwapAt (left : LeftOffset) : Fin 8 → Fin 8 :=
  Equiv.swap (leftIndex left) 5

private theorem windowSwapAt_fourth : windowSwapAt fourthOffset = windowSwap := by
  funext i
  fin_cases i <;> rfl

private theorem windowSwapAt_zero (left : LeftOffset) : windowSwapAt left 0 = 0 := by
  unfold windowSwapAt
  apply Equiv.swap_apply_of_ne_of_ne _ (by decide)
  intro he
  have h := congrArg Fin.val he
  change 0 = left.val at h
  have := left.property
  omega

private theorem windowSwapAt_involutive (left : LeftOffset) :
    Function.Involutive (windowSwapAt left) := by
  intro i
  exact congrArg (fun e : Equiv.Perm (Fin 8) => e i) (Equiv.swap_swap (leftIndex left) 5)

private theorem swaps_nonfirst (left : LeftOffset) {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    {s : ℕ} (hs : s ∈ marks) (i : Fin 8) (hi : i ≠ 0) :
    swapIndexAt left marks hb hd (atOffset s (hb s hs) i) =
      atOffset s (hb s hs) (windowSwapAt left i) := by
  apply Fin.ext
  have hl := left.property
  have hi' : 0 < i.val := by
    by_contra! h
    exact hi (Fin.ext (by omega))
  have hi8 := i.isLt
  by_cases hil : i = leftIndex left
  · subst i
    rw [swapIndexAt_val_left _ _ _ _ _ ⟨s, hs, rfl⟩]
    simp [atOffset, windowSwapAt, leftIndex]
    omega
  by_cases h5 : i = 5
  · subst i
    rw [swapIndexAt_val_right _ _ _ _ _ ⟨s, hs, rfl⟩]
    simp [atOffset, windowSwapAt, leftIndex]
    omega
  have hleft : ¬ IsLeftAt left marks (atOffset s (hb s hs) i) := by
    rintro ⟨t, ht, he⟩
    change s + i.val = t + left.val at he
    rcases lt_trichotomy t s with h | rfl | h
    · have := hd t ht s hs h
      omega
    · exact hil (Fin.ext (by change i.val = left.val; omega))
    · have := hd s hs t ht h
      omega
  have hright : ¬ IsRight marks (atOffset s (hb s hs) i) := by
    rintro ⟨t, ht, he⟩
    change s + i.val = t + 5 at he
    rcases lt_trichotomy t s with h | rfl | h
    · have := hd t ht s hs h
      omega
    · exact h5 (Fin.ext (by omega))
    · have := hd s hs t ht h
      omega
  rw [swapIndexAt_val_other _ _ _ _ _ hleft hright]
  rw [windowSwapAt, Equiv.swap_apply_of_ne_of_ne hil h5]

private theorem windowSwap_nonfirst (left : LeftOffset) (i : Fin 8) (hi : i ≠ 0) :
    windowSwapAt left i ≠ 0 := by
  intro he
  exact hi ((windowSwapAt_involutive left).injective (he.trans (windowSwapAt_zero left).symm))

private noncomputable def swapPermAt (left : LeftOffset) {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) : Equiv.Perm (Fin n) where
  toFun := swapIndexAt left marks hb hd
  invFun := swapIndexAt left marks hb hd
  left_inv := swapIndexAt_involutive left marks hb hd
  right_inv := swapIndexAt_involutive left marks hb hd

/-- The ordered comparisons needed when a shift-five overlap changes the first entry. -/
def FirstOrderCertificateAt (left : LeftOffset) (p : Fin 8 → Fin 8) : Prop :=
  ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t + 12 < n),
    ContainsAt π t p → ContainsAt π (t + 5) p →
    ∀ j : Fin 8, j ≠ 0 →
    (π ⟨t + left.val, by have := left.property; omega⟩ < π ⟨t + 5 + j.val, by have := j.isLt; omega⟩ ↔
      p 0 < p j)

private theorem first_comparison (left : LeftOffset) {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8) (hcert : FirstOrderCertificateAt left p)
    (hπ : ∀ s ∈ marks, ContainsAt π s p) {s : ℕ} (hs : s ∈ marks)
    (j : Fin 8) (hj : j ≠ 0) :
    π (swapIndexAt left marks hb hd (atOffset s (hb s hs) 0)) <
      π (atOffset s (hb s hs) j) ↔ p 0 < p j := by
  have hleft : ¬ IsLeftAt left marks (atOffset s (hb s hs) 0) := by
    rintro ⟨t, ht, he⟩
    change s + 0 = t + left.val at he
    have := left.property
    have hts : t < s := by omega
    have := hd t ht s hs hts
    omega
  by_cases hright : IsRight marks (atOffset s (hb s hs) 0)
  · obtain ⟨t, ht, he⟩ := hright
    change s + 0 = t + 5 at he
    have hst : s = t + 5 := by omega
    have hw₀ : swapIndexAt left marks hb hd (atOffset s (hb s hs) 0) =
        atOffset t (hb t ht) (leftIndex left) := by
      apply Fin.ext
      rw [swapIndexAt_val_right _ _ _ _ _ ⟨t, ht, he⟩]
      change (s + 0) - (5 - left.val) = t + left.val
      have := left.property
      omega
    rw [hw₀]
    have hroom : t + 12 < n := by have := hb s hs; omega
    have hsecond : ContainsAt π (t + 5) p := hst ▸ hπ s hs
    simpa [atOffset, leftIndex, hst] using hcert π t hroom (hπ t ht) hsecond j hj
  · have hw₀ : swapIndexAt left marks hb hd (atOffset s (hb s hs) 0) =
        atOffset s (hb s hs) 0 :=
      Fin.ext (swapIndexAt_val_other _ _ _ _ _ hleft hright)
    rw [hw₀]
    obtain ⟨_, hpattern⟩ := hπ s hs
    exact hpattern 0 j

private theorem containsAt_swapped_of_certificate (left : LeftOffset) {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8) (hzero : ∀ j : Fin 8, j ≠ 0 → p 0 ≠ p j)
    (hcert : FirstOrderCertificateAt left p) (hπ : ∀ s ∈ marks, ContainsAt π s p)
    {s : ℕ} (hs : s ∈ marks) :
    ContainsAt ((swapPermAt left marks hb hd).trans π) s (p ∘ windowSwapAt left) := by
  obtain ⟨_, hpattern⟩ := hπ s hs
  let m := atOffset s (hb s hs)
  let f := swapIndexAt left marks hb hd
  have hnonfirst (i : Fin 8) (hi : i ≠ 0) : f (m i) = m (windowSwapAt left i) :=
    swaps_nonfirst left marks hb hd hs i hi
  have hswap₀ : windowSwapAt left 0 = 0 := windowSwapAt_zero left
  have hcompare (i : Fin 8) (hi : i ≠ 0) :
      π (f (m 0)) < π (f (m i)) ↔ p 0 < p (windowSwapAt left i) := by
    rw [hnonfirst i hi]
    have hother : windowSwap i ≠ 0 := by
      intro he
      exact hi ((windowSwapAt_involutive left).injective (he.trans hswap₀.symm))
    exact first_comparison left marks hb hd π p hcert hπ hs (windowSwapAt left i) hother
  refine ⟨hb s hs, ?_⟩
  intro i j
  change (π (f (m i)) < π (f (m j))) ↔ p (windowSwapAt left i) < p (windowSwapAt left j)
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
        have hm := (swapIndexAt_involutive left marks hb hd).injective (π.injective he)
        have hv := congrArg Fin.val hm
        change s + 0 = s + i.val at hv
        exact hi (Fin.ext (by omega))
      have hpne : p 0 ≠ p (windowSwapAt left i) := hzero _ (windowSwap_nonfirst left i hi)
      constructor
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt fun hy =>
          (not_lt_of_gt h) ((hcompare i hi).mpr hy)) hpne.symm
      · intro h
        exact lt_of_le_of_ne (le_of_not_gt fun hy =>
          (not_lt_of_gt h) ((hcompare i hi).mp hy)) hπne.symm
    · rw [hnonfirst i hi, hnonfirst j hj]
      exact hpattern _ _

abbrev FirstOrderCertificate := FirstOrderCertificateAt fourthOffset

private theorem certificate_of_minimum (p : Fin 8 → Fin 8)
    (hfirst : ∀ j : Fin 8, j ≠ 0 → p 0 < p j)
    (hsecond : ∀ j : Fin 8, j ≠ 0 → j ≠ 2 → p 2 < p j)
    (hcross : p 3 < p 7) : FirstOrderCertificate p := by
  intro n π t ht ht0 ht5 j hj
  obtain ⟨_, hbefore⟩ := ht0
  obtain ⟨_, hafter⟩ := ht5
  apply iff_of_true _ (hfirst j hj)
  have hlt : π ⟨t + 3, by omega⟩ < π ⟨t + 5 + 2, by omega⟩ :=
    (hbefore 3 7).mpr hcross
  by_cases hj2 : j = 2
  · subst j
    exact hlt
  · exact hlt.trans ((hafter 2 j).mpr (hsecond j hj hj2))

/-- Swapping marked windows changes their order type from either pattern to the other. -/
theorem containsAt_swapped {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8)
    (hfirst : ∀ i : Fin 8, i ≠ 0 → p 0 < p i)
    (hsecond : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i)
    (hcross : p 3 < p 7)
    (hπ : ∀ s ∈ marks, ContainsAt π s p) {s : ℕ} (hs : s ∈ marks) :
    ContainsAt ((swapPermAt fourthOffset marks hb hd).trans π) s (p ∘ windowSwap) := by
  simpa only [windowSwapAt_fourth] using
    containsAt_swapped_of_certificate fourthOffset marks hb hd π p
      (fun j hj => ne_of_lt (hfirst j hj)) (certificate_of_minimum p hfirst hsecond hcross) hπ hs

private def Marked {n : ℕ} (p : Fin 8 → Fin 8) (marks : Finset ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ s ∈ marks, ContainsAt π s p

private noncomputable def certifiedSwap (left : LeftOffset) {n : ℕ} (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8) (hoverlap : (∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)) (hzero : ∀ j : Fin 8, j ≠ 0 → p 0 ≠ p j)
    (hcert : FirstOrderCertificateAt left p) (hswap : p ∘ windowSwapAt left = q)
    (π : {f : Equiv.Perm (Fin n) // Marked p marks f}) :
    {f : Equiv.Perm (Fin n) // Marked q marks f} := by
  let hb := marked_starts_bounded π.val p marks π.property
  let hd := marked_starts_separated_of_overlap π.val p hoverlap marks π.property
  refine ⟨(swapPermAt left marks hb hd).trans π.val, ?_⟩
  intro s hs
  rw [← hswap]
  exact containsAt_swapped_of_certificate left marks hb hd π.val p hzero hcert π.property hs

private theorem certifiedSwap_twice (left : LeftOffset) {n : ℕ} (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8) (hoverlap : (∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)) (hoverlapQ : (∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7))
    (hzero : ∀ j : Fin 8, j ≠ 0 → p 0 ≠ p j) (hzeroQ : ∀ j : Fin 8, j ≠ 0 → q 0 ≠ q j)
    (hcert : FirstOrderCertificateAt left p) (hcertQ : FirstOrderCertificateAt left q)
    (hpq : p ∘ windowSwapAt left = q) (hqp : q ∘ windowSwapAt left = p)
    (π : {f : Equiv.Perm (Fin n) // Marked p marks f}) :
    certifiedSwap left marks q p hoverlapQ hzeroQ hcertQ hqp
      (certifiedSwap left marks p q hoverlap hzero hcert hpq π) = π := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact congrArg π.val
    (swapIndexAt_involutive left marks (marked_starts_bounded π.val p marks π.property)
      (marked_starts_separated_of_overlap π.val p hoverlap marks π.property) i)

private noncomputable def markedEquiv_of_certificate (left : LeftOffset) (n : ℕ) (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8) (hoverlap : (∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)) (hoverlapQ : (∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7))
    (hzero : ∀ j : Fin 8, j ≠ 0 → p 0 ≠ p j) (hzeroQ : ∀ j : Fin 8, j ≠ 0 → q 0 ≠ q j)
    (hcert : FirstOrderCertificateAt left p) (hcertQ : FirstOrderCertificateAt left q)
    (hpq : p ∘ windowSwapAt left = q) (hqp : q ∘ windowSwapAt left = p) :
    {f : Equiv.Perm (Fin n) // Marked p marks f} ≃
      {f : Equiv.Perm (Fin n) // Marked q marks f} where
  toFun := certifiedSwap left marks p q hoverlap hzero hcert hpq
  invFun := certifiedSwap left marks q p hoverlapQ hzeroQ hcertQ hqp
  left_inv := certifiedSwap_twice left marks p q hoverlap hoverlapQ hzero hzeroQ hcert hcertQ hpq hqp
  right_inv := certifiedSwap_twice left marks q p hoverlapQ hoverlap hzeroQ hzero hcertQ hcert hqp hpq

/-- A reusable marked-occurrence bijection for a pair exchanged by positions
four and six, provided their overlap and rank checks meet the finite criteria. -/
noncomputable def markedEquivOfSwap (n : ℕ) (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8)
    (hoverlap : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hoverlapQ : ∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7)
    (hfirst : ∀ i : Fin 8, i ≠ 0 → p 0 < p i)
    (hsecond : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i)
    (hcross : p 3 < p 7)
    (hfirstQ : ∀ i : Fin 8, i ≠ 0 → q 0 < q i)
    (hsecondQ : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → q 2 < q i)
    (hcrossQ : q 3 < q 7)
    (hpq : p ∘ windowSwap = q) (hqp : q ∘ windowSwap = p) :
    {f : Equiv.Perm (Fin n) // Marked p marks f} ≃
      {f : Equiv.Perm (Fin n) // Marked q marks f} :=
  markedEquiv_of_certificate fourthOffset n marks p q hoverlap hoverlapQ
    (fun j hj => ne_of_lt (hfirst j hj)) (fun j hj => ne_of_lt (hfirstQ j hj))
    (certificate_of_minimum p hfirst hsecond hcross)
    (certificate_of_minimum q hfirstQ hsecondQ hcrossQ)
    (by simpa only [windowSwapAt_fourth] using hpq) (by simpa only [windowSwapAt_fourth] using hqp)

/-- A bijection between the permutations realizing all prescribed starts for
the two patterns. -/
noncomputable def markedEquiv (n : ℕ) (marks : Finset ℕ) :
    {f : Equiv.Perm (Fin n) // Marked sigma marks f} ≃
      {f : Equiv.Perm (Fin n) // Marked tau marks f} :=
  markedEquivOfSwap n marks sigma tau
    sigma_overlap_compatible_only_at_5_or_7 tau_overlap_compatible_only_at_5_or_7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    windowSwap_sigma windowSwap_tau

/-- All starting positions where the permutation has the designated pattern. -/
noncomputable def occurrenceSet {n : ℕ} (p : Fin 8 → Fin 8) (π : Equiv.Perm (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ContainsAt π i.val p

private theorem subset_occurrenceSet_iff {n : ℕ} (p : Fin 8 → Fin 8)
    (marks : Finset (Fin n)) (π : Equiv.Perm (Fin n)) :
    marks ⊆ occurrenceSet p π ↔ Marked p (marks.image Fin.val) π := by
  classical
  constructor
  · intro h s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    exact (Finset.mem_filter.mp (h hi)).2
  · intro h i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      h i.val (Finset.mem_image_of_mem Fin.val hi)⟩

/-- A certified first-entry replacement extends to all marked windows and
yields equality of exact occurrence-set counts. -/
theorem exactOccurrenceCount_eq_of_certificateAt (left : LeftOffset) (n : ℕ) (marks : Finset (Fin n))
    (p q : Fin 8 → Fin 8)
    (hoverlap : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hoverlapQ : ∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7)
    (hzero : ∀ j : Fin 8, j ≠ 0 → p 0 ≠ p j)
    (hzeroQ : ∀ j : Fin 8, j ≠ 0 → q 0 ≠ q j)
    (hcert : FirstOrderCertificateAt left p) (hcertQ : FirstOrderCertificateAt left q)
    (hpq : p ∘ windowSwapAt left = q) (hqp : q ∘ windowSwapAt left = p) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet q) marks := by
  apply WilfEquivalence.exactCount_eq_of_markedEquiv
  intro chosen
  exact (Equiv.subtypeEquivRight (subset_occurrenceSet_iff p chosen)).trans
    ((markedEquiv_of_certificate left n (chosen.image Fin.val) p q hoverlap hoverlapQ hzero hzeroQ
      hcert hcertQ hpq hqp).trans
      (Equiv.subtypeEquivRight (subset_occurrenceSet_iff q chosen)).symm)

/-- A certified first-entry replacement extends to all marked windows and
yields equality of exact occurrence-set counts. -/
theorem exactOccurrenceCount_eq_of_certificate (n : ℕ) (marks : Finset (Fin n))
    (p q : Fin 8 → Fin 8)
    (hoverlap : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hoverlapQ : ∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7)
    (hzero : ∀ j : Fin 8, j ≠ 0 → p 0 ≠ p j)
    (hzeroQ : ∀ j : Fin 8, j ≠ 0 → q 0 ≠ q j)
    (hcert : FirstOrderCertificate p) (hcertQ : FirstOrderCertificate q)
    (hpq : p ∘ windowSwap = q) (hqp : q ∘ windowSwap = p) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet q) marks :=
  exactOccurrenceCount_eq_of_certificateAt fourthOffset n marks p q hoverlap hoverlapQ
    hzero hzeroQ hcert hcertQ
    (by simpa only [windowSwapAt_fourth] using hpq) (by simpa only [windowSwapAt_fourth] using hqp)

/-- The same marked-window argument yields equality of exact occurrence-set
counts for any pair satisfying its checked overlap and rank hypotheses. -/
theorem exactOccurrenceCount_eq_of_swap (n : ℕ) (marks : Finset (Fin n))
    (p q : Fin 8 → Fin 8)
    (hoverlap : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hoverlapQ : ∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7)
    (hfirst : ∀ i : Fin 8, i ≠ 0 → p 0 < p i)
    (hsecond : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i)
    (hcross : p 3 < p 7)
    (hfirstQ : ∀ i : Fin 8, i ≠ 0 → q 0 < q i)
    (hsecondQ : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → q 2 < q i)
    (hcrossQ : q 3 < q 7)
    (hpq : p ∘ windowSwap = q) (hqp : q ∘ windowSwap = p) :
    WilfCounts.exactCount (occurrenceSet p) marks =
      WilfCounts.exactCount (occurrenceSet q) marks := by
  apply WilfEquivalence.exactCount_eq_of_markedEquiv
  intro chosen
  exact (Equiv.subtypeEquivRight (subset_occurrenceSet_iff p chosen)).trans
    ((markedEquivOfSwap n (chosen.image Fin.val) p q hoverlap hoverlapQ hfirst hsecond
      hcross hfirstQ hsecondQ hcrossQ hpq hqp).trans
      (Equiv.subtypeEquivRight (subset_occurrenceSet_iff q chosen)).symm)

/-- The two patterns are super-strongly c-Wilf equivalent: every prescribed
exact occurrence set is realized by the same number of permutations. -/
theorem exactOccurrenceCount_eq (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet sigma) marks =
      WilfCounts.exactCount (occurrenceSet tau) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks sigma tau
    sigma_overlap_compatible_only_at_5_or_7 tau_overlap_compatible_only_at_5_or_7
    (by intro i hi; fin_cases i <;> simp_all [sigma])
    (by intro i hi hi2; fin_cases i <;> simp_all [sigma]) (by decide)
    (by intro i hi; fin_cases i <;> simp_all [tau])
    (by intro i hi hi2; fin_cases i <;> simp_all [tau]) (by decide)
    windowSwap_sigma windowSwap_tau

theorem exactOccurrenceCount_eq_16238475_16248375 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair16238475) marks =
      WilfCounts.exactCount (occurrenceSet pair16248375) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair16238475 pair16248375
    (overlap_compatible_only_at_5_or_7_of_decide pair16238475
      (overlap_check_pair16238475))
    (overlap_compatible_only_at_5_or_7_of_decide pair16248375
      (overlap_check_pair16248375))
    (by intro i hi; fin_cases i <;> simp_all [pair16238475])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair16238475]) (by decide)
    (by intro i hi; fin_cases i <;> simp_all [pair16248375])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair16248375]) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_17236485_17246385 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair17236485) marks =
      WilfCounts.exactCount (occurrenceSet pair17246385) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair17236485 pair17246385
    (overlap_compatible_only_at_5_or_7_of_decide pair17236485 overlap_check_pair17236485)
    (overlap_compatible_only_at_5_or_7_of_decide pair17246385 overlap_check_pair17246385)
    (by intro i hi; fin_cases i <;> simp_all [pair17236485])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair17236485]) (by decide)
    (by intro i hi; fin_cases i <;> simp_all [pair17246385])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair17246385]) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_17238465_17248365 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair17238465) marks =
      WilfCounts.exactCount (occurrenceSet pair17248365) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair17238465 pair17248365
    (overlap_compatible_only_at_5_or_7_of_decide pair17238465 overlap_check_pair17238465)
    (overlap_compatible_only_at_5_or_7_of_decide pair17248365 overlap_check_pair17248365)
    (by intro i hi; fin_cases i <;> simp_all [pair17238465])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair17238465]) (by decide)
    (by intro i hi; fin_cases i <;> simp_all [pair17248365])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair17248365]) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_18237465_18247365 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair18237465) marks =
      WilfCounts.exactCount (occurrenceSet pair18247365) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair18237465 pair18247365
    (overlap_compatible_only_at_5_or_7_of_decide pair18237465 overlap_check_pair18237465)
    (overlap_compatible_only_at_5_or_7_of_decide pair18247365 overlap_check_pair18247365)
    (by intro i hi; fin_cases i <;> simp_all [pair18237465])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair18237465]) (by decide)
    (by intro i hi; fin_cases i <;> simp_all [pair18247365])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair18247365]) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_18236475_18246375 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair18236475) marks =
      WilfCounts.exactCount (occurrenceSet pair18246375) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair18236475 pair18246375
    (overlap_compatible_only_at_5_or_7_of_decide pair18236475 overlap_check_pair18236475)
    (overlap_compatible_only_at_5_or_7_of_decide pair18246375 overlap_check_pair18246375)
    (by intro i hi; fin_cases i <;> simp_all [pair18236475])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair18236475]) (by decide)
    (by intro i hi; fin_cases i <;> simp_all [pair18246375])
    (by intro i hi hi2; fin_cases i <;> simp_all [pair18246375]) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

#print axioms exactOccurrenceCount_eq
#print axioms exactOccurrenceCount_eq_16238475_16248375
#print axioms exactOccurrenceCount_eq_17236485_17246385
#print axioms exactOccurrenceCount_eq_17238465_17248365
#print axioms exactOccurrenceCount_eq_18237465_18247365
#print axioms exactOccurrenceCount_eq_18236475_18246375

end Implications.WilfPatternSwap
