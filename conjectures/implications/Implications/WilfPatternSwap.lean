import Implications.WilfGlobalSwap
import Implications.WilfMarked
import Implications.WilfEquivalence

/-! The effect of simultaneous position swaps on occurrences in marked windows. -/

namespace Implications.WilfPatternSwap

open WilfMarked WilfGlobalSwap

private def atOffset {n : ℕ} (s : ℕ) (hs : s + 7 < n) (i : Fin 8) : Fin n :=
  ⟨s + i.val, by have := i.isLt; omega⟩

private theorem swaps_nonfirst {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    {s : ℕ} (hs : s ∈ marks) (i : Fin 8) (hi : i ≠ 0) :
    swapIndex marks hb hd (atOffset s (hb s hs) i) =
      atOffset s (hb s hs) (windowSwap i) := by
  apply Fin.ext
  have hi' : 0 < i.val := by
    by_contra! h
    exact hi (Fin.ext (by omega))
  have hi8 := i.isLt
  by_cases h3 : i = 3
  · subst i
    rw [swapIndex_val_left _ _ _ _ ⟨s, hs, rfl⟩]
    rfl
  by_cases h5 : i = 5
  · subst i
    rw [swapIndex_val_right _ _ _ _ ⟨s, hs, rfl⟩]
    simp [atOffset, windowSwap]
  have hleft : ¬ IsLeft marks (atOffset s (hb s hs) i) := by
    rintro ⟨t, ht, he⟩
    change s + i.val = t + 3 at he
    rcases lt_trichotomy t s with h | rfl | h
    · have := hd t ht s hs h
      omega
    · exact h3 (Fin.ext (by omega))
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
  rw [swapIndex_val_other _ _ _ _ hleft hright]
  simp [windowSwap, h3, h5]

private theorem swaps_first_lt_second {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8) (hcross : p 3 < p 7)
    (hπ : ∀ s ∈ marks, ContainsAt π s p) {s : ℕ} (hs : s ∈ marks) :
    π (swapIndex marks hb hd (atOffset s (hb s hs) 0)) <
      π (atOffset s (hb s hs) 2) := by
  have hleft : ¬ IsLeft marks (atOffset s (hb s hs) 0) := by
    rintro ⟨t, ht, he⟩
    change s + 0 = t + 3 at he
    have hts : t < s := by omega
    have := hd t ht s hs hts
    omega
  by_cases hright : IsRight marks (atOffset s (hb s hs) 0)
  · obtain ⟨t, ht, he⟩ := hright
    change s + 0 = t + 5 at he
    have hw₀ : swapIndex marks hb hd (atOffset s (hb s hs) 0) =
        atOffset t (hb t ht) 3 := by
      apply Fin.ext
      rw [swapIndex_val_right _ _ _ _ ⟨t, ht, he⟩]
      change (s + 0) - 2 = t + 3
      omega
    have hw₂ : atOffset s (hb s hs) 2 = atOffset t (hb t ht) 7 := by
      apply Fin.ext
      change s + 2 = t + 7
      omega
    rw [hw₀, hw₂]
    obtain ⟨_, hpattern⟩ := hπ t ht
    exact (hpattern 3 7).mpr hcross
  · have hw₀ : swapIndex marks hb hd (atOffset s (hb s hs) 0) =
        atOffset s (hb s hs) 0 := Fin.ext (swapIndex_val_other _ _ _ _ hleft hright)
    rw [hw₀]
    obtain ⟨_, hpattern⟩ := hπ s hs
    exact (hpattern 0 2).mpr (by rcases hp with rfl | rfl <;> decide)

private theorem rank_first_lt (p : Fin 8 → Fin 8)
    (hfirst : ∀ i : Fin 8, i ≠ 0 → p 0 < p i) :
    ∀ i : Fin 8, i ≠ 0 → p 0 < p i := hfirst

private theorem rank_second_lt (p : Fin 8 → Fin 8)
    (hsecond : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i) :
    ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i := hsecond

private theorem windowSwap_nonfirst (i : Fin 8) (hi : i ≠ 0) : windowSwap i ≠ 0 := by
  intro he
  apply hi
  rw [← windowSwap_involutive i, he]
  rfl

private noncomputable def swapPerm {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t) : Equiv.Perm (Fin n) where
  toFun := swapIndex marks hb hd
  invFun := swapIndex marks hb hd
  left_inv := swapIndex_involutive marks hb hd
  right_inv := swapIndex_involutive marks hb hd

/-- Swapping marked windows changes their order type from either pattern to the other. -/
theorem containsAt_swapped {n : ℕ} (marks : Finset ℕ)
    (hb : ∀ s ∈ marks, s + 7 < n)
    (hd : ∀ s ∈ marks, ∀ t ∈ marks, s < t → s + 5 ≤ t)
    (π : Equiv.Perm (Fin n)) (p : Fin 8 → Fin 8)
    (hfirst : ∀ i : Fin 8, i ≠ 0 → p 0 < p i)
    (hsecond : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i)
    (hcross : p 3 < p 7)
    (hπ : ∀ s ∈ marks, ContainsAt π s p) {s : ℕ} (hs : s ∈ marks) :
    ContainsAt ((swapPerm marks hb hd).trans π) s (p ∘ windowSwap) := by
  obtain ⟨_, hpattern⟩ := hπ s hs
  let m := atOffset s (hb s hs)
  let f := swapIndex marks hb hd
  have hnonfirst : ∀ i : Fin 8, i ≠ 0 → f (m i) = m (windowSwap i) :=
    fun i hi => swaps_nonfirst marks hb hd hs i hi
  have hmin : ∀ i : Fin 8, i ≠ 0 → π (f (m 0)) < π (f (m i)) := by
    intro i hi
    rw [hnonfirst i hi]
    have hminwindow := swaps_first_lt_second marks hb hd π p hcross hπ hs
    by_cases hi₂ : windowSwap i = 2
    · rw [hi₂]
      exact hminwindow
    · exact hminwindow.trans ((hpattern 2 (windowSwap i)).mpr
        (rank_second_lt p hsecond _ (windowSwap_nonfirst i hi) hi₂))
  refine ⟨hb s hs, ?_⟩
  intro i j
  change (π (f (m i)) < π (f (m j))) ↔ p (windowSwap i) < p (windowSwap j)
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp
    · exact iff_of_true (hmin j hj) (rank_first_lt p hfirst _ (windowSwap_nonfirst j hj))
  · by_cases hj : j = 0
    · subst j
      exact iff_of_false (not_lt_of_gt (hmin i hi))
        (not_lt_of_gt (rank_first_lt p hfirst _ (windowSwap_nonfirst i hi)))
    · rw [hnonfirst i hi, hnonfirst j hj]
      exact hpattern _ _

private def Marked {n : ℕ} (p : Fin 8 → Fin 8) (marks : Finset ℕ)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ s ∈ marks, ContainsAt π s p

private noncomputable def swapMarked {n : ℕ} (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8)
    (hoverlap : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hfirst : ∀ i : Fin 8, i ≠ 0 → p 0 < p i)
    (hsecond : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i)
    (hcross : p 3 < p 7) (hq : p ∘ windowSwap = q)
    (π : {f : Equiv.Perm (Fin n) // Marked p marks f}) :
    {f : Equiv.Perm (Fin n) // Marked q marks f} := by
  let hb := marked_starts_bounded π.val p marks π.property
  let hd := marked_starts_separated_of_overlap π.val p hoverlap marks π.property
  refine ⟨(swapPerm marks hb hd).trans π.val, ?_⟩
  intro s hs
  rw [← hq]
  exact containsAt_swapped marks hb hd π.val p hfirst hsecond hcross π.property hs

private theorem swapMarked_swapMarked {n : ℕ} (marks : Finset ℕ)
    (p q : Fin 8 → Fin 8)
    (hoverlap : ∀ d, 1 ≤ d → d < 8 → overlapCompatible p d = true → d = 5 ∨ d = 7)
    (hoverlapQ : ∀ d, 1 ≤ d → d < 8 → overlapCompatible q d = true → d = 5 ∨ d = 7)
    (hfirst : ∀ i : Fin 8, i ≠ 0 → p 0 < p i)
    (hsecond : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → p 2 < p i)
    (hcross : p 3 < p 7)
    (hfirstQ : ∀ i : Fin 8, i ≠ 0 → q 0 < q i)
    (hsecondQ : ∀ i : Fin 8, i ≠ 0 → i ≠ 2 → q 2 < q i)
    (hcrossQ : q 3 < q 7)
    (hpq : p ∘ windowSwap = q) (hqp : q ∘ windowSwap = p)
    (π : {f : Equiv.Perm (Fin n) // Marked p marks f}) :
    swapMarked marks q p hoverlapQ hfirstQ hsecondQ hcrossQ hqp
      (swapMarked marks p q hoverlap hfirst hsecond hcross hpq π) = π := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact congrArg π.val (swapIndex_involutive marks (marked_starts_bounded π.val p marks π.property)
    (marked_starts_separated_of_overlap π.val p hoverlap marks π.property) i)

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
      {f : Equiv.Perm (Fin n) // Marked q marks f} where
  toFun := swapMarked marks p q hoverlap hfirst hsecond hcross hpq
  invFun := swapMarked marks q p hoverlapQ hfirstQ hsecondQ hcrossQ hqp
  left_inv := swapMarked_swapMarked marks p q hoverlap hoverlapQ hfirst hsecond hcross
    hfirstQ hsecondQ hcrossQ hpq hqp
  right_inv := swapMarked_swapMarked marks q p hoverlapQ hoverlap hfirstQ hsecondQ hcrossQ
    hfirst hsecond hcross hqp hpq

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

/-- A bijection between the permutations realizing all prescribed starts for
the two patterns. -/
noncomputable def markedEquiv (n : ℕ) (marks : Finset ℕ) :
    {f : Equiv.Perm (Fin n) // Marked sigma marks f} ≃
      {f : Equiv.Perm (Fin n) // Marked tau marks f} where
  toFun := swapMarked marks sigma tau sigma_overlap_compatible_only_at_5_or_7
    (by intro i hi; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by intro i hi hi2; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by decide) windowSwap_sigma
  invFun := swapMarked marks tau sigma tau_overlap_compatible_only_at_5_or_7
    (by intro i hi; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by intro i hi hi2; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by decide) windowSwap_tau
  left_inv := swapMarked_swapMarked marks sigma tau sigma_overlap_compatible_only_at_5_or_7
    tau_overlap_compatible_only_at_5_or_7
    (by intro i hi; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by intro i hi hi2; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide) (by decide)
    (by intro i hi; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by intro i hi hi2; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide) (by decide)
    windowSwap_sigma windowSwap_tau
  right_inv := swapMarked_swapMarked marks tau sigma tau_overlap_compatible_only_at_5_or_7
    sigma_overlap_compatible_only_at_5_or_7
    (by intro i hi; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by intro i hi hi2; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide) (by decide)
    (by intro i hi; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide)
    (by intro i hi hi2; rcases i with ⟨i, hi8⟩; interval_cases i <;> decide) (by decide)
    windowSwap_tau windowSwap_sigma

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

/-- The two patterns are super-strongly c-Wilf equivalent: every prescribed
exact occurrence set is realized by the same number of permutations. -/
theorem exactOccurrenceCount_eq (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet sigma) marks =
      WilfCounts.exactCount (occurrenceSet tau) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks sigma tau
    sigma_overlap_compatible_only_at_5_or_7 tau_overlap_compatible_only_at_5_or_7
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    windowSwap_sigma windowSwap_tau

theorem exactOccurrenceCount_eq_16238475_16248375 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair16238475) marks =
      WilfCounts.exactCount (occurrenceSet pair16248375) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair16238475 pair16248375
    (overlap_compatible_only_at_5_or_7_of_decide pair16238475
      (overlap_check_pair16238475))
    (overlap_compatible_only_at_5_or_7_of_decide pair16248375
      (overlap_check_pair16248375))
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_17236485_17246385 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair17236485) marks =
      WilfCounts.exactCount (occurrenceSet pair17246385) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair17236485 pair17246385
    (overlap_compatible_only_at_5_or_7_of_decide pair17236485 overlap_check_pair17236485)
    (overlap_compatible_only_at_5_or_7_of_decide pair17246385 overlap_check_pair17246385)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_17238465_17248365 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair17238465) marks =
      WilfCounts.exactCount (occurrenceSet pair17248365) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair17238465 pair17248365
    (overlap_compatible_only_at_5_or_7_of_decide pair17238465 overlap_check_pair17238465)
    (overlap_compatible_only_at_5_or_7_of_decide pair17248365 overlap_check_pair17248365)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_18237465_18247365 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair18237465) marks =
      WilfCounts.exactCount (occurrenceSet pair18247365) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair18237465 pair18247365
    (overlap_compatible_only_at_5_or_7_of_decide pair18237465 overlap_check_pair18237465)
    (overlap_compatible_only_at_5_or_7_of_decide pair18247365 overlap_check_pair18247365)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

theorem exactOccurrenceCount_eq_18236475_18246375 (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet pair18236475) marks =
      WilfCounts.exactCount (occurrenceSet pair18246375) marks := by
  exact exactOccurrenceCount_eq_of_swap n marks pair18236475 pair18246375
    (overlap_compatible_only_at_5_or_7_of_decide pair18236475 overlap_check_pair18236475)
    (overlap_compatible_only_at_5_or_7_of_decide pair18246375 overlap_check_pair18246375)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by intro i hi; fin_cases i <;> decide)
    (by intro i hi hi2; fin_cases i <;> decide) (by decide)
    (by funext i; fin_cases i <;> rfl)
    (by funext i; fin_cases i <;> rfl)

#print axioms exactOccurrenceCount_eq
#print axioms exactOccurrenceCount_eq_16238475_16248375
#print axioms exactOccurrenceCount_eq_17236485_17246385
#print axioms exactOccurrenceCount_eq_17238465_17248365
#print axioms exactOccurrenceCount_eq_18237465_18247365
#print axioms exactOccurrenceCount_eq_18236475_18246375

end Implications.WilfPatternSwap
