import Mathlib

/-!
# Finite counting bounds for smooth integers in prime gaps

The first estimate in the elementary cutoff argument for Erdős #932: gaps of
size at least `B` among the first `N` consecutive prime gaps have total count
at most `p_N / B`. The proof is the disjoint-interval argument expressed by
telescoping the consecutive prime gaps.
-/

namespace Implications.SmoothGapCounting

open Filter

/-- The `n`th prime, in the indexing convention used by formal-conjectures. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The gap between the `n`th prime and its successor. -/
noncomputable def primeGap (n : ℕ) : ℕ := primeAt (n + 1) - primeAt n

private theorem primeCounting_primeAt (n : ℕ) :
    Nat.primeCounting (primeAt n) = n + 1 := by
  change Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

private theorem primeAt_count_asymptotic :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      Real.log (primeAt n : ℝ) / (primeAt n : ℝ)) atTop (𝓝 1) := by
  have hprime : Tendsto (fun n : ℕ => (primeAt n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp primeAt_strictMono.tendsto_atTop
  have heq := Nat.isEquivalent_primeCounting.comp_tendsto hprime
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log (primeAt n : ℝ) ≠ 0 := by
    filter_upwards [hprime.eventually (eventually_gt_atTop 1)] with n hn
    exact (Real.log_pos hn).ne'
  have hratio := (isEquivalent_iff_tendsto_one (by
    filter_upwards [hprime.eventually (eventually_gt_atTop 1)] with n hn
    exact (div_ne_zero (by exact_mod_cast (primeAt n).ne_zero)
      (Real.log_pos hn).ne'))).mp heq
  have hfloor (n : ℕ) : ⌊(primeAt n : ℝ)⌋₊ = primeAt n := by simp
  have hratio' : Tendsto (fun n : ℕ =>
      ((Nat.primeCounting (primeAt n) : ℝ) /
        ((primeAt n : ℝ) / Real.log (primeAt n : ℝ)))) atTop (𝓝 1) := by
    convert hratio using 1 <;> simp [Function.comp_apply, hfloor]
  have hfinal : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      Real.log (primeAt n : ℝ) / (primeAt n : ℝ)) atTop (𝓝 1) := by
    refine hratio'.congr' ?_
    filter_upwards [] with n
    rw [primeCounting_primeAt]
    field_simp
  exact hfinal

private theorem primeAt_strictMono : StrictMono primeAt := by
  intro a b hab
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime hab

/-- For every cutoff `B`, each of the first `N` gaps of size at least `B`
contributes at least `B` to the telescoping sum of all gaps. Consequently,
their count is at most the `N`th prime divided by `B` (in the cross-multiplied
form, which also covers `B = 0`). -/
theorem largeGapCount (N B : ℕ) :
    (B : ℝ) * (((Finset.range N).filter (fun r => B ≤ primeGap r)).card : ℝ) ≤
      (primeAt N : ℝ) := by
  let L := (Finset.range N).filter (fun r => B ≤ primeGap r)
  change (B : ℝ) * (L.card : ℝ) ≤ (primeAt N : ℝ)
  calc
    _ = ∑ _r ∈ L, (B : ℝ) := by simp [mul_comm]
    _ ≤ ∑ r ∈ L, (primeGap r : ℝ) :=
      Finset.sum_le_sum fun r hr => Nat.cast_le.mpr (Finset.mem_filter.mp hr).2
    _ ≤ ∑ r ∈ Finset.range N, (primeGap r : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun r _ _ => Nat.cast_nonneg _
    _ = (primeAt N : ℝ) - (primeAt 0 : ℝ) := by
      have hcast (r : ℕ) : (primeGap r : ℝ) =
          (primeAt (r + 1) : ℝ) - (primeAt r : ℝ) := by
        rw [primeGap, Nat.cast_sub (primeAt_strictMono (by omega)).le]
      simp_rw [hcast]
      exact Finset.sum_range_sub (fun i => (primeAt i : ℝ)) N
    _ ≤ (primeAt N : ℝ) := by
      exact sub_le_self _ (by positivity)

/-- Disjoint finite sets, each with at least `j` elements and all contained in
`U`, contribute at least `j` elements apiece to `U`. -/
theorem disjointCardBound {ι α : Type*} [DecidableEq α]
    (S : Finset ι) (A : ι → Finset α) (U : Finset α) (j : ℕ)
    (hdisj : (S : Set ι).PairwiseDisjoint A)
    (hlarge : ∀ i ∈ S, j ≤ (A i).card)
    (hsub : S.biUnion A ⊆ U) :
    j * S.card ≤ U.card := by
  calc
    j * S.card = ∑ i ∈ S, j := by simp [mul_comm]
    _ ≤ ∑ i ∈ S, (A i).card := by
      exact Finset.sum_le_sum fun i hi => hlarge i hi
    _ = (S.biUnion A).card := (Finset.card_biUnion hdisj).symm
    _ ≤ U.card := Finset.card_le_card hsub

/-- The open interiors between distinct consecutive primes are pairwise
disjoint. -/
theorem primeGapInteriors_pairwiseDisjoint (N : ℕ) :
    ((Finset.range N : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun r => Finset.Ioo (primeAt r) (primeAt (r + 1))) := by
  intro i hi k hk hik
  rcases lt_or_gt_of_ne hik with hlt | hgt
  · apply Finset.disjoint_left.mpr
    intro x hxi hxk
    simp only [Finset.mem_Ioo] at hxi hxk
    have hik' : i + 1 ≤ k := by omega
    have hgap : primeAt (i + 1) ≤ primeAt k := primeAt_strictMono.monotone hik'
    omega
  · apply Finset.disjoint_left.mpr
    intro x hxk hxi
    simp only [Finset.mem_Ioo] at hxi hxk
    have hki' : k + 1 ≤ i := by omega
    have hgap : primeAt (k + 1) ≤ primeAt i := primeAt_strictMono.monotone hki'
    omega

/-- A finite multi-hit bound for prime gaps. If every selected gap contributes
at least `j` smooth integers, and all of those integers lie in a common finite
set `U`, then the number of selected gaps is at most `|U| / j`. Pairwise
disjointness of the prime-gap interiors is proved here, not assumed. -/
theorem primeGapSmoothCountBound {N j : ℕ} (S U : Finset ℕ)
    (hS : S ⊆ Finset.range N)
    (hlarge : ∀ r ∈ S, j ≤
      ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
        (fun m => m.maxPrimeFac < primeGap r)).card)
    (hsub : S.biUnion (fun r =>
      (Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
        (fun m => m.maxPrimeFac < primeGap r)) ⊆ U) :
    j * S.card ≤ U.card := by
  apply disjointCardBound S
    (fun r => (Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
      (fun m => m.maxPrimeFac < primeGap r)) U j
  · intro r hr s hs hrs
    have hd := primeGapInteriors_pairwiseDisjoint N (hS hr) (hS hs) hrs
    apply Finset.disjoint_left.mpr
    intro m hmr hms
    exact (Finset.disjoint_left.mp hd)
      (Finset.mem_filter.mp hmr).1 (Finset.mem_filter.mp hms).1
  · exact hlarge
  · exact hsub

/-- The cutoff form of the multi-hit bound for gaps no longer than `Y`.
Every qualifying integer then has all prime factors below `Y`, and lies below
the `N`th prime. Thus `j` hits in each selected gap consume `j` distinct
members of the finite set of `Y`-smooth integers below `p_N`. -/
theorem smallGapMultiHitBound {N Y j : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.range N)
    (hgap : ∀ r ∈ S, primeGap r ≤ Y)
    (hlarge : ∀ r ∈ S, j ≤
      ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
        (fun m => m.maxPrimeFac < primeGap r)).card) :
    j * S.card ≤
      ((Finset.range (primeAt N + 1)).filter (fun m => m.maxPrimeFac < Y)).card := by
  apply primeGapSmoothCountBound S
    ((Finset.range (primeAt N + 1)).filter (fun m => m.maxPrimeFac < Y)) hS hlarge
  intro m hm
  rcases Finset.mem_biUnion.mp hm with ⟨r, hr, hmr⟩
  have hmi := Finset.mem_filter.mp hmr
  have hmIoo := Finset.mem_Ioo.mp hmi.1
  have hrN := Finset.mem_range.mp (hS hr)
  have hrp : r + 1 ≤ N := by omega
  have hp : primeAt (r + 1) ≤ primeAt N := primeAt_strictMono.monotone hrp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
  exact lt_of_lt_of_le hmi.2 (hgap r hr)

/-- The number of `B`-smooth integers at most `primeAt N`, including zero as
allowed by the `maxPrimeFac` predicate, is bounded by Mathlib's square-root
estimate for smooth numbers. The extra `1` accounts for zero, which is not a
member of `Nat.smoothNumbers B`. -/
theorem smoothGapUniverseCardBound (N B : ℕ) :
    ((Finset.range (primeAt N + 1)).filter (fun m => m.maxPrimeFac < B)).card ≤
      1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt := by
  let U := (Finset.range (primeAt N + 1)).filter (fun m => m.maxPrimeFac < B)
  have hsubset : U ⊆ insert 0 (Nat.smoothNumbersUpTo (primeAt N) B) := by
    intro m hm
    have hmem := Finset.mem_filter.mp hm
    by_cases hm0 : m = 0
    · simp [hm0]
    · apply Finset.mem_insert.mpr
      right
      apply Nat.mem_smoothNumbersUpTo.mpr
      refine ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hmem.1), ?_⟩
      apply Nat.mem_smoothNumbers'.2
      intro p hp hpd
      by_cases hm1 : m = 1
      · subst m
        exact (hp.not_dvd_one hpd).elim
      · have htwo : 1 < m := by omega
        exact lt_of_le_of_lt (Nat.le_maxPrimeFac hm0 hp hpd) hmem.2
  calc
    U.card ≤ (insert 0 (Nat.smoothNumbersUpTo (primeAt N) B)).card :=
      Finset.card_le_card hsubset
    _ ≤ 1 + (Nat.smoothNumbersUpTo (primeAt N) B).card := by
      simpa [Nat.add_comm] using
        (Finset.card_insert_le 0 (Nat.smoothNumbersUpTo (primeAt N) B))
    _ ≤ 1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt := by
      exact Nat.add_le_add_left (Nat.smoothNumbersUpTo_card_le _ _) 1

/-- Finite cutoff estimate for prime gaps with at least `j` smooth interior
integers. Gaps of size at least `B` are bounded by the telescoping prime-gap
sum, while hits in shorter gaps inject disjointly into the global set of
`B`-smooth integers below `p_N`:

`B * j * hitCount ≤ j * p_N + B * smoothCount`.
-/
theorem cutoffHitCount (N B j : ℕ) (hB : 0 < B) :
    (B : ℝ) * j * (((Finset.range N).filter (fun r =>
      j ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
        (fun m => m.maxPrimeFac < primeGap r)).card)).card : ℝ) ≤
      (j : ℝ) * primeAt N + (B : ℝ) *
        (((Finset.range (primeAt N + 1)).filter (fun m => m.maxPrimeFac < B)).card : ℝ) := by
  let H := (Finset.range N).filter (fun r =>
    j ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
      (fun m => m.maxPrimeFac < primeGap r)).card)
  let L := H.filter (fun r => B ≤ primeGap r)
  let S := H.filter (fun r => primeGap r < B)
  let U := (Finset.range (primeAt N + 1)).filter (fun m => m.maxPrimeFac < B)
  have hpart : H = L ∪ S := by
    ext r
    simp [H, L, S]
    omega
  have hdisj : Disjoint L S := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    exact (not_lt_of_ge (Finset.mem_filter.mp hr).2) (Finset.mem_filter.mp hs).2
  have hcard : H.card = L.card + S.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have hLsub : L ⊆ (Finset.range N).filter (fun r => B ≤ primeGap r) := by
    intro r hr
    have hrH := (Finset.mem_filter.mp hr).1
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hrH).1,
      (Finset.mem_filter.mp hr).2⟩
  have hLnat := Finset.card_le_card hLsub
  have hLbound := largeGapCount N B
  have hLcard : (L.card : ℝ) ≤
      (((Finset.range N).filter (fun r => B ≤ primeGap r)).card : ℝ) := by
    exact_mod_cast hLnat
  have hLB : (B : ℝ) * (L.card : ℝ) ≤ primeAt N := by
    calc
      (B : ℝ) * (L.card : ℝ) ≤
          (B : ℝ) * (((Finset.range N).filter (fun r => B ≤ primeGap r)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hLcard (by positivity)
      _ ≤ _ := hLbound
  have hSsub : S ⊆ Finset.range N := by
    intro r hr
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  have hSlarge : ∀ r ∈ S, j ≤
      ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
        (fun m => m.maxPrimeFac < primeGap r)).card := by
    intro r hr
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
  have hSgap : ∀ r ∈ S, primeGap r ≤ B := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.le
  have hSboundNat := smallGapMultiHitBound S hSsub hSgap hSlarge
  have hSbound : (j : ℝ) * (S.card : ℝ) ≤ (U.card : ℝ) := by
    have hcast : ((j * S.card : ℕ) : ℝ) ≤ ((U.card : ℕ) : ℝ) := by
      exact_mod_cast hSboundNat
    simpa [Nat.cast_mul] using hcast
  have hLscaled : (B : ℝ) * j * (L.card : ℝ) ≤ (j : ℝ) * primeAt N := by
    calc
      _ = (j : ℝ) * ((B : ℝ) * (L.card : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLB (by positivity)
  have hSscaled : (B : ℝ) * j * (S.card : ℝ) ≤ (B : ℝ) * (U.card : ℝ) := by
    calc
      _ = (B : ℝ) * ((j : ℝ) * (S.card : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hSbound (by positivity)
  rw [hcard]
  calc
    (B : ℝ) * (j : ℝ) * (↑(L.card + S.card) : ℝ) =
        (B : ℝ) * (j : ℝ) * (L.card : ℝ) + (B : ℝ) * (j : ℝ) * (S.card : ℝ) := by
      rw [Nat.cast_add]
      ring
    _ ≤ (j : ℝ) * primeAt N + (B : ℝ) * (U.card : ℝ) := add_le_add hLscaled hSscaled

/-- The finite cutoff estimate with the smooth-number term evaluated using
Mathlib's bound `2^π(B) * √p_N` (and one extra element for zero). -/
theorem cutoffHitCount_smoothNumbers (N B j : ℕ) (hB : 0 < B) :
    (B : ℝ) * j * (((Finset.range N).filter (fun r =>
      j ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
        (fun m => m.maxPrimeFac < primeGap r)).card)).card : ℝ) ≤
      (j : ℝ) * primeAt N + (B : ℝ) *
        ((1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt : ℕ) : ℝ) := by
  have hcut := cutoffHitCount N B j hB
  have hsmooth := smoothGapUniverseCardBound N B
  have hsmoothCast :
      ((((Finset.range (primeAt N + 1)).filter
        (fun m => m.maxPrimeFac < B)).card : ℕ) : ℝ) ≤
        ((1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt : ℕ) : ℝ) := by
    exact_mod_cast hsmooth
  calc
    _ ≤ (j : ℝ) * primeAt N + (B : ℝ) *
        (((Finset.range (primeAt N + 1)).filter
          (fun m => m.maxPrimeFac < B)).card : ℝ) := hcut
    _ ≤ (j : ℝ) * primeAt N + (B : ℝ) *
        ((1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt : ℕ) : ℝ) := by
      gcongr

end Implications.SmoothGapCounting
