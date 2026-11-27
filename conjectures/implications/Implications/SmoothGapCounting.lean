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

/-- A logarithmic cutoff for counting smooth numbers in the first `N` prime gaps. -/
noncomputable def logLogCutoff (n : ℕ) : ℕ :=
  ⌊Real.log (primeAt n : ℝ) * Real.log (Real.log (primeAt n : ℝ)) / 16⌋₊

private theorem primeCounting_primeAt (n : ℕ) :
    Nat.primeCounting (primeAt n) = n + 1 := by
  change Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

private theorem primeAt_count_asymptotic :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      Real.log (primeAt n : ℝ) / (primeAt n : ℝ)) atTop (nhds 1) := by
  have hnat : Tendsto primeAt atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun n hbn => ?_⟩
    have hp := Nat.add_two_le_nth_prime n
    change b ≤ Nat.nth Nat.Prime n
    omega
  have hprime : Tendsto (fun n : ℕ => (primeAt n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp hnat
  have heq := Nat.isEquivalent_primeCounting.comp_tendsto hprime
  have hden : ∀ᶠ n : ℕ in atTop,
      (primeAt n : ℝ) / Real.log (primeAt n : ℝ) ≠ 0 := by
    filter_upwards [hprime.eventually (eventually_gt_atTop 1)] with n hn
    exact div_ne_zero (by linarith) (Real.log_pos hn).ne'
  have hratio := (Asymptotics.isEquivalent_iff_tendsto_one hden).mp heq
  have hratio' : Tendsto (fun n : ℕ =>
      ((Nat.primeCounting (primeAt n) : ℝ) /
        ((primeAt n : ℝ) / Real.log (primeAt n : ℝ)))) atTop (nhds 1) := by
    convert hratio using 1
    ext n
    simp
  have hfinal : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      Real.log (primeAt n : ℝ) / (primeAt n : ℝ)) atTop (nhds 1) := by
    refine hratio'.congr' ?_
    filter_upwards [hprime.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    rw [primeCounting_primeAt]
    field_simp
  exact hfinal

private theorem eventually_primeBelow_count_le_two_mul
    (B : ℕ → ℕ) (hB : Tendsto (fun n => (B n : ℝ)) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      ((B n).primesBelow.card : ℝ) ≤ 2 * (B n : ℝ) / Real.log (B n : ℝ) := by
  have heq := Nat.isEquivalent_primeCounting.comp_tendsto hB
  have hden : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) / Real.log (B n : ℝ) ≠ 0 := by
    filter_upwards [hB.eventually (eventually_gt_atTop 1)] with n hn
    exact div_ne_zero (by linarith) (Real.log_pos hn).ne'
  have hratio := (Asymptotics.isEquivalent_iff_tendsto_one hden).mp heq
  have hlt : ∀ᶠ n : ℕ in atTop,
      ((Nat.primeCounting (B n) : ℝ) / ((B n : ℝ) / Real.log (B n : ℝ))) < 2 := by
    filter_upwards [hratio.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))]
      with n hn
    simpa using hn
  filter_upwards [hB.eventually (eventually_gt_atTop 1), hlt] with n hn hpi
  have hlog : 0 < Real.log (B n : ℝ) := Real.log_pos hn
  have hdenpos : 0 < (B n : ℝ) / Real.log (B n : ℝ) := div_pos (by linarith) hlog
  have hpi' :
      (Nat.primeCounting (B n) : ℝ) < 2 * ((B n : ℝ) / Real.log (B n : ℝ)) :=
    (div_lt_iff₀ hdenpos).mp hpi
  have hcard : (B n).primesBelow.card ≤ Nat.primeCounting (B n) := by
    calc
      (B n).primesBelow.card = Nat.primeCounting' (B n) :=
        Nat.primesBelow_card_eq_primeCounting' _
      _ = Nat.primeCounting (B n - 1) := (Nat.primeCounting_sub_one _).symm
      _ ≤ Nat.primeCounting (B n) := Nat.monotone_primeCounting (Nat.sub_le _ _)
  have hcard' : ((B n).primesBelow.card : ℝ) ≤ Nat.primeCounting (B n) := by
    exact_mod_cast hcard
  calc
    ((B n).primesBelow.card : ℝ) ≤ Nat.primeCounting (B n) := hcard'
    _ ≤ 2 * ((B n : ℝ) / Real.log (B n : ℝ)) := hpi'.le
    _ = 2 * (B n : ℝ) / Real.log (B n : ℝ) := by ring

private theorem logLogCutoff_tendsto_atTop :
    Tendsto (fun n => (logLogCutoff n : ℝ)) atTop atTop := by
  have hp : Tendsto (fun n => (primeAt n : ℝ)) atTop atTop := by
    have hnat : Tendsto primeAt atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, fun n hbn => ?_⟩
      have hp := Nat.add_two_le_nth_prime n
      change b ≤ Nat.nth Nat.Prime n
      omega
    exact tendsto_natCast_atTop_atTop.comp hnat
  have hlog : Tendsto (fun n => Real.log (primeAt n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hp
  have hloglog : Tendsto (fun n => Real.log (Real.log (primeAt n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hprod : Tendsto (fun n =>
      Real.log (primeAt n : ℝ) * Real.log (Real.log (primeAt n : ℝ)) / 16)
      atTop atTop := by
    convert (hlog.atTop_mul_atTop₀ hloglog).atTop_div_const (by norm_num : (0 : ℝ) < 16)
      using 1
  exact tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp hprod)

private theorem eventually_logLogCutoff_log_lower :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (primeAt n : ℝ)) / 2 ≤ Real.log (logLogCutoff n : ℝ) := by
  have hprime : Tendsto (fun n : ℕ => (primeAt n : ℝ)) atTop atTop := by
    have hnat : Tendsto primeAt atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, fun n hbn => ?_⟩
      have hp := Nat.add_two_le_nth_prime n
      change b ≤ Nat.nth Nat.Prime n
      omega
    exact tendsto_natCast_atTop_atTop.comp hnat
  have hlog := Real.tendsto_log_atTop.comp hprime
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually_ge_atTop 1024, hloglog.eventually_ge_atTop 1]
    with n hL hLL
  change 1024 ≤ Real.log (primeAt n : ℝ) at hL
  change 1 ≤ Real.log (Real.log (primeAt n : ℝ)) at hLL
  have hLpos : 0 < Real.log (primeAt n : ℝ) := by linarith
  have hsqrt_le : Real.sqrt (Real.log (primeAt n : ℝ)) ≤
      (Real.log (primeAt n : ℝ)) / 32 := by
    nlinarith [Real.sq_sqrt (le_of_lt hLpos)]
  have hfloor : Real.log (primeAt n : ℝ) *
      Real.log (Real.log (primeAt n : ℝ)) / 16 <
      (logLogCutoff n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hB_lower : Real.sqrt (Real.log (primeAt n : ℝ)) ≤ (logLogCutoff n : ℝ) := by
    have hratio : (Real.log (primeAt n : ℝ)) / 32 ≤
        Real.log (primeAt n : ℝ) * Real.log (Real.log (primeAt n : ℝ)) / 16 - 1 := by
      nlinarith [hL, hLL]
    linarith
  rw [← Real.log_sqrt (le_of_lt hLpos)]
  exact Real.log_le_log (by positivity) hB_lower

private theorem eventually_logLogCutoff_lower :
    ∀ᶠ n : ℕ in atTop,
      Real.log (primeAt n : ℝ) * Real.log (Real.log (primeAt n : ℝ)) / 32 ≤
        (logLogCutoff n : ℝ) := by
  have hprime : Tendsto (fun n : ℕ => (primeAt n : ℝ)) atTop atTop := by
    have hnat : Tendsto primeAt atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, fun n hbn => ?_⟩
      have hp := Nat.add_two_le_nth_prime n
      change b ≤ Nat.nth Nat.Prime n
      omega
    exact tendsto_natCast_atTop_atTop.comp hnat
  have hlog := Real.tendsto_log_atTop.comp hprime
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually_ge_atTop 1024, hloglog.eventually_ge_atTop 1]
    with n hL hLL
  change 1024 ≤ Real.log (primeAt n : ℝ) at hL
  change 1 ≤ Real.log (Real.log (primeAt n : ℝ)) at hLL
  have hX : 2 ≤ Real.log (primeAt n : ℝ) *
      Real.log (Real.log (primeAt n : ℝ)) / 16 := by nlinarith
  have hf : Real.log (primeAt n : ℝ) *
      Real.log (Real.log (primeAt n : ℝ)) / 16 <
      (logLogCutoff n : ℝ) + 1 := Nat.lt_floor_add_one _
  nlinarith

private theorem eventually_primeAt_over_index_le :
    ∀ᶠ n : ℕ in atTop,
      (primeAt n : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log (primeAt n : ℝ) := by
  have hratio := primeAt_count_asymptotic
  filter_upwards [hratio.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
    with n hn
  have hx : 0 < (primeAt n : ℝ) := by exact_mod_cast (Nat.prime_nth_prime n).pos
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul : (1 / 2 : ℝ) * (primeAt n : ℝ) <
      ((n + 1 : ℕ) : ℝ) * Real.log (primeAt n : ℝ) :=
    (lt_div_iff₀ hx).mp hn
  apply (div_le_iff₀ hN).2
  nlinarith

private theorem eventually_logLogCutoff_primeCount_le :
    ∀ᶠ n : ℕ in atTop,
      ((logLogCutoff n).primesBelow.card : ℝ) ≤
        Real.log (primeAt n : ℝ) / 4 := by
  filter_upwards [eventually_primeBelow_count_le_two_mul logLogCutoff logLogCutoff_tendsto_atTop,
    eventually_logLogCutoff_log_lower,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (by
        rw [tendsto_atTop_atTop]
        intro b
        refine ⟨b, fun n hbn => ?_⟩
        have hp := Nat.add_two_le_nth_prime n
        change b ≤ Nat.nth Nat.Prime n
        omega)))).eventually_ge_atTop 1]
    with n hpi hlogB hLL
  change 1 ≤ Real.log (Real.log (primeAt n : ℝ)) at hLL
  have hL : 0 < Real.log (primeAt n : ℝ) := by
    have hp : 1 < (primeAt n : ℝ) := by
      exact_mod_cast (show 1 < Nat.nth Nat.Prime n from
        Nat.Prime.one_lt (Nat.prime_nth_prime n))
    exact Real.log_pos hp
  have hLLpos : 0 < Real.log (Real.log (primeAt n : ℝ)) := by linarith
  have hBupper : (logLogCutoff n : ℝ) ≤
      Real.log (primeAt n : ℝ) * Real.log (Real.log (primeAt n : ℝ)) / 16 :=
    Nat.floor_le (by positivity)
  have hbound : 2 * (logLogCutoff n : ℝ) / Real.log (logLogCutoff n : ℝ) ≤
      Real.log (primeAt n : ℝ) / 4 := by
    calc
      2 * (logLogCutoff n : ℝ) / Real.log (logLogCutoff n : ℝ) ≤
          2 * (Real.log (primeAt n : ℝ) * Real.log (Real.log (primeAt n : ℝ)) / 16) /
            (Real.log (Real.log (primeAt n : ℝ)) / 2) := by
        gcongr
      _ = Real.log (primeAt n : ℝ) / 4 := by
        field_simp
        <;> norm_num
  exact hpi.trans hbound

private theorem log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at h ⊢
  linarith

private theorem eventually_logLogCutoff_smoothFactor_le :
    ∀ᶠ n : ℕ in atTop,
      (2 ^ (logLogCutoff n).primesBelow.card : ℝ) *
        Real.sqrt (primeAt n : ℝ) ≤
          Real.exp (3 * Real.log (primeAt n : ℝ) / 4) := by
  filter_upwards [eventually_logLogCutoff_primeCount_le] with n hpi
  let k := (logLogCutoff n).primesBelow.card
  have hL : 0 < Real.log (primeAt n : ℝ) := by
    have hp : 1 < (primeAt n : ℝ) := by
      exact_mod_cast (show 1 < Nat.nth Nat.Prime n from
        Nat.Prime.one_lt (Nat.prime_nth_prime n))
    exact Real.log_pos hp
  have hx : 0 < (primeAt n : ℝ) := by
    exact_mod_cast (Nat.prime_nth_prime n).pos
  have hk : (k : ℝ) ≤ Real.log (primeAt n : ℝ) / 4 := by
    dsimp [k]
    exact hpi
  have hpow : (2 ^ k : ℝ) = Real.exp ((k : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ k = (Real.exp (Real.log 2)) ^ k := by
        rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((k : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
  have hexp : Real.exp ((k : ℝ) * Real.log 2) ≤
      Real.exp (Real.log (primeAt n : ℝ) / 4) := by
    apply Real.exp_le_exp.mpr
    have harg : (k : ℝ) * Real.log 2 ≤ (k : ℝ) := by
      nlinarith [log_two_lt_one, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact harg.trans hk
  have hsqrt : Real.sqrt (primeAt n : ℝ) =
      Real.exp (Real.log (primeAt n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [hpow, hsqrt]
  calc
    Real.exp ((k : ℝ) * Real.log 2) * Real.exp (Real.log (primeAt n : ℝ) / 2) ≤
        Real.exp (Real.log (primeAt n : ℝ) / 4) *
          Real.exp (Real.log (primeAt n : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = Real.exp (3 * Real.log (primeAt n : ℝ) / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring

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
    · apply Finset.mem_insert_of_mem
      apply Nat.mem_smoothNumbersUpTo.mpr
      refine ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hmem.1), ?_⟩
      apply Nat.mem_smoothNumbers'.2
      intro p hp hpd
      exact lt_of_le_of_lt (Nat.le_maxPrimeFac hm0 hp hpd) hmem.2
  calc
    U.card ≤ (insert 0 (Nat.smoothNumbersUpTo (primeAt N) B)).card :=
      Finset.card_le_card hsubset
    _ ≤ 1 + (Nat.smoothNumbersUpTo (primeAt N) B).card := by
      simpa [Nat.add_comm] using Finset.card_insert_le 0 (Nat.smoothNumbersUpTo (primeAt N) B)
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
Mathlib's bound using the number of primes strictly below `B` (and one extra element for zero). -/
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

/-- An explicit upper bound for the proportion of the first `N` prime gaps
with at least `j` qualifying integers. The cutoff `B` is free to depend on
`N`; the two terms expose the tradeoff between large gaps and smooth integers.
-/
theorem hitIndexProportionBound (N B j : ℕ) (hB : 0 < B) :
    (j : ℝ) * (((Finset.range N).filter (fun r =>
      j ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
        (fun m => m.maxPrimeFac < primeGap r)).card)).card : ℝ) /
        (N + 1 : ℝ) ≤
      (((j : ℝ) * primeAt N) / (N + 1 : ℝ)) / B +
        (1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt) / (N + 1 : ℝ) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hn : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hcut := cutoffHitCount_smoothNumbers N B j hB
  have hden : (0 : ℝ) < (B : ℝ) * (N + 1 : ℝ) := mul_pos hb hn
  calc
    _ = ((B : ℝ) * (j : ℝ) * (((Finset.range N).filter (fun r =>
        j ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
          (fun m => m.maxPrimeFac < primeGap r)).card)).card : ℝ)) /
          ((B : ℝ) * (N + 1 : ℝ)) := by
      field_simp
    _ ≤ ((j : ℝ) * primeAt N + (B : ℝ) *
        ((1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt : ℕ) : ℝ)) /
          ((B : ℝ) * (N + 1 : ℝ)) :=
      div_le_div_of_nonneg_right hcut (le_of_lt hden)
    _ = (((j : ℝ) * primeAt N) / (N + 1 : ℝ)) / B +
        (1 + 2 ^ B.primesBelow.card * (primeAt N).sqrt) / (N + 1 : ℝ) := by
      field_simp
      push_cast
      rfl

/-- An explicit eventual two-term upper bound for the relative count of
two-hit gaps. The first term is the logarithmic cutoff contribution; the
second is the smooth-number tail after applying Mathlib's square-root bound.
-/
theorem eventually_twoHitGapCount_bound :
    ∀ᶠ n : ℕ in atTop,
      (((Finset.range n).filter (fun r =>
        2 ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
          (fun m => m.maxPrimeFac < primeGap r)).card)).card : ℝ) /
          (n + 1 : ℝ) ≤
        64 / Real.log (Real.log (primeAt n : ℝ)) +
          (1 + Real.exp (3 * Real.log (primeAt n : ℝ) / 4)) /
            (2 * (n + 1 : ℝ)) := by
  filter_upwards [eventually_logLogCutoff_lower,
    eventually_primeAt_over_index_le,
    eventually_logLogCutoff_smoothFactor_le,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (by
        rw [tendsto_atTop_atTop]
        intro b
        refine ⟨b, fun n hbn => ?_⟩
        have hp := Nat.add_two_le_nth_prime n
        change b ≤ Nat.nth Nat.Prime n
        omega)))).eventually_gt_atTop 0]
    with n hB hindex htail hLLpos
  change 0 < Real.log (Real.log (primeAt n : ℝ)) at hLLpos
  have hLpos : 0 < Real.log (primeAt n : ℝ) := by
    exact Real.log_pos (by
      exact_mod_cast (show 1 < Nat.nth Nat.Prime n from
        Nat.Prime.one_lt (Nat.prime_nth_prime n)))
  have hBpos : 0 < logLogCutoff n := by
    have : 0 < Real.log (primeAt n : ℝ) *
        Real.log (Real.log (primeAt n : ℝ)) / 32 := by positivity
    exact Nat.cast_pos.mp (lt_of_lt_of_le this hB)
  have hNpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hprop := hitIndexProportionBound n (logLogCutoff n) 2 hBpos
  let C := (((Finset.range n).filter (fun r =>
    2 ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
      (fun m => m.maxPrimeFac < primeGap r)).card)).card : ℝ)
  have hcount : C / (n + 1 : ℝ) ≤
      ((primeAt n : ℝ) / (n + 1 : ℝ)) / (logLogCutoff n) +
        (1 + 2 ^ (logLogCutoff n).primesBelow.card *
          (primeAt n).sqrt) / (2 * (n + 1 : ℝ)) := by
    dsimp [C] at hprop ⊢
    have hden : (0 : ℝ) < 2 * (n + 1 : ℝ) * logLogCutoff n := by positivity
    field_simp at hprop ⊢
    nlinarith
  have hindex' : (primeAt n : ℝ) / (n + 1 : ℝ) ≤
      2 * Real.log (primeAt n : ℝ) := by
    simpa [Nat.cast_add] using hindex
  have hfirst : ((primeAt n : ℝ) / (n + 1 : ℝ)) /
        (logLogCutoff n) ≤ 64 / Real.log (Real.log (primeAt n : ℝ)) := by
    calc
      _ ≤ (2 * Real.log (primeAt n : ℝ)) / (logLogCutoff n) :=
        div_le_div_of_nonneg_right hindex' (by positivity)
      _ ≤ (2 * Real.log (primeAt n : ℝ)) /
          (Real.log (primeAt n : ℝ) * Real.log (Real.log (primeAt n : ℝ)) / 32) := by
        gcongr
      _ = 64 / Real.log (Real.log (primeAt n : ℝ)) := by
        field_simp
        <;> ring
  have htail' :
      (1 + 2 ^ (logLogCutoff n).primesBelow.card * (primeAt n).sqrt) /
          (2 * (n + 1 : ℝ)) ≤
        (1 + Real.exp (3 * Real.log (primeAt n : ℝ) / 4)) /
          (2 * (n + 1 : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      1 + 2 ^ (logLogCutoff n).primesBelow.card * (primeAt n).sqrt ≤
          1 + 2 ^ (logLogCutoff n).primesBelow.card *
            Real.sqrt (primeAt n : ℝ) := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt
      _ ≤ 1 + Real.exp (3 * Real.log (primeAt n : ℝ) / 4) := by
        simpa [add_comm] using add_le_add_left htail 1
  simpa [C] using hcount.trans (add_le_add hfirst htail')

/-- The smooth-number tail in the two-hit estimate tends to zero. This is the
prime number theorem comparison `p_N / (N + 1) ≤ 2 log p_N` followed by the
fact that a logarithm is dominated by any positive power. -/
private theorem eventually_twoHitGapCount_tail_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (1 + Real.exp (3 * Real.log (primeAt n : ℝ) / 4)) /
        (2 * (n + 1 : ℝ))) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (primeAt n : ℝ)) atTop atTop := by
    have hnat : Tendsto primeAt atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, fun n hbn => ?_⟩
      have hprime := Nat.add_two_le_nth_prime n
      change b ≤ Nat.nth Nat.Prime n
      omega
    exact tendsto_natCast_atTop_atTop.comp hnat
  have hlogsmall :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hlogsmall' : Tendsto (fun n : ℕ =>
      Real.log (primeAt n : ℝ) / (primeAt n : ℝ) ^ (1 / 4 : ℝ))
      atTop (nhds 0) := by
    convert hlogsmall.comp hp using 1 <;> rfl
  have hbase : Tendsto (fun n : ℕ =>
      (1 : ℝ) / (n + 1 : ℝ)) atTop (nhds 0) := by
    convert tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop) using 1
    ext n
    simp [one_div]
  have htail : Tendsto (fun n : ℕ =>
      Real.exp (3 * Real.log (primeAt n : ℝ) / 4) /
        (2 * (n + 1 : ℝ))) atTop (nhds 0) := by
    have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (primeAt n : ℝ) := by
      filter_upwards [hp.eventually (eventually_gt_atTop (1 : ℝ))] with n hn
      exact Real.log_pos hn
    have hindex := eventually_primeAt_over_index_le
    have hpowpos : ∀ᶠ n : ℕ in atTop, 0 < (primeAt n : ℝ) ^ (1 / 4 : ℝ) := by
      filter_upwards [hp.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
      exact Real.rpow_pos_of_pos hn _
    have hrewrite : ∀ᶠ n : ℕ in atTop,
        Real.exp (3 * Real.log (primeAt n : ℝ) / 4) /
            (2 * (n + 1 : ℝ)) =
          ((primeAt n : ℝ) / (n + 1 : ℝ)) /
            (2 * (primeAt n : ℝ) ^ (1 / 4 : ℝ)) := by
      filter_upwards [hlog, hp.eventually (eventually_gt_atTop (0 : ℝ))] with n hln hpn
      have hidentity : Real.exp (3 * Real.log (primeAt n : ℝ) / 4) *
          (primeAt n : ℝ) ^ (1 / 4 : ℝ) = (primeAt n : ℝ) := by
        rw [Real.rpow_def_of_pos hpn]
        rw [← Real.exp_add]
        congr 1
        have : 3 * Real.log (primeAt n : ℝ) / 4 +
            Real.log (primeAt n : ℝ) * (1 / 4 : ℝ) =
            Real.log (primeAt n : ℝ) := by ring
        rw [this, Real.exp_log hpn]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      nlinarith [hidentity]
    have hfactor : Tendsto (fun n : ℕ =>
        ((primeAt n : ℝ) / (n + 1 : ℝ)) /
          (2 * (primeAt n : ℝ) ^ (1 / 4 : ℝ))) atTop (nhds 0) := by
      have hratio := hlogsmall'
      have hevent : ∀ᶠ n : ℕ in atTop,
          (primeAt n : ℝ) / (n + 1 : ℝ) ≤ 2 * Real.log (primeAt n : ℝ) :=
        eventually_primeAt_over_index_le
      have hbound : ∀ᶠ n : ℕ in atTop,
          0 ≤ ((primeAt n : ℝ) / (n + 1 : ℝ)) /
            (2 * (primeAt n : ℝ) ^ (1 / 4 : ℝ)) ∧
          ((primeAt n : ℝ) / (n + 1 : ℝ)) /
            (2 * (primeAt n : ℝ) ^ (1 / 4 : ℝ)) ≤
              Real.log (primeAt n : ℝ) /
                (primeAt n : ℝ) ^ (1 / 4 : ℝ) := by
        filter_upwards [hevent, hp.eventually (eventually_gt_atTop (0 : ℝ))]
          with n hn hp0
        have hden : 0 < 2 * (primeAt n : ℝ) ^ (1 / 4 : ℝ) :=
          mul_pos (by norm_num) (Real.rpow_pos_of_pos hp0 _)
        constructor
        · positivity
        · rw [div_le_div_iff₀ hden]
          nlinarith [Real.rpow_pos_of_pos hp0 (1 / 4 : ℝ)]
      exact squeeze_zero' (by
        filter_upwards [hp.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
        positivity) (hbound.mono fun n hn => hn.2) hratio
    exact hfactor.congr' hrewrite.symm
  have hsum := hbase.add (by simpa [div_eq_mul_inv, mul_assoc] using htail)
  convert hsum.const_mul (1 / 2 : ℝ) using 1 <;> field_simp <;> ring

/-- The proportion of the first `N` prime gaps containing at least two
qualifying smooth integers tends to zero. -/
theorem twoHitGapCount_proportion_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (((Finset.range n).filter (fun r =>
        2 ≤ ((Finset.Ioo (primeAt r) (primeAt (r + 1))).filter
          (fun m => m.maxPrimeFac < primeGap r)).card)).card : ℝ) /
          (n + 1 : ℝ)) atTop (nhds 0) := by
  have hfirst : Tendsto (fun n : ℕ =>
      64 / Real.log (Real.log (primeAt n : ℝ))) atTop (nhds 0) := by
    have hll : Tendsto (fun n : ℕ => Real.log (Real.log (primeAt n : ℝ)))
        atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (by
          rw [tendsto_atTop_atTop]
          intro b
          refine ⟨b, fun n hbn => ?_⟩
          have hp := Nat.add_two_le_nth_prime n
          change b ≤ Nat.nth Nat.Prime n
          omega)))
    convert (tendsto_const_nhds.div_atTop hll).const_mul 64 using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have hsum := hfirst.add eventually_twoHitGapCount_tail_tendsto_zero
  apply squeeze_zero' (by
    filter_upwards [] with n
    positivity) (by
    filter_upwards [eventually_twoHitGapCount_bound] with n hn
    exact hn) hsum

end Implications.SmoothGapCounting
