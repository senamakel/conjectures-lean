import Mathlib

/-!
# Reciprocal primes in dyadic blocks

The smooth-number Rankin estimate for Erdős #932 needs control of a finite
Euler product.  Its first input is an upper bound for the reciprocal-prime
sum.  This file records the elementary dyadic consequence of Chebyshev's
upper bound, in the form used by the later Rankin argument.
-/

namespace Implications.SmoothPrimeReciprocal

open Filter

private theorem card_primes_Icc_eq_primeCounting (n : ℕ) :
    ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
  have hset : (Finset.Icc 1 n).filter Nat.Prime = Nat.primesLE n := by
    ext p
    simp [Nat.mem_primesLE]
  rw [hset, Nat.primesLE_card_eq_primeCounting]

/-- The reciprocal-prime mass in one dyadic block is `O(1/k)`. -/
private theorem reciprocalPrimeDyadic_eventually :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / p) ≤ D / (k + 1 : ℝ) := by
  let B : ℝ := Real.log 4 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hpi := Chebyshev.eventually_primeCounting_le (εpos := by norm_num : (0 : ℝ) < 1)
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ (k + 1)) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [hpow.eventually hpi] with k hk
  have hkcast :
      (Nat.primeCounting (2 ^ (k + 1)) : ℝ) ≤
        B * (2 : ℝ) ^ (k + 1) / Real.log ((2 : ℝ) ^ (k + 1)) := by
    simpa [B, Nat.floor_natCast, Real.log_pow] using hk
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : 0 < (k + 1 : ℝ) := by positivity
  have hblock :
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / p) ≤
      (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / (2 : ℝ) ^ k := by
    have hden : 0 < (2 : ℝ) ^ k := by positivity
    have hterm : ∀ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / p ≤ 1 / (2 : ℝ) ^ k := by
      intro p hp
      have hlow : (2 : ℝ) ^ k ≤ p := by
        exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
      exact one_div_le_one_div_of_le hden hlow
    have hcard : ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime).card ≤
        Nat.primeCounting (2 ^ (k + 1)) := by
      rw [← card_primes_Icc_eq_primeCounting]
      apply Finset.card_le_card
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_filter.mp hp).2.one_le,
          (Finset.mem_Ico.mp hp'.1).2.le⟩, hp'.2⟩
    calc
      _ ≤ ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          1 / (2 : ℝ) ^ k := Finset.sum_le_sum hterm
      _ = (((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime).card : ℝ) /
          (2 : ℝ) ^ k := by simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard)
          (by positivity)
  have hpow_succ : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [pow_succ]; ring
  have hlog_pow : Real.log ((2 : ℝ) ^ (k + 1)) = (k + 1 : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  refine ⟨(2 * B / Real.log 2), by positivity, ?_⟩
  calc
    _ ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / (2 : ℝ) ^ k := hblock
    _ ≤ (B * (2 : ℝ) ^ (k + 1) / Real.log ((2 : ℝ) ^ (k + 1))) /
        (2 : ℝ) ^ k := by
      exact div_le_div_of_nonneg_right hkcast (by positivity)
    _ = (2 * B / Real.log 2) / (k + 1 : ℝ) := by
      rw [hlog_pow, hpow_succ]
      field_simp

/-- A finite `O(log log N)` upper bound for the reciprocal primes through `N`.

The extra `1` inside the logarithm keeps the statement valid for small `N`.
The proof bins primes by `Nat.log 2 p`, applies the dyadic Chebyshev estimate,
then bounds the resulting harmonic sum. -/
theorem reciprocalPrimeSum_le_dyadic_harmonic :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ,
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 : ℝ) / p) ≤
        D * (1 + Real.log ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by
  obtain ⟨D₀, hD₀, hevent⟩ := reciprocalPrimeDyadic_eventually
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  let block (k : ℕ) : ℝ :=
    ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p
  let extra : ℝ := ∑ k ∈ Finset.Icc 0 K, (k + 1 : ℝ) * block k
  refine ⟨D₀ + extra + 1, ?_, ?_⟩
  · have hextra : 0 ≤ extra := by
      dsimp [extra]
      apply Finset.sum_nonneg
      intro k hk
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro p hp
      exact div_nonneg (by positivity) (by positivity)
    linarith
  · intro N
    classical
    let S := (Finset.Icc 1 N).filter Nat.Prime
    let T := Finset.Icc 0 (Nat.log 2 N)
    have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
      intro p hp
      have hp' := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.log_mono_right hp'.2⟩
    have hfiber : ∀ k ∈ T,
        (∑ p ∈ S.filter (fun p => Nat.log 2 p = k), (1 : ℝ) / p) ≤ block k := by
      intro k hk
      apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hprime := (Finset.mem_filter.mp hp'.1).2
      have hlog : Nat.log 2 p = k := hp'.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hprime⟩
      · simpa [hlog] using Nat.pow_log_le_self 2 hprime.ne_zero
      · simpa [hlog, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self Nat.one_lt_two p
    have hdecomp :
        (∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k), (1 : ℝ) / p) =
          ∑ p ∈ S, (1 : ℝ) / p :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    have hblocks :
        (∑ k ∈ T, block k) ≤ ∑ k ∈ T, D₀ / (k + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hlarge : K ≤ k
      · exact hK k hlarge
      · have hkK : k ∈ Finset.Icc 0 K := Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_of_not_ge hlarge⟩
        have hsingle : (k + 1 : ℝ) * block k ≤ extra := by
          exact Finset.single_le_sum
            (s := Finset.Icc 0 K) (fun i hi => by
              dsimp [block]
              apply mul_nonneg (by positivity)
              apply Finset.sum_nonneg
              intro p hp
              exact div_nonneg (by positivity) (by positivity)) hkK
        have hblock_nonneg : 0 ≤ block k := by
          dsimp [block]
          apply Finset.sum_nonneg
          intro p hp
          exact div_nonneg (by positivity) (by positivity)
        have hkpos : 0 < (k + 1 : ℝ) := by positivity
        apply (le_div_iff₀ hkpos).2
        dsimp [extra] at hsingle ⊢
        nlinarith
    have hsum_shift :
        (∑ k ∈ T, (1 : ℝ) / (k + 1 : ℝ)) =
          ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / j := by
      have himage : T.image (fun k : ℕ => k + 1) = Finset.Icc 1 (Nat.log 2 N + 1) := by
        ext j
        simp [T]
      have hinj : Set.InjOn (fun k : ℕ => k + 1) T := by
        intro a ha b hb hab
        omega
      rw [← himage, Finset.sum_image hinj]
      simp
    calc
      (∑ p ∈ S, (1 : ℝ) / p) =
          ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k), (1 : ℝ) / p := hdecomp.symm
      _ ≤ ∑ k ∈ T, block k := Finset.sum_le_sum hfiber
      _ ≤ ∑ k ∈ T, D₀ / (k + 1 : ℝ) := hblocks
      _ = D₀ * ∑ k ∈ T, (1 : ℝ) / (k + 1 : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = D₀ * ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / j := by rw [hsum_shift]
      _ ≤ D₀ * (1 + Real.log ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _)
        have hDblock := hK K (le_refl K)
        have hblocknonneg : 0 ≤ block K := by
          dsimp [block]
          apply Finset.sum_nonneg
          intro p hp
          exact div_nonneg (by positivity) (by positivity)
        positivity
      _ ≤ (D₀ + extra + 1) * (1 + Real.log ((Nat.log 2 N + 1 : ℕ) : ℝ)) := by
        have hfactor : 0 ≤ 1 + Real.log ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
          have : (1 : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
          have hl := Real.log_nonneg this
          linarith
        have hextra : 0 ≤ extra := by
          dsimp [extra]
          apply Finset.sum_nonneg
          intro k hk
          apply mul_nonneg (by positivity)
          dsimp [block]
          apply Finset.sum_nonneg
          intro p hp
          exact div_nonneg (by positivity) (by positivity)
        gcongr

end Implications.SmoothPrimeReciprocal
