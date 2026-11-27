import Implications.SmoothGapInfinitude
import Implications.SmoothGapRankin
import Implications.SmoothPrimeReciprocal

/-! The weighted smooth-number estimate applied to the finite prime-gap cutoff. -/

namespace Implications.SmoothGapAnalytic

open SmoothGapCounting SmoothGapInfinitude SmoothGapRankin SmoothPrimeReciprocal

/-- The number of the first `N` prime gaps having at least `j` qualifying integers. -/
noncomputable def hitCount (N j : ℕ) : ℕ :=
  ((Finset.range N).filter (fun r => j ≤ (hits r).card)).card

/-- A uniform analytic bound on the finite cutoff estimate, with separate
terms for large gaps and for smooth numbers inside shorter gaps. -/
theorem hitCount_le_rankin_cutoff :
    ∃ D : ℝ, 0 < D ∧ ∀ (N B j : ℕ) (s : ℝ),
      2 ≤ B → 1 / 2 ≤ s → s ≤ 1 →
      (j : ℝ) * hitCount N j / (N + 1 : ℝ) ≤
        ((j : ℝ) * primeAt N / (N + 1 : ℝ)) / B +
          (1 + (primeAt N : ℝ) ^ s *
            Real.exp (4 * (B : ℝ) ^ (1 - s) * D *
              (1 + Real.log (((Nat.log 2 B + 1 : ℕ) : ℝ)))) / (N + 1 : ℝ) := by
  obtain ⟨D, hD, hproduct⟩ := primeEulerProduct_rankin_bound
  refine ⟨D, hD, fun N B j s hB hslo hshi => ?_⟩
  have hp : 0 < primeAt N := (Nat.prime_nth_prime N).pos
  have hs : 0 < s := by linarith
  have hBpos : 0 < B := by omega
  have hweight (p : ℕ) : rankinWeight s p = ((p : ℝ) ^ s)⁻¹ := by
    change (p : ℝ) ^ (-s) = _
    exact Real.rpow_neg (by positivity) _
  have hcount := smoothNumbersUpTo_card_le_rankin (primeAt N) B s hp hs
  simp only [hweight] at hcount
  have hM := hcount.trans (mul_le_mul_of_nonneg_left (hproduct B s hB hslo hshi)
    (Real.rpow_nonneg (by positivity : 0 ≤ (primeAt N : ℝ)) _))
  simpa [hitCount, hits] using
    hitIndexProportionBound_of_smoothNumbersUpTo N B j hBpos _ hM

#print axioms hitCount_le_rankin_cutoff

end Implications.SmoothGapAnalytic
