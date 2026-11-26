import Mathlib
import Vendor.PNT.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
import Vendor.PNT.PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
import Erdos985.Analytic.Hadamard.Fiber

/-!
# Hadamard factorization, logarithmic-derivative form, for entire functions of order ≤ 1

If `f` is entire, `f 0 ≠ 0`, and `‖f z‖ ≤ C exp(C ‖z‖ log(‖z‖ + 2))`, then the zeros `ρ`
(with multiplicity `m ρ`) satisfy `Σ m ρ / ‖ρ‖^(1+ε) < ∞` for every `ε > 0`, and
`f'/f (z) = b + Σ_ρ m ρ (1/(z - ρ) + 1/ρ)` away from the zeros.

The proof uses the general finite-order Hadamard factorization vendored from
PrimeNumberTheoremAnd (`Vendor/PNT`), whose zeros are indexed with multiplicity by
`Complex.Hadamard.divisorZeroIndex₀`; `Erdos985.Analytic.HadamardAux.hasSum_weighted`
converts those sums into multiplicity-weighted sums over `{ρ // f ρ = 0}`.
-/

namespace Erdos985.Analytic

open Complex.Hadamard HadamardAux

theorem hadamard_logDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + ε)) ∧
    ∃ b : ℂ, ∀ z : ℂ, f z ≠ 0 →
      Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) ∧
      deriv f z / f z = b + ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  have hord := entireOfOrderAtMost_one hf hf0 hgrowth
  have hnot : ∃ z, f z ≠ 0 := ⟨0, hf0⟩
  have hsum2 : Summable (fun p : divisorZeroIndex₀ f Set.univ =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
    simpa [Nat.floor_one] using hord.summable_norm_inv_pow_divisorZeroIndex₀ (by norm_num) hnot
  constructor
  · intro ε hε
    obtain ⟨C', hC', hlog⟩ :=
      hord.exists_log_growth (τ := 1 + ε / 2) (by linarith) (by linarith)
    have hs := summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (τ := 1 + ε)
      (by linarith) (by linarith) hf hnot ⟨C', hC', hlog⟩
    have hW := hasSum_weighted hf hf0 (fun x : ℂ => ‖x‖⁻¹ ^ (1 + ε)) hs.hasSum
    refine hW.summable.congr fun ρ => ?_
    simp [nsmul_eq_mul, Real.inv_rpow (norm_nonneg _), div_eq_mul_inv]
  · obtain ⟨P, hdeg, hfac⟩ :=
      hadamard_factorization_of_order (by norm_num : (0 : ℝ) ≤ 1) hnot hord
    refine ⟨P.coeff 1, fun z hz => ?_⟩
    have hz' : ∀ p : divisorZeroIndex₀ f Set.univ, z ≠ divisorZeroIndex₀_val p :=
      fun p h => hz (h ▸ val_isZero hf p)
    have hS := summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq hsum2 hz'
    have hW := hasSum_weighted hf hf0 (fun x : ℂ => 1 / (z - x) + 1 / x) hS.hasSum
    simp only [nsmul_eq_mul] at hW
    refine ⟨hW.summable, ?_⟩
    rw [hW.tsum_eq]
    have h0 : analyticOrderNatAt f 0 = 0 := by
      by_contra h
      exact hf0 (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
    set G : ℂ → ℂ := divisorCanonicalProduct 1 f Set.univ with hG
    have hfun : f = fun w => Complex.exp (Polynomial.eval w P) * G w := by
      funext w
      simpa [h0, G, Nat.floor_one] using hfac w
    have hdiff_exp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Polynomial.eval w P)) z :=
      (P.differentiable.differentiableAt (x := z)).cexp
    have hG0 : G z ≠ 0 := divisorCanonicalProduct_ne_zero_of_forall_ne 1 f hsum2 hz'
    have hGd : DifferentiableAt ℂ G z := differentiableAt_divisorCanonicalProduct_univ 1 f hsum2 z
    have hP1 : Polynomial.eval z P.derivative = P.coeff 1 := by
      have hdeg' : P.degree ≤ 1 := by simpa [Nat.floor_one] using hdeg
      rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg']
      simp
    have hL : logDeriv f z = logDeriv ((fun w : ℂ => Complex.exp (Polynomial.eval w P)) * G) z := by
      conv_lhs => rw [hfun]
      rfl
    rw [← logDeriv_apply, hL, logDeriv_mul (f := fun w : ℂ => Complex.exp (Polynomial.eval w P)) (g := G) z
        (Complex.exp_ne_zero _) hG0 hdiff_exp hGd,
      Polynomial.logDeriv_exp_eval, hP1,
      logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne hsum2 hz']

end Erdos985.Analytic
