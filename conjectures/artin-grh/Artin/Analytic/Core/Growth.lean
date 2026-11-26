import Artin.Analytic.Continuation
import Erdos985.Analytic.XiGrowth

/-!
# `ξ_K` has order at most one

`ContinuationData.xi_growth_aux`: `‖ξ_K(s)‖ ≤ C exp(C ‖s‖ log(‖s‖ + 2))` for all `s`, with `C`
depending on `K`. This is the body of `ContinuationData.xi_growth` (`Artin/Analytic/Core/Xi.lean`).

* For `Re s ≥ 2`, `ξ(s) = s (s - 1) |d|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)`. Here
  `|ζ_K(s)| ≤ ∑ a_n n^{-2}` (the Dirichlet series converges absolutely at `2`, by the ideal count
  `Ideal.tendsto_norm_le_div_atTop₀` behind Mathlib's class number formula), `|Γ(w)| ≤ Γ(Re w)`
  (`norm_Gamma_le_Gamma_re`, from Euler's integral), and `Γ(σ) ≤ (σ + 1)^{σ + 1}` for `σ ≥ 1`
  (`Gamma_le_exp`, from `Γ(σ) ≤ Γ(σ + 1) ≤ Γ(⌈σ⌉ + 1) = ⌈σ⌉!` and monotonicity on `[2, ∞)`).
* For `1/2 ≤ Re s ≤ 2` this is `D.strip_bound`.
* For `Re s < 1/2`, `ξ(s) = ξ(1 - s)`.

The bound is put in erdos-985's class `LogGrowth` (`‖F s‖ ≤ K exp(a (‖s‖ + b) log(‖s‖ + b))`) and
converted with `Erdos985.Analytic.growth_of_logGrowth`.
-/

namespace Artin.Analytic

open Complex NumberField MeasureTheory Filter Topology Erdos985.Analytic.XiOrderAux
open scoped Real

/-- `|Γ(s)| ≤ Γ(Re s)` for `Re s > 0`, from Euler's integral. -/
lemma norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, sub_re, one_re]

/-- `Γ(σ) ≤ exp((σ + 1) log(σ + 1))` for `σ ≥ 1`. -/
lemma Gamma_le_exp {σ : ℝ} (hσ : 1 ≤ σ) :
    Real.Gamma σ ≤ Real.exp ((σ + 1) * Real.log (σ + 1)) := by
  have hσ0 : 0 < σ := by linarith
  have h1 : Real.Gamma σ ≤ Real.Gamma (σ + 1) := by
    rw [Real.Gamma_add_one hσ0.ne']
    have := Real.Gamma_pos_of_pos hσ0
    nlinarith
  set N : ℕ := ⌈σ⌉₊ with hN
  have hσN : σ ≤ N := Nat.le_ceil σ
  have hNσ : (N : ℝ) < σ + 1 := Nat.ceil_lt_add_one hσ0.le
  have hN1 : (1 : ℝ) ≤ N := hσ.trans hσN
  have h2 : Real.Gamma (σ + 1) ≤ Real.Gamma (N + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith) (by simp; linarith)
      (by linarith)
  have h3 : Real.Gamma (N + 1) ≤ (N : ℝ) ^ N := by
    rw [Real.Gamma_nat_eq_factorial]; exact_mod_cast Nat.factorial_le_pow N
  have h4 : (N : ℝ) ^ N ≤ (σ + 1) ^ (σ + 1) := by
    calc (N : ℝ) ^ N ≤ (σ + 1) ^ N := pow_le_pow_left₀ (by linarith) hNσ.le N
      _ = (σ + 1) ^ (N : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (σ + 1) ^ (σ + 1) := Real.rpow_le_rpow_of_exponent_le (by linarith) hNσ.le
  rw [Real.rpow_def_of_pos (by linarith), mul_comm] at h4
  linarith

/-- `E(u) = (u + 3) log(u + 3) ≥ u + 3`. -/
lemma le_mul_log_add_three {u : ℝ} (hu : 0 ≤ u) : u + 3 ≤ (u + 3) * Real.log (u + 3) := by
  have := one_le_log_of_three_le (show 3 ≤ u + 3 by linarith)
  nlinarith

/-- `‖Γ_ℝ(s)‖ ≤ exp((‖s‖ + 3) log(‖s‖ + 3))` for `Re s ≥ 2`. -/
lemma norm_Gammaℝ_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Gammaℝ s‖ ≤ Real.exp ((‖s‖ + 3) * Real.log (‖s‖ + 3)) := by
  rw [Gammaℝ_def, norm_mul]
  have hpi : ‖(π : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    simp; linarith
  have hre : (s / 2).re = s.re / 2 := by simp
  have hG := norm_Gamma_le_Gamma_re (s := s / 2) (by rw [hre]; linarith)
  rw [hre] at hG
  have hG2 := Gamma_le_exp (σ := s.re / 2) (by linarith)
  have hsn : s.re ≤ ‖s‖ := re_le_norm s
  have hmono : (s.re / 2 + 1) * Real.log (s.re / 2 + 1) ≤
      (‖s‖ + 3) * Real.log (‖s‖ + 3) := ulogu_mono (by linarith) (by linarith)
  calc ‖(π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ ≤ 1 * ‖Complex.Gamma (s / 2)‖ := by
        gcongr
    _ ≤ Real.exp ((‖s‖ + 3) * Real.log (‖s‖ + 3)) := by
        rw [one_mul]
        exact hG.trans (hG2.trans (Real.exp_le_exp.2 hmono))

/-- `‖Γ_ℂ(s)‖ ≤ 2 exp((‖s‖ + 3) log(‖s‖ + 3))` for `Re s ≥ 2`. -/
lemma norm_Gammaℂ_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Gammaℂ s‖ ≤ 2 * Real.exp ((‖s‖ + 3) * Real.log (‖s‖ + 3)) := by
  rw [Gammaℂ_def, norm_mul, norm_mul, Complex.norm_two]
  have h2pi : ‖((2 * π : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    simp; linarith
  have hG := norm_Gamma_le_Gamma_re (s := s) (by linarith)
  have hG2 := Gamma_le_exp (σ := s.re) (by linarith)
  have hsn : s.re ≤ ‖s‖ := re_le_norm s
  have hmono : (s.re + 1) * Real.log (s.re + 1) ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) :=
    ulogu_mono (by linarith) (by linarith)
  have e : ((2 : ℂ) * π) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  calc 2 * ‖((2 * π : ℝ) : ℂ) ^ (-s)‖ * ‖Complex.Gamma s‖ ≤ 2 * 1 * ‖Complex.Gamma s‖ := by
        gcongr
    _ ≤ 2 * Real.exp ((‖s‖ + 3) * Real.log (‖s‖ + 3)) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (hG.trans (hG2.trans (Real.exp_le_exp.2 hmono)))
          (by norm_num)

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The Dirichlet series of `ζ_K` converges absolutely at `s = 2`. -/
lemma LSeriesSummable_dedekindZeta_two :
    LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 := by
  have hlim : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp,
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ring.HasFiniteQuotients.finite_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (f := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)) (r := 1) (s := 2)
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
    (fun _ => Nat.cast_nonneg _) zero_le_one (by norm_num)
  simpa using h

/-- `|ζ_K(s)| ≤ ∑ a_n n^{-2}` for `Re s ≥ 2`. -/
lemma norm_dedekindZeta_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖dedekindZeta K s‖ ≤ ∑' n, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ := by
  have h2 := LSeriesSummable_dedekindZeta_two K
  have hs' : LSeriesSummable
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s :=
    h2.of_re_le_re (by simpa using hs)
  rw [dedekindZeta, LSeries]
  refine (norm_tsum_le_tsum_norm hs'.norm).trans
    (hs'.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n)
      h2.norm)

namespace ContinuationData

variable (D : ContinuationData K)

/-- Bound for `Re s ≥ 2`. -/
lemma norm_xi_le_of_two_le_re : ∃ C a : ℝ, 0 ≤ a ∧ ∀ s : ℂ, 2 ≤ s.re →
    ‖D.ξ s‖ ≤ C * Real.exp (a * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) := by
  set Z2 := ∑' n, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖
  set ld := Real.log |(discr K : ℝ)|
  set r₁ := InfinitePlace.nrRealPlaces K
  set r₂ := InfinitePlace.nrComplexPlaces K
  have hd1 : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs (discr_ne_zero K)
    exact_mod_cast this
  have hld : 0 ≤ ld := Real.log_nonneg hd1
  refine ⟨2 ^ r₂ * Z2, 2 + ld + r₁ + r₂, by positivity, fun s hs => ?_⟩
  set E := (‖s‖ + 3) * Real.log (‖s‖ + 3) with hE
  have hsn : 0 ≤ ‖s‖ := norm_nonneg s
  have hE3 : ‖s‖ + 3 ≤ E := le_mul_log_add_three hsn
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  rw [D.ξ_eq s (by linarith) hs1, completedOf, gammaFactorK, D.isDedekindZeta.2 s (by linarith)]
  have hpoly : ‖s * (s - 1)‖ ≤ Real.exp (2 * E) := by
    rw [norm_mul]
    have h1 : ‖s - 1‖ ≤ ‖s‖ + 3 := (norm_sub_le _ _).trans (by simp)
    have h2 : ‖s‖ + 3 ≤ Real.exp E := by
      have := Real.add_one_le_exp E; linarith
    calc ‖s‖ * ‖s - 1‖ ≤ (‖s‖ + 3) * (‖s‖ + 3) := by gcongr; linarith
      _ ≤ Real.exp E * Real.exp E := by gcongr
      _ = Real.exp (2 * E) := by rw [← Real.exp_add]; ring_nf
  have hdisc : ‖(((|(discr K : ℝ)| : ℝ)) : ℂ) ^ (s / 2)‖ ≤ Real.exp (ld * E) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Real.rpow_def_of_pos (by linarith)]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hld)
    have : (s / 2).re ≤ ‖s‖ := by
      have := re_le_norm s; simp; linarith
    linarith
  have hR : ‖Gammaℝ s ^ r₁‖ ≤ Real.exp (r₁ * E) := by
    rw [norm_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_Gammaℝ_le hs) r₁
  have hC : ‖Gammaℂ s ^ r₂‖ ≤ 2 ^ r₂ * Real.exp (r₂ * E) := by
    rw [norm_pow, Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_Gammaℂ_le hs) r₂
  have hZ := norm_dedekindZeta_le (K := K) hs
  have hZ0 : 0 ≤ Z2 := tsum_nonneg fun _ => norm_nonneg _
  calc ‖s * (s - 1) * ((((|(discr K : ℝ)| : ℝ)) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ *
        Gammaℂ s ^ r₂ * dedekindZeta K s)‖
      = ‖s * (s - 1)‖ * (‖(((|(discr K : ℝ)| : ℝ)) : ℂ) ^ (s / 2)‖ * ‖Gammaℝ s ^ r₁‖ *
        ‖Gammaℂ s ^ r₂‖ * ‖dedekindZeta K s‖) := by simp only [norm_mul]
    _ ≤ Real.exp (2 * E) * (Real.exp (ld * E) * Real.exp (r₁ * E) *
          (2 ^ r₂ * Real.exp (r₂ * E)) * Z2) := by gcongr
    _ = 2 ^ r₂ * Z2 * Real.exp ((2 + ld + r₁ + r₂) * E) := by
        rw [show (2 + ld + r₁ + r₂) * E = 2 * E + ld * E + r₁ * E + r₂ * E by ring,
          Real.exp_add, Real.exp_add, Real.exp_add]
        ring

/-- **`ξ_K` has order at most one**: `‖ξ(s)‖ ≤ C exp(C ‖s‖ log(‖s‖ + 2))`. -/
theorem xi_growth_aux :
    ∃ C : ℝ, ∀ s : ℂ, ‖D.ξ s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨C₁, a, ha, h1⟩ := D.norm_xi_le_of_two_le_re
  obtain ⟨M, hM⟩ := D.strip_bound
  set K₁ := max C₁ |M| with hK₁
  set a₁ := max a 2 with ha₁
  have hK₁0 : 0 ≤ K₁ := (abs_nonneg M).trans (le_max_right _ _)
  have hhalf : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖D.ξ s‖ ≤ K₁ * Real.exp (a₁ * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) := by
    intro s hs
    set E := (‖s‖ + 3) * Real.log (‖s‖ + 3) with hE
    have hsn : 0 ≤ ‖s‖ := norm_nonneg s
    have hE3 : ‖s‖ + 3 ≤ E := le_mul_log_add_three hsn
    by_cases h2 : 2 ≤ s.re
    · calc ‖D.ξ s‖ ≤ C₁ * Real.exp (a * E) := h1 s h2
        _ ≤ K₁ * Real.exp (a * E) := by gcongr; exact le_max_left _ _
        _ ≤ K₁ * Real.exp (a₁ * E) := by
            gcongr
            · linarith
            · exact le_max_left _ _
    · push Not at h2
      have hexp : (1 + ‖s‖) ^ 2 ≤ Real.exp (2 * E) := by
        have h3 : ‖s‖ + 3 ≤ Real.exp E := by have := Real.add_one_le_exp E; linarith
        calc (1 + ‖s‖) ^ 2 ≤ Real.exp E ^ 2 := by gcongr; linarith
          _ = Real.exp (2 * E) := by rw [← Real.exp_nat_mul]; norm_num
      calc ‖D.ξ s‖ ≤ M * (1 + ‖s‖) ^ 2 := hM s hs h2.le
        _ ≤ |M| * (1 + ‖s‖) ^ 2 := by gcongr; exact le_abs_self M
        _ ≤ K₁ * Real.exp (2 * E) := by
            gcongr
            exact le_max_right _ _
        _ ≤ K₁ * Real.exp (a₁ * E) := by
            gcongr
            · linarith
            · exact le_max_right _ _
  have hLG : LogGrowth D.ξ := by
    refine ⟨K₁, a₁, 4, by positivity, by norm_num, fun s => ?_⟩
    have hsn : 0 ≤ ‖s‖ := norm_nonneg s
    by_cases hs : 1 / 2 ≤ s.re
    · refine (hhalf s hs).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (expo_mono (b := 3) (b' := 4) (by positivity) le_rfl (by norm_num) hsn (by linarith)))
        hK₁0)
    · push Not at hs
      rw [← D.ξ_one_sub s]
      refine (hhalf (1 - s) (by simp; linarith)).trans ?_
      have h1s : ‖1 - s‖ ≤ ‖s‖ + 1 := (norm_sub_le _ _).trans (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (expo_mono (b := 3) (b' := 4)
        (by positivity) le_rfl (by norm_num) (norm_nonneg _) (by linarith))) hK₁0
  exact Erdos985.Analytic.growth_of_logGrowth hLG

end ContinuationData

end Artin.Analytic
