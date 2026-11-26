import Erdos985.Analytic.ExplicitFormula.Bounds.GammaPart
import Erdos985.Analytic.ExplicitFormula.Bounds.LogDeriv

/-!
# The gamma part for the character mod 1, and `ζ'/ζ(2)`
-/

open Complex MeasureTheory Filter Topology ArithmeticFunction

namespace Erdos985.Analytic.PrincipalAux

open BoundsAux

/-- Refinement of `tsum_tau_bound` for `a = 0`: `Σ_k tau x (2k) + log x ∈ [1 − 3/(2x), 1]`. -/
theorem tsum_tau_even_bound (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => tau x (2 * k)) ∧
      1 - 3 / (2 * x) ≤ ∑' k : ℕ, tau x (2 * k) + Real.log x ∧
      ∑' k : ℕ, tau x (2 * k) + Real.log x ≤ 1 := by
  have hup : ∀ k : ℕ, tau x (2 * (k + 1)) ≤
      (3 * (1 / x) - 1) / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := fun k =>
    tau_le_even x hx k
  have hlo : ∀ k : ℕ, -(1 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ tau x (2 * (k + 1)) :=
    fun k => tau_ge x hx k (2 * (k + 1)) le_rfl
  have hS : Summable (fun k : ℕ => tau x (2 * k)) := by
    simpa using (tsum_tau_bound x hx 0 (by norm_num)).1
  have hg : Summable (fun k : ℕ => tau x (2 * (k + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k)) 1).mpr hS
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq_zero_add]
  have hle : ∑' k : ℕ, tau x (2 * (k + 1)) ≤ (3 * (1 / x) - 1) / 2 := by
    have := Summable.tsum_le_tsum hup hg (hasSum_u.summable.mul_left _)
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  have hge : -(1 / 2) ≤ ∑' k : ℕ, tau x (2 * (k + 1)) := by
    have := Summable.tsum_le_tsum hlo (hasSum_u.summable.mul_left _) hg
    rwa [tsum_mul_left, hasSum_u.tsum_eq, mul_one] at this
  have h0 : tau x (2 * 0) = (1 - 1 / x) / 2 - (Real.log x - 1 + 1 / x) := by simp [tau]
  rw [h0]
  have e : 3 / (2 * x) = 3 / 2 * (1 / x) := by field_simp
  rw [e]
  constructor <;> linarith

/-- `gammaPart χ x = Σ_k tau x (2k + a)`. -/
theorem gammaPart_eq_tsum_tau {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ)
    (hx : 1 ≤ x) :
    gammaPart χ x = ((∑' k : ℕ, tau x (2 * k + parity χ) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hsum : ∀ t : ℝ, (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) *
      (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, gTerm x (2 * k + parity χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    exact (((hasSum_gammaLogDeriv χ hs).mul_right _).div_const _).tsum_eq.symm
  have hnorm : ∀ m : ℕ, ∫ t, ‖gTerm x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖gTerm x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (integrable_gTerm x hx m).norm (hQi.norm.const_mul _)
            (fun t => norm_gTerm_le x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖gTerm x (2 * k + parity χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hgp : gammaPart χ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, gTerm x (2 * k + parity χ) t := by
    unfold gammaPart
    congr 1
    congr 1
    funext t
    exact hsum t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => integrable_gTerm x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [integral_gTerm x hx]
  rw [← Complex.ofReal_tsum]

lemma parity_one : parity (1 : DirichletCharacter ℂ 1) = 0 := by
  simp [parity, DirichletCharacter.Even]

theorem gammaPart_one_bound' (x : ℕ) (hx : 1 ≤ x) :
    (gammaPart (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
    1 - 3 / (2 * (x : ℝ)) ≤ (gammaPart (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
    (gammaPart (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
  rw [gammaPart_eq_tsum_tau _ x hx, parity_one]
  simp only [add_zero, Complex.ofReal_im, Complex.ofReal_re, true_and]
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  exact (tsum_tau_even_bound x hx1).2

theorem logDeriv_zeta_two_bound' :
    (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
    -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧
      (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div re2
  have e : deriv riemannZeta 2 / riemannZeta 2
      = -((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [← lseries_eq2 (fun n => (Λ n : ℝ)), key]; ring
  rw [e]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re,
    true_and]
  have hS := S2_le
  have h0 : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  constructor <;> linarith

end Erdos985.Analytic.PrincipalAux
