import Schoenfeld.Density
import Schoenfeld.Psi1

/-!
# `ψ` at integers from the differenced explicit formula, under RH

erdos-985's weighted explicit formula (`explicit_formula_zeta`) gives, for natural `x ≥ 1`,

`Ψ₁(x) = x²/2 − Re Σ_ρ m x^{ρ+1}/(ρ(ρ+1)) + κ x + x E(x) + δ`

with constants `κ, δ` (sums over zeros and `ζ'/ζ(2)`) and `E(x) = Re Γ-part + log x ∈
[1 − 3/(2x), 1]`. Differencing between `a` and `b = a + h` cancels `δ`, and
`|b^{ρ+1} − a^{ρ+1}| ≤ min(|ρ+1| h √b, 2 b^{3/2})` bounds the zero part by `h √b F(2b/h)` with
`F(T) = Σ m min(1/|ρ|, T/|ρ|²)` (`Schoenfeld/Density.lean`). With
`h ψ(a) ≤ Ψ₁(b) − Ψ₁(a) ≤ h ψ(b)`:

* `psi_nat_upper`: `ψ(a) − a ≤ h/2 − 1.8 + 1.5/h + √b F(2b/h)`;
* `psi_nat_lower`: `b − ψ(b) ≤ h/2 + 2.6 + 1.5/h + √b F(2b/h)`;
* `psi_real_bound`: `|ψ(x) − x| ≤ h/2 + 3.6 + 1.5/h + √(x+h) F(2(x+h)/h)` for real
  `x ≥ h + 2`.
-/

namespace Schoenfeld

open Complex Erdos985.Analytic ArithmeticFunction Chebyshev

/-- `m · 2/(ρ(2−ρ))`. -/
noncomputable def tA (ρ : Zeros) : ℂ := (mult ρ : ℂ) * (2 / ((ρ : ℂ) * (2 - ρ)))
/-- `m · 1/((2−ρ)(1+ρ))`. -/
noncomputable def tB (ρ : Zeros) : ℂ := (mult ρ : ℂ) * (1 / ((2 - (ρ : ℂ)) * (1 + ρ)))
/-- `m · x^ρ/(ρ(ρ+1))`. -/
noncomputable def tW (x : ℕ) (ρ : Zeros) : ℂ :=
  (mult ρ : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))

section Norms

variable {ρ : ℂ}

lemma norm_pos_of_re (hρ : ρ.re = 1 / 2) : 0 < ‖ρ‖ :=
  norm_pos_iff.mpr fun h => by rw [h] at hρ; norm_num at hρ

lemma norm_two_sub' (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖(2 : ℂ) - ρ‖ := by
  rw [BoundsAux.norm_two_sub_eq hρ]; exact BoundsAux.norm_le_norm_add_one hρ

lemma norm_one_add' (hρ : ρ.re = 1 / 2) : ‖ρ‖ ≤ ‖(1 : ℂ) + ρ‖ := by
  rw [add_comm]; exact BoundsAux.norm_le_norm_add_one hρ

lemma norm_inv_mul_le {u v : ℂ} (hu : ‖ρ‖ ≤ ‖u‖) (hv : ‖ρ‖ ≤ ‖v‖) (h0 : 0 < ‖ρ‖) (c : ℝ)
    (hc : 0 ≤ c) {w : ℂ} (hw : ‖w‖ ≤ c) : ‖w / (u * v)‖ ≤ c / ‖ρ‖ ^ 2 := by
  rw [norm_div, norm_mul]
  have hu0 : 0 < ‖u‖ := h0.trans_le hu
  have hv0 : 0 < ‖v‖ := h0.trans_le hv
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖w‖ * ‖ρ‖ ^ 2 ≤ c * (‖u‖ * ‖v‖) := by
        rw [sq]; exact mul_le_mul hw (mul_le_mul hu hv h0.le hu0.le) (by positivity) hc
    _ = _ := rfl

end Norms

lemma norm_tA_le (hRH : RiemannHypothesis) (ρ : Zeros) :
    ‖tA ρ‖ ≤ 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have hρ := re_eq_half hRH ρ
  unfold tA
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mult_nonneg ρ)]
  have := norm_inv_mul_le le_rfl (norm_two_sub' hρ) (norm_pos_of_re hρ) 2 (by norm_num)
    (w := 2) (by simp)
  calc mult ρ * ‖2 / ((ρ : ℂ) * (2 - ρ))‖ ≤ mult ρ * (2 / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left this (mult_nonneg ρ)
    _ = _ := by ring

lemma norm_tB_le (hRH : RiemannHypothesis) (ρ : Zeros) :
    ‖tB ρ‖ ≤ mult ρ / ‖(ρ : ℂ)‖ ^ 2 := by
  have hρ := re_eq_half hRH ρ
  unfold tB
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mult_nonneg ρ)]
  have := norm_inv_mul_le (norm_two_sub' hρ) (norm_one_add' hρ) (norm_pos_of_re hρ) 1
    (by norm_num) (w := 1) (by simp)
  calc mult ρ * ‖1 / ((2 - (ρ : ℂ)) * (1 + ρ))‖ ≤ mult ρ * (1 / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left this (mult_nonneg ρ)
    _ = _ := by ring

lemma norm_cpow_nat (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(x : ℂ) ^ ρ‖ = √(x : ℝ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  rw [show (x : ℂ) = ((x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hρ,
    Real.sqrt_eq_rpow]

lemma norm_tW_le (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) (ρ : Zeros) :
    ‖tW x ρ‖ ≤ √(x : ℝ) * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) := by
  have hρ := re_eq_half hRH ρ
  unfold tW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mult_nonneg ρ)]
  have := norm_inv_mul_le le_rfl (BoundsAux.norm_le_norm_add_one hρ) (norm_pos_of_re hρ) _
    (Real.sqrt_nonneg _) (w := (x : ℂ) ^ (ρ : ℂ)) (norm_cpow_nat x hx hρ).le
  calc mult ρ * ‖(x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖
      ≤ mult ρ * (√(x : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := mul_le_mul_of_nonneg_left this (mult_nonneg ρ)
    _ = _ := by ring

lemma summable_tA (hRH : RiemannHypothesis) : Summable tA :=
  Summable.of_norm_bounded ((zeroSum_summable hRH).mul_left 2) (norm_tA_le hRH)

lemma summable_tB (hRH : RiemannHypothesis) : Summable tB :=
  Summable.of_norm_bounded (zeroSum_summable hRH) (norm_tB_le hRH)

lemma summable_tW (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) : Summable (tW x) :=
  Summable.of_norm_bounded ((zeroSum_summable hRH).mul_left _) (norm_tW_le hRH x hx)

/-- The constant `κ = Re Σ m · 2/(ρ(2−ρ)) − 7/2 − ζ'/ζ(2)`. -/
noncomputable def kappa : ℝ :=
  (∑' ρ, tA ρ).re - 7 / 2 - (deriv riemannZeta 2 / riemannZeta 2).re

/-- The constant `δ = 3 + ζ'/ζ(2) − 3 Re Σ m/((2−ρ)(1+ρ))`. -/
noncomputable def delta : ℝ :=
  3 + (deriv riemannZeta 2 / riemannZeta 2).re - 3 * (∑' ρ, tB ρ).re

/-- `E(x) = Re Γ-part + log x`. -/
noncomputable def Efun (x : ℕ) : ℝ := (gammaPart (1 : DirichletCharacter ℂ 1) x).re + Real.log x

/-- The explicit formula for `Ψ₁` at integers. -/
theorem psi1_nat_eq (hRH : RiemannHypothesis) (x : ℕ) (hx : 1 ≤ x) :
    psi1 x = (x : ℝ) ^ 2 / 2 - x * (∑' ρ, tW x ρ).re + kappa * x + x * Efun x + delta := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hid := explicit_formula_zeta x hx
  have hzt : ∀ ρ : Zeros, (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ
      = tA ρ - (3 / (x : ℂ)) * tB ρ - tW x ρ := by
    intro ρ
    rw [BoundsAux.zeroTerm_eq x hx (re_eq_half hRH ρ), tA, tB, tW, mult]
    push_cast
    ring
  simp_rw [hzt] at hid
  rw [Summable.tsum_sub ((summable_tA hRH).sub ((summable_tB hRH).mul_left _))
      (summable_tW hRH x hx), Summable.tsum_sub (summable_tA hRH) ((summable_tB hRH).mul_left _),
    tsum_mul_left] at hid
  have hre := congrArg Complex.re hid
  have hL2 : (deriv riemannZeta 2 / riemannZeta 2).im = 0 := (logDeriv_zeta_two_bound).1
  have hΓ : (gammaPart (1 : DirichletCharacter ℂ 1) x).im = 0 := (gammaPart_one_bound x hx).1
  have e3 : (3 / (x : ℂ)) = ((3 / x : ℝ) : ℂ) := by push_cast; rfl
  have e1 : (1 - 1 / (x : ℂ)) = ((1 - 1 / x : ℝ) : ℂ) := by push_cast; rfl
  have e2 : ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
      = (((x : ℝ) / 2 + Real.log x - 7 / 2 + 3 / x : ℝ) : ℂ) := by push_cast; rfl
  rw [e1, e2, e3] at hre
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul] at hre
  rw [psi1_nat x hx, hre, kappa, delta, Efun]
  field_simp
  ring

lemma kappa_bounds (hRH : RiemannHypothesis) : -2.6 ≤ kappa + 1 ∧ kappa + 1 ≤ -1.8 := by
  have hA : ‖∑' ρ, tA ρ‖ ≤ 2 * (1 / 20) := by
    calc ‖∑' ρ, tA ρ‖ ≤ ∑' ρ, 2 * (mult ρ / ‖(ρ : ℂ)‖ ^ 2) :=
          tsum_of_norm_bounded ((zeroSum_summable hRH).mul_left 2).hasSum (norm_tA_le hRH)
      _ = 2 * ∑' ρ, mult ρ / ‖(ρ : ℂ)‖ ^ 2 := tsum_mul_left
      _ ≤ 2 * (1 / 20) := by linarith [zeroSum_le hRH]
  have hAr := (Complex.abs_re_le_norm (∑' ρ, tA ρ)).trans hA
  obtain ⟨-, hl1, hl2⟩ := logDeriv_zeta_two_bound
  rw [abs_le] at hAr
  unfold kappa
  constructor <;> linarith [hAr.1, hAr.2]

lemma Efun_bounds (x : ℕ) (hx : 1 ≤ x) : (x : ℝ) - 3 / 2 ≤ x * Efun x ∧ x * Efun x ≤ x := by
  obtain ⟨-, h1, h2⟩ := gammaPart_one_bound x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  unfold Efun
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hx0.le
    have e : (x : ℝ) * (1 - 3 / (2 * x)) = x - 3 / 2 := by field_simp
    linarith
  · nlinarith

/-! ### The zero part of the difference -/

lemma cpow_succ_diff_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)‖ ≤ ‖ρ + 1‖ * ((b - a) * √b) := by
  have hρ1 : ρ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have hI := integral_cpow (a := a) (b := b) (r := ρ) (Or.inl (by rw [hρ]; norm_num))
  have e : (b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1) = (ρ + 1) * ∫ x in a..b, (x : ℂ) ^ ρ := by
    rw [hI]; field_simp
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun x : ℝ => (x : ℂ) ^ ρ) (C := √b) (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      have hx0 : 0 < x := ha.trans hx.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, hρ, ← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_sqrt hx.2)
  rw [abs_of_nonneg (by linarith)] at hb
  linarith

lemma norm_cpow_succ {b : ℝ} (hb : 0 < b) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖(b : ℂ) ^ (ρ + 1)‖ = b * √b := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, add_re, hρ, one_re,
    show (1 / 2 + 1 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

lemma nat_mul_cpow (x : ℕ) (hx : 1 ≤ x) (ρ : ℂ) :
    (x : ℂ) * (x : ℂ) ^ ρ = ((x : ℝ) : ℂ) ^ (ρ + 1) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  rw [show ((x : ℝ) : ℂ) = (x : ℂ) by push_cast; rfl, cpow_add _ _ hx0, cpow_one, mul_comm]

lemma tW_diff_le (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) (ρ : Zeros) :
    ‖((a + h : ℕ) : ℂ) * tW (a + h) ρ - (a : ℂ) * tW a ρ‖
      ≤ h * √((a + h : ℕ) : ℝ) * fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hρ := re_eq_half hRH ρ
  set b : ℕ := a + h with hbdef
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hbR : (b : ℝ) = a + h := by rw [hbdef]; push_cast; ring
  have hb0 : (0 : ℝ) < b := by rw [hbR]; linarith
  have hab : (a : ℝ) ≤ b := by rw [hbR]; linarith
  have hN := norm_pos_of_re hρ
  have hN1 := BoundsAux.norm_le_norm_add_one hρ
  have e : ((b : ℕ) : ℂ) * tW b ρ - (a : ℂ) * tW a ρ
      = (mult ρ : ℂ) * ((((b : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - ((a : ℝ) : ℂ) ^ ((ρ : ℂ) + 1))
        / ((ρ : ℂ) * ((ρ : ℂ) + 1))) := by
    unfold tW
    rw [← nat_mul_cpow b (by omega), ← nat_mul_cpow a ha]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (mult_nonneg ρ), norm_div, norm_mul]
  set D := ‖((b : ℝ) : ℂ) ^ ((ρ : ℂ) + 1) - ((a : ℝ) : ℂ) ^ ((ρ : ℂ) + 1)‖
  have hD1 : D ≤ ‖(ρ : ℂ) + 1‖ * (h * √(b : ℝ)) := by
    have := cpow_succ_diff_le ha0 hab hρ
    rwa [show (b : ℝ) - a = h by rw [hbR]; ring] at this
  have hD2 : D ≤ 2 * (b * √(b : ℝ)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_cpow_succ hb0 hρ, norm_cpow_succ ha0 hρ]
    have : (a : ℝ) * √(a : ℝ) ≤ b * √(b : ℝ) :=
      mul_le_mul hab (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg _) hb0.le
    linarith
  have hN10 : 0 < ‖(ρ : ℂ) + 1‖ := hN.trans_le hN1
  unfold fmin
  rw [show (h : ℝ) * √(b : ℝ) * (mult ρ * min (1 / ‖(ρ : ℂ)‖) (2 * b / h / ‖(ρ : ℂ)‖ ^ 2))
      = mult ρ * (h * √(b : ℝ) * min (1 / ‖(ρ : ℂ)‖) (2 * b / h / ‖(ρ : ℂ)‖ ^ 2)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (mult_nonneg ρ)
  rw [mul_min_of_nonneg _ _ (by positivity), le_min_iff]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    calc D ≤ ‖(ρ : ℂ) + 1‖ * (h * √(b : ℝ)) := hD1
      _ = h * √(b : ℝ) * (1 / ‖(ρ : ℂ)‖) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖) := by field_simp
  · rw [div_le_iff₀ (by positivity)]
    calc D ≤ 2 * (b * √(b : ℝ)) := hD2
      _ = h * √(b : ℝ) * (2 * b / h / ‖(ρ : ℂ)‖ ^ 2) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ)‖) := by
          field_simp
      _ ≤ h * √(b : ℝ) * (2 * b / h / ‖(ρ : ℂ)‖ ^ 2) * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖) := by
          gcongr

theorem zeroPart_diff_le (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    |((a + h : ℕ) : ℝ) * (∑' ρ, tW (a + h) ρ).re - (a : ℝ) * (∑' ρ, tW a ρ).re|
      ≤ h * √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hT : 0 ≤ 2 * ((a + h : ℕ) : ℝ) / h := by positivity
  have hsF := (fmin_summable hRH hT).mul_left (h * √((a + h : ℕ) : ℝ))
  have e : ((a + h : ℕ) : ℝ) * (∑' ρ, tW (a + h) ρ).re - (a : ℝ) * (∑' ρ, tW a ρ).re
      = (∑' ρ, (((a + h : ℕ) : ℂ) * tW (a + h) ρ - (a : ℂ) * tW a ρ)).re := by
    rw [Summable.tsum_sub ((summable_tW hRH _ (by omega)).mul_left _)
      ((summable_tW hRH a ha).mul_left _), tsum_mul_left, tsum_mul_left, Complex.sub_re]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [← tsum_mul_left]
  exact tsum_of_norm_bounded hsF.hasSum (tW_diff_le hRH a h ha hh)

/-- `Ψ₁(b) − Ψ₁(a)` for `b = a + h`. -/
theorem psi1_diff_bound (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    |psi1 ((a + h : ℕ) : ℝ) - psi1 a - ((((a + h : ℕ) : ℝ) ^ 2 - (a : ℝ) ^ 2) / 2
        + (kappa + 1) * h)|
      ≤ 3 / 2 + h * √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hb := psi1_nat_eq hRH (a + h) (by omega)
  have ha' := psi1_nat_eq hRH a ha
  have hZ := zeroPart_diff_le hRH a h ha hh
  obtain ⟨eb1, eb2⟩ := Efun_bounds (a + h) (by omega)
  obtain ⟨ea1, ea2⟩ := Efun_bounds a ha
  have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
  rw [hb, ha']
  rw [abs_le] at hZ ⊢
  rw [hbR] at eb1 eb2 hZ ⊢
  constructor <;> nlinarith [hZ.1, hZ.2]

theorem psi_nat_upper (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    ψ a - a ≤ h / 2 - 1.8 + 1.5 / h
      + √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hd := (psi1_diff (a : ℝ) h hh0.le).1
  have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
  have hB := psi1_diff_bound hRH a h ha hh
  rw [hbR] at hB ⊢
  have hk := kappa_bounds hRH
  set F := √((a : ℝ) + h) * ∑' ρ, fmin (2 * ((a : ℝ) + h) / h) ρ
  have hB' := (abs_le.mp hB).2
  have key : (h : ℝ) * (ψ a - a) ≤ h * (h / 2 - 1.8 + 1.5 / h + F) := by
    have e : (h : ℝ) * (1.5 / h) = 3 / 2 := by field_simp; norm_num
    nlinarith
  exact le_of_mul_le_mul_left key hh0

theorem psi_nat_lower (hRH : RiemannHypothesis) (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    ((a + h : ℕ) : ℝ) - ψ ((a + h : ℕ) : ℝ) ≤ h / 2 + 2.6 + 1.5 / h
      + √((a + h : ℕ) : ℝ) * ∑' ρ, fmin (2 * ((a + h : ℕ) : ℝ) / h) ρ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hd := (psi1_diff (a : ℝ) h hh0.le).2
  have hbR : ((a + h : ℕ) : ℝ) = a + h := by push_cast; ring
  have hB := psi1_diff_bound hRH a h ha hh
  rw [hbR] at hB ⊢
  have hk := kappa_bounds hRH
  set F := √((a : ℝ) + h) * ∑' ρ, fmin (2 * ((a : ℝ) + h) / h) ρ
  have hB' := (abs_le.mp hB).1
  have key : (h : ℝ) * ((a + h) - ψ (a + h)) ≤ h * (h / 2 + 2.6 + 1.5 / h + F) := by
    have e : (h : ℝ) * (1.5 / h) = 3 / 2 := by field_simp; norm_num
    nlinarith
  exact le_of_mul_le_mul_left key hh0

/-- The bound for real `x`. -/
theorem psi_real_bound (hRH : RiemannHypothesis) (x : ℝ) (h : ℕ) (hh : 1 ≤ h)
    (hx : (h : ℝ) + 2 ≤ x) :
    |ψ x - x| ≤ h / 2 + 3.6 + 1.5 / h + √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hx0 : 0 ≤ x := by linarith
  set n := ⌊x⌋₊ with hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hψ : ψ x = ψ n := by rw [psi_eq_psi_coe_floor]
  have hhn : h + 1 ≤ n := by
    have : ((h + 1 : ℕ) : ℝ) < (n : ℝ) + 1 := by push_cast; linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  -- monotonicity of the zero term
  have hmono : ∀ y : ℝ, 0 ≤ y → y ≤ x + h →
      √y * ∑' ρ, fmin (2 * y / h) ρ ≤ √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ := by
    intro y hy hyx
    have hT : 0 ≤ 2 * y / h := by positivity
    exact mul_le_mul (Real.sqrt_le_sqrt hyx) (fmin_tsum_mono hRH hT (by gcongr))
      (tsum_nonneg (fmin_nonneg hT)) (Real.sqrt_nonneg _)
  rw [hψ, abs_le]
  constructor
  · -- lower: `b = n = (n − h) + h`
    have hL := psi_nat_lower hRH (n - h) h (by omega) hh
    rw [show n - h + h = n by omega] at hL
    have := hmono n (by positivity) (by linarith)
    linarith
  · have hU := psi_nat_upper hRH n h (by omega) hh
    have := hmono ((n + h : ℕ) : ℝ) (by positivity) (by push_cast; linarith)
    linarith

end Schoenfeld
