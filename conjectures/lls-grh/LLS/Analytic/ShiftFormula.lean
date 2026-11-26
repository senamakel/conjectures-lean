import LLS.Defs
import LLS.Analytic.Shift.ZeroPart

/-! # LLS Lemma 2.3: the shifted Cesàro explicit formula, under GRH

Assembly of `LLS.ShiftAux.shift_identity` (Perron + Hadamard, exact),
`LLS.ShiftAux.zeroPart_eq` (the zero sum, `|Z| ≤ Z2/√x`), the functional equation
`D(0, χ) = −(log N + D(1, χ⁻¹))` and `LLS.ShiftAux.re_gamma_shift_le` (gamma part).
-/

namespace LLS

open Complex Erdos985 Erdos985.Analytic ShiftAux

variable {N : ℕ} [NeZero N]

/-- LLS Lemma 2.3 (one-sided form), Mathlib normalisation:
`Re Σ_{n<x} Λ(n)χ(n)/n (1 − n/x) ≤ −Re D(1, χ) − (log N + Re D(1, χ⁻¹))/x + Z2/√x + E(x)`.
It comes from `Σ_{n<x} … = −D(1, χ) + D(0, χ)/x − Σ_ρ m_ρ x^{ρ−1}/(ρ(ρ−1)) + Γ''(x)`. -/
theorem re_cesShift_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 2 ≤ x) :
    (cesShift χ x).re ≤ -(D χ 1).re - (Real.log N + (D χ⁻¹ 1).re) / x
      + Z2 χ / √(x : ℝ) + Eshift x := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  obtain ⟨Z, hZ, hZeq⟩ := zeroPart_eq hGRH hprim hχ x hx1
  have hid := shift_identity hGRH hprim hχ x hx1
  have hc3 := logDeriv_LFunction_eq hχ (s := 3) (by norm_num)
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ (s := 1)
    (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) (by norm_num))
  rw [sub_self] at hFE
  have hD0 : D χ 0 = -((Real.log N : ℂ) + D χ⁻¹ 1) := by
    unfold D; rw [← hFE]; ring
  have hmain : cesShift χ x = -D χ 1 + D χ 0 / x - Z
      + (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3) := by
    rw [hid, hZeq, hc3]
    unfold D
    ring
  have hG := re_gamma_shift_le χ x hx1
  have hre0 : (D χ 0 / (x : ℂ)).re = -(Real.log N + (D χ⁻¹ 1).re) / x := by
    rw [Complex.div_natCast_re, hD0, neg_re, add_re, ofReal_re]
  have hZre : -Z.re ≤ Z2 χ / √(x : ℝ) := by
    have := Complex.abs_re_le_norm Z
    have := neg_abs_le Z.re
    linarith
  have hre : (cesShift χ x).re = -(D χ 1).re + (D χ 0 / (x : ℂ)).re - Z.re
      + (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re := by
    rw [hmain, add_re, sub_re, add_re, neg_re]
  rw [hre, hre0, neg_div]
  linarith

end LLS
