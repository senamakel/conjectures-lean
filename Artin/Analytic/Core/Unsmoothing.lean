import Artin.Analytic.Core.ExplicitFormula

/-!
# From the weighted sum to `ψ_K` (blueprint A4)

The Cesàro weight is removed by differencing. For natural `y ≥ 1`,
`T(y) = y W_K(y) = ∑_{m=1}^{y} ψ_K(m)` (`mul_weightedPsiK_eq`), and `ψ_K` is non-decreasing
(`psiK_natCast_mono`), so for `1 ≤ h`

`T(x) - T(x - h) ≤ h ψ_K(x) ≤ T(x + h) - T(x)`.

Write `T(y) = y²/2 + E(y)` (`efError`). The explicit formula expresses `E(y)` through the zeros,
the gamma factors and two elementary terms (`efError_eq`). Its increments over `[y, y + h]` are
(under RH, uniformly in `K`, with `L(y) = log |d_K| + n log(y + 2)`):

* zeros (`zeroDiff_le`): `∑_ρ m_ρ |(y+h) zeroTerm(y+h, ρ) - y zeroTerm(y, ρ)| ≪ h √y L(y) log(y + 2)`;
* gamma factors (`gammaDiff_le`): `|(y+h) Γ_K(y+h) - y Γ_K(y)| ≤ n h (log(y + h) + 4)`;
* elementary terms: `≤ h (log(y + h) + 1 + 7/2 + 0.6 n)`.

Taking `h = ⌊√x⌋` gives `|ψ_K(x) - x| ≪ √x (log |d_K| + n log x) log x` (`psiK_natCast_le`), and
real `x` follows from `ψ_K(x) = ψ_K(⌈x⌉)` (`psiKBound_of_continuation`).

Only `zeroDiff_le` uses local zero counting: the zero term is
`h (1/(2 - ρ) + 1/ρ) - ((y+h)^{ρ+1} - y^{ρ+1})/(ρ(ρ+1))`; the first part is `2h/|ρ(ρ+1)|` (on
`Re ρ = 1/2`, `|2 - ρ| = |ρ + 1|`), summed by `zeroSum_le`; the second is
`≤ min(√(2y) h/|ρ|, 2 (2y)^{3/2}/|ρ|²)`, and summing over unit windows `|Im ρ - j| ≤ 1` with
`zeroCount_le`, splitting at `|Im ρ| = y/h`, gives `≪ h √y L(y) log(y + 2)`.
This is the standard unsmoothing (Davenport, *Multiplicative Number Theory*, §17–18, for `ζ`;
Lagarias–Odlyzko 1977, §9; Serre 1981, §2.4, Théorème 4).
-/

namespace Artin.Analytic

open Complex NumberField ArtinPrimitiveRootsConjecture Filter Topology Erdos985.Analytic

variable {K : Type*} [Field K] [NumberField K]

/-- `y W_K(y) = ∑_{m=1}^{y} ψ_K(m)`. -/
theorem mul_weightedPsiK_eq (y : ℕ) :
    (y : ℝ) * weightedPsiK K y = ∑ m ∈ Finset.Icc 1 y, psiK K m := by
  sorry

/-- `ψ_K` is non-decreasing on the natural numbers. -/
theorem psiK_natCast_mono : Monotone (fun m : ℕ => psiK K m) := by
  intro a b hab
  simp only [psiK_natCast_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hab)
    (fun n _ _ => vonMangoldtK_nonneg K n)

variable (K) in
/-- `E(y) = y W_K(y) - y²/2`. -/
noncomputable def efError (y : ℕ) : ℝ := (y : ℝ) * weightedPsiK K y - (y : ℝ) ^ 2 / 2

namespace ContinuationData

variable (D : ContinuationData K)

/-- The zero sum of the explicit formula. -/
noncomputable def zeroSum (y : ℕ) : ℂ :=
  ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℂ) * zeroTerm y ρ

/-- The explicit formula, multiplied by `y`: `E(y)` through zeros, gamma factors and elementary
terms. -/
theorem efError_eq (y : ℕ) (hy : 1 ≤ y) :
    efError K y = ((y : ℂ) * D.zeroSum y).re + ((y : ℂ) * gammaPartK K y).re
      + (y * Real.log y - 7 / 2 * y + 3) - (y - 1) * (deriv D.Z 2 / D.Z 2).re := by
  have h := congrArg Complex.re (congrArg (fun z => (y : ℂ) * z) (D.explicit_formula y hy))
  have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
  rw [efError]
  have e1 : ((y : ℂ) * ((weightedPsiK K y : ℝ) : ℂ)).re = y * weightedPsiK K y := by
    rw [← ofReal_natCast, ← ofReal_mul, ofReal_re]
  rw [← e1, h]
  rw [mul_sub, mul_add, mul_add, sub_re, add_re, add_re]
  simp only [zeroSum]
  have e2 : ((y : ℂ) * ((y : ℂ) / 2 + (Real.log y : ℂ) - 7 / 2 + 3 / (y : ℂ))).re
      = (y : ℝ) ^ 2 / 2 + (y * Real.log y - 7 / 2 * y + 3) := by
    have : (y : ℂ) * ((y : ℂ) / 2 + (Real.log y : ℂ) - 7 / 2 + 3 / (y : ℂ))
        = (((y : ℝ) ^ 2 / 2 + (y * Real.log y - 7 / 2 * y + 3) : ℝ) : ℂ) := by
      push_cast; field_simp; ring
    rw [this, ofReal_re]
  have e3 : ((y : ℂ) * ((1 - 1 / (y : ℂ)) * (deriv D.Z 2 / D.Z 2))).re
      = (y - 1) * (deriv D.Z 2 / D.Z 2).re := by
    have : (y : ℂ) * ((1 - 1 / (y : ℂ)) * (deriv D.Z 2 / D.Z 2))
        = (((y : ℝ) - 1 : ℝ) : ℂ) * (deriv D.Z 2 / D.Z 2) := by
      push_cast; field_simp
    rw [this, re_ofReal_mul]
  rw [e2, e3]
  ring

/-- **Zero increments** (the analytic heart of A4; see the module docstring). Under RH, with an
absolute constant, for `1 ≤ h ≤ y`:
`∑_ρ m_ρ |(y+h) zeroTerm(y+h, ρ) - y zeroTerm(y, ρ)| ≤ C₀ h √y (log |d_K| + n log(y+2)) log(y+2)`.
Proof: `zeroSum_le` for the part `h (1/(2-ρ) + 1/ρ)`; for the rest, `|w^{ρ+1}|` increments are
`≤ |ρ+1| h (2y)^{1/2}` and `≤ 2 (2y)^{3/2}`, and `zeroCount_le` on the windows
`|Im ρ - j| ≤ 1`, `j ∈ ℤ`, bounds `∑_{|Im ρ| ≤ y/h} m_ρ/|ρ|` by `≪ L log(y+2)` and
`∑_{|Im ρ| > y/h} m_ρ/|ρ|² ≪ L h/y`. -/
theorem zeroDiff_le :
    ∃ C₀ : ℝ, ∀ (K : Type) [Field K] [NumberField K] (D : ContinuationData K),
      DedekindZetaRH K → ∀ y h : ℕ, 1 ≤ h → h ≤ y →
      Summable (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℝ) *
        ‖((y + h : ℕ) : ℂ) * zeroTerm (y + h) ρ - (y : ℂ) * zeroTerm y ρ‖) ∧
      ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℝ) *
        ‖((y + h : ℕ) : ℂ) * zeroTerm (y + h) ρ - (y : ℂ) * zeroTerm y ρ‖ ≤
      C₀ * h * Real.sqrt y * (Real.log |(discr K : ℝ)| + Module.finrank ℚ K * Real.log (y + 2)) *
        Real.log (y + 2) := by
  sorry

end ContinuationData

/-- **Gamma increments**: `|(y+h) Γ_K(y+h) - y Γ_K(y)| ≤ n h (log(y+h) + 4)` for `y ≥ 2`.
Proof: `Γ_K = r₁ Γ⁰ + r₂ (Γ⁰ + Γ¹)` with `Γᵃ(y) = ∑_k tau y (2k+a)` (`gammaPartP_eq_tsum_tau`)
and `r₁ + 2 r₂ = n`; termwise, `y tau(y, m)` is explicit: for `m = 0` it is
`(y-1)/2 - y log y + y - 1`, for `m = 1` it is `(y-1)/3 - y + 1 + log y`, and for `m ≥ 2` it is
`(y-1)/(m+2) - y^{1-m}/(m(m-1)) - y/m + 1/(m-1)`, whose increment is
`≤ h (2/m² + 2^{1-m})`. -/
theorem gammaDiff_le (y h : ℕ) (hy : 2 ≤ y) :
    ‖((y + h : ℕ) : ℂ) * gammaPartK K (y + h) - (y : ℂ) * gammaPartK K y‖ ≤
      Module.finrank ℚ K * h * (Real.log (y + h) + 4) := by
  sorry

/-- **ψ_K at integers** under RH and Hecke's continuation, with an absolute constant. -/
theorem psiK_natCast_le :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (D : ContinuationData K),
      DedekindZetaRH K → ∀ x : ℕ, 2 ≤ x →
      |psiK K x - x| ≤ C * Real.sqrt x *
        (Real.log |(discr K : ℝ)| + Module.finrank ℚ K * Real.log x) * Real.log x := by
  sorry

/-- **The analytic core, per field** (blueprint A1–A4): RH for `ζ_K` and Hecke's continuation
give `PsiKBound K C`, with `C` absolute. -/
theorem psiKBound_of_continuation :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K],
      DedekindZetaRH K → DedekindContinuation K → PsiKBound K C := by
  sorry

end Artin.Analytic
