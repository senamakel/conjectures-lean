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
* gamma factors (`gammaDiff_le`): `|(y+h) Γ_K(y+h) - y Γ_K(y)| ≤ n h (log(y + h) + 8)`;
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
  Erdos985.Analytic.BoundsAux

variable {K : Type*} [Field K] [NumberField K]

/-- `y W_K(y) = ∑_{m=1}^{y} ψ_K(m)`. -/
theorem mul_weightedPsiK_eq (y : ℕ) :
    (y : ℝ) * weightedPsiK K y = ∑ m ∈ Finset.Icc 1 y, psiK K m := by
  have hS : ∀ y : ℕ, (y : ℝ) * weightedPsiK K y =
      ∑ n ∈ Finset.range y, vonMangoldtK K n * ((y : ℝ) - n) := by
    intro y
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp [weightedPsiK]
    have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [weightedPsiK, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  rw [hS]
  induction y with
  | zero => simp
  | succ y ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih, psiK_natCast_eq_sum, Finset.sum_range_succ,
      Finset.sum_range_succ (fun n => vonMangoldtK K n)]
    push_cast
    have : ∑ n ∈ Finset.range y, vonMangoldtK K n * ((y : ℝ) + 1 - n) =
        ∑ n ∈ Finset.range y, vonMangoldtK K n * ((y : ℝ) - n) +
          ∑ n ∈ Finset.range y, vonMangoldtK K n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    ring

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

lemma log_add_sub_log_le {y h : ℝ} (hy : 0 < y) (hh : 0 ≤ h) :
    0 ≤ Real.log (y + h) - Real.log y ∧ y * (Real.log (y + h) - Real.log y) ≤ h := by
  refine ⟨sub_nonneg.2 (Real.log_le_log hy (by linarith)), ?_⟩
  rw [← Real.log_div (by linarith) hy.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (y + h) / y by positivity)
  have e : (y + h) / y - 1 = h / y := by field_simp; ring
  rw [e] at this
  calc y * Real.log ((y + h) / y) ≤ y * (h / y) := mul_le_mul_of_nonneg_left this hy.le
    _ = h := by field_simp

lemma mul_tau_incr_zero {y h : ℝ} (hy : 1 ≤ y) (hh : 0 ≤ h) :
    |(y + h) * tau (y + h) 0 - y * tau y 0| ≤ h * (Real.log (y + h) + 2) := by
  have e : ∀ x : ℝ, 0 < x → x * tau x 0 = (x - 1) / 2 - x * Real.log x + x - 1 := by
    intro x hx; simp only [tau, ↓reduceIte]; field_simp; ring
  rw [e _ (by linarith), e _ (by linarith)]
  obtain ⟨h1, h2⟩ := log_add_sub_log_le (y := y) (h := h) (by linarith) hh
  have hL : 0 ≤ Real.log (y + h) := Real.log_nonneg (by linarith)
  have hyl : 0 ≤ y * (Real.log (y + h) - Real.log y) := mul_nonneg (by linarith) h1
  rw [abs_le]; constructor <;> nlinarith

lemma mul_tau_incr_one {y h : ℝ} (hy : 1 ≤ y) (hh : 0 ≤ h) :
    |(y + h) * tau (y + h) 1 - y * tau y 1| ≤ h := by
  have e : ∀ x : ℝ, 0 < x → x * tau x 1 = (x - 1) / 3 - x + 1 + Real.log x := by
    intro x hx; simp only [tau, one_ne_zero, ↓reduceIte]; field_simp; ring
  rw [e _ (by linarith), e _ (by linarith)]
  obtain ⟨h1, h2⟩ := log_add_sub_log_le (y := y) (h := h) (by linarith) hh
  have : Real.log (y + h) - Real.log y ≤ h := by nlinarith
  rw [abs_le]; constructor <;> nlinarith

lemma mul_tau_incr_ge_two {y h : ℝ} (hy : 1 ≤ y) (hh : 1 ≤ h) {m : ℕ} (hm : 2 ≤ m) :
    |(y + h) * tau (y + h) m - y * tau y m| ≤ 3 * h / ((m : ℝ) * (m - 1)) := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set A : ℝ → ℝ := fun x => x * (1 / x) ^ m with hA
  have hAb : ∀ x : ℝ, 1 ≤ x → 0 ≤ A x ∧ A x ≤ 1 := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have e : A x = (1 / x) ^ (m - 1) := by
      simp only [hA]
      rw [show m = (m - 1) + 1 by omega, pow_succ]
      simp only [Nat.add_sub_cancel]
      field_simp
    rw [e]
    have h0 : 0 ≤ 1 / x := by positivity
    have h1 : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
    exact ⟨pow_nonneg h0 _, pow_le_one₀ h0 h1⟩
  have e : ∀ x : ℝ, 0 < x → x * tau x m =
      (x - 1) / (2 + m) - A x / (m * (m - 1)) - x / m + 1 / (m - 1) := by
    intro x hx
    simp only [tau, hm0, hm1, ↓reduceIte, hA]
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    have : (m : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [e _ (by linarith), e _ (by linarith)]
  obtain ⟨a0, a1⟩ := hAb (y + h) (by linarith)
  obtain ⟨b0, b1⟩ := hAb y hy
  have hmm : 0 < (m : ℝ) * (m - 1) := by nlinarith
  have key : (y + h - 1) / (2 + m) - A (y + h) / (m * (m - 1)) - (y + h) / m + 1 / (m - 1) -
      ((y - 1) / (2 + m) - A y / (m * (m - 1)) - y / m + 1 / (m - 1)) =
      -(2 * h / (m * (2 + m))) + (A y - A (y + h)) / (m * (m - 1)) := by
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    have : (m : ℝ) ≠ 0 := by linarith
    have : (2 : ℝ) + m ≠ 0 := by linarith
    field_simp
    ring
  rw [key]
  have t1 : 2 * h / (m * (2 + m)) ≤ 2 * h / ((m : ℝ) * (m - 1)) :=
    div_le_div_of_nonneg_left (by linarith) hmm (by nlinarith)
  have t2 : |(A y - A (y + h)) / (m * (m - 1))| ≤ h / ((m : ℝ) * (m - 1)) := by
    rw [abs_div, abs_of_pos hmm]
    exact div_le_div_of_nonneg_right (by rw [abs_le]; constructor <;> linarith) hmm.le
  have t0 : 0 ≤ 2 * h / (m * (2 + m)) := by positivity
  calc |-(2 * h / (m * (2 + m))) + (A y - A (y + h)) / (m * (m - 1))|
      ≤ |-(2 * h / (m * (2 + m)))| + |(A y - A (y + h)) / (m * (m - 1))| := abs_add_le _ _
    _ ≤ 2 * h / ((m : ℝ) * (m - 1)) + h / ((m : ℝ) * (m - 1)) := by
        rw [abs_neg, abs_of_nonneg t0]; linarith
    _ = 3 * h / ((m : ℝ) * (m - 1)) := by ring

/-- Increment of `x ∑_k tau x (2k + a)`. -/
lemma tsum_tau_incr_le {y h : ℝ} (hy : 1 ≤ y) (hh : 1 ≤ h) {a : ℕ} (ha : a ≤ 1) :
    |(y + h) * ∑' k : ℕ, tau (y + h) (2 * k + a) - y * ∑' k : ℕ, tau y (2 * k + a)| ≤
      |(y + h) * tau (y + h) a - y * tau y a| + 3 * h := by
  obtain ⟨s1, -⟩ := tsum_tau_bound (y + h) (by linarith) a ha
  obtain ⟨s2, -⟩ := tsum_tau_bound y hy a ha
  set f : ℕ → ℝ := fun k => (y + h) * tau (y + h) (2 * k + a) - y * tau y (2 * k + a) with hf
  have hfs : Summable f := (s1.mul_left (y + h)).sub (s2.mul_left y)
  have e : (y + h) * ∑' k : ℕ, tau (y + h) (2 * k + a) - y * ∑' k : ℕ, tau y (2 * k + a) =
      ∑' k, f k := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (s1.mul_left (y + h)).tsum_sub (s2.mul_left y)]
  rw [e, hfs.tsum_eq_zero_add]
  have h0 : f 0 = (y + h) * tau (y + h) a - y * tau y a := by simp [hf]
  rw [h0]
  refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
  have hb : ∀ k : ℕ, ‖f (k + 1)‖ ≤ 3 * h * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    intro k
    rw [Real.norm_eq_abs]
    have hm : 2 ≤ 2 * (k + 1) + a := by omega
    refine (mul_tau_incr_ge_two hy hh hm).trans ?_
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have hm' : (2 * (k : ℝ) + 2) ≤ ((2 * (k + 1) + a : ℕ) : ℝ) := by push_cast; linarith
    rw [mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
    have : ((k : ℝ) + 1) * (k + 2) ≤ ((2 * (k + 1) + a : ℕ) : ℝ) * (((2 * (k + 1) + a : ℕ) : ℝ) - 1) := by
      nlinarith
    nlinarith
  have hsu := hasSum_u.summable.mul_left (3 * h)
  calc |∑' k, f (k + 1)| = ‖∑' k, f (k + 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, 3 * h * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) :=
        tsum_of_norm_bounded hsu.hasSum hb
    _ = 3 * h := by rw [tsum_mul_left, hasSum_u.tsum_eq, mul_one]

/-- **Gamma increments**: `|(y+h) Γ_K(y+h) - y Γ_K(y)| ≤ n h (log(y+h) + 8)` for `y ≥ 1`.
Proof: `Γ_K = r₁ Γ⁰ + r₂ (Γ⁰ + Γ¹)` with `Γᵃ(y) = ∑_k tau y (2k+a)` (`gammaPartP_eq_tsum_tau`)
and `r₁ + 2 r₂ = n`; termwise, `y tau(y, m)` is explicit: for `m = 0` it is
`(y-1)/2 - y log y + y - 1`, for `m = 1` it is `(y-1)/3 - y + 1 + log y`, and for `m ≥ 2` it is
`(y-1)/(m+2) - y^{1-m}/(m(m-1)) - y/m + 1/(m-1)`, whose increment is
`≤ 2h/m² + 1/(m(m-1))`. -/
theorem gammaDiff_le (y h : ℕ) (hy : 1 ≤ y) :
    ‖((y + h : ℕ) : ℂ) * gammaPartK K (y + h) - (y : ℂ) * gammaPartK K y‖ ≤
      Module.finrank ℚ K * h * (Real.log (y + h) + 8) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set Y : ℝ := (y : ℝ) with hY
  set H : ℝ := (h : ℝ) with hH
  set Δ : ℕ → ℝ := fun a => (Y + H) * ∑' k : ℕ, tau (Y + H) (2 * k + a) -
    Y * ∑' k : ℕ, tau Y (2 * k + a) with hΔ
  have hL : 0 ≤ Real.log (Y + H) := Real.log_nonneg (by linarith)
  have hΔ0 : |Δ 0| ≤ H * (Real.log (Y + H) + 5) := by
    have := tsum_tau_incr_le hyR hhR (a := 0) (by norm_num)
    have h0 := mul_tau_incr_zero hyR (by linarith : (0 : ℝ) ≤ H)
    simp only [hΔ]; simp only [add_zero] at this ⊢
    linarith
  have hΔ1 : |Δ 1| ≤ 4 * H := by
    have := tsum_tau_incr_le hyR hhR (a := 1) le_rfl
    have h1 := mul_tau_incr_one hyR (by linarith : (0 : ℝ) ≤ H)
    simp only [hΔ]; linarith
  have hgp : ∀ (a x : ℕ), 1 ≤ x → gammaPartP a x = ((∑' k : ℕ, tau x (2 * k + a) : ℝ) : ℂ) :=
    fun a x hx => gammaPartP_eq_tsum_tau a x hx
  have e : ((y + h : ℕ) : ℂ) * gammaPartK K (y + h) - (y : ℂ) * gammaPartK K y =
      (InfinitePlace.nrRealPlaces K : ℂ) * (Δ 0 : ℂ) +
        (InfinitePlace.nrComplexPlaces K : ℂ) * ((Δ 0 : ℂ) + (Δ 1 : ℂ)) := by
    simp only [gammaPartK, hgp 0 (y + h) (by omega), hgp 1 (y + h) (by omega), hgp 0 y hy,
      hgp 1 y hy, hΔ, Y, H]
    push_cast
    ring
  rw [e]
  have hrk : (InfinitePlace.nrRealPlaces K : ℝ) + 2 * InfinitePlace.nrComplexPlaces K =
      Module.finrank ℚ K := by exact_mod_cast InfinitePlace.card_add_two_mul_card_eq_rank K
  have hr1 : (0 : ℝ) ≤ InfinitePlace.nrRealPlaces K := Nat.cast_nonneg _
  have hr2 : (0 : ℝ) ≤ InfinitePlace.nrComplexPlaces K := Nat.cast_nonneg _
  calc ‖(InfinitePlace.nrRealPlaces K : ℂ) * (Δ 0 : ℂ) +
        (InfinitePlace.nrComplexPlaces K : ℂ) * ((Δ 0 : ℂ) + (Δ 1 : ℂ))‖
      ≤ (InfinitePlace.nrRealPlaces K : ℝ) * |Δ 0| +
          (InfinitePlace.nrComplexPlaces K : ℝ) * (|Δ 0| + |Δ 1|) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_mul, Complex.norm_natCast]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hr2
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (InfinitePlace.nrRealPlaces K : ℝ) * (H * (Real.log (Y + H) + 8)) +
          (InfinitePlace.nrComplexPlaces K : ℝ) * (2 * (H * (Real.log (Y + H) + 8))) := by
        gcongr
        · linarith
        · nlinarith
    _ = Module.finrank ℚ K * H * (Real.log (Y + H) + 8) := by rw [← hrk]; ring

namespace ContinuationData

variable (D : ContinuationData K)

lemma summable_zeroTerm (hRH : DedekindZetaRH K) (y : ℕ) (hy : 1 ≤ y) :
    Summable (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℂ) * zeroTerm y ρ) := by
  refine Summable.of_norm_bounded ((D.zeroSum_le hRH).1.mul_left (√(y : ℝ) + 2 + 3 / y))
    fun ρ => ?_
  rw [norm_mul, Complex.norm_natCast]
  have h := norm_zeroTerm_le y hy (D.xi_zero_re_eq_half hRH ρ.2)
  calc (D.mult ρ : ℝ) * ‖zeroTerm y ρ‖
      ≤ (D.mult ρ : ℝ) * ((√(y : ℝ) + 2 + 3 / y) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
        mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by ring

lemma norm_zeroSum_diff_le (hRH : DedekindZetaRH K) (y h : ℕ) (hy : 1 ≤ y)
    (hs : Summable (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℝ) *
        ‖((y + h : ℕ) : ℂ) * zeroTerm (y + h) ρ - (y : ℂ) * zeroTerm y ρ‖)) :
    ‖((y + h : ℕ) : ℂ) * D.zeroSum (y + h) - (y : ℂ) * D.zeroSum y‖ ≤
      ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℝ) *
        ‖((y + h : ℕ) : ℂ) * zeroTerm (y + h) ρ - (y : ℂ) * zeroTerm y ρ‖ := by
  have h1 := (D.summable_zeroTerm hRH (y + h) (by omega)).mul_left ((y + h : ℕ) : ℂ)
  have h2 := (D.summable_zeroTerm hRH y hy).mul_left (y : ℂ)
  have e : ((y + h : ℕ) : ℂ) * D.zeroSum (y + h) - (y : ℂ) * D.zeroSum y =
      ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℂ) *
        (((y + h : ℕ) : ℂ) * zeroTerm (y + h) ρ - (y : ℂ) * zeroTerm y ρ) := by
    rw [zeroSum, zeroSum, ← tsum_mul_left, ← tsum_mul_left, ← h1.tsum_sub h2]
    exact tsum_congr fun ρ => by ring
  rw [e]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun ρ => ?_))
  · refine hs.congr fun ρ => ?_
    rw [norm_mul, Complex.norm_natCast]
  · rw [norm_mul, Complex.norm_natCast]

end ContinuationData

set_option maxHeartbeats 1600000 in
/-- Increments of `E`: `|E(y+h) - E(y)| ≤ C₁ h √y (log |d_K| + n log(y+2)) log(y+2)` for
`1 ≤ h ≤ y`, with `C₁` absolute. -/
theorem efError_diff_le :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (K : Type) [Field K] [NumberField K] (D : ContinuationData K),
      DedekindZetaRH K → ∀ y h : ℕ, 1 ≤ h → h ≤ y →
      |efError K (y + h) - efError K y| ≤ C₁ * h * Real.sqrt y *
        (Real.log |(discr K : ℝ)| + Module.finrank ℚ K * Real.log (y + 2)) * Real.log (y + 2) := by
  obtain ⟨C₀, hC₀⟩ := ContinuationData.zeroDiff_le
  set C₀' := max C₀ 0
  refine ⟨C₀' + 18, by positivity, fun K _ _ D hRH y h hh hhy => ?_⟩
  have hy1 : 1 ≤ y := hh.trans hhy
  obtain ⟨hzs, hzb⟩ := hC₀ K D hRH y h hh hhy
  have eA := D.efError_eq (y + h) (by omega)
  have eB := D.efError_eq y hy1
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  set ld := Real.log |(discr K : ℝ)|
  set ℓ := Real.log ((y : ℝ) + 2)
  have hn : 1 ≤ n := one_le_finrank
  have hld : 0 ≤ ld := log_abs_discr_nonneg
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy1
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhyR : (h : ℝ) ≤ y := by exact_mod_cast hhy
  have hℓ : 1 ≤ ℓ := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hsy : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hyR
  set B := ld + n * ℓ
  have hB : n ≤ B := by
    have : n ≤ n * ℓ := le_mul_of_one_le_right (by linarith) hℓ
    simp only [B]; linarith
  have hB0 : 0 ≤ B := by linarith
  have hsB : B ≤ Real.sqrt y * B := le_mul_of_one_le_left hB0 hsy
  -- zeros
  have hZ : |((((y + h : ℕ) : ℂ) * D.zeroSum (y + h)).re - (((y : ℂ) * D.zeroSum y)).re)| ≤
      C₀' * h * Real.sqrt y * B * ℓ := by
    rw [← sub_re]
    refine (abs_re_le_norm _).trans ((D.norm_zeroSum_diff_le hRH y h hy1 hzs).trans
      (hzb.trans ?_))
    have : 0 ≤ (h : ℝ) * Real.sqrt y * B * ℓ := by
      have : 0 ≤ B := by linarith
      positivity
    have e1 : C₀ * h * Real.sqrt y * B * ℓ = C₀ * ((h : ℝ) * Real.sqrt y * B * ℓ) := by ring
    have e2 : C₀' * h * Real.sqrt y * B * ℓ = C₀' * ((h : ℝ) * Real.sqrt y * B * ℓ) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  -- gamma factors
  have hlyh : Real.log ((y : ℝ) + h) ≤ 2 * ℓ := by
    have : Real.log ((y : ℝ) + h) ≤ Real.log (((y : ℝ) + 2) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlyh0 : 0 ≤ Real.log ((y : ℝ) + h) := Real.log_nonneg (by linarith)
  have hG : |((((y + h : ℕ) : ℂ) * gammaPartK K (y + h)).re - (((y : ℂ) * gammaPartK K y)).re)| ≤
      10 * n * h * ℓ := by
    rw [← sub_re]
    refine (abs_re_le_norm _).trans ?_
    have hg := gammaDiff_le (K := K) y h hy1
    calc ‖((y + h : ℕ) : ℂ) * gammaPartK K (y + h) - (y : ℂ) * gammaPartK K y‖
        ≤ n * h * (Real.log ((y : ℝ) + h) + 8) := hg
      _ ≤ 10 * n * h * ℓ := by
          have h1 : Real.log ((y : ℝ) + h) + 8 ≤ 10 * ℓ := by linarith
          have h2 : 0 ≤ n * h := by positivity
          calc n * h * (Real.log ((y : ℝ) + h) + 8) ≤ n * h * (10 * ℓ) :=
                mul_le_mul_of_nonneg_left h1 h2
            _ = 10 * n * h * ℓ := by ring
  -- elementary terms
  have hlog : |((y + h : ℕ) : ℝ) * Real.log ((y + h : ℕ) : ℝ) - y * Real.log y| ≤
      h * (Real.log ((y : ℝ) + h) + 1) := by
    push_cast
    have hmono : y * Real.log y ≤ ((y : ℝ) + h) * Real.log ((y : ℝ) + h) := by
      have := Real.log_le_log (by linarith : (0 : ℝ) < y) (by linarith : (y : ℝ) ≤ y + h)
      have := Real.log_nonneg hyR
      nlinarith
    have hup : ((y : ℝ) + h) * Real.log ((y : ℝ) + h) - y * Real.log y ≤
        h * (Real.log ((y : ℝ) + h) + 1) := by
      have h1 : Real.log ((y : ℝ) + h) - Real.log y ≤ h / y := by
        rw [← Real.log_div (by linarith) (by linarith)]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (y + h) / y by positivity)
        have e : ((y : ℝ) + h) / y - 1 = h / y := by field_simp; ring
        linarith
      have h2 : (y : ℝ) * (Real.log ((y : ℝ) + h) - Real.log y) ≤ h := by
        have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ y)
        rwa [mul_div_cancel₀ _ (by linarith : (y : ℝ) ≠ 0)] at this
      nlinarith
    rw [abs_le]; constructor <;> linarith
  have hc2 : |(deriv D.Z 2 / D.Z 2).re| ≤ 0.6 * n :=
    (abs_re_le_norm _).trans (D.norm_logDeriv_Z_le (by norm_num))
  -- assemble
  have hcast : ((y + h : ℕ) : ℝ) - 1 - (y - 1) = h := by push_cast; ring
  have key : efError K (y + h) - efError K y =
      (((((y + h : ℕ) : ℂ) * D.zeroSum (y + h)).re - (((y : ℂ) * D.zeroSum y)).re)) +
      (((((y + h : ℕ) : ℂ) * gammaPartK K (y + h)).re - (((y : ℂ) * gammaPartK K y)).re)) +
      (((y + h : ℕ) : ℝ) * Real.log ((y + h : ℕ) : ℝ) - y * Real.log y) - 7 / 2 * h -
      h * (deriv D.Z 2 / D.Z 2).re := by
    rw [eA, eB]; push_cast; ring
  rw [key]
  have hT1 : h * (Real.log ((y : ℝ) + h) + 1) ≤ 3 * h * ℓ := by
    have : Real.log ((y : ℝ) + h) + 1 ≤ 3 * ℓ := by linarith
    calc (h : ℝ) * (Real.log ((y : ℝ) + h) + 1) ≤ h * (3 * ℓ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 3 * h * ℓ := by ring
  have hc2' : |(h : ℝ) * (deriv D.Z 2 / D.Z 2).re| ≤ h * (0.6 * n) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h)]
    exact mul_le_mul_of_nonneg_left hc2 (by positivity)
  have hT2 : 7 / 2 * (h : ℝ) + h * (0.6 * n) ≤ 5 * n * h := by
    have h1 : (h : ℝ) ≤ n * h := le_mul_of_one_le_left (by positivity) hn
    have e : (h : ℝ) * (0.6 * n) = 0.6 * (n * h) := by ring
    have e2 : 5 * n * (h : ℝ) = 5 * (n * h) := by ring
    rw [e, e2]; linarith
  have hX : (h : ℝ) * ℓ ≤ h * Real.sqrt y * B * ℓ := by
    have h1 : 1 ≤ Real.sqrt y * B := by linarith
    have h2 : 0 ≤ (h : ℝ) * ℓ := by positivity
    calc (h : ℝ) * ℓ = (h * ℓ) * 1 := by ring
      _ ≤ (h * ℓ) * (Real.sqrt y * B) := mul_le_mul_of_nonneg_left h1 h2
      _ = h * Real.sqrt y * B * ℓ := by ring
  have hY : n * h * ℓ ≤ h * Real.sqrt y * B * ℓ := by
    have h1 : n ≤ Real.sqrt y * B := by linarith
    have h2 : 0 ≤ (h : ℝ) * ℓ := by positivity
    calc n * h * ℓ = (h * ℓ) * n := by ring
      _ ≤ (h * ℓ) * (Real.sqrt y * B) := mul_le_mul_of_nonneg_left h1 h2
      _ = h * Real.sqrt y * B * ℓ := by ring
  have hW : n * h ≤ n * h * ℓ := by
    have : 0 ≤ n * h := by positivity
    calc n * h = n * h * 1 := by ring
      _ ≤ n * h * ℓ := mul_le_mul_of_nonneg_left hℓ this
  have h1 := abs_le.1 hZ
  have h2 := abs_le.1 hG
  have h3 := abs_le.1 (hlog.trans hT1)
  have h4 := abs_le.1 hc2'
  have hfin : C₀' * h * Real.sqrt y * B * ℓ + 10 * n * h * ℓ + 3 * h * ℓ + 5 * n * h ≤
      (C₀' + 18) * h * Real.sqrt y * B * ℓ := by
    have e : (C₀' + 18) * h * Real.sqrt y * B * ℓ =
        C₀' * h * Real.sqrt y * B * ℓ + 18 * (h * Real.sqrt y * B * ℓ) := by ring
    rw [e]
    linarith
  rw [abs_le]
  constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- **ψ_K at integers** under RH and Hecke's continuation, with an absolute constant. -/
theorem psiK_natCast_le :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (D : ContinuationData K),
      DedekindZetaRH K → ∀ x : ℕ, 2 ≤ x →
      |psiK K x - x| ≤ C * Real.sqrt x *
        (Real.log |(discr K : ℝ)| + Module.finrank ℚ K * Real.log x) * Real.log x := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := efError_diff_le
  refine ⟨4 * C₁ + 2, fun K _ _ D hRH x hx => ?_⟩
  set h := Nat.sqrt x with hhdef
  have hh1 : 1 ≤ h := Nat.sqrt_pos.2 (by omega)
  have hhh : h * h ≤ x := Nat.sqrt_le x
  have h2h : 2 * h ≤ x := by
    rcases Nat.lt_or_ge h 2 with h' | h'
    · omega
    · nlinarith
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  set ld := Real.log |(discr K : ℝ)|
  have hn : 1 ≤ n := one_le_finrank
  have hld : 0 ≤ ld := log_abs_discr_nonneg
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hhx : (h : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le (by have : ((h * h : ℕ) : ℝ) ≤ x := by exact_mod_cast hhh
                              push_cast at this; nlinarith)
  set Q := Real.sqrt x * (ld + n * Real.log ((x : ℝ) + 2)) * Real.log ((x : ℝ) + 2)
  -- `T(y) = ∑_{m ≤ y} ψ(m) = y²/2 + E(y)`
  have hT : ∀ y : ℕ, ∑ m ∈ Finset.Ioc 0 y, psiK K m = (y : ℝ) ^ 2 / 2 + efError K y := by
    intro y
    have e : Finset.Ioc 0 y = Finset.Icc 1 y := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [e, ← mul_weightedPsiK_eq, efError]; ring
  have hmono := psiK_natCast_mono (K := K)
  -- upper bound
  have hup : (h : ℝ) * psiK K x ≤ (h : ℝ) * x + (h : ℝ) ^ 2 / 2 + C₁ * h * Q := by
    have hs : ∑ m ∈ Finset.Ioc x (x + h), psiK K m =
        ((x + h : ℕ) : ℝ) ^ 2 / 2 + efError K (x + h) - ((x : ℝ) ^ 2 / 2 + efError K x) := by
      rw [← hT, ← hT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le x) (Nat.le_add_right x h)]
      ring
    have hge : (h : ℝ) * psiK K x ≤ ∑ m ∈ Finset.Ioc x (x + h), psiK K m := by
      have := Finset.card_nsmul_le_sum (Finset.Ioc x (x + h)) (fun m : ℕ => psiK K m)
        (psiK K x) (fun m hm => hmono (Finset.mem_Ioc.1 hm).1.le)
      rw [Nat.card_Ioc, nsmul_eq_mul, Nat.add_sub_cancel_left] at this
      exact this
    have hE := hC₁ K D hRH x h hh1 (by omega)
    have hE' := (abs_le.1 hE).2
    have hQ : C₁ * h * Real.sqrt x * (ld + n * Real.log ((x : ℝ) + 2)) * Real.log ((x : ℝ) + 2)
        = C₁ * h * Q := by simp only [Q]; ring
    rw [hQ] at hE'
    rw [hs] at hge
    push_cast at hge
    nlinarith
  -- lower bound
  have hlow : (h : ℝ) * x - (h : ℝ) ^ 2 / 2 - C₁ * h * Q ≤ (h : ℝ) * psiK K x := by
    set y := x - h with hy
    have hyx : y + h = x := by omega
    have hs : ∑ m ∈ Finset.Ioc y x, psiK K m =
        (x : ℝ) ^ 2 / 2 + efError K x - ((y : ℝ) ^ 2 / 2 + efError K y) := by
      rw [← hT, ← hT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le y) (by omega : y ≤ x)]
      ring
    have hle : ∑ m ∈ Finset.Ioc y x, psiK K m ≤ (h : ℝ) * psiK K x := by
      have := Finset.sum_le_card_nsmul (Finset.Ioc y x) (fun m : ℕ => psiK K m)
        (psiK K x) (fun m hm => hmono (Finset.mem_Ioc.1 hm).2)
      rw [Nat.card_Ioc, nsmul_eq_mul, show x - y = h by omega] at this
      exact this
    have hE := hC₁ K D hRH y h hh1 (by omega)
    rw [hyx] at hE
    have hE' := (abs_le.1 hE).1
    have hyR : (y : ℝ) = x - h := by rw [hy]; push_cast [Nat.cast_sub (by omega : h ≤ x)]; ring
    have hy2 : (y : ℝ) + 2 ≤ x + 2 := by rw [hyR]; linarith
    have hy1 : (1 : ℝ) ≤ y := by rw [hyR]; have : ((2 * h : ℕ) : ℝ) ≤ x := by exact_mod_cast h2h
                                 push_cast at this; linarith
    have hmon : C₁ * h * Real.sqrt y * (ld + n * Real.log ((y : ℝ) + 2)) * Real.log ((y : ℝ) + 2)
        ≤ C₁ * h * Q := by
      have l1 : Real.log ((y : ℝ) + 2) ≤ Real.log ((x : ℝ) + 2) := Real.log_le_log (by linarith) hy2
      have l0 : 0 ≤ Real.log ((y : ℝ) + 2) := Real.log_nonneg (by linarith)
      have s1 : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt (by rw [hyR]; linarith)
      simp only [Q]
      have a1 : 0 ≤ C₁ * h := by positivity
      have a2 : ld + n * Real.log ((y : ℝ) + 2) ≤ ld + n * Real.log ((x : ℝ) + 2) := by
        have := mul_le_mul_of_nonneg_left l1 (by linarith : (0 : ℝ) ≤ n); linarith
      have a3 : 0 ≤ ld + n * Real.log ((y : ℝ) + 2) := add_nonneg hld (mul_nonneg (by linarith) l0)
      calc C₁ * h * Real.sqrt y * (ld + n * Real.log ((y : ℝ) + 2)) * Real.log ((y : ℝ) + 2)
          = (C₁ * h) * (Real.sqrt y * (ld + n * Real.log ((y : ℝ) + 2)) *
              Real.log ((y : ℝ) + 2)) := by ring
        _ ≤ (C₁ * h) * (Real.sqrt x * (ld + n * Real.log ((x : ℝ) + 2)) *
              Real.log ((x : ℝ) + 2)) := by
            apply mul_le_mul_of_nonneg_left _ a1
            apply mul_le_mul (mul_le_mul s1 a2 a3 (Real.sqrt_nonneg _)) l1 l0
            exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
        _ = _ := by ring
    rw [hs] at hle
    rw [hyR] at hle
    nlinarith
  -- divide by `h`
  have hhpos : (0 : ℝ) < h := by linarith
  have hb : |psiK K x - x| ≤ (h : ℝ) / 2 + C₁ * Q := by
    rw [abs_le]; constructor
    · have : (h : ℝ) * (-(h / 2 + C₁ * Q)) ≤ h * (psiK K x - x) := by nlinarith
      exact le_of_mul_le_mul_left this hhpos
    · have : (h : ℝ) * (psiK K x - x) ≤ h * ((h : ℝ) / 2 + C₁ * Q) := by nlinarith
      exact le_of_mul_le_mul_left this hhpos
  -- compare logs
  have hl2 := Real.log_two_gt_d9
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hxR
  have hlx2 : Real.log ((x : ℝ) + 2) ≤ 2 * Real.log x := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
  set P := ld + n * Real.log x
  have hP2 : Real.log 2 ≤ P := by
    have : Real.log 2 ≤ n * Real.log x := by nlinarith
    simp only [P]; linarith
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hQ : Q ≤ 4 * (Real.sqrt x * P * Real.log x) := by
    have a1 : ld + n * Real.log ((x : ℝ) + 2) ≤ 2 * P := by
      have := mul_le_mul_of_nonneg_left hlx2 (by linarith : (0 : ℝ) ≤ n)
      simp only [P]; linarith
    have a0 : 0 ≤ ld + n * Real.log ((x : ℝ) + 2) :=
      add_nonneg hld (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
    simp only [Q]
    calc Real.sqrt x * (ld + n * Real.log ((x : ℝ) + 2)) * Real.log ((x : ℝ) + 2)
        ≤ Real.sqrt x * (2 * P) * (2 * Real.log x) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left a1 (Real.sqrt_nonneg _)) hlx2
            (Real.log_nonneg (by linarith))
          exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
      _ = 4 * (Real.sqrt x * P * Real.log x) := by ring
  have hhalf : (h : ℝ) / 2 ≤ 2 * (Real.sqrt x * P * Real.log x) := by
    have a : Real.log 2 * Real.log 2 ≤ P * Real.log x := mul_le_mul hP2 hlx (by linarith) (by linarith)
    have c : 1 / 4 ≤ P * Real.log x := by nlinarith
    calc (h : ℝ) / 2 ≤ Real.sqrt x / 2 := by linarith
      _ = 2 * Real.sqrt x * (1 / 4) := by ring
      _ ≤ 2 * Real.sqrt x * (P * Real.log x) :=
          mul_le_mul_of_nonneg_left c (by positivity)
      _ = 2 * (Real.sqrt x * P * Real.log x) := by ring
  calc |psiK K x - x| ≤ (h : ℝ) / 2 + C₁ * Q := hb
    _ ≤ 2 * (Real.sqrt x * P * Real.log x) + C₁ * (4 * (Real.sqrt x * P * Real.log x)) := by
        gcongr
    _ = (4 * C₁ + 2) * Real.sqrt x * (ld + n * Real.log x) * Real.log x := by ring

/-- **The analytic core, per field** (blueprint A1–A4): RH for `ζ_K` and Hecke's continuation
give `PsiKBound K C`, with `C` absolute. -/
theorem psiKBound_of_continuation :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K],
      DedekindZetaRH K → DedekindContinuation K → PsiKBound K C := by
  obtain ⟨C, hC⟩ := psiK_natCast_le
  set C' := max C 0
  refine ⟨8 * C' + 3, fun K _ _ hRH ⟨D⟩ x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set N : ℕ := ⌈x⌉₊ with hN
  have hNx : x ≤ N := Nat.le_ceil x
  have hNx1 : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  have hψ : psiK K x = psiK K N := by
    rw [psiK_eq_sum K hx0, psiK_natCast_eq_sum]
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  set ld := Real.log |(discr K : ℝ)|
  have hn : 1 ≤ n := one_le_finrank
  have hld : 0 ≤ ld := log_abs_discr_nonneg
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl2 := Real.log_two_gt_d9
  have hlN : Real.log N ≤ 2 * Real.log x := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hsN : Real.sqrt N ≤ 2 * Real.sqrt x := by
    have : Real.sqrt N ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hsx : 1 ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hmain := hC K D hRH N hN2
  have hC' : |psiK K N - N| ≤ C' * Real.sqrt N * (ld + n * Real.log N) * Real.log N := by
    refine hmain.trans ?_
    have hA : 0 ≤ ld + n * Real.log N := add_nonneg hld (mul_nonneg (by linarith) hlN0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.sqrt_nonneg _)) hA) hlN0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set P := ld + n * Real.log x
  have hP : n * Real.log 2 ≤ P := by nlinarith
  have hstep : C' * Real.sqrt N * (ld + n * Real.log N) * Real.log N ≤
      8 * C' * (Real.sqrt x * P * Real.log x) := by
    have h1 : ld + n * Real.log N ≤ 2 * P := by nlinarith
    have h2 : C' * Real.sqrt N ≤ C' * (2 * Real.sqrt x) := mul_le_mul_of_nonneg_left hsN hC'0
    have hA : 0 ≤ ld + n * Real.log N := add_nonneg hld (mul_nonneg (by linarith) hlN0)
    have hB : 0 ≤ C' * (2 * Real.sqrt x) := by positivity
    have hP0 : 0 ≤ P := by nlinarith
    calc C' * Real.sqrt N * (ld + n * Real.log N) * Real.log N
        ≤ C' * (2 * Real.sqrt x) * (ld + n * Real.log N) * Real.log N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hA) hlN0
      _ ≤ C' * (2 * Real.sqrt x) * (2 * P) * Real.log N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hB) hlN0
      _ ≤ C' * (2 * Real.sqrt x) * (2 * P) * (2 * Real.log x) :=
          mul_le_mul_of_nonneg_left hlN (by positivity)
      _ = 8 * C' * (Real.sqrt x * P * Real.log x) := by ring
  have hone : 1 ≤ 3 * (Real.sqrt x * P * Real.log x) := by
    have hP2 : Real.log 2 ≤ P := by nlinarith
    have : Real.log 2 * Real.log 2 ≤ P * Real.log x :=
      mul_le_mul hP2 hlx (by linarith) (by linarith)
    have h3 : P * Real.log x ≤ Real.sqrt x * (P * Real.log x) := by
      nlinarith
    nlinarith
  have htri : |psiK K x - x| ≤ |psiK K N - N| + 1 := by
    rw [hψ]
    calc |psiK K N - x| = |(psiK K N - N) + (N - x)| := by ring_nf
      _ ≤ |psiK K N - N| + |(N : ℝ) - x| := abs_add_le _ _
      _ ≤ |psiK K N - N| + 1 := by
          gcongr; rw [abs_le]; constructor <;> linarith
  calc |psiK K x - x| ≤ 8 * C' * (Real.sqrt x * P * Real.log x)
        + 3 * (Real.sqrt x * P * Real.log x) := by linarith
    _ = (8 * C' + 3) * Real.sqrt x * (ld + n * Real.log x) * Real.log x := by ring

end Artin.Analytic
