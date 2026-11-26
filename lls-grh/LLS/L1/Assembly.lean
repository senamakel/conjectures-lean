import LLS.L1.Integrate
import LLS.L1.CesLower
import LLS.L1.Principal
import LLS.Analytic.ZeroSum
import LLS.Analytic.ShiftFormula
import LLS.Key

/-!
# Assembly of the `L(1, χ)` bounds (LLS §5)

For `χ` primitive mod `q` and `x ≥ 2`, with `l = log x`, `U = Re Λ'/Λ(1, χ)`, `Z = Σ m_ρ/|ρ|²`
and `P₂(x) = Σ_{n<x} Λ(n)/n (1 − n/x)`:

* Lemma 2.5: `log |L(1,χ)| = Re l1Sum χ x − Re (L'/L)(1)/l + θ (Z/√x + 2/x)/l²`;
* `Re (L'/L)(1) = U − Re G(1)` (`D_one_eq`);
* Lemma 2.3 both ways: `−U(1 − 1/x) = Re S'(χ) + θ Z (1/√x + 1/x) − E`, with
  `E ∈ [EshiftLo x, Eshift x]` and `|Re S'(χ)| ≤ P₂(x)`;
* `Z (1 + 1/x − 2/√x) ≤ log q (1 − 1/x) + 2 P₂(x) + 2 Eshift x`.

The results are `log |L(1,χ)| ≤ l1Sum1 x + (upper)/l + …` and the matching lower bound.
-/

namespace LLS

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic

variable {N : ℕ} [NeZero N]

/-- `P₂(x) = Σ_{n<x} Λ(n)/n (1 − n/x)`. -/
noncomputable def P2sum (x : ℕ) : ℝ := ∑ n ∈ Finset.range x, (Λ n : ℝ) / n * (1 - (n : ℝ) / x)

lemma abs_re_cesShift_le {M : ℕ} (φ : DirichletCharacter ℂ M) (x : ℕ) :
    |(cesShift φ x).re| ≤ P2sum x := by
  rw [cesShift, Complex.re_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hnx : n < x := Finset.mem_range.1 hn
  have hw : 0 ≤ (Λ n : ℝ) / n * (1 - (n : ℝ) / x) := by
    have : (n : ℝ) / x ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (show 0 < x by omega))]; exact_mod_cast hnx.le
    have : 0 ≤ (Λ n : ℝ) / n := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    nlinarith
  have e : (Λ n : ℂ) * φ n / n * (1 - (n : ℂ) / x)
      = (((Λ n : ℝ) / n * (1 - (n : ℝ) / x) : ℝ) : ℂ) * φ n := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, abs_mul, abs_of_nonneg hw]
  have h1 : |(φ n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one φ _)
  nlinarith [abs_nonneg (φ n).re]

lemma abs_re_l1Sum_le {M : ℕ} (φ : DirichletCharacter ℂ M) (x : ℕ) :
    |(l1Sum φ x).re| ≤ l1Sum1 x := by
  rw [l1Sum, Complex.re_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hnx : n ≤ x := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  set w : ℝ := (Λ n : ℝ) / ((n : ℝ) * Real.log n) * (Real.log ((x : ℝ) / n) / Real.log x)
  have hw : 0 ≤ w := by
    have h1 : 0 ≤ Real.log ((x : ℝ) / n) := log_div_nonneg hnx
    have h2 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
    have h3 : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)
    have : 0 ≤ (Λ n : ℝ) / ((n : ℝ) * Real.log n) := div_nonneg vonMangoldt_nonneg h3
    exact mul_nonneg this (div_nonneg h1 h2)
  have e : (Λ n : ℂ) * φ n / ((n : ℂ) * (Real.log n : ℂ))
        * ((Real.log ((x : ℝ) / n) / Real.log x : ℝ) : ℂ) = (w : ℂ) * φ n := by
    simp only [w]; push_cast; ring
  rw [e, Complex.re_ofReal_mul, abs_mul, abs_of_nonneg hw]
  have h1 : |(φ n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one φ _)
  nlinarith [abs_nonneg (φ n).re]

/-- `Re G(1)` for both parities. -/
lemma re_gammaLogDeriv_one (χ : DirichletCharacter ℂ N) :
    -(1 / 2) * Real.log Real.pi - Real.eulerMascheroniConstant / 2 - Real.log 2
        ≤ (gammaLogDeriv χ 1).re ∧
      (gammaLogDeriv χ 1).re ≤ -(1 / 2) * Real.log Real.pi - Real.eulerMascheroniConstant / 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gammaLogDeriv parity
  split_ifs
  · have h : ((1 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 1 / 2 := by norm_num
    rw [h, Complex.digamma_one_half]
    have e : (-2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ))
        = ((-2 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
      push_cast; rw [Complex.ofReal_log (by norm_num)]; push_cast; ring
    rw [e]
    simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    norm_num
    constructor <;> linarith
  · have h : ((1 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 1 := by norm_num
    rw [h, Complex.digamma_one]
    simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    norm_num
    constructor <;> linarith

/-- `Z (1 + 1/x − 2/√x) ≤ log N (1 − 1/x) + 2 P₂(x) + 2 E(x)`, for any primitive `χ ≠ 1`. -/
theorem Z2_le_general (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 2 ≤ x) :
    Z2 χ * (1 + 1 / x - 2 / √(x : ℝ))
      ≤ Real.log N * (1 - 1 / x) + 2 * P2sum x + 2 * Eshift x := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have uC := re_cesShift_le hGRH hprim hχ x hx
  have uCi := re_cesShift_le hGRH hprim.inv hχi x hx
  rw [inv_inv] at uCi
  obtain ⟨-, hZ⟩ := Z2_eq hGRH hprim hχ
  obtain ⟨-, hZi⟩ := Z2_eq hGRH hprim.inv hχi
  rw [inv_inv] at hZi
  have hZZ : Z2 χ⁻¹ = Z2 χ := by rw [hZi, hZ]; ring
  rw [hZZ] at uCi
  have l1 := abs_re_cesShift_le χ x
  have l2 := abs_re_cesShift_le χ⁻¹ x
  rw [abs_le] at l1 l2
  set U := (D χ 1).re
  set V := (D χ⁻¹ 1).re
  set a := 1 / (x : ℝ)
  set b := 1 / √(x : ℝ)
  have e1 : (Real.log N + V) / (x : ℝ) = (Real.log N + V) * a := by simp [a, div_eq_mul_inv]
  have e2 : (Real.log N + U) / (x : ℝ) = (Real.log N + U) * a := by simp [a, div_eq_mul_inv]
  have e3 : Z2 χ / √(x : ℝ) = Z2 χ * b := by simp [b, div_eq_mul_inv]
  have e4 : 2 / √(x : ℝ) = 2 * b := by simp [b, div_eq_mul_inv]
  rw [e1, e3] at uC
  rw [e2, e3] at uCi
  rw [e4]
  have hUV : U * a + V * a = Z2 χ * a - Real.log N * a := by
    rw [← add_mul, show U + V = Z2 χ - Real.log N by rw [hZ]; ring, sub_mul]
  have hUV' : U + V = Z2 χ - Real.log N := by rw [hZ]; ring
  linarith

/-- The real-variable quantities of the assembly at `x`, with `Z` the zero sum. -/
lemma l1_core (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 2 ≤ x) :
    let l := Real.log x
    let U := (D χ 1).re
    let ℓ := (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
    |Real.log ‖DirichletCharacter.LFunction χ 1‖ - (l1Sum χ x).re + ℓ / l|
        ≤ (Z2 χ / √(x : ℝ) + 2 / x) / l ^ 2 ∧
      ℓ = U - (gammaLogDeriv χ 1).re ∧
      -U * (1 - 1 / x) ≤ P2sum x + Z2 χ * (1 / x + 1 / √(x : ℝ)) - EshiftLo x ∧
      -P2sum x - Z2 χ * (1 / √(x : ℝ) - 1 / x) - Eshift x ≤ -U * (1 - 1 / x) := by
  intro l U ℓ
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  refine ⟨log_norm_L1_le hGRH hprim hχ x hx, ?_, ?_, ?_⟩
  · have h := congrArg Complex.re (D_one_eq hχ)
    simp only [Complex.add_re] at h
    simp only [U, ℓ]; linarith
  · have hge := re_cesShift_ge hGRH hprim hχ x hx
    have hab := abs_re_cesShift_le χ x
    rw [abs_le] at hab
    obtain ⟨-, hZ⟩ := Z2_eq hGRH hprim hχ
    set V := (D χ⁻¹ 1).re
    have e : (Real.log N + V) / (x : ℝ) = (Z2 χ - U) * (1 / x) := by
      rw [hZ]; simp only [U]; ring
    have e2 : Z2 χ / √(x : ℝ) = Z2 χ * (1 / √(x : ℝ)) := by ring
    rw [e, e2] at hge
    nlinarith
  · have hle := re_cesShift_le hGRH hprim hχ x hx
    have hab := abs_re_cesShift_le χ x
    rw [abs_le] at hab
    obtain ⟨-, hZ⟩ := Z2_eq hGRH hprim hχ
    set V := (D χ⁻¹ 1).re
    have e : (Real.log N + V) / (x : ℝ) = (Z2 χ - U) * (1 / x) := by
      rw [hZ]; simp only [U]; ring
    have e2 : Z2 χ / √(x : ℝ) = Z2 χ * (1 / √(x : ℝ)) := by ring
    rw [e, e2] at hle
    nlinarith

end LLS
