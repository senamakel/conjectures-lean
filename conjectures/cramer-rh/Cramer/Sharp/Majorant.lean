import Cramer.Sharp.SecondDiff
import Cramer.ZeroSum

/-!
# A Lorentzian majorant for `‖D_ρ‖`, and the zero sum it gives

With `A = h² a^{−1/2}`, `σ = 7a/(3h)` and `400 h ≤ a`, every zero `ρ = 1/2 + iγ` satisfies

`‖D_ρ‖ ≤ (9/7) A σ² / (σ² + γ²)`.

In `x = γh/(2a)` this reads `‖D_ρ‖ ≤ A · (7/4)/(49/36 + x²)`. For `x² ≤ 2` it follows from the
sharp bound `A (sin²x/x² + h/a + 2|γ|h²/a²)` (`Cramer.Sharp.SecondDiff`), with
`sin x ≤ x(1 − x²/6 + x⁴/120)` and one polynomial inequality; for `x² ≥ 2` the trivial bound
`4(a+2h)^{3/2}/|γ|²` suffices. The Lorentzian `(7/4)/(49/36 + x²)` is a near-optimal single
Lorentzian majorant of `sin²x/x²`: its integral is `(9/7)(7/6)π = (3/2)π` against `π` for
`sin²x/x²`, and the best single one has `≈ 1.4492 π`.

Hadamard's product at `s = 1/2 + σ` then gives `Σ_ρ m_ρ ‖D_ρ‖ ≤ (9/7) A σ (L(1/2+σ) + 1/40)
= 3h√a (L(1/2+σ) + 1/40)`.
-/

namespace Cramer

open Complex Erdos985.Analytic

/-- `T(y) = 1 − y/6 + y²/120`, so that `sin x ≤ x T(x²)` for `x ≥ 0`. -/
noncomputable def Tpoly (y : ℝ) : ℝ := 1 - y / 6 + y ^ 2 / 120

lemma sin_sq_div_sq_le {x : ℝ} (hx : x ≠ 0) (hx2 : x ^ 2 ≤ 2) :
    Real.sin x ^ 2 / x ^ 2 ≤ Tpoly (x ^ 2) ^ 2 := by
  have hx2' : 0 < x ^ 2 := by positivity
  rw [div_le_iff₀ hx2']
  set t := |x| with ht
  have ht0 : 0 ≤ t := abs_nonneg x
  have htx : t ^ 2 = x ^ 2 := sq_abs x
  have ht2 : t ≤ 3 / 2 := by nlinarith
  have hsin : Real.sin x ^ 2 = Real.sin t ^ 2 := by
    rcases le_total 0 x with h | h
    · rw [ht, abs_of_nonneg h]
    · rw [ht, abs_of_nonpos h, Real.sin_neg, neg_sq]
  have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by
    linarith [Real.pi_gt_three])
  have hs1 := sin_le_taylor5 ht0
  have hT : t - t ^ 3 / 6 + t ^ 5 / 120 = t * Tpoly (t ^ 2) := by unfold Tpoly; ring
  rw [hsin, ← htx]
  have hTpos : 0 ≤ t * Tpoly (t ^ 2) := by
    unfold Tpoly; apply mul_nonneg ht0; nlinarith
  rw [hT] at hs1
  calc Real.sin t ^ 2 ≤ (t * Tpoly (t ^ 2)) ^ 2 := pow_le_pow_left₀ hs0 hs1 2
    _ = Tpoly (t ^ 2) ^ 2 * t ^ 2 := by ring

/-- The polynomial inequality behind the majorant. -/
lemma majorant_poly {y δ : ℝ} (h0 : 0 ≤ y) (h2 : y ≤ 2) (hδ : δ ≤ 1 / 400) :
    (Tpoly y ^ 2 + δ * (3 + 2 * y)) * (49 / 36 + y) ≤ 7 / 4 := by
  have hmono : (Tpoly y ^ 2 + δ * (3 + 2 * y)) * (49 / 36 + y)
      ≤ (Tpoly y ^ 2 + (1 / 400) * (3 + 2 * y)) * (49 / 36 + y) := by
    gcongr
  refine hmono.trans ?_
  unfold Tpoly
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h2), sq_nonneg (y - 3 / 2),
    mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h2)) (sq_nonneg (y - 3 / 2)),
    mul_nonneg h0 (sq_nonneg (y - 3 / 2)), mul_nonneg (sub_nonneg.2 h2) (sq_nonneg (y - 3 / 2))]

/-- `‖ρ(ρ+1)‖ ≥ (Im ρ)²`. -/
lemma im_sq_le_norm_mul (ρ : ℂ) : ρ.im ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
  rw [norm_mul]
  have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have h2 : |ρ.im| ≤ ‖ρ + 1‖ := by
    have := Complex.abs_im_le_norm (ρ + 1); simpa using this
  rw [← sq_abs]
  calc |ρ.im| ^ 2 = |ρ.im| * |ρ.im| := sq _
    _ ≤ ‖ρ‖ * ‖ρ + 1‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

/-- **The pointwise majorant.** -/
theorem norm_second_diff_gρ_le_lorentz {ρ : ℂ} (hρ : ρ.re = 1 / 2) {a h : ℝ} (ha : 0 < a)
    (hh : 0 < h) (hδ : 400 * h ≤ a) :
    ‖gρ ρ (a + 2 * h) - 2 * gρ ρ (a + h) + gρ ρ a‖
      ≤ (9 / 7) * (h ^ 2 * a ^ (-(1 / 2 : ℝ))) * ((7 * a / (3 * h)) ^ 2
          / ((7 * a / (3 * h)) ^ 2 + ρ.im ^ 2)) := by
  set γ := ρ.im with hγ
  set A := h ^ 2 * a ^ (-(1 / 2 : ℝ)) with hA
  have hA0 : 0 < A := by positivity
  set x := γ * h / (2 * a) with hx
  set y := x ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg x
  -- the right-hand side in terms of `y`
  have hR : (9 / 7) * A * ((7 * a / (3 * h)) ^ 2 / ((7 * a / (3 * h)) ^ 2 + γ ^ 2))
      = A * ((7 / 4) / (49 / 36 + y)) := by
    have hγ2 : γ ^ 2 = 4 * a ^ 2 * y / h ^ 2 := by
      rw [hy, hx]; field_simp; ring
    rw [hγ2]
    field_simp
    ring
  rw [hR]
  have hyden : 0 < 49 / 36 + y := by linarith
  rcases eq_or_ne γ 0 with hγ0 | hγ0
  · -- `γ = 0`: the trivial bound
    have hy00 : y = 0 := by rw [hy, hx, hγ0]; ring
    rw [hy00]
    refine (norm_second_diff_gρ_le hρ ha hh.le).trans ?_
    rw [← hA]; nlinarith
  rcases le_or_gt y 2 with hy2 | hy2
  · -- small `|x|`: the sharp bound
    have hx0 : x ≠ 0 := by
      rw [hx]; exact div_ne_zero (mul_ne_zero hγ0 hh.ne') (by positivity)
    refine (norm_second_diff_gρ_sharp hρ hγ0 ha hh).trans ?_
    rw [← hγ, ← hx, ← hA]
    set δ := h / a with hδdef
    have hδ0 : 0 ≤ δ := by positivity
    have hδ1 : δ ≤ 1 / 400 := by rw [hδdef, div_le_iff₀ ha]; linarith
    have herr : 2 * |γ| * h ^ 2 / a ^ 2 ≤ δ * (2 + 2 * y) := by
      have e : 2 * |γ| * h ^ 2 / a ^ 2 = 4 * |x| * δ := by
        rw [hx, hδdef, abs_div, abs_mul, abs_of_pos hh, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
        field_simp; ring
      rw [e]
      have : 2 * |x| ≤ 1 + y := by
        rw [hy, ← sq_abs x]; nlinarith [sq_nonneg (|x| - 1)]
      nlinarith
    have hs := sin_sq_div_sq_le hx0 (by rw [← hy]; exact hy2)
    rw [← hy] at hs
    have hP := majorant_poly hy0 hy2 hδ1
    have key : Real.sin x ^ 2 / x ^ 2 + δ + 2 * |γ| * h ^ 2 / a ^ 2
        ≤ (7 / 4) / (49 / 36 + y) := by
      rw [le_div_iff₀ hyden]
      have : Real.sin x ^ 2 / x ^ 2 + δ + 2 * |γ| * h ^ 2 / a ^ 2 ≤ Tpoly y ^ 2 + δ * (3 + 2 * y) := by
        linarith
      calc _ ≤ (Tpoly y ^ 2 + δ * (3 + 2 * y)) * (49 / 36 + y) :=
            mul_le_mul_of_nonneg_right this hyden.le
        _ ≤ 7 / 4 := hP
    exact mul_le_mul_of_nonneg_left key hA0.le
  · -- large `|x|`: the trivial bound `4 b^{3/2}/γ²`
    refine (norm_second_diff_gρ_le' hρ ha hh.le).trans ?_
    set b := a + 2 * h with hb
    have hb0 : 0 < b := by positivity
    have hab : a ≤ b := by linarith
    have hb1 : b ≤ (201 / 200) * a := by linarith
    have hγ2pos : 0 < γ ^ 2 := by positivity
    have hden : γ ^ 2 ≤ ‖ρ * (ρ + 1)‖ := im_sq_le_norm_mul ρ
    have hsa : 0 < √a := Real.sqrt_pos.mpr ha
    have h32 : b ^ (3 / 2 : ℝ) ≤ b ^ 2 / √a := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb0, Real.rpow_one,
        ← Real.sqrt_eq_rpow, le_div_iff₀ hsa]
      have : √a ≤ √b := Real.sqrt_le_sqrt hab
      have hsb : √b * √b = b := Real.mul_self_sqrt hb0.le
      have h1 : √b * √a ≤ b := by nlinarith [mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg b)]
      nlinarith [mul_le_mul_of_nonneg_left h1 hb0.le]
    have hAeq : A = h ^ 2 / √a := by
      rw [hA, Real.rpow_neg ha.le, Real.sqrt_eq_rpow]; field_simp
    have hγ2 : γ ^ 2 = 4 * a ^ 2 * y / h ^ 2 := by rw [hy, hx]; field_simp; ring
    calc 4 * b ^ (3 / 2 : ℝ) / ‖ρ * (ρ + 1)‖ ≤ 4 * (b ^ 2 / √a) / γ ^ 2 := by
          apply div_le_div₀ (by positivity) (by linarith) hγ2pos hden
      _ ≤ A * ((7 / 4) / (49 / 36 + y)) := by
          rw [hAeq, hγ2]
          have hy0' : 0 < y := by linarith
          have eL : 4 * (b ^ 2 / √a) / (4 * a ^ 2 * y / h ^ 2) = (b ^ 2 * h ^ 2) / (√a * (a ^ 2 * y)) := by
            field_simp
          have eR : h ^ 2 / √a * (7 / 4 / (49 / 36 + y)) = (7 / 4 * h ^ 2) / (√a * (49 / 36 + y)) := by
            field_simp
          rw [eL, eR, div_le_div_iff₀ (by positivity) (by positivity)]
          have hbb : b ^ 2 ≤ (201 / 200) ^ 2 * a ^ 2 := by
            have := pow_le_pow_left₀ hb0.le hb1 2; nlinarith
          have hkey : (201 / 200) ^ 2 * (49 / 36 + y) ≤ (7 / 4) * y := by nlinarith
          have hh2 : 0 < h ^ 2 := by positivity
          have this : b ^ 2 * (49 / 36 + y) ≤ a ^ 2 * ((7 / 4) * y) := by
            calc b ^ 2 * (49 / 36 + y) ≤ (201 / 200) ^ 2 * a ^ 2 * (49 / 36 + y) :=
                  mul_le_mul_of_nonneg_right hbb hyden.le
              _ = a ^ 2 * ((201 / 200) ^ 2 * (49 / 36 + y)) := by ring
              _ ≤ a ^ 2 * ((7 / 4) * y) := mul_le_mul_of_nonneg_left hkey (by positivity)
          have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ h ^ 2 * √a)
          nlinarith

/-- **The zero sum for a Lorentzian weight.** Under RH, if `0 ≤ w(ρ) ≤ K σ²/(σ² + (Im ρ)²)` for
every zero `ρ` of `ξ` (`σ > 3/2`, `K ≥ 0`), then `Σ_ρ m_ρ w(ρ) ≤ K σ (L(1/2+σ) + 1/40)`. -/
theorem lorentz_zeroSum_le (hRH : RiemannHypothesis) {σ K : ℝ} (hσ : 3 / 2 < σ) (hK : 0 ≤ K)
    (w : {ρ : ℂ // xiZeta ρ = 0} → ℝ) (hw0 : ∀ ρ, 0 ≤ w ρ)
    (hw : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, w ρ ≤ K * (σ ^ 2 / (σ ^ 2 + (ρ : ℂ).im ^ 2))) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} => (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ) ∧
    ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ
      ≤ K * σ * (Lup (1 / 2 + σ) + 1 / 40) := by
  obtain ⟨hS, hle⟩ := zeroSum_re_le (s := 1 / 2 + σ) (by linarith)
  set r : {ρ : ℂ // xiZeta ρ = 0} → ℝ := fun ρ =>
    ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (((1 / 2 + σ : ℝ) : ℂ) - ρ) + 1 / ρ)).re
  have hr : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, r ρ = (analyticOrderNatAt xiZeta ρ : ℝ) *
      (1 / (((1 / 2 + σ : ℝ) : ℂ) - ρ) + 1 / ρ).re := by
    intro ρ; simp [r, mul_re]
  have hpt : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      σ ^ 2 / (σ ^ 2 + (ρ : ℂ).im ^ 2) ≤ σ * (1 / (((1 / 2 + σ : ℝ) : ℂ) - ρ) + 1 / ρ).re := by
    intro ρ
    have hρ := xiZeta_zero_re_RH hRH ρ.2
    obtain ⟨⟨x, γ⟩, hz⟩ := ρ
    simp only at hρ ⊢
    subst hρ
    have hre2 : (1 / (((1 / 2 + σ : ℝ) : ℂ) - ⟨1 / 2, γ⟩) + 1 / ⟨1 / 2, γ⟩).re
        = σ / (σ ^ 2 + γ ^ 2) + (1 / 2) / (1 / 4 + γ ^ 2) := by
      simp [normSq_apply]
      field_simp
      ring
    rw [hre2]
    have : 0 ≤ σ * ((1 / 2) / (1 / 4 + γ ^ 2)) := by
      apply mul_nonneg (by linarith); positivity
    have e : σ ^ 2 / (σ ^ 2 + γ ^ 2) = σ * (σ / (σ ^ 2 + γ ^ 2)) := by ring
    rw [e, mul_add]
    linarith
  have hcmp : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ ≤ K * σ * r ρ := by
    intro ρ
    rw [hr]
    have hm : (0 : ℝ) ≤ analyticOrderNatAt xiZeta ρ := Nat.cast_nonneg _
    have h1 : w ρ ≤ K * (σ * (1 / (((1 / 2 + σ : ℝ) : ℂ) - ρ) + 1 / ρ).re) :=
      (hw ρ).trans (mul_le_mul_of_nonneg_left (hpt ρ) hK)
    have := mul_le_mul_of_nonneg_left h1 hm
    linarith
  have hnn : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, 0 ≤ (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ :=
    fun ρ => mul_nonneg (Nat.cast_nonneg _) (hw0 ρ)
  have hS' : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => K * σ * r ρ := hS.mul_left _
  have hsum := Summable.of_nonneg_of_le hnn hcmp hS'
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, K * σ * r ρ := hsum.tsum_le_tsum hcmp hS'
    _ = K * σ * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, r ρ := tsum_mul_left
    _ ≤ K * σ * (Lup (1 / 2 + σ) + 1 / 40) := by
        apply mul_le_mul_of_nonneg_left hle; nlinarith

end Cramer
