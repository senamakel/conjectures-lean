import Littlewood.Termwise
import Lindelof.Monotone
import Erdos985.Analytic.Principal.Identity.Zeros

/-!
# Step 4: the zeros of `ξ` under RH

Notation: `m ρ = ord_ρ ξ` for `ρ` in the zero set `{ρ // ξ ρ = 0}`.

* `hasSum_logDeriv_xi_sub`: Hadamard's expansion, differenced at `z` and `s`, kills the
  Hadamard constant: `ξ'/ξ(z) - ξ'/ξ(s) = Σ m (1/(z-ρ) - 1/(s-ρ))`.
* `hasSum_re_logDeriv_xi` (RH): `Re ξ'/ξ(s) = Σ_ρ m Re 1/(s-ρ)` for `Re s > 1/2`; each term
  is `m (σ - 1/2)/|s - ρ|² ≥ 0`. The constant and the `1/ρ` terms cancel by `ξ(1 - s̄) = conj ξ(s)`.
* `perron_xi` (RH): the term-by-term Perron formula for `-ξ'/ξ`.
-/

open Complex MeasureTheory ComplexConjugate

namespace Littlewood

open Erdos985.Analytic Erdos985.Analytic.PrincipalAux

/-- The zero set of `ξ`. -/
abbrev XiZero := {ρ : ℂ // xiZeta ρ = 0}

/-- The multiplicity of a zero, as a complex number. -/
noncomputable abbrev mult (ρ : XiZero) : ℂ := (analyticOrderNatAt xiZeta ρ : ℂ)

lemma xiZeta_ne_zero_of_one_lt {z : ℂ} (hz : 1 ≤ z.re) : xiZeta z ≠ 0 := fun h => by
  linarith [(PrincipalAux.xiZeta_zero_re_mem h).2]

lemma countable_xiZero : Countable XiZero := PrincipalAux.countable_xiZeta_zeros

/-- Hadamard, differenced. -/
theorem hasSum_logDeriv_xi_sub {z s : ℂ} (hz : xiZeta z ≠ 0) (hs : xiZeta s ≠ 0) :
    HasSum (fun ρ : XiZero => mult ρ * (1 / (z - ρ) - 1 / (s - ρ)))
      (deriv xiZeta z / xiZeta z - deriv xiZeta s / xiZeta s) := by
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv differentiable_xiZeta
    (by rw [xiZeta_zero]; exact one_ne_zero) xiZeta_growth
  obtain ⟨h1s, h1e⟩ := hb z hz
  obtain ⟨h2s, h2e⟩ := hb s hs
  have := h1s.hasSum.sub h2s.hasSum
  rw [h1e, h2e]
  convert this using 1
  · funext ρ; ring
  · ring

/-- Under RH: `Re ξ'/ξ(s) = Σ_ρ m Re 1/(s - ρ)` for `Re s > 1/2`. -/
theorem hasSum_re_logDeriv_xi (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasSum (fun ρ : XiZero => (mult ρ * (1 / (s - ρ))).re) (deriv xiZeta s / xiZeta s).re := by
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv differentiable_xiZeta
    (by rw [xiZeta_zero]; exact one_ne_zero) xiZeta_growth
  set w := 1 - conj s with hw
  have hs0 : xiZeta s ≠ 0 := Lindelof.xiZeta_ne_zero_of_RH hRH hs
  have hw0 : xiZeta w ≠ 0 := by
    rw [hw, xiZeta_one_sub, Lindelof.xiZeta_conj, map_ne_zero]; exact hs0
  obtain ⟨hsz, hz'⟩ := hb s hs0
  obtain ⟨hsw, hw'⟩ := hb w hw0
  have hLw : deriv xiZeta w / xiZeta w = -conj (deriv xiZeta s / xiZeta s) := by
    rw [hw, Lindelof.deriv_xiZeta_one_sub, xiZeta_one_sub, Lindelof.deriv_xiZeta_conj,
      Lindelof.xiZeta_conj, map_div₀]
    ring
  -- the difference of the two Hadamard sums
  have hdiff := (hsz.hasSum.sub hsw.hasSum)
  have hval : (∑' ρ : XiZero, mult ρ * (1 / (s - ρ) + 1 / ρ)) -
      ∑' ρ : XiZero, mult ρ * (1 / (w - ρ) + 1 / ρ)
      = deriv xiZeta s / xiZeta s - deriv xiZeta w / xiZeta w := by
    rw [hz', hw']; ring
  rw [hval, hLw] at hdiff
  have hre := Complex.hasSum_re hdiff
  -- termwise: under RH, `Re(1/(s-ρ) - 1/(w-ρ)) = 2 Re 1/(s-ρ)`
  have hterm : ∀ ρ : XiZero, (mult ρ * (1 / (s - ρ) + 1 / ρ) - mult ρ * (1 / (w - ρ) + 1 / ρ)).re
      = 2 * (mult ρ * (1 / (s - ρ))).re := by
    intro ρ
    have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
    have hN : normSq (w - ρ) = normSq (s - ρ) := by
      simp only [hw, normSq_apply, sub_re, sub_im, one_re, one_im, conj_re, conj_im, hρ]
      ring
    have e : mult ρ * (1 / (s - ρ) + 1 / ρ) - mult ρ * (1 / (w - ρ) + 1 / ρ) =
        mult ρ * ((s - ρ)⁻¹ - (w - ρ)⁻¹) := by ring
    rw [e, mul_re, mul_re, sub_re, sub_im, inv_re, inv_re, hN, one_div, inv_re]
    simp only [mult, natCast_re, natCast_im, zero_mul, sub_zero, sub_re, hρ, hw, one_re, conj_re]
    ring
  simp_rw [hterm] at hre
  have hfin : (deriv xiZeta s / xiZeta s - -conj (deriv xiZeta s / xiZeta s)).re
      = 2 * (deriv xiZeta s / xiZeta s).re := by
    simp only [sub_re, neg_re, conj_re]; ring
  rw [hfin] at hre
  have := hre.div_const 2
  simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at this
  exact this

/-- Each zero term of `hasSum_re_logDeriv_xi` is `m (σ - 1/2) / |s - ρ|²`. -/
lemma re_mult_div (hRH : RiemannHypothesis) (s : ℂ) (ρ : XiZero) :
    (mult ρ * (1 / (s - ρ))).re = (analyticOrderNatAt xiZeta ρ : ℝ) * ((s.re - 1 / 2) / normSq (s - ρ)) := by
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  rw [mul_re, one_div, inv_re, inv_im]
  simp [mult, sub_re, hρ]

/-- Under RH, `|ρ| ≤ (|s|/η + 1) |ρ - s|` where `η = Re s - 1/2 > 0`. -/
lemma norm_le_mul_norm_sub (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) (ρ : XiZero) :
    ‖(ρ : ℂ)‖ ≤ (‖s‖ / (s.re - 1 / 2) + 1) * ‖(ρ : ℂ) - s‖ := by
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  have hη : 0 < s.re - 1 / 2 := by linarith
  have hd : s.re - 1 / 2 ≤ ‖(ρ : ℂ) - s‖ := by
    have := abs_re_le_norm ((ρ : ℂ) - s)
    rw [sub_re, hρ, abs_of_neg (by linarith)] at this
    linarith
  have h1 : ‖(ρ : ℂ)‖ ≤ ‖s‖ + ‖(ρ : ℂ) - s‖ := by
    calc ‖(ρ : ℂ)‖ = ‖s + ((ρ : ℂ) - s)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖s‖ ≤ ‖s‖ / (s.re - 1 / 2) * ‖(ρ : ℂ) - s‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]
    exact mul_le_mul_of_nonneg_left hd (norm_nonneg _)
  nlinarith

/-- The summability hypothesis of `perron_termwise` for the zeros of `ξ` (RH). -/
theorem summable_zero_weight (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun ρ : XiZero =>
      ‖-mult ρ‖ / ‖(ρ : ℂ) - s‖ * (1 + ‖(ρ : ℂ) - s‖) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨hsum_ε, -⟩ := hadamard_logDeriv differentiable_xiZeta
    (by rw [xiZeta_zero]; exact one_ne_zero) xiZeta_growth
  have hS := hsum_ε (1 / 2) (by norm_num)
  set B := ‖s‖ / (s.re - 1 / 2) + 1 with hB
  have hB0 : 0 < B := by
    have : 0 < s.re - 1 / 2 := by linarith
    positivity
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ρ => ?_)
    (hS.mul_left (B ^ (1 + 1 / 2 : ℝ)))
  have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
  have hρ0 : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 fun h => by rw [h] at hρ; norm_num at hρ
  set d := ‖(ρ : ℂ) - s‖ with hd
  have hd0 : 0 < d := by
    have := abs_re_le_norm ((ρ : ℂ) - s)
    rw [sub_re, hρ, abs_of_neg (by linarith)] at this
    rw [hd]; linarith
  have hle := norm_le_mul_norm_sub hRH hs ρ
  rw [norm_neg, show ‖mult ρ‖ = (analyticOrderNatAt xiZeta ρ : ℝ) by simp [mult]]
  set mm := (analyticOrderNatAt xiZeta ρ : ℝ)
  have hmm : 0 ≤ mm := Nat.cast_nonneg _
  -- `(1 + d)^{-1/2} ≤ d^{-1/2}` and `‖ρ‖^{3/2} ≤ B^{3/2} d^{3/2}`
  have h1 : (1 + d) ^ (-(1 / 2 : ℝ)) ≤ d ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hd0 (by linarith) (by norm_num)
  have h2 : ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ) ≤ B ^ (1 + 1 / 2 : ℝ) * d ^ (1 + 1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hB0.le hd0.le]
    exact Real.rpow_le_rpow (norm_nonneg _) hle (by norm_num)
  have h3 : mm / d * d ^ (-(1 / 2 : ℝ)) = mm / d ^ (1 + 1 / 2 : ℝ) := by
    rw [Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
    field_simp
  calc mm / d * (1 + d) ^ (-(1 / 2 : ℝ)) ≤ mm / d * d ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = mm / d ^ (1 + 1 / 2 : ℝ) := h3
    _ ≤ B ^ (1 + 1 / 2 : ℝ) * (mm / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        calc mm / d ^ (1 + 1 / 2 : ℝ) * ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)
            ≤ mm / d ^ (1 + 1 / 2 : ℝ) * (B ^ (1 + 1 / 2 : ℝ) * d ^ (1 + 1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = B ^ (1 + 1 / 2 : ℝ) * mm := by
              field_simp

/-- **Perron for `-ξ'/ξ`** (RH): for `Re s > 1/2`, `x ≥ 1`,
`(1/2π) ∫ -ξ'/ξ(s + w) x^w / w² dv = -ξ'/ξ(s) log x - Σ_ρ m (x^{ρ-s} - 1)/(ρ - s)²`. -/
theorem perron_xi (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    Integrable (fun v : ℝ => -(deriv xiZeta (s + lineP v) / xiZeta (s + lineP v)) *
      ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))) ∧
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, -(deriv xiZeta (s + lineP v) / xiZeta (s + lineP v)) *
        ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
      = -(deriv xiZeta s / xiZeta s) * Real.log x +
          ∑' ρ : XiZero, -mult ρ * (((x : ℂ) ^ ((ρ : ℂ) - s) - 1) / ((ρ : ℂ) - s) ^ 2) := by
  have := countable_xiZero
  have hs0 : xiZeta s ≠ 0 := Lindelof.xiZeta_ne_zero_of_RH hRH hs
  have hline : ∀ v : ℝ, xiZeta (s + lineP v) ≠ 0 := fun v =>
    xiZeta_ne_zero_of_one_lt (by simp; linarith)
  refine perron_termwise (ι := XiZero) (G := fun z => -(deriv xiZeta z / xiZeta z)) hx
    (fun ρ : XiZero => (ρ : ℂ)) (fun ρ : XiZero => -mult ρ) (fun ρ => ?_) (fun ρ h => ?_) (summable_zero_weight hRH hs) (fun v => ?_) ?_
  · have hρ : (ρ : ℂ).re = 1 / 2 := Lindelof.xiZeta_zero_re_of_RH hRH ρ.2
    simp only [sub_re, hρ]; linarith
  · exact hs0 (h ▸ ρ.2)
  · have h := (hasSum_logDeriv_xi_sub (hline v) hs0).neg
    convert h using 1
    · funext ρ; ring
    · ring
  · have hcd : Continuous (deriv xiZeta) :=
      (differentiable_xiZeta.contDiff (n := 1)).continuous_deriv le_rfl
    have hc : Continuous fun v : ℝ => s + lineP v := continuous_const.add continuous_lineP
    exact ((hcd.comp hc).div (differentiable_xiZeta.continuous.comp hc) hline).neg

end Littlewood
