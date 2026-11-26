import Erdos985.Analytic.Principal

/-!
# Sums over the zeros of `ξ` under RH

`ξ = xiZeta` is erdos-985's entire completed zeta function, zeros `ρ` with multiplicity
`mult ρ`. Under RH every zero has `Re ρ = 1/2`, and:

* `zeroSum_hasSum`: `Σ_ρ m/|ρ|² = 2 + γ − log 4π` (`< 1/20`), so `|ρ|² ≥ 20` for every zero;
* `kern_hasSum`: for real `a > 1/2`, `Σ_ρ m · a/(a² + γ²) = Re ξ'/ξ(a + 1/2)` (Hadamard; the
  constant of the factorisation cancels against `Σ Re 1/ρ`);
* `kern_le`: for `a ≥ 2`, `Σ_ρ m · a/(a² + γ²) ≤ ½ log a − ½ log 2π + (12/5)/a`, using
  `ξ'/ξ = ζ'/ζ + 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2)`, `ζ'/ζ(s) ≤ 0` and `ψ(y) ≤ log y`.

The last bound is the zero-density input: a Poisson-kernel form of `N(T+1) − N(T) ≪ log T`.
-/

namespace Schoenfeld

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux ArithmeticFunction

/-- The zeros of `ξ`. -/
abbrev Zeros := {ρ : ℂ // xiZeta ρ = 0}

instance : Countable Zeros := countable_xiZeta_zeros

/-- Multiplicity of a zero, as a real number. -/
noncomputable def mult (ρ : Zeros) : ℝ := (analyticOrderNatAt xiZeta (ρ : ℂ) : ℝ)

lemma mult_nonneg (ρ : Zeros) : 0 ≤ mult ρ := Nat.cast_nonneg _

lemma one_le_mult (ρ : Zeros) : 1 ≤ mult ρ := by
  unfold mult
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (xiZeta_order_ne_zero ρ.2)

/-- Under RH, `ξ` has no zeros with `Re s > 1/2`. -/
theorem xiZeta_ne_zero_of_half_lt (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) : xiZeta s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; rw [xiZeta_one] at h; norm_num at h
  rw [xiZeta_eq hs0 hs1] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd h hs1'
    · exact h
  have hζ : riemannZeta s = 0 := by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s hζ htriv hs1
  linarith

theorem re_eq_half (hRH : RiemannHypothesis) (ρ : Zeros) : (ρ : ℂ).re = 1 / 2 := by
  have h1 : ¬ 1 / 2 < (ρ : ℂ).re := fun h => xiZeta_ne_zero_of_half_lt hRH h ρ.2
  have h2 : ¬ 1 / 2 < (1 - (ρ : ℂ)).re := fun h =>
    xiZeta_ne_zero_of_half_lt hRH h (by rw [xiZeta_one_sub]; exact ρ.2)
  simp only [sub_re, one_re] at h2
  linarith

lemma normSq_of_re {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
  rw [← normSq_eq_norm_sq, normSq_apply, hρ]; ring

lemma re_inv_of_re {ρ : ℂ} (hρ : ρ.re = 1 / 2) : (1 / ρ).re = 1 / 2 / ‖ρ‖ ^ 2 := by
  rw [one_div, inv_re, normSq_eq_norm_sq, hρ]

/-- `Σ_ρ m/|ρ|² = 2 + γ − log 4π`. -/
theorem zeroSum_hasSum (hRH : RiemannHypothesis) :
    HasSum (fun ρ : Zeros => mult ρ / ‖(ρ : ℂ)‖ ^ 2)
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) := by
  have hx0 : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; norm_num
  have hx1 : xiZeta 1 ≠ 0 := by rw [xiZeta_one]; norm_num
  obtain ⟨-, b, H⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨s1, e1⟩ := H 1 hx1
  have hz : ∀ ρ : Zeros, (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero, deriv_xiZeta_zero, xiZeta_zero, div_one] at e0
  rw [deriv_xiZeta_one, xiZeta_one, div_one] at e1
  set T := ∑' ρ : Zeros, (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ) with hT
  have hTv : T = 2 * completedRiemannZeta₀ 1 := by
    have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
      rw [← completedRiemannZeta₀_one_sub]; norm_num
    rw [h01] at e0
    linear_combination e0 - e1
  have hre := Complex.reCLM.hasSum s1.hasSum
  rw [← hT, hTv] at hre
  simp only [Complex.reCLM_apply, re_two_completedRiemannZeta₀_one] at hre
  refine hre.congr_fun fun ρ => ?_
  have hρ := re_eq_half hRH ρ
  have h1 : (1 - (ρ : ℂ)) = (starRingEnd ℂ) ρ := by
    apply Complex.ext <;> simp [hρ]; norm_num
  rw [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re, h1, one_div,
    inv_re, normSq_conj, re_inv_of_re hρ, conj_re, normSq_eq_norm_sq, hρ, mult]
  ring

theorem zeroSum_summable (hRH : RiemannHypothesis) :
    Summable (fun ρ : Zeros => mult ρ / ‖(ρ : ℂ)‖ ^ 2) := (zeroSum_hasSum hRH).summable

theorem zeroSum_le (hRH : RiemannHypothesis) :
    ∑' ρ : Zeros, mult ρ / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 := by
  rw [(zeroSum_hasSum hRH).tsum_eq]; exact two_add_gamma_sub_log_lt.le

/-- Every zero has `|ρ|² ≥ 20`. -/
theorem twenty_le_normSq (hRH : RiemannHypothesis) (ρ : Zeros) : 20 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
  have hpos : 0 < ‖(ρ : ℂ)‖ ^ 2 := by
    have : (ρ : ℂ) ≠ 0 := fun h => by have := re_eq_half hRH ρ; rw [h] at this; norm_num at this
    positivity
  have h1 : mult ρ / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
    ((zeroSum_summable hRH).le_tsum ρ fun j _ => div_nonneg (mult_nonneg j) (sq_nonneg _)).trans
      (zeroSum_le hRH)
  have h2 : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ 1 / 20 :=
    le_trans (div_le_div_of_nonneg_right (one_le_mult ρ) hpos.le) h1
  rw [div_le_div_iff₀ hpos (by norm_num)] at h2
  linarith

/-! ### The Poisson kernel sum -/

/-- `m · a/(a² + γ²)`: the real part of `m/(a + 1/2 − ρ)` when `Re ρ = 1/2`. -/
noncomputable def kern (a : ℝ) (ρ : Zeros) : ℝ := mult ρ * (a / (a ^ 2 + (ρ : ℂ).im ^ 2))

lemma kern_nonneg {a : ℝ} (ha : 0 ≤ a) (ρ : Zeros) : 0 ≤ kern a ρ :=
  mul_nonneg (mult_nonneg ρ) (div_nonneg ha (by positivity))

theorem kern_hasSum (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 / 2 < a) :
    HasSum (kern a) (deriv xiZeta ((a + 1 / 2 : ℝ) : ℂ) / xiZeta ((a + 1 / 2 : ℝ) : ℂ)).re := by
  set s : ℂ := ((a + 1 / 2 : ℝ) : ℂ) with hs
  have hx0 : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; norm_num
  have hxs : xiZeta s ≠ 0 := xiZeta_ne_zero_of_half_lt hRH (by simp [hs]; linarith)
  obtain ⟨-, b, H⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨ss, es⟩ := H s hxs
  have hz : ∀ ρ : Zeros, (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero, deriv_xiZeta_zero, xiZeta_zero, div_one] at e0
  -- `Re b = −(2 + γ − log 4π)/2`
  have hb : b.re = -((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2) := by
    have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
      rw [← completedRiemannZeta₀_one_sub]; norm_num
    have := re_two_completedRiemannZeta₀_one
    rw [← e0, h01, neg_re]
    rw [show (2 * completedRiemannZeta₀ 1).re = 2 * (completedRiemannZeta₀ 1).re by
      simp [mul_re]] at this
    linarith
  have hre := Complex.reCLM.hasSum ss.hasSum
  simp only [Complex.reCLM_apply] at hre
  have hD : (deriv xiZeta s / xiZeta s).re - b.re
      = (∑' ρ : Zeros, (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re := by
    rw [es, add_re]; ring
  have hhalf := (zeroSum_hasSum hRH).mul_left (1 / 2)
  have hsub := (hre.sub hhalf)
  rw [← hD, hb] at hsub
  convert hsub using 1
  · funext ρ
    have hρ := re_eq_half hRH ρ
    have hsr : (s - (ρ : ℂ)).re = a := by simp [hs, hρ]
    have hsi : (s - (ρ : ℂ)).im = -(ρ : ℂ).im := by simp [hs]
    have hns : normSq (s - (ρ : ℂ)) = a ^ 2 + (ρ : ℂ).im ^ 2 := by
      rw [normSq_apply, hsr, hsi]; ring
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, add_re]
    rw [re_inv_of_re hρ, one_div (s - (ρ : ℂ)), inv_re, hns, hsr, kern, mult]
    ring
  · ring

/-- `ζ'/ζ(s) = −Σ Λ(n) n^{−s}` is real and `≤ 0` for real `s > 1`. -/
theorem logDeriv_zeta_real_nonpos {s : ℝ} (hs : 1 < s) :
    (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).im = 0 ∧
      (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re ≤ 0 := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (Λ n : ℂ)) (s : ℂ) n
      = (((Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast; rfl
  have hL : LSeries (fun n => (Λ n : ℂ)) (s : ℂ)
      = ((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]; exact tsum_congr hterm
  have e : deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      = -((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [← hL, key]; ring
  rw [e]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re,
    true_and, neg_nonpos]
  exact tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)

/-- `Re ξ'/ξ(a + 1/2) ≤ ½ log a − ½ log 2π + (12/5)/a` for `a ≥ 2`. -/
theorem logDeriv_xi_le {a : ℝ} (ha : 2 ≤ a) :
    (deriv xiZeta ((a + 1 / 2 : ℝ) : ℂ) / xiZeta ((a + 1 / 2 : ℝ) : ℂ)).re
      ≤ Real.log a / 2 - Real.log (2 * Real.pi) / 2 + 12 / 5 / a := by
  set s : ℝ := a + 1 / 2 with hsdef
  have hs1 : 1 < s := by linarith
  have hs1' : 1 < (s : ℂ).re := by simpa using hs1
  have e := logDeriv_riemannZeta_eq hs1'
  have hD : deriv xiZeta (s : ℂ) / xiZeta (s : ℂ) = deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      + 1 / (s : ℂ) + 1 / ((s : ℂ) - 1) + gammaLogDeriv (1 : DirichletCharacter ℂ 1) (s : ℂ) := by
    rw [e]; ring
  rw [hD, gammaLogDeriv_one]
  have hdg : digamma ((s : ℂ) / 2) = ((BoundsAux.rD (s / 2) : ℝ) : ℂ) := by
    rw [show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; ring]
    exact BoundsAux.digamma_ofReal (by linarith)
  have hrD := (BoundsAux.rD_bounds (x := s / 2) (by linarith)).2
  obtain ⟨-, hz⟩ := logDeriv_zeta_real_nonpos hs1
  rw [hdg]
  have e1 : (1 / (s : ℂ)).re = 1 / s := by
    rw [show (1 / (s : ℂ)) = ((1 / s : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have e2 : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    rw [show (1 / ((s : ℂ) - 1)) = ((1 / (s - 1) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have e3 : (-(1 / 2) * ((Real.log Real.pi : ℝ) : ℂ) + 1 / 2 * ((BoundsAux.rD (s / 2) : ℝ) : ℂ)).re
      = -(1 / 2) * Real.log Real.pi + 1 / 2 * BoundsAux.rD (s / 2) := by
    rw [show (-(1 / 2) * ((Real.log Real.pi : ℝ) : ℂ) + 1 / 2 * ((BoundsAux.rD (s / 2) : ℝ) : ℂ))
      = (((-(1 / 2) * Real.log Real.pi + 1 / 2 * BoundsAux.rD (s / 2)) : ℝ) : ℂ) by push_cast; ring,
      ofReal_re]
  rw [add_re, add_re, add_re, e1, e2, e3]
  -- numerics
  have ha0 : 0 < a := by linarith
  have hlog2 : Real.log (s / 2) = Real.log s - Real.log 2 :=
    Real.log_div (by linarith) (by norm_num)
  have hls : Real.log s ≤ Real.log a + 1 / (2 * a) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s / a by positivity)
    rw [Real.log_div (by linarith) ha0.ne'] at h
    have : s / a - 1 = 1 / (2 * a) := by rw [hsdef]; field_simp; ring
    linarith
  have hpi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  have hfr : 1 / s + 1 / (s - 1) + 1 / (4 * a) ≤ 12 / 5 / a := by
    rw [hsdef, div_add_div _ _ (by linarith) (by linarith), div_add_div _ _ (by positivity)
      (by positivity), div_le_div_iff₀ (by positivity) ha0]
    nlinarith [mul_pos ha0 ha0, mul_pos (mul_pos ha0 ha0) ha0]
  have : 1 / (2 * a) / 2 = 1 / (4 * a) := by field_simp; ring
  nlinarith

theorem kern_le (hRH : RiemannHypothesis) {a : ℝ} (ha : 2 ≤ a) :
    ∑' ρ : Zeros, kern a ρ ≤ Real.log a / 2 - Real.log (2 * Real.pi) / 2 + 12 / 5 / a := by
  rw [(kern_hasSum hRH (by linarith)).tsum_eq]; exact logDeriv_xi_le ha

end Schoenfeld
