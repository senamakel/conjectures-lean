import LLS.Analytic.ZeroSum
import LLS.Analytic.LogFormula
import Erdos985.Analytic.Constants
import Erdos985.Analytic.Digamma

/-!
# Zero sums at `s = 1`, `s = 1 + a` and `s = 2`, for a primitive character under GRH

For a primitive non-trivial `ψ` mod `N`, write `D(s) = Λ'/Λ(s, ψ)` (Mathlib's completed
`L`-function, no conductor factor) and `Z₂ = Σ_ρ m_ρ/|ρ|²`. Under GRH every zero has
`Re ρ = 1/2`, and the Hadamard product gives, with `0 ≤ a`:

* `Re D(1) ≤ Re D(1 + a) + (a/(1 + 2a)) Z₂` (`re_D_one_le`), from
  `Re (1/(1 + a − ρ) − 1/(1 − ρ)) ≥ −(a/(1 + 2a))/|ρ|²`;
* `Z₂(ψ⁻¹) = Z₂(ψ)` and `Z₂ ≤ (1 + 2a)(log N + Re D(1 + a, ψ) + Re D(1 + a, ψ⁻¹))`
  (`Z2_le`), from `Z₂ = log N + Re D(1, ψ) + Re D(1, ψ⁻¹)` (`LLS.Z2_eq`);
* `‖D(0)‖ ≤ log N + Z₂ + 2.52` (`norm_D_zero_le`), from the functional equation
  `−D(0, ψ) = log N + D(1, ψ⁻¹)`, `‖D(1) − D(2)‖ ≤ Z₂` and `‖D(2)‖ ≤ 2.52`.

This is the zero-sum input of Bach–Sorenson's Lemma 4.6 (their kernel `x^s/(s + a)²`), in the
form needed for the kernel `x^s/s²` of `LLS.LogAux.log_explicit_formula`.
-/

namespace BachSorenson.Two

open Complex Erdos985 Erdos985.Analytic LLS

variable {N : ℕ} [NeZero N]

/-- The Hadamard difference `D(z) − D(w) = Σ_ρ m_ρ (1/(z − ρ) − 1/(w − ρ))`. -/
lemma hasSum_D_sub {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {z w : ℂ}
    (hz : DirichletCharacter.completedLFunction χ z ≠ 0)
    (hw : DirichletCharacter.completedLFunction χ w ≠ 0) :
    HasSum (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
          * (1 / (z - ρ) - 1 / (w - ρ))) (D χ z - D χ w) := by
  obtain ⟨-, b, H⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  obtain ⟨sz, ez⟩ := H z hz
  obtain ⟨sw, ew⟩ := H w hw
  have := sz.hasSum.sub sw.hasSum
  convert this using 1
  · funext ρ; ring
  · unfold D; rw [ez, ew]; ring

lemma completed_ne_zero_of_one_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) : DirichletCharacter.completedLFunction χ s ≠ 0 :=
  DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs

lemma real_shift_ge {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    -(a / (1 + 2 * a)) / (1 / 4 + u)
      ≤ (1 / 2 + a) / ((1 / 2 + a) ^ 2 + u) - (1 / 2) / (1 / 4 + u) := by
  have h4 : (0 : ℝ) < 1 + 2 * a := by linarith
  have hA : (0 : ℝ) < 1 / 4 + u := by linarith
  have hB : (0 : ℝ) < (1 / 2 + a) ^ 2 + u := by positivity
  have key : (1 / 2) / ((1 + 2 * a) * (1 / 4 + u)) ≤ (1 / 2 + a) / ((1 / 2 + a) ^ 2 + u) := by
    rw [div_le_div_iff₀ (by positivity) hB]
    nlinarith [mul_nonneg ha hu, mul_nonneg (mul_nonneg ha ha) hu]
  have e : (1 / 2) / ((1 + 2 * a) * (1 / 4 + u)) - (1 / 2) / (1 / 4 + u)
      = -(a / (1 + 2 * a)) / (1 / 4 + u) := by
    field_simp; ring
  linarith

/-- On the critical line, `Re (1/(1 + a − ρ) − 1/(1 − ρ)) ≥ −(a/(1 + 2a))/|ρ|²`. -/
lemma re_shift_ge {ρ : ℂ} (hρ : ρ.re = 1 / 2) {a : ℝ} (ha : 0 ≤ a) :
    -(a / (1 + 2 * a)) / ‖ρ‖ ^ 2 ≤ (1 / ((1 + a : ℝ) - ρ) - 1 / (1 - ρ) : ℂ).re := by
  obtain ⟨r, γ⟩ := ρ
  simp only at hρ
  subst hρ
  rw [← Complex.normSq_eq_norm_sq]
  have h := real_shift_ge ha (sq_nonneg γ)
  simp [normSq_apply]
  convert h using 2 <;> ring

lemma hasSum_Z2 (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    HasSum (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2)
      (Z2 χ) :=
  (Z2_eq hGRH hprim hχ).1.hasSum

/-- `Re D(1) ≤ Re D(1 + a) + (a/(1 + 2a)) Z₂`. -/
theorem re_D_one_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℝ} (ha : 0 ≤ a) :
    (D χ 1).re ≤ (D χ ((1 + a : ℝ) : ℂ)).re + a / (1 + 2 * a) * Z2 χ := by
  have h1 := completed_ne_zero_of_one_le χ hχ (s := ((1 + a : ℝ) : ℂ)) (by simp; linarith)
  have h0 := completed_ne_zero_of_one_le χ hχ (s := 1) (by simp)
  have hS := Complex.reCLM.hasSum (hasSum_D_sub hprim hχ h1 h0)
  have hZ := (hasSum_Z2 hGRH hprim hχ).mul_left (-(a / (1 + 2 * a)))
  have hle := hasSum_le (fun ρ => ?_) hZ hS
  · simp only [Complex.reCLM_apply, sub_re] at hle
    linarith
  · have hre := completedLFunction_zero_re hGRH hprim hχ ρ.2
    have := re_shift_ge hre ha
    simp only [Complex.reCLM_apply]
    rw [show ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
        * (1 / (((1 + a : ℝ) : ℂ) - ρ) - 1 / (1 - ρ))).re
        = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          * (1 / (((1 + a : ℝ) : ℂ) - ρ) - 1 / (1 - ρ)).re by
      rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]]
    have hm : (0 : ℝ) ≤ analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ :=
      Nat.cast_nonneg _
    have e : -(a / (1 + 2 * a)) * ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ)
        ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ)
          ρ : ℝ) * (-(a / (1 + 2 * a)) / ‖(ρ : ℂ)‖ ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left this hm

lemma Z2_inv (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) : Z2 χ⁻¹ = Z2 χ := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  rw [(Z2_eq hGRH hprim.inv hχi).2, (Z2_eq hGRH hprim hχ).2, inv_inv]
  ring

/-- `Z₂ ≤ (1 + 2a)(log N + Re D(1 + a, ψ) + Re D(1 + a, ψ⁻¹))`. -/
theorem Z2_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {a : ℝ} (ha : 0 ≤ a) :
    Z2 χ ≤ (1 + 2 * a) * (Real.log N + (D χ ((1 + a : ℝ) : ℂ)).re
      + (D χ⁻¹ ((1 + a : ℝ) : ℂ)).re) := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have e := (Z2_eq hGRH hprim hχ).2
  have h1 := re_D_one_le hGRH hprim hχ ha
  have h2 := re_D_one_le hGRH hprim.inv hχi ha
  rw [Z2_inv hGRH hprim hχ] at h2
  have h4 : (0 : ℝ) < 1 + 2 * a := by linarith
  have key : Z2 χ * (1 - 2 * (a / (1 + 2 * a))) ≤ Real.log N + (D χ ((1 + a : ℝ) : ℂ)).re
      + (D χ⁻¹ ((1 + a : ℝ) : ℂ)).re := by nlinarith
  have e2 : 1 - 2 * (a / (1 + 2 * a)) = 1 / (1 + 2 * a) := by field_simp; ring
  rw [e2, mul_one_div, div_le_iff₀ h4] at key
  linarith

/-- On the critical line, `‖1/(1 − ρ) − 1/(2 − ρ)‖ ≤ 1/|ρ|²`. -/
lemma norm_one_two_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖1 / (1 - ρ) - 1 / (2 - ρ)‖ ≤ 1 / ‖ρ‖ ^ 2 := by
  have h10 : (1 : ℂ) - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have h20 : (2 : ℂ) - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have e : 1 / (1 - ρ) - 1 / (2 - ρ) = 1 / ((1 - ρ) * (2 - ρ)) := by
    field_simp; ring
  rw [e, norm_div, norm_one, norm_mul]
  have hn1 : ‖1 - ρ‖ = ‖ρ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (1 - ρ)), ← Real.sqrt_sq (norm_nonneg ρ),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    congr 1
    obtain ⟨r, γ⟩ := ρ
    simp only at hρ; subst hρ
    simp [normSq_apply]; ring
  have hn2 : ‖ρ‖ ≤ ‖2 - ρ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (2 - ρ)), ← Real.sqrt_sq (norm_nonneg ρ),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    apply Real.sqrt_le_sqrt
    obtain ⟨r, γ⟩ := ρ
    simp only at hρ; subst hρ
    simp [normSq_apply]; nlinarith
  have hp : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  rw [hn1, sq]
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hn2 hp.le)

/-- `‖D(1) − D(2)‖ ≤ Z₂` under GRH. -/
theorem norm_D_one_sub_two_le (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ‖D χ 1 - D χ 2‖ ≤ Z2 χ := by
  have h1 := completed_ne_zero_of_one_le χ hχ (s := 1) (by simp)
  have h2 := completed_ne_zero_of_one_le χ hχ (s := 2) (by simp)
  have hS := hasSum_D_sub hprim hχ h1 h2
  have hb := tsum_of_norm_bounded (hasSum_Z2 hGRH hprim hχ) (f := fun ρ :
      {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
          * (1 / (1 - ρ) - 1 / (2 - ρ))) (fun ρ => by
    have h := norm_one_two_le (completedLFunction_zero_re hGRH hprim hχ ρ.2)
    have hm : (0 : ℝ) ≤ analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ :=
      Nat.cast_nonneg _
    calc ‖(analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
          * (1 / (1 - (ρ : ℂ)) - 1 / (2 - ρ))‖
        = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          * ‖1 / (1 - (ρ : ℂ)) - 1 / (2 - ρ)‖ := by rw [norm_mul, Complex.norm_natCast]
      _ ≤ (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          * (1 / ‖(ρ : ℂ)‖ ^ 2) := mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring)
  rwa [hS.tsum_eq] at hb

lemma digamma_three_halves : Complex.digamma (3 / 2) = 2 - 2 * Complex.log 2
    - Real.eulerMascheroniConstant := by
  have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h := Complex.digamma_apply_add_one (1 / 2) hs
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Complex.digamma_one_half] at h
  rw [h]; ring

lemma re_digamma_three_halves : (Complex.digamma (3 / 2)).re
    = 2 - 2 * Real.log 2 - Real.eulerMascheroniConstant := by
  have hl : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    have := Complex.ofReal_log (x := 2) (by norm_num); push_cast at this; exact this.symm
  have e : (2 : ℂ) - 2 * ((Real.log 2 : ℝ) : ℂ) - ((Real.eulerMascheroniConstant : ℝ) : ℂ)
      = ((2 - 2 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by push_cast; ring
  rw [digamma_three_halves, hl, e, Complex.ofReal_re]

omit [NeZero N] in
/-- `gammaLogDeriv χ 2` is real, with `|·| ≤ 1`. -/
lemma gammaLogDeriv_two (χ : DirichletCharacter ℂ N) :
    ∃ g : ℝ, gammaLogDeriv χ 2 = (g : ℂ) ∧ |g| ≤ 1 := by
  have hγ := DigammaAux.eulerMascheroniConstant_gt
  have hγ' := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hlpi : Real.log Real.pi < 1.15 := by
    rw [Real.log_lt_iff_lt_exp Real.pi_pos]
    have := Real.quadratic_le_exp_of_nonneg (x := (0.15 : ℝ)) (by norm_num)
    have h3 := Real.exp_one_gt_d9
    have : Real.exp 1.15 = Real.exp 1 * Real.exp 0.15 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hlpi0 : 1 < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    have := Real.exp_one_lt_d9; linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  unfold gammaLogDeriv parity
  split_ifs
  · refine ⟨-(1 / 2) * Real.log Real.pi - 1 / 2 * Real.eulerMascheroniConstant, ?_, ?_⟩
    · rw [show ((2 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 1 by norm_num, Complex.digamma_one]
      push_cast; ring
    · rw [abs_le]; constructor <;> linarith
  · refine ⟨-(1 / 2) * Real.log Real.pi + 1 / 2 * (2 - 2 * Real.log 2
      - Real.eulerMascheroniConstant), ?_, ?_⟩
    · rw [show ((2 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 3 / 2 by norm_num, digamma_three_halves]
      have hl : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
        have := Complex.ofReal_log (x := 2) (by norm_num); push_cast at this; exact this.symm
      rw [hl]; push_cast; ring
    · rw [abs_le]; constructor <;> linarith

/-- `‖D(2)‖ ≤ 2.52`. -/
lemma norm_D_two_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : ‖D χ 2‖ ≤ 2.52 := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have e := logDeriv_LFunction_eq hχ hs
  have hD : D χ 2 = deriv (DirichletCharacter.LFunction χ) 2 / DirichletCharacter.LFunction χ 2
      + gammaLogDeriv χ 2 := by unfold D; rw [e]; ring
  obtain ⟨g, hg, hg'⟩ := gammaLogDeriv_two χ
  have hL : ‖deriv (DirichletCharacter.LFunction χ) 2 / DirichletCharacter.LFunction χ 2‖
      ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs]
    have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
    have h' : deriv (LSeries fun n => χ n) 2 / LSeries (fun n => χ n) 2
        = -LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) 2 := by
      simp only [Pi.mul_def] at h; rw [h, neg_div, neg_neg]
    rw [h', norm_neg, LSeries]
    refine tsum_of_norm_bounded summable_vonMangoldt_rpow.hasSum fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq]; simp only [hn, ↓reduceIte, norm_mul]
      have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
      have hΛ : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
        rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [hΛ]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hp : (n : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ ((2 : ℂ).re) := by
        simp only [re_ofNat]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      have hp0 : (0 : ℝ) < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
      calc ‖χ n‖ * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ ((2 : ℂ).re)
          ≤ 1 * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) := by
            apply div_le_div₀ (by positivity) (by gcongr) hp0 hp
        _ = _ := by ring
  have hL' := hL.trans tsum_vonMangoldt_rpow_le
  rw [hD, hg]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- `‖D(0, ψ)‖ ≤ log N + Z₂(ψ) + 2.52` under GRH. -/
theorem norm_D_zero_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) : ‖D χ 0‖ ≤ Real.log N + Z2 χ + 2.52 := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hi1 := completed_ne_zero_of_one_le χ⁻¹ hχi (s := 1) (by simp)
  have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ (s := 1) hi1
  rw [sub_self] at hFE
  have hD0 : D χ 0 = -((Real.log N : ℂ) + D χ⁻¹ 1) := by unfold D; rw [← hFE]; ring
  have h12 := norm_D_one_sub_two_le hGRH hprim.inv hχi
  rw [Z2_inv hGRH hprim hχ] at h12
  have h2 := norm_D_two_le hχi
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rw [hD0, norm_neg]
  calc ‖(Real.log N : ℂ) + D χ⁻¹ 1‖ ≤ ‖(Real.log N : ℂ)‖ + ‖D χ⁻¹ 1‖ := norm_add_le _ _
    _ ≤ Real.log N + (‖D χ⁻¹ 1 - D χ⁻¹ 2‖ + ‖D χ⁻¹ 2‖) := by
        rw [Complex.norm_real, Real.norm_of_nonneg hlog]
        gcongr
        calc ‖D χ⁻¹ 1‖ = ‖(D χ⁻¹ 1 - D χ⁻¹ 2) + D χ⁻¹ 2‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by linarith

end BachSorenson.Two
