import Lindelof.Main
import Mertens.Statement

/-!
# Step A: `1/ζ(s) ≪ |t|^ε` on `σ ≥ 1/2 + δ` under RH

lindelof-rh gives a holomorphic logarithm `M` of `zetaQ = ζ₁/(s+1)` on `σ > 1/2` with
`‖M(σ+it)‖ ≤ C log(|t|+2)^α`, `α < 1`, on `1/2 + δ ≤ σ ≤ 2` (Borel–Carathéodory, then
Hadamard three-lines). Then `1/ζ = (s-1)/((s+1) exp M)`, so `‖1/ζ‖ ≤ exp ‖M‖ ≤ C_ε (|t|+2)^ε`.

`invZ s = (s - 1)/ζ₁(s)` is the entire-on-`σ > 1/2` version of `1/ζ` (it is `0` at `s = 1`,
where Mathlib's `riemannZeta 1` is a junk value).
-/

namespace Mertens

open Complex Filter Lindelof
open scoped ArithmeticFunction.Moebius

/-- `(s - 1)/ζ₁(s)`, equal to `1/ζ(s)` for `s ≠ 1`. -/
noncomputable def invZ (s : ℂ) : ℂ := (s - 1) / riemannZeta₁ s

lemma invZ_eq {s : ℂ} (hs : s ≠ 1) : invZ s = (riemannZeta s)⁻¹ := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv, inv_inv]
  unfold invZ
  rw [div_eq_mul_inv]

theorem differentiableOn_invZ (hRH : RiemannHypothesis) :
    DifferentiableOn ℂ invZ halfPlane := by
  have h1 : DifferentiableOn ℂ (fun s : ℂ => s - 1) halfPlane := by fun_prop
  have h2 : DifferentiableOn ℂ riemannZeta₁ halfPlane :=
    differentiable_riemannZeta₁.differentiableOn
  exact h1.div h2 (fun s hs => riemannZeta₁_ne_zero_of_RH hRH hs)

lemma norm_sub_one_le_norm_add_one {s : ℂ} (hs : 0 ≤ s.re) : ‖s - 1‖ ≤ ‖s + 1‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, sub_zero, add_re, add_im, add_zero]
  nlinarith

/-- `C L^α ≤ η L + K` for all `t`, where `L = log(|t| + 2)` and `0 ≤ α < 1`. -/
lemma exists_log_rpow_le {α C η : ℝ} (hα : α < 1) (hα0 : 0 ≤ α) (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      C * Real.log (|t| + 2) ^ α ≤ η * Real.log (|t| + 2) + K := by
  obtain ⟨T, hT⟩ := (eventually_mul_log_rpow_le (C := C) hα hη).exists_forall_of_atTop
  have hlogpos : ∀ x : ℝ, 0 < Real.log (|x| + 2) := fun x =>
    Real.log_pos (by linarith [abs_nonneg x])
  refine ⟨|C| * Real.log (|T| + 2) ^ α, by
    have := hlogpos T; positivity, fun t => ?_⟩
  have hK0 : 0 ≤ |C| * Real.log (|T| + 2) ^ α := by have := hlogpos T; positivity
  by_cases ht : T ≤ |t|
  · have := hT |t| ht
    linarith
  · push Not at ht
    have hL := hlogpos t
    have h1 : C * Real.log (|t| + 2) ^ α ≤ |C| * Real.log (|t| + 2) ^ α :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h2 : Real.log (|t| + 2) ^ α ≤ Real.log (|T| + 2) ^ α := by
      apply Real.rpow_le_rpow hL.le _ hα0
      apply Real.log_le_log (by positivity)
      linarith [le_abs_self T]
    have h3 : |C| * Real.log (|t| + 2) ^ α ≤ |C| * Real.log (|T| + 2) ^ α :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    nlinarith

lemma rpow_le_one_add_rpow {L β α : ℝ} (hL : 0 < L) (hβ0 : 0 ≤ β) (hβα : β ≤ α) :
    L ^ β ≤ 1 + L ^ α := by
  by_cases h : L ≤ 1
  · have := Real.rpow_le_one hL.le h hβ0
    have := Real.rpow_nonneg hL.le α
    linarith
  · push Not at h
    have := Real.rpow_le_rpow_of_exponent_le h.le hβα
    linarith

/-- **Step A**, strip version: under RH, for `0 < δ < 3/2` and `ε > 0`,
`‖invZ s‖ ≤ C (|t| + 2)^ε` on `1/2 + δ ≤ σ ≤ 2`, for all `t`. -/
theorem norm_invZ_le (hRH : RiemannHypothesis) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδ' : δ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 →
      ‖invZ s‖ ≤ C * (|s.im| + 2) ^ ε := by
  obtain ⟨M, hMd, hexp, C₀, hC₀⟩ := exists_log_zetaQ hRH
  obtain ⟨C₂, hC₂⟩ := norm_log_zetaQ_le hRH hMd hexp ⟨C₀, hC₀⟩ (δ / 2) (by positivity)
  set a : ℝ := 1 / 2 + δ / 2 with ha
  have hab : a < 2 := by linarith
  have hsub : {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} ⊆ halfPlane := fun s hs => by
    show 1 / 2 < s.re
    linarith [hs.1]
  obtain ⟨C₃, hC₃⟩ := norm_le_log_rpow_of_strip (B := C₀) hab (hMd.mono hsub)
    (fun s h1 h2 => hC₂ s h1 h2) (fun s h => hC₀ s (by linarith) (by linarith))
  set α : ℝ := (3 / 2 - δ) / (2 - a) with hα
  have h2a : 0 < 2 - a := by linarith
  have hα1 : α < 1 := by rw [hα, div_lt_one h2a]; linarith
  have hα0 : 0 ≤ α := div_nonneg (by linarith) h2a.le
  obtain ⟨K, hK0, hK⟩ := exists_log_rpow_le (C := |C₃|) hα1 hα0 hε
  refine ⟨Real.exp (|C₃| + K), Real.exp_pos _, fun s h1 h2 => ?_⟩
  have hs : (s.re : ℂ) + s.im * I = s := re_add_im s
  have hM := hC₃ s.re s.im (by linarith) h2
  rw [hs] at hM
  set L := Real.log (|s.im| + 2) with hLdef
  have hL0 : 0 < L := Real.log_pos (by linarith [abs_nonneg s.im])
  have hβ0 : 0 ≤ (2 - s.re) / (2 - a) := div_nonneg (by linarith) h2a.le
  have hβα : (2 - s.re) / (2 - a) ≤ α := div_le_div_of_nonneg_right (by linarith) h2a.le
  have hβ := rpow_le_one_add_rpow hL0 hβ0 hβα
  have hMb : ‖M s‖ ≤ |C₃| + ε * L + K := by
    have e1 : C₃ * L ^ ((2 - s.re) / (2 - a)) ≤ |C₃| * (1 + L ^ α) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C₃) (Real.rpow_nonneg hL0.le _)).trans
        (mul_le_mul_of_nonneg_left hβ (abs_nonneg _))
    have e2 := hK s.im
    rw [← hLdef] at e2
    nlinarith
  have hsH : s ∈ halfPlane := show 1 / 2 < s.re by linarith
  have hplus : s + 1 ≠ 0 := by
    intro h
    have := congrArg re h
    simp at this
    linarith
  have hζ : riemannZeta₁ s = (s + 1) * exp (M s) := by
    rw [hexp s hsH, zetaQ, mul_div_cancel₀ _ hplus]
  have hnorm : ‖invZ s‖ ≤ Real.exp ‖M s‖ := by
    rw [invZ, hζ, norm_div, norm_mul, Complex.norm_exp]
    have hp : 0 < ‖s + 1‖ := norm_pos_iff.mpr hplus
    have hle := norm_sub_one_le_norm_add_one (s := s) (by linarith)
    rw [div_le_iff₀ (by positivity)]
    have : Real.exp ‖M s‖ * Real.exp (M s).re ≥ 1 := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := neg_abs_le (M s).re
      have := abs_re_le_norm (M s)
      linarith
    nlinarith [norm_nonneg (s - 1)]
  calc ‖invZ s‖ ≤ Real.exp ‖M s‖ := hnorm
    _ ≤ Real.exp (|C₃| + K + ε * L) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (|C₃| + K) * (|s.im| + 2) ^ ε := by
      rw [Real.exp_add, Real.rpow_def_of_pos (by linarith [abs_nonneg s.im]), hLdef, mul_comm ε]

/-- `‖1/ζ(s)‖ ≤ ∑ 1/n²`-type bound for `σ ≥ 2`. -/
lemma norm_inv_zeta_le_of_two_le :
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(riemannZeta s)⁻¹‖ ≤ C := by
  have hsumm : Summable fun n => ‖LSeries.term (1 : ℕ → ℂ) 2 n‖ :=
    (LSeriesSummable_one_iff.mpr (by norm_num)).norm
  refine ⟨∑' n, ‖LSeries.term (1 : ℕ → ℂ) 2 n‖, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hinv : (riemannZeta s)⁻¹ = LSeries (fun n => (μ n : ℂ)) s := by
    apply inv_eq_of_mul_eq_one_right
    rw [← LSeries_one_eq_riemannZeta hs1]
    exact LSeries_one_mul_Lseries_moebius hs1
  rw [hinv, LSeries]
  refine tsum_of_norm_bounded hsumm.hasSum fun n => ?_
  refine (LSeries.norm_term_le_of_re_le_re _ (show (2 : ℂ).re ≤ s.re by simpa using hs) n).trans
    (LSeries.norm_term_le _ ?_)
  simp only [Pi.one_apply, norm_one]
  have := ArithmeticFunction.abs_moebius_le_one (n := n)
  rw [show ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ = |(ArithmeticFunction.moebius n : ℝ)| by
    rw [← Complex.norm_intCast]]
  exact_mod_cast this

/-- **Step A**: under RH, `1/ζ(s) ≪_{ε,δ} |t|^ε` on `σ ≥ 1/2 + δ`, `|t| ≥ 1`. -/
theorem invZeta_bound_of_RH (hRH : RiemannHypothesis) : InvZetaBound := by
  intro ε hε δ hδ
  set δ' := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  obtain ⟨C, hC0, hC⟩ := norm_invZ_le hRH hε hδ'0 (by
    have := min_le_right δ 1; linarith)
  obtain ⟨C₂, hC₂⟩ := norm_inv_zeta_le_of_two_le
  refine ⟨C * 3 ^ ε + |C₂|, fun s h1 h2 => ?_⟩
  have hpow : 1 ≤ |s.im| ^ ε := Real.one_le_rpow h2 hε.le
  by_cases hs2 : s.re ≤ 2
  · have hs1 : s ≠ 1 := by
      rintro rfl
      simp at h2
      linarith
    rw [← invZ_eq hs1]
    have hb := hC s (by have := min_le_left δ 1; linarith) hs2
    have h3 : (|s.im| + 2) ^ ε ≤ 3 ^ ε * |s.im| ^ ε := by
      rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
    calc ‖invZ s‖ ≤ C * (|s.im| + 2) ^ ε := hb
      _ ≤ C * (3 ^ ε * |s.im| ^ ε) := by gcongr
      _ ≤ (C * 3 ^ ε + |C₂|) * |s.im| ^ ε := by
        nlinarith [abs_nonneg C₂, Real.rpow_nonneg (abs_nonneg s.im) ε]
  · push Not at hs2
    have := hC₂ s hs2.le
    have : 0 ≤ C * 3 ^ ε := by positivity
    nlinarith [le_abs_self C₂, abs_nonneg C₂]

end Mertens
