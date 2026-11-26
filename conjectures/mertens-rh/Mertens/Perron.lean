import Erdos985.Analytic.Perron.Weighted
import Erdos985.Analytic.Perron.Bounds
import Mertens.InvZeta
import Mertens.Shift

/-!
# Step C: the Cesàro–Perron formula for `μ` on the line `σ₀ > 1/2`

erdos-985's `perron_weighted` gives, on the line `Re s = 2`,
`∑_{0<n<N} μ(n)(1 - n/N) = (1/2π) ∫ (1/ζ)(s) N^s / (s(s+1)) dt`. Under RH the integrand
`F_N(s) = invZ(s) N^s/(s(s+1))` is holomorphic on `σ > 1/2` and `O((1+|t|)^{-3/2})` uniformly on
`σ₀ ≤ σ ≤ 2` (Step A with `ε = 1/2`), so Step B moves the line to any `σ₀ ∈ (1/2, 2)`.
-/

namespace Mertens

open Complex MeasureTheory Filter Set Topology Lindelof
open scoped ArithmeticFunction.Moebius

/-- The Perron integrand `invZ(s) y^s / (s(s+1))`. -/
noncomputable def F (y : ℝ) (s : ℂ) : ℂ := invZ s * (y : ℂ) ^ s / (s * (s + 1))

lemma norm_ge_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    min s.re 1 * (1 + |s.im|) / 2 ≤ ‖s‖ := by
  have h1 : s.re ≤ ‖s‖ := le_trans (le_abs_self _) (abs_re_le_norm s)
  have h2 : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have hm1 : min s.re 1 ≤ 1 := min_le_right _ _
  have hm2 : min s.re 1 ≤ s.re := min_le_left _ _
  have hm0 : 0 < min s.re 1 := lt_min hs one_pos
  nlinarith [abs_nonneg s.im]

lemma norm_add_one_ge {s : ℂ} (hs : 0 ≤ s.re) : (1 + |s.im|) / 2 ≤ ‖s + 1‖ := by
  have h := norm_ge_of_re_pos (s := s + 1) (by simp; linarith)
  have : min (s + 1).re 1 = 1 := min_eq_right (by simp; linarith)
  rw [this, one_mul, add_im, one_im, add_zero] at h
  exact h

lemma ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  rintro rfl; simp at hs

lemma add_one_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s + 1 ≠ 0 := by
  intro h
  have := congrArg re h
  simp at this
  linarith

/-- `1/‖s(s+1)‖ ≤ (4/m) (1 + |t|)^{-2}` for `Re s ≥ m`, `0 < m ≤ 1`. -/
lemma inv_norm_mul_le {s : ℂ} {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hs : m ≤ s.re) :
    1 / (‖s‖ * ‖s + 1‖) ≤ 4 / m * (1 + |s.im|) ^ (-2 : ℝ) := by
  have h1 := norm_ge_of_re_pos (s := s) (by linarith)
  have h2 := norm_add_one_ge (s := s) (by linarith)
  have hmm : m ≤ min s.re 1 := le_min hs hm1
  have hu : 0 < 1 + |s.im| := by positivity
  have hprod : m * (1 + |s.im|) ^ 2 / 4 ≤ ‖s‖ * ‖s + 1‖ := by
    have : m * (1 + |s.im|) / 2 ≤ ‖s‖ :=
      le_trans (by gcongr) h1
    calc m * (1 + |s.im|) ^ 2 / 4 = (m * (1 + |s.im|) / 2) * ((1 + |s.im|) / 2) := by ring
      _ ≤ ‖s‖ * ‖s + 1‖ := by
        apply mul_le_mul this h2 (by positivity) (norm_nonneg _)
  have hpos : 0 < m * (1 + |s.im|) ^ 2 / 4 := by positivity
  rw [Real.rpow_neg hu.le, Real.rpow_two]
  calc 1 / (‖s‖ * ‖s + 1‖) ≤ 1 / (m * (1 + |s.im|) ^ 2 / 4) :=
        one_div_le_one_div_of_le hpos hprod
    _ = 4 / m * ((1 + |s.im|) ^ 2)⁻¹ := by field_simp

/-- The strip `σ₀ ≤ σ ≤ 2` lies in `σ > 1/2`. -/
lemma strip_subset {σ₀ : ℝ} (h : 1 / 2 < σ₀) :
    {s : ℂ | σ₀ ≤ s.re ∧ s.re ≤ 2} ⊆ halfPlane := fun s hs =>
  show 1 / 2 < s.re by linarith [hs.1]

theorem differentiableOn_F (hRH : RiemannHypothesis) {y σ₀ : ℝ} (hy : 0 < y) (h : 1 / 2 < σ₀) :
    DifferentiableOn ℂ (F y) {s : ℂ | σ₀ ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  have hre : 0 < s.re := by linarith [hs.1]
  have h1 : DifferentiableWithinAt ℂ invZ {s : ℂ | σ₀ ≤ s.re ∧ s.re ≤ 2} s :=
    ((differentiableOn_invZ hRH).mono (strip_subset h)) s hs
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (ofReal_ne_zero.2 hy.ne'))
  have h3 : DifferentiableAt ℂ (fun s : ℂ => s * (s + 1)) s := by fun_prop
  have h4 : s * (s + 1) ≠ 0 := mul_ne_zero (ne_zero_of_re_pos hre) (add_one_ne_zero_of_re_pos hre)
  exact (h1.mul h2.differentiableWithinAt).div h3.differentiableWithinAt h4

/-- Uniform bound on the strip: `‖F_y(s)‖ ≤ K y^σ (1 + |t|)^{-3/2}`. -/
theorem norm_F_le (hRH : RiemannHypothesis) {σ₀ : ℝ} (h1 : 1 / 2 < σ₀) (h2 : σ₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (y : ℝ), 0 < y → ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 →
      ‖F y s‖ ≤ K * y ^ s.re * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := norm_invZ_le hRH (ε := 1 / 2) (δ := σ₀ - 1 / 2) (by norm_num)
    (by linarith) (by linarith)
  set m := min σ₀ 1 with hm
  have hm0 : 0 < m := lt_min (by linarith) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  refine ⟨C * 2 * (4 / m), by positivity, fun y hy s hs1 hs2 => ?_⟩
  have hre : 0 < s.re := by linarith
  have hu : 0 < 1 + |s.im| := by positivity
  have hinv := hC s (by linarith) hs2
  have hpow : (|s.im| + 2) ^ (1 / 2 : ℝ) ≤ 2 * (1 + |s.im|) ^ (1 / 2 : ℝ) := by
    calc (|s.im| + 2) ^ (1 / 2 : ℝ) ≤ (2 * (1 + |s.im|)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) (by norm_num)
      _ = 2 ^ (1 / 2 : ℝ) * (1 + |s.im|) ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) hu.le
      _ ≤ 2 * (1 + |s.im|) ^ (1 / 2 : ℝ) := by
          gcongr
          exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hden := inv_norm_mul_le hm0 hm1 (show m ≤ s.re from (min_le_left _ _).trans hs1)
  have hF : ‖F y s‖ = ‖invZ s‖ * y ^ s.re * (1 / (‖s‖ * ‖s + 1‖)) := by
    rw [F, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
    ring
  rw [hF]
  have hcomb : (1 + |s.im|) ^ (1 / 2 : ℝ) * (1 + |s.im|) ^ (-2 : ℝ) =
      (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hu]; norm_num
  have hy' : 0 < y ^ s.re := Real.rpow_pos_of_pos hy _
  calc ‖invZ s‖ * y ^ s.re * (1 / (‖s‖ * ‖s + 1‖))
      ≤ (C * (2 * (1 + |s.im|) ^ (1 / 2 : ℝ))) * y ^ s.re *
          (4 / m * (1 + |s.im|) ^ (-2 : ℝ)) := by
        gcongr
        exact hinv.trans (by gcongr)
    _ = C * 2 * (4 / m) * y ^ s.re *
          ((1 + |s.im|) ^ (1 / 2 : ℝ) * (1 + |s.im|) ^ (-2 : ℝ)) := by ring
    _ = C * 2 * (4 / m) * y ^ s.re * (1 + |s.im|) ^ (-(3 / 2) : ℝ) := by rw [hcomb]

lemma continuous_line (c : ℝ) : Continuous fun t : ℝ => (c : ℂ) + t * I :=
  continuous_const.add (continuous_ofReal.mul continuous_const)

lemma line_re (c t : ℝ) : ((c : ℂ) + t * I).re = c := by simp
lemma line_im (c t : ℝ) : ((c : ℂ) + t * I).im = t := by simp

/-- A function continuous on the line and bounded by `K (1+|t|)^{-r}`, `r > 1`, is integrable. -/
lemma integrable_of_le_rpow {g : ℝ → ℂ} (hg : Continuous g) {K r : ℝ} (hr : 1 < r)
    (hb : ∀ t, ‖g t‖ ≤ K * (1 + |t|) ^ (-r)) : Integrable g := by
  have hi : Integrable fun t : ℝ => K * (1 + |t|) ^ (-r) := by
    have := (Erdos985.Analytic.PerronAux.integrable_one_add_abs_rpow hr 0).const_mul K
    simpa using this
  exact hi.mono' hg.aestronglyMeasurable (Eventually.of_forall hb)

theorem continuousOn_F (hRH : RiemannHypothesis) {y σ₀ : ℝ} (hy : 0 < y) (h : 1 / 2 < σ₀) :
    ContinuousOn (F y) {s : ℂ | σ₀ ≤ s.re ∧ s.re ≤ 2} :=
  (differentiableOn_F hRH hy h).continuousOn

theorem continuous_F_line (hRH : RiemannHypothesis) {y σ₀ c : ℝ} (hy : 0 < y) (h : 1 / 2 < σ₀)
    (hc1 : σ₀ ≤ c) (hc2 : c ≤ 2) : Continuous fun t : ℝ => F y ((c : ℂ) + t * I) :=
  (continuousOn_F hRH hy h).comp_continuous (continuous_line c) fun t => by
    simp only [mem_ofPred_eq, line_re]; exact ⟨hc1, hc2⟩

theorem integrable_F_line (hRH : RiemannHypothesis) {y σ₀ c : ℝ} (hy : 0 < y) (h : 1 / 2 < σ₀)
    (h2 : σ₀ < 2) (hc1 : σ₀ ≤ c) (hc2 : c ≤ 2) :
    Integrable fun t : ℝ => F y ((c : ℂ) + t * I) := by
  obtain ⟨K, -, hK⟩ := norm_F_le hRH h h2
  refine integrable_of_le_rpow (continuous_F_line hRH hy h hc1 hc2) (r := 3 / 2) (K := K * y ^ c)
    (by norm_num) fun t => ?_
  have := hK y hy ((c : ℂ) + t * I) (by rw [line_re]; exact hc1) (by rw [line_re]; exact hc2)
  rwa [line_re, line_im] at this

/-- **Step C, shift**: under RH the Perron integral on `Re s = 2` equals the one on `σ₀`. -/
theorem integral_F_shift (hRH : RiemannHypothesis) {y σ₀ : ℝ} (hy : 0 < y) (h1 : 1 / 2 < σ₀)
    (h2 : σ₀ < 2) :
    ∫ t : ℝ, F y ((σ₀ : ℂ) + t * I) = ∫ t : ℝ, F y ((2 : ℝ) + t * I) := by
  obtain ⟨K, hK0, hK⟩ := norm_F_le hRH h1 h2
  refine integral_vertical_eq_of_strip h2.le (differentiableOn_F hRH hy h1)
    (integrable_F_line hRH hy h1 h2 le_rfl h2.le)
    (integrable_F_line hRH hy h1 h2 h2.le le_rfl) ?_
  intro η hη
  set K' := K * max (y ^ σ₀) (y ^ (2 : ℝ)) with hK'
  have hK'0 : 0 < K' := by
    have : 0 < y ^ σ₀ := Real.rpow_pos_of_pos hy _
    positivity
  filter_upwards [eventually_ge_atTop (K' / η), eventually_ge_atTop (0 : ℝ)] with T hT hT0
  intro σ hσ1 hσ2
  have hyσ : y ^ σ ≤ max (y ^ σ₀) (y ^ (2 : ℝ)) := by
    rcases le_or_gt 1 y with hy1 | hy1
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hy1 hσ2)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hy hy1.le hσ1)
  have hbound : ∀ u : ℝ, |u| = T → ‖F y ((σ : ℂ) + u * I)‖ ≤ η := by
    intro u hu
    have := hK y hy ((σ : ℂ) + u * I) (by rw [line_re]; exact hσ1) (by rw [line_re]; exact hσ2)
    rw [line_re, line_im, hu] at this
    have hT1 : (1 + T) ^ (-(3 / 2) : ℝ) ≤ (1 + T) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hT2 : (1 + T) ^ (-1 : ℝ) = 1 / (1 + T) := by rw [Real.rpow_neg_one, one_div]
    have hT3 : K' * (1 / (1 + T)) ≤ η := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      rw [div_le_iff₀ hη] at hT
      nlinarith
    calc ‖F y ((σ : ℂ) + u * I)‖ ≤ K * y ^ σ * (1 + T) ^ (-(3 / 2) : ℝ) := this
      _ ≤ K' * (1 + T) ^ (-1 : ℝ) := by
        rw [hK']
        apply mul_le_mul (mul_le_mul_of_nonneg_left hyσ hK0.le) hT1 (by positivity)
        positivity
      _ ≤ η := by rw [hT2]; exact hT3
  exact ⟨hbound T (abs_of_nonneg hT0), hbound (-T) (by rw [abs_neg, abs_of_nonneg hT0])⟩

lemma LSeries_moebius_eq_invZ {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ)) s = invZ s := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  rw [invZ_eq hs1]
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← LSeries_one_eq_riemannZeta hs]
  exact LSeries_one_mul_Lseries_moebius hs

/-- **Step C**: the Cesàro–Perron formula for `μ` on the line `σ₀ ∈ (1/2, 2)`, under RH. -/
theorem cesaro_moebius_eq (hRH : RiemannHypothesis) {σ₀ : ℝ} (h1 : 1 / 2 < σ₀) (h2 : σ₀ < 2)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, (μ n : ℂ) * (1 - (n : ℂ) / N)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, F N ((σ₀ : ℂ) + t * I) := by
  have hsum : Summable fun n : ℕ => ‖(μ n : ℂ)‖ / (n : ℝ) ^ (2 : ℝ) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 2))
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hP := Erdos985.Analytic.PerronKernel.perron_weighted (fun n => (μ n : ℂ)) 2 (by norm_num)
    hsum N hN
  rw [hP, integral_F_shift hRH (by exact_mod_cast hN) h1 h2]
  congr 2
  funext t
  have hre : 1 < (((2 : ℝ) : ℂ) + t * I).re := by simp
  rw [LSeries_moebius_eq_invZ hre, F]
  push_cast
  ring

end Mertens
