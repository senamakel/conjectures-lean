import Mathlib

/-!
# Pointwise and integral bounds for the rational Perron kernels on `Re s = c`
-/

open Complex MeasureTheory Set Filter Topology

namespace Erdos985.Analytic.PerronAux

lemma norm_line_sq (c t : ℝ) : ‖(c : ℂ) + t * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, normSq_add_mul_I]

lemma line_add_one (c t : ℝ) : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
  push_cast; ring

lemma abs_im_le_norm_line (c t : ℝ) : |t| ≤ ‖(c : ℂ) + t * I‖ := by
  simpa using abs_im_le_norm ((c : ℂ) + t * I)

lemma re_le_norm_sub (c t : ℝ) (w : ℂ) : c - w.re ≤ ‖(c : ℂ) + t * I - w‖ := by
  have := re_le_norm ((c : ℂ) + t * I - w)
  simpa using this

lemma abs_sub_im_le_norm_sub (c t : ℝ) (w : ℂ) : |t - w.im| ≤ ‖(c : ℂ) + t * I - w‖ := by
  have := abs_im_le_norm ((c : ℂ) + t * I - w)
  simpa using this

lemma c_le_norm_line {c : ℝ} (_hc : 0 ≤ c) (t : ℝ) : c ≤ ‖(c : ℂ) + t * I‖ := by
  have := re_le_norm ((c : ℂ) + t * I)
  simpa using this

lemma norm_line_le_add_one {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + 1‖ := by
  rw [line_add_one]
  have h1 := norm_line_sq c t
  have h2 := norm_line_sq (c + 1) t
  have := norm_nonneg ((c : ℂ) + t * I)
  have := norm_nonneg (((c + 1 : ℝ) : ℂ) + t * I)
  nlinarith

lemma one_le_norm_line_add_one {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 1 ≤ ‖(c : ℂ) + t * I + 1‖ := by
  rw [line_add_one]; have := c_le_norm_line (c := c + 1) (by linarith) t; linarith

lemma min_mul_le_norm_line_sq (c t : ℝ) :
    min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ ^ 2 := by
  rw [norm_line_sq]
  have h1 : min (c ^ 2) 1 ≤ c ^ 2 := min_le_left _ _
  have h2 : min (c ^ 2) 1 ≤ 1 := min_le_right _ _
  nlinarith [sq_nonneg t]

lemma line_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith

lemma line_add_one_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I + 1 ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith

lemma line_sub_ne_zero {c : ℝ} (t : ℝ) {w : ℂ} (hw : w.re < c) : (c : ℂ) + t * I - w ≠ 0 := by
  intro h; have := congrArg re h; simp at this; linarith

/-- Generic integrability for `G(t) / (s (s+1))` with `G` continuous and bounded. -/
lemma integrable_div_line_two {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ t, ‖G t‖ ≤ B) :
    Integrable fun t : ℝ => G t / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (integrable_inv_one_add_sq.const_mul (B / min (c ^ 2) 1)).mono' ?_ (ae_of_all _ ?_)
  · refine (hG.div (by fun_prop) fun t => ?_).aestronglyMeasurable
    exact mul_ne_zero (line_ne_zero hc t) (line_add_one_ne_zero hc t)
  · intro t
    rw [norm_div, norm_mul]
    have hs := min_mul_le_norm_line_sq c t
    have h1 := norm_line_le_add_one hc.le t
    have hpos : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.2 (line_ne_zero hc t)
    have hpos1 : 0 < ‖(c : ℂ) + t * I + 1‖ := norm_pos_iff.2 (line_add_one_ne_zero hc t)
    have key : min (c ^ 2) 1 * (1 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc ‖G t‖ ≤ B := hB t
      _ = B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ * (min (c ^ 2) 1 * (1 + t ^ 2)) := by
          field_simp
      _ ≤ B / min (c ^ 2) 1 * (1 + t ^ 2)⁻¹ *
          (‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) := by
          gcongr

/-- Generic integrability for `G(t) / ((s - w) s (s+1))` with `G` continuous and bounded. -/
lemma integrable_div_line_three {c : ℝ} (hc : 0 < c) {G : ℝ → ℂ} (hG : Continuous G) {B : ℝ}
    (hB : ∀ t, ‖G t‖ ≤ B) {w : ℂ} (hw : w.re < c) :
    Integrable fun t : ℝ =>
      G t / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  have hδ : 0 < c - w.re := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hG' : Continuous fun t : ℝ => G t / ((c : ℂ) + t * I - w) :=
    hG.div (by fun_prop) fun t => line_sub_ne_zero t hw
  have := integrable_div_line_two hc hG' (B := B / (c - w.re)) fun t => by
    rw [norm_div]
    exact div_le_div₀ hB0 (hB t) hδ (re_le_norm_sub c t w)
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only
  rw [div_div, mul_assoc]


/-! ### Pointwise identities for the kernels with `x^s` -/

lemma norm_cpow_line {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]; simp

lemma continuous_cpow_line {x : ℝ} (hx : 0 < x) (c : ℝ) :
    Continuous fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.2 hx.ne'))

/-- Exact norm of the Perron kernel with an extra pole `w`. -/
lemma norm_perron_kernel {x : ℝ} (hx : 0 < x) (c t : ℝ) (w : ℂ) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
      = x ^ c / (‖(c : ℂ) + t * I - w‖ * ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖) := by
  rw [norm_div, norm_cpow_line hx, norm_mul, norm_mul]

/-- Integrability of the Perron kernel `x^s/((s-w)s(s+1))` on `Re s = c`. -/
lemma integrable_perron_kernel {x c : ℝ} (hx : 0 < x) (hc : 0 < c) {w : ℂ} (hw : w.re < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  integrable_div_line_three hc (continuous_cpow_line hx c) (B := x ^ c)
    (fun t => (norm_cpow_line hx c t).le) hw

/-- Integrability of the Cesàro kernel `x^s/(s(s+1))` on `Re s = c`. -/
lemma integrable_cesaro_kernel {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Integrable fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) :=
  integrable_div_line_two hc (continuous_cpow_line hx c) (B := x ^ c)
    (fun t => (norm_cpow_line hx c t).le)

/-! ### An integral bound explicit in `w` -/

/-- If `a + b ≥ D` then `1/(ab) ≤ (D/2)^{-θ} (a^{-(2-θ)} + b^{-(2-θ)})`. -/
lemma one_div_mul_le_rpow {a b D θ : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (hab : D ≤ a + b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 / (a * b) ≤ (D / 2) ^ (-θ) * (a ^ (-(2 - θ)) + b ^ (-(2 - θ))) := by
  -- one-sided version, `a ≤ b`
  have key : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b → D ≤ a + b →
      1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
    intro a b ha hb hle hab
    have hb2 : D / 2 ≤ b := by linarith
    have h1 : b ^ (-θ) ≤ (D / 2) ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb2 (by linarith)
    have hp : (0 : ℝ) ≤ 1 - θ := by linarith
    have hap : a ^ (1 - θ) ≤ b ^ (1 - θ) := Real.rpow_le_rpow ha.le hle hp
    have hA : a ^ (-(2 - θ)) = (a * a ^ (1 - θ))⁻¹ := by
      rw [Real.rpow_neg ha.le, show 2 - θ = 1 + (1 - θ) by ring, Real.rpow_add ha, Real.rpow_one]
    have hB : b ^ (-θ) = b ^ (1 - θ) / b := by
      rw [Real.rpow_neg hb.le, show θ = 1 - (1 - θ) by ring, Real.rpow_sub hb, Real.rpow_one]
      field_simp
      rw [show 1 - (1 - (1 - θ)) = 1 - θ by ring]
    have hapos : 0 < a ^ (1 - θ) := Real.rpow_pos_of_pos ha _
    have hbpos : 0 < b ^ (1 - θ) := Real.rpow_pos_of_pos hb _
    calc 1 / (a * b) ≤ b ^ (-θ) * a ^ (-(2 - θ)) := by
          rw [hA, hB, div_le_iff₀ (by positivity)]
          field_simp
          exact hap
      _ ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := by
          gcongr
  have hA0 : 0 ≤ a ^ (-(2 - θ)) := Real.rpow_nonneg ha.le _
  have hB0 : 0 ≤ b ^ (-(2 - θ)) := Real.rpow_nonneg hb.le _
  have hD0 : 0 ≤ (D / 2) ^ (-θ) := Real.rpow_nonneg (by positivity) _
  rcases le_total a b with h | h
  · calc 1 / (a * b) ≤ (D / 2) ^ (-θ) * a ^ (-(2 - θ)) := key a b ha hb h hab
      _ ≤ _ := by gcongr; linarith
  · calc 1 / (a * b) = 1 / (b * a) := by rw [mul_comm]
      _ ≤ (D / 2) ^ (-θ) * b ^ (-(2 - θ)) := key b a hb ha h (by linarith)
      _ ≤ _ := by gcongr; linarith


lemma norm_sub_lb {c δ : ℝ} (t : ℝ) {w : ℂ} (hw : w.re ≤ c - δ) :
    min δ 1 / 2 * (1 + |t - w.im|) ≤ ‖(c : ℂ) + t * I - w‖ := by
  have h1 := re_le_norm_sub c t w
  have h2 := abs_sub_im_le_norm_sub c t w
  have h3 : min δ 1 ≤ δ := min_le_left _ _
  have h4 : min δ 1 ≤ 1 := min_le_right _ _
  have h5 := abs_nonneg (t - w.im)
  nlinarith

lemma norm_add_one_lb {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    1 / 2 * (1 + |t|) ≤ ‖(c : ℂ) + t * I + 1‖ := by
  have h1 := one_le_norm_line_add_one hc t
  have h2 : |t| ≤ ‖(c : ℂ) + t * I + 1‖ := by
    rw [line_add_one]; exact abs_im_le_norm_line _ t
  linarith

lemma integrable_one_add_abs_rpow {r : ℝ} (hr : 1 < r) (v : ℝ) :
    Integrable fun t : ℝ => (1 + |t - v|) ^ (-r) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using h.comp_sub_right v

lemma integral_one_add_abs_rpow (r v : ℝ) :
    ∫ t : ℝ, (1 + |t - v|) ^ (-r) = ∫ t : ℝ, (1 + |t|) ^ (-r) :=
  integral_sub_right_eq_self (fun t : ℝ => (1 + |t|) ^ (-r)) v

/-- **Integral bound explicit in `w`.** For `Re w ≤ c - δ` and `0 ≤ θ < 1`,
`∫ |x^s / ((s - w)(s + 1))| dt ≤ K x^c (1 + |w|)^{-θ}` with `K = K(δ, θ)` independent of
`x`, `c` and `w`.  (Since `∫ dt/|s(s+1)| ≍ 1`, no bound better than `(1+|w|)^{-1}` is possible
here; summing over zeros `ρ` one uses the paired kernel
`x^s/(s(s+1)) (1/(s-ρ) + 1/ρ) = x^s/(ρ (s-ρ)(s+1))`, whose integral is then
`O(x^c |ρ|^{-1-θ})`.) -/
theorem integral_norm_kernel_two_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      Integrable (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) ∧
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖
        ≤ K * x ^ c * (1 + ‖w‖) ^ (-θ) := by
  set r : ℝ := 2 - θ with hr_def
  have hr : 1 < r := by rw [hr_def]; linarith
  set m : ℝ := min δ 1 / 2 with hm_def
  have hm : 0 < m := by rw [hm_def]; exact half_pos (lt_min hδ one_pos)
  set J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-r) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  set A : ℝ := m ^ (-r) + (1 / 2 : ℝ) ^ (-r) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(6⁻¹ : ℝ) ^ (-θ) * A * J, by positivity, ?_⟩
  intro x c hx hc w hw
  have hwc : w.re < c := by linarith
  set D : ℝ := max 1 ‖w + 1‖ with hD_def
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  set C : ℝ := x ^ c * (D / 2) ^ (-θ) with hC
  have hC0 : 0 ≤ C := by positivity
  -- the dominating function
  set h : ℝ → ℝ := fun t => C * (m ^ (-r) * (1 + |t - w.im|) ^ (-r) +
    (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r)) with hh
  have hint : Integrable h :=
    (((integrable_one_add_abs_rpow hr w.im).const_mul _).add
      ((integrable_one_add_abs_rpow hr 0).const_mul _)).const_mul _
  have hpt : ∀ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ ≤ h t := by
    intro t
    set a := ‖(c : ℂ) + t * I - w‖
    set b := ‖(c : ℂ) + t * I + 1‖
    have ha : 0 < a := norm_pos_iff.2 (line_sub_ne_zero t hwc)
    have hb : 0 < b := norm_pos_iff.2 (line_add_one_ne_zero hc t)
    have hDab : D ≤ a + b := by
      refine max_le (by have := one_le_norm_line_add_one hc.le t; linarith) ?_
      have : w + 1 = ((c : ℂ) + t * I + 1) - ((c : ℂ) + t * I - w) := by ring
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    have hab := one_div_mul_le_rpow ha hb hD hDab hθ0 hθ1.le
    have hal : a ^ (-r) ≤ m ^ (-r) * (1 + |t - w.im|) ^ (-r) := by
      rw [← Real.mul_rpow hm.le (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (norm_sub_lb t hw) (by linarith)
    have hbl : b ^ (-r) ≤ (1 / 2 : ℝ) ^ (-r) * (1 + |t - 0|) ^ (-r) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity), sub_zero]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (norm_add_one_lb hc.le t) (by linarith)
    rw [norm_div, norm_cpow_line hx, norm_mul, div_eq_mul_one_div]
    simp only [hh, hC]
    rw [mul_assoc]
    gcongr
    refine hab.trans ?_
    rw [hr_def] at hal hbl
    gcongr
  refine ⟨?_, ?_⟩
  · refine hint.mono' ?_ (ae_of_all _ hpt)
    exact ((continuous_cpow_line hx c).div (by fun_prop) fun t =>
      mul_ne_zero (line_sub_ne_zero t hwc) (line_add_one_ne_zero hc t)).aestronglyMeasurable
  · calc _ ≤ ∫ t, h t := integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hint
          (ae_of_all _ hpt)
      _ = C * A * J := by
          simp only [hh]
          rw [integral_const_mul, integral_add ((integrable_one_add_abs_rpow hr w.im).const_mul _)
            ((integrable_one_add_abs_rpow hr 0).const_mul _), integral_const_mul,
            integral_const_mul, integral_one_add_abs_rpow, integral_one_add_abs_rpow]
          rw [hA]; ring
      _ ≤ _ := by
          rw [hC]
          have hw1 : (1 + ‖w‖) / 6 ≤ D / 2 := by
            have : ‖w‖ ≤ ‖w + 1‖ + 1 := by
              have := norm_sub_le (w + 1) 1; simpa using this
            have h1 : ‖w + 1‖ ≤ D := le_max_right _ _
            have h2 : (1 : ℝ) ≤ D := le_max_left _ _
            linarith
          have hθ' : (D / 2) ^ (-θ) ≤ (6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ) := by
            rw [← Real.mul_rpow (by norm_num) (by positivity)]
            exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          calc x ^ c * (D / 2) ^ (-θ) * A * J
              ≤ x ^ c * ((6⁻¹ : ℝ) ^ (-θ) * (1 + ‖w‖) ^ (-θ)) * A * J := by gcongr
            _ = _ := by ring

/-- The same bound for the kernel `x^s/((s-w)s(s+1))` of `perron_residue` (gaining `1/c`). -/
theorem integral_norm_perron_kernel_le {δ θ : ℝ} (hδ : 0 < δ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x c : ℝ, 0 < x → 0 < c → ∀ w : ℂ, w.re ≤ c - δ →
      ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖
        ≤ K / c * x ^ c * (1 + ‖w‖) ^ (-θ) := by
  obtain ⟨K, hK, hb⟩ := integral_norm_kernel_two_le hδ hθ0 hθ1
  refine ⟨K, hK, fun x c hx hc w hw => ?_⟩
  obtain ⟨hI, hle⟩ := hb x c hx hc w hw
  have hpt : ∀ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ ≤
      c⁻¹ * ‖(x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ := by
    intro t
    have hs : c ≤ ‖(c : ℂ) + t * I‖ := c_le_norm_line hc.le t
    have e : (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) =
        ((c : ℂ) + t * I)⁻¹ * ((x : ℂ) ^ ((c : ℂ) + t * I) /
          (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))) := by
      field_simp
    rw [e, norm_mul, norm_inv]
    gcongr
  calc _ ≤ ∫ t : ℝ, c⁻¹ * ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (hI.norm.const_mul _)
          (ae_of_all _ hpt)
    _ = c⁻¹ * ∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I + 1))‖ := integral_const_mul _ _
    _ ≤ c⁻¹ * (K * x ^ c * (1 + ‖w‖) ^ (-θ)) := by gcongr
    _ = _ := by ring

end Erdos985.Analytic.PerronAux
