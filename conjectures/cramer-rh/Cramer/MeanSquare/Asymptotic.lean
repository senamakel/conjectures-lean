import Cramer.MeanSquare.Main
import Cramer.MeanSquare.Approx
import Cramer.MeanSquare.Tail
import Cramer.MeanSquare.Limit

/-!
# Asymptotic, step 5: `∫_1^X ((ψ(x) − x)/x)² dx ∼ (Σ_ρ m_ρ²/|ρ|²) log X`

Write `f(y) = (ψ(y) − y)/y` and, for a finite set `S` of zeros, `g_S(y) = y^{−1/2} W_S(log y)`
with `W_S(u) = Σ_{ρ ∈ S} (m_ρ/ρ) e^{iγu}`.

* On a block `[Y, 4Y]` (`δ = 1/Y`), `f + g_S = (ψ − y + √y G)/y − (G − W_S)/√y`, so
  `∫_Y^{4Y} |f + g_S|² ≤ K/√Y + 9 η_S(1/Y)² + 3C·tail(S)` (`block_FF`), and summing blocks
  `∫_1^X |f + g_S|² ≤ K' + ε log X` once `S` and the starting block are large.
* `∫_1^X |g_S|² = ∫_0^{log X} |W_S|² = (Σ_{ρ ∈ S} m_ρ²/|ρ|²) log X + O_S(1)` (`finite_mean`).
* `tendsto_of_approx` turns the pointwise `f² ≤ (1+t)|g_S|² + (1+1/t)|f + g_S|²` (and its
  mirror) into the asymptotic.
-/

namespace Cramer.MeanSq

open Complex Erdos985.Analytic Erdos233 MeasureTheory intervalIntegral Filter Topology Chebyshev

/-! ### Change of variables `y = e^u` -/

lemma integral_comp_log_div {h : ℝ → ℝ} (hh : Continuous h) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : ∫ y in a..b, h (Real.log y) / y = ∫ u in Real.log a..Real.log b, h u := by
  have hsub := integral_comp_mul_deriv' (a := Real.log a) (b := Real.log b)
    (f := Real.exp) (f' := Real.exp) (g := fun y => h (Real.log y) / y)
    (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn (by
      refine ContinuousOn.div (hh.comp_continuousOn ?_) continuousOn_id ?_
      · exact Real.continuousOn_log.mono fun y hy => by
          obtain ⟨u, -, rfl⟩ := hy
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact (Real.exp_pos u).ne'
      · rintro y ⟨u, -, rfl⟩; exact (Real.exp_pos u).ne')
  rw [Real.exp_log ha, Real.exp_log (by linarith)] at hsub
  rw [← hsub]
  refine integral_congr fun u _ => ?_
  simp only [Function.comp, Real.log_exp]
  field_simp [(Real.exp_pos u).ne']

/-! ### The functions -/

/-- `f(y) = (ψ(y) − y)/y`. -/
noncomputable def fR (y : ℝ) : ℝ := (ψ y - y) / y

/-- `g_S(y) = y^{−1/2} W_S(log y)`. -/
noncomputable def gW (S : Finset Zeros) (y : ℝ) : ℂ :=
  ((Real.sqrt y)⁻¹ : ℝ) * wave S binv (Real.log y)

/-- `f + g_S`. -/
noncomputable def FF (S : Finset Zeros) (y : ℝ) : ℂ := (fR y : ℂ) + gW S y

lemma norm_gW_sq (S : Finset Zeros) {y : ℝ} (hy : 0 < y) :
    ‖gW S y‖ ^ 2 = ‖wave S binv (Real.log y)‖ ^ 2 / y := by
  rw [gW, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, inv_pow,
    Real.sq_sqrt hy.le]
  ring

lemma measurable_FF (S : Finset Zeros) : Measurable (FF S) := by
  have hψ : Measurable (fun y : ℝ => ψ y) := psi_mono.measurable
  have hw : Measurable (wave S binv) := (continuous_wave S binv).measurable
  unfold FF fR gW
  have h1 : Measurable fun y : ℝ => (ψ y - y) / y := (hψ.sub measurable_id).div measurable_id
  have h2 : Measurable fun y : ℝ => (Real.sqrt y)⁻¹ :=
    (Real.continuous_sqrt.measurable).inv
  have h3 : Measurable fun y : ℝ => wave S binv (Real.log y) := hw.comp Real.measurable_log
  exact (Complex.measurable_ofReal.comp h1).add
    ((Complex.measurable_ofReal.comp h2).mul h3)

lemma continuousOn_gW (S : Finset Zeros) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (gW S) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hpos : ∀ y ∈ Set.Icc a b, 0 < y := fun y hy => lt_of_lt_of_le ha hy.1
  unfold gW
  refine ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
    ((Real.continuous_sqrt.continuousOn).inv₀ fun y hy => (Real.sqrt_pos.2 (hpos y hy)).ne'))
    ((continuous_wave S binv).comp_continuousOn (Real.continuousOn_log.mono fun y hy => ?_))
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact (hpos y hy).ne'

lemma ii_gW (S : Finset Zeros) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => ‖gW S y‖ ^ 2) volume a b :=
  ((continuousOn_gW S ha hab).norm.pow 2).intervalIntegrable

lemma ii_fR {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => fR y ^ 2) volume a b :=
  intervalIntegrable_sq_div ha hab

lemma norm_FF_sq_le (S : Finset Zeros) (y : ℝ) :
    ‖FF S y‖ ^ 2 ≤ 2 * fR y ^ 2 + 2 * ‖gW S y‖ ^ 2 := by
  have h : ‖FF S y‖ ≤ |fR y| + ‖gW S y‖ := by
    unfold FF
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ ‖FF S y‖ := norm_nonneg _
  have : ‖FF S y‖ ^ 2 ≤ (|fR y| + ‖gW S y‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_abs (fR y), sq_nonneg (|fR y| - ‖gW S y‖)]

lemma ii_FF (S : Finset Zeros) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y => ‖FF S y‖ ^ 2) volume a b := by
  refine (((ii_fR ha hab).const_mul 2).add ((ii_gW S ha hab).const_mul 2)).mono_fun'
    (((measurable_FF S).norm.pow_const 2).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  exact norm_FF_sq_le S y

/-! ### One block -/

lemma log_sq_le_sqrt {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 2 ≤ 16 * Real.sqrt t := by
  have h0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 := Real.log_le_rpow_div (x := t) (by linarith) (by norm_num : (0 : ℝ) < 1 / 4)
  have h2 : Real.log t ≤ 4 * t ^ (1 / 4 : ℝ) := by
    have : t ^ (1 / 4 : ℝ) / (1 / 4) = 4 * t ^ (1 / 4 : ℝ) := by ring
    linarith
  have h3 : (t ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  calc Real.log t ^ 2 ≤ (4 * t ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h2 2
    _ = 16 * Real.sqrt t := by rw [mul_pow, h3]; norm_num

theorem block_FF (hRH : RiemannHypothesis) : ∃ K₁ Ct : ℝ, 0 ≤ K₁ ∧ 0 < Ct ∧
    ∀ (S : Finset Zeros) (Y : ℝ), 2 ≤ Y →
    ∫ y in Y..4 * Y, ‖FF S y‖ ^ 2
      ≤ K₁ / Real.sqrt Y + 9 * eta S (1 / Y) ^ 2 + 3 * (Ct * tailS S) := by
  obtain ⟨B, hB0, hB⟩ := psi_approx hRH
  obtain ⟨Ct, hCt, hT⟩ := tail_mean hRH
  set K₀ : ℝ := 2 * B ^ 2 + 1536 with hK₀
  refine ⟨9 * K₀, Ct, by positivity, hCt, fun S Y hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hY4 : Y ≤ 4 * Y := by linarith
  set δ : ℝ := 1 / Y with hδdef
  have hδ : 0 < δ := by positivity
  have hδ' : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ hY0 (by norm_num)]; linarith
  obtain ⟨htc, htm⟩ := hT S δ hδ hδ'
  set tl : ℝ → ℂ := zeroWave (tcoef S δ) with htl
  set η := eta S δ with hη
  have hη0 : 0 ≤ η := by
    rw [hη, eta]; exact Finset.sum_nonneg fun ρ _ => by positivity
  set sY := Real.sqrt Y with hsY
  have hsY0 : 0 < sY := Real.sqrt_pos.2 hY0
  -- the pointwise bound
  set bnd : ℝ → ℝ := fun y => 3 * (K₀ / (Y * sY) + η ^ 2 / Y + ‖tl (Real.log y)‖ ^ 2 / y)
    with hbnd
  have hpt : ∀ y ∈ Set.Icc Y (4 * Y), ‖FF S y‖ ^ 2 ≤ bnd y := by
    rintro y ⟨hy1, hy2⟩
    have hy0 : 0 < y := by linarith
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
    have hsyy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
    set A : ℂ := ((ψ y - y : ℝ) : ℂ) + (Real.sqrt y : ℂ) * G δ (Real.log y) with hA
    have hAb : ‖A‖ ≤ B + 4 * Real.log (y + 4) := hB Y y hY hy1 hy2
    have hGW := G_sub_wave hRH S hδ hδ' (Real.log y)
    have hid : FF S y = ((1 / y : ℝ) : ℂ) * A
        - ((Real.sqrt y)⁻¹ : ℝ) * (G δ (Real.log y) - wave S binv (Real.log y)) := by
      have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy0.ne'
      have hsc : (Real.sqrt y : ℂ) ≠ 0 := ofReal_ne_zero.2 hsy.ne'
      have hsq : (Real.sqrt y : ℂ) * (Real.sqrt y : ℂ) = (y : ℂ) := by
        rw [← ofReal_mul, hsyy]
      rw [FF, fR, gW, hA]
      push_cast
      rw [← hsq]
      field_simp
      ring
    set L := Real.log (y + 4) with hL
    have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
    have hn : ‖FF S y‖ ≤ (B + 4 * L) / y + η / Real.sqrt y + ‖tl (Real.log y)‖ / Real.sqrt y := by
      rw [hid]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      have e1 : 1 / y * ‖A‖ ≤ (B + 4 * L) / y := by
        rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hAb hy0.le
      have e2 : (Real.sqrt y)⁻¹ * ‖G δ (Real.log y) - wave S binv (Real.log y)‖
          ≤ η / Real.sqrt y + ‖tl (Real.log y)‖ / Real.sqrt y := by
        rw [← add_div, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right hGW hsy.le
      linarith
    -- `(B + 4L)² ≤ K₀ √y`
    have hLs : L ^ 2 ≤ 48 * Real.sqrt y := by
      have h1 := log_sq_le_sqrt (t := y + 4) (by linarith)
      have h2 : Real.sqrt (y + 4) ≤ 3 * Real.sqrt y := by
        rw [show (3 : ℝ) * Real.sqrt y = Real.sqrt (9 * y) by
          rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      rw [← hL] at h1
      linarith
    have hs1 : 1 ≤ Real.sqrt y := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hBL : (B + 4 * L) ^ 2 ≤ K₀ * Real.sqrt y := by
      have : (B + 4 * L) ^ 2 ≤ 2 * B ^ 2 + 32 * L ^ 2 := by nlinarith [sq_nonneg (B - 4 * L)]
      rw [hK₀]; nlinarith [sq_nonneg B]
    -- squares
    have hsq3 : ‖FF S y‖ ^ 2 ≤ 3 * (((B + 4 * L) / y) ^ 2 + (η / Real.sqrt y) ^ 2
        + (‖tl (Real.log y)‖ / Real.sqrt y) ^ 2) := by
      have h0 : 0 ≤ ‖FF S y‖ := norm_nonneg _
      have := pow_le_pow_left₀ h0 hn 2
      nlinarith [sq_nonneg ((B + 4 * L) / y - η / Real.sqrt y),
        sq_nonneg ((B + 4 * L) / y - ‖tl (Real.log y)‖ / Real.sqrt y),
        sq_nonneg (η / Real.sqrt y - ‖tl (Real.log y)‖ / Real.sqrt y)]
    have t1 : ((B + 4 * L) / y) ^ 2 ≤ K₀ / (Y * sY) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsY : sY ≤ Real.sqrt y := Real.sqrt_le_sqrt hy1
      have hy2' : Y * sY * Real.sqrt y ≤ y ^ 2 := by
        have : Y * sY ≤ y * Real.sqrt y :=
          mul_le_mul hy1 hsY hsY0.le hy0.le
        calc Y * sY * Real.sqrt y ≤ y * Real.sqrt y * Real.sqrt y :=
              mul_le_mul_of_nonneg_right this hsy.le
          _ = y ^ 2 := by rw [mul_assoc, hsyy]; ring
      have hK0 : 0 ≤ K₀ := by positivity
      calc (B + 4 * L) ^ 2 * (Y * sY) ≤ K₀ * Real.sqrt y * (Y * sY) :=
            mul_le_mul_of_nonneg_right hBL (by positivity)
        _ = K₀ * (Y * sY * Real.sqrt y) := by ring
        _ ≤ K₀ * y ^ 2 := mul_le_mul_of_nonneg_left hy2' hK0
    have t2 : (η / Real.sqrt y) ^ 2 ≤ η ^ 2 / Y := by
      rw [div_pow, Real.sq_sqrt hy0.le]
      exact div_le_div_of_nonneg_left (by positivity) hY0 hy1
    have t3 : (‖tl (Real.log y)‖ / Real.sqrt y) ^ 2 = ‖tl (Real.log y)‖ ^ 2 / y := by
      rw [div_pow, Real.sq_sqrt hy0.le]
    simp only [hbnd]
    linarith
  -- integrate
  have hlogc : ContinuousOn (fun y => ‖tl (Real.log y)‖ ^ 2 / y) (Set.uIcc Y (4 * Y)) := by
    rw [Set.uIcc_of_le hY4]
    have hpos : ∀ y ∈ Set.Icc Y (4 * Y), 0 < y := fun y hy => lt_of_lt_of_le hY0 hy.1
    refine ContinuousOn.div ((htc.comp_continuousOn (Real.continuousOn_log.mono fun y hy => ?_)).norm.pow 2)
      continuousOn_id fun y hy => (hpos y hy).ne'
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hpos y hy).ne'
  have hbI : IntervalIntegrable bnd volume Y (4 * Y) := by
    simp only [hbnd]
    exact ((intervalIntegrable_const).add hlogc.intervalIntegrable).const_mul 3
  have htail : ∫ y in Y..4 * Y, ‖tl (Real.log y)‖ ^ 2 / y ≤ Ct * tailS S := by
    rw [integral_comp_log_div (h := fun u => ‖tl u‖ ^ 2) (htc.norm.pow 2) hY0 hY4]
    have hlog4 : Real.log (4 * Y) = Real.log Y + Real.log 4 := by
      rw [Real.log_mul (by norm_num) hY0.ne']; ring
    have hlog4' : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    refine le_trans ?_ (htm (Real.log Y))
    exact integral_mono_interval le_rfl (by rw [hlog4]; linarith) (by rw [hlog4]; linarith)
      (Filter.Eventually.of_forall fun u => by positivity)
      ((htc.norm.pow 2).intervalIntegrable _ _)
  have hint : ∫ y in Y..4 * Y, bnd y = 3 * ((4 * Y - Y) * (K₀ / (Y * sY) + η ^ 2 / Y)
      + ∫ y in Y..4 * Y, ‖tl (Real.log y)‖ ^ 2 / y) := by
    simp only [hbnd]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      hlogc.intervalIntegrable, intervalIntegral.integral_const, smul_eq_mul]
  have hc1 : (4 * Y - Y) * (K₀ / (Y * sY) + η ^ 2 / Y) = 3 * K₀ / sY + 3 * η ^ 2 := by
    field_simp; ring
  calc ∫ y in Y..4 * Y, ‖FF S y‖ ^ 2 ≤ ∫ y in Y..4 * Y, bnd y :=
        integral_mono_on hY4 (ii_FF S hY0 hY4) hbI hpt
    _ = 3 * ((4 * Y - Y) * (K₀ / (Y * sY) + η ^ 2 / Y)
          + ∫ y in Y..4 * Y, ‖tl (Real.log y)‖ ^ 2 / y) := hint
    _ ≤ 3 * ((3 * K₀ / sY + 3 * η ^ 2) + Ct * tailS S) := by rw [hc1]; gcongr
    _ = 9 * K₀ / sY + 9 * η ^ 2 + 3 * (Ct * tailS S) := by ring

/-! ### Summing blocks -/

lemma quarter_induction_from (I B : ℝ → ℝ) {Y₀ : ℝ} (hY₀ : 0 < Y₀)
    (hbase : ∀ X, Y₀ ≤ X → X ≤ 4 * Y₀ → I X ≤ B X)
    (hstep : ∀ X, 4 * Y₀ < X → I (X / 4) ≤ B (X / 4) → I X ≤ B X) :
    ∀ X, Y₀ ≤ X → I X ≤ B X := by
  have key : ∀ n : ℕ, ∀ X, Y₀ ≤ X → X ≤ 4 * Y₀ * 4 ^ n → I X ≤ B X := by
    intro n
    induction n with
    | zero => intro X h1 h2; exact hbase X h1 (by simpa using h2)
    | succ n ih =>
      intro X h1 h2
      by_cases h8 : X ≤ 4 * Y₀
      · exact hbase X h1 h8
      · push Not at h8
        refine hstep X h8 (ih (X / 4) (by linarith) ?_)
        rw [pow_succ] at h2
        linarith
  intro X hX
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (X / Y₀) (by norm_num : (1 : ℝ) < 4)
  refine key n X hX ?_
  rw [div_lt_iff₀ hY₀] at hn
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) n]

theorem sum_blocks (S : Finset Zeros) {Y₀ β : ℝ} (hY₀ : 2 ≤ Y₀) (hβ : 0 ≤ β)
    (hb : ∀ Y, Y₀ ≤ Y → ∫ y in Y..4 * Y, ‖FF S y‖ ^ 2 ≤ β) :
    ∀ X, Y₀ ≤ X → ∫ y in Y₀..X, ‖FF S y‖ ^ 2 ≤ β + β / Real.log 4 * Real.log X := by
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hY0 : 0 < Y₀ := by linarith
  refine quarter_induction_from (fun X => ∫ y in Y₀..X, ‖FF S y‖ ^ 2)
    (fun X => β + β / Real.log 4 * Real.log X) hY0 (fun X h1 h2 => ?_) (fun X h8 ih => ?_)
  · have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have : ∫ y in Y₀..X, ‖FF S y‖ ^ 2 ≤ ∫ y in Y₀..4 * Y₀, ‖FF S y‖ ^ 2 :=
      integral_mono_interval le_rfl h1 h2 (Filter.Eventually.of_forall fun y => by positivity)
        (ii_FF S hY0 (by linarith))
    have h3 := hb Y₀ le_rfl
    have : 0 ≤ β / Real.log 4 * Real.log X := by positivity
    linarith
  · have hX4 : 0 < X / 4 := by linarith
    have hsplit : ∫ y in Y₀..X, ‖FF S y‖ ^ 2
        = (∫ y in Y₀..X / 4, ‖FF S y‖ ^ 2) + ∫ y in X / 4..4 * (X / 4), ‖FF S y‖ ^ 2 := by
      rw [show 4 * (X / 4) = X by ring]
      exact (integral_add_adjacent_intervals (ii_FF S hY0 (by linarith))
        (ii_FF S hX4 (by linarith))).symm
    have hlog : Real.log (X / 4) = Real.log X - Real.log 4 :=
      Real.log_div (by linarith) (by norm_num)
    have h3 := hb (X / 4) (by linarith)
    rw [hsplit]
    rw [hlog] at ih
    have e : β / Real.log 4 * (Real.log X - Real.log 4) = β / Real.log 4 * Real.log X - β := by
      field_simp
    linarith

/-! ### The asymptotic -/

lemma im_injective (hRH : RiemannHypothesis) {ρ ρ' : Zeros} (h : ρ ≠ ρ') :
    (ρ : ℂ).im ≠ (ρ' : ℂ).im := by
  intro him
  apply h
  apply Subtype.ext
  apply Complex.ext
  · rw [zero_re_of_RH hRH ρ, zero_re_of_RH hRH ρ']
  · exact him

/-- **Cramér's asymptotic** (zeros of `ξ` form): under RH,
`(∫_1^X ((ψ(x) − x)/x)² dx) / log X → Σ_ρ ‖m_ρ/ρ‖²`. -/
theorem logMeanSquare_tendsto (hRH : RiemannHypothesis) :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, ((ψ x - x) / x) ^ 2) / Real.log X) atTop
      (𝓝 (∑' ρ, ‖binv ρ‖ ^ 2)) := by
  obtain ⟨K₁, Ct, hK₁, hCt, hblock⟩ := block_FF hRH
  have hbs := binv_summable hRH
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine tendsto_of_approx (tsum_nonneg fun ρ => by positivity) fun ε hε => ?_
  -- choose `S`
  have hpos : 0 < ε * Real.log 4 / 2 / (3 * Ct) := by positivity
  obtain ⟨S, hS1, hS2⟩ := ((hbs.hasSum.eventually (Metric.closedBall_mem_nhds _ hε)).and
    ((tailS_tendsto hRH).eventually (gt_mem_nhds hpos))).exists
  have hS1' : |∑ ρ ∈ S, ‖binv ρ‖ ^ 2 - ∑' ρ, ‖binv ρ‖ ^ 2| ≤ ε := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hS1
  have hS2' : 3 * (Ct * tailS S) ≤ ε * Real.log 4 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hS2; nlinarith
  -- choose the first block
  have hsmall : Tendsto (fun Y : ℝ => K₁ / Real.sqrt Y + 9 * eta S (1 / Y) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y : ℝ => K₁ / Real.sqrt Y) atTop (𝓝 0) :=
      Real.tendsto_sqrt_atTop.const_div_atTop K₁
    have h2 : Tendsto (fun Y : ℝ => 9 * eta S (1 / Y) ^ 2) atTop (𝓝 0) := by
      simpa using ((eta_tendsto hRH S).pow 2).const_mul 9
    simpa using h1.add h2
  have hpos2 : 0 < ε * Real.log 4 / 2 := by positivity
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1
    ((hsmall.eventually (gt_mem_nhds hpos2)).and (eventually_ge_atTop (2 : ℝ)))
  set Y₁ := max Y₀ 2 with hY₁
  have hY₁2 : 2 ≤ Y₁ := le_max_right _ _
  set β := ε * Real.log 4 with hβ
  have hb : ∀ Y, Y₁ ≤ Y → ∫ y in Y..4 * Y, ‖FF S y‖ ^ 2 ≤ β := fun Y hY => by
    obtain ⟨h1, h2⟩ := hY₀ Y (le_trans (le_max_left _ _) hY)
    have := hblock S Y h2
    linarith
  have hsum := sum_blocks S hY₁2 (by positivity) hb
  set cS := ∑ ρ ∈ S, ‖binv ρ‖ ^ 2 with hcS
  refine ⟨cS, offDiag S binv, (∫ y in (1 : ℝ)..Y₁, ‖FF S y‖ ^ 2) + β,
    fun X => ∫ y in (1 : ℝ)..X, ‖gW S y‖ ^ 2, fun X => ∫ y in (1 : ℝ)..X, ‖FF S y‖ ^ 2,
    hS1', ?_⟩
  filter_upwards [eventually_ge_atTop Y₁] with X hX
  have hX1 : 1 ≤ X := by linarith
  refine ⟨?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · -- the finite approximant
    have hW : ∫ y in (1 : ℝ)..X, ‖gW S y‖ ^ 2 = ∫ u in (0 : ℝ)..Real.log X, ‖wave S binv u‖ ^ 2 := by
      have e : ∫ y in (1 : ℝ)..X, ‖gW S y‖ ^ 2
          = ∫ y in (1 : ℝ)..X, ‖wave S binv (Real.log y)‖ ^ 2 / y := by
        refine integral_congr fun y hy => ?_
        rw [Set.uIcc_of_le hX1] at hy
        exact norm_gW_sq S (by linarith [hy.1])
      rw [e, integral_comp_log_div (h := fun u => ‖wave S binv u‖ ^ 2)
        ((continuous_wave S binv).norm.pow 2) one_pos hX1, Real.log_one]
    rw [hW]
    have := finite_mean S binv (fun ρ _ ρ' _ h => im_injective hRH h) 0 (Real.log X)
    rw [sub_zero, mul_comm] at this; exact this
  · -- the error
    have hsplit : ∫ y in (1 : ℝ)..X, ‖FF S y‖ ^ 2
        = (∫ y in (1 : ℝ)..Y₁, ‖FF S y‖ ^ 2) + ∫ y in Y₁..X, ‖FF S y‖ ^ 2 :=
      (integral_add_adjacent_intervals (ii_FF S one_pos (by linarith))
        (ii_FF S (by linarith) hX)).symm
    have h := hsum X hX
    have e : β / Real.log 4 = ε := by rw [hβ]; field_simp
    rw [e] at h
    rw [hsplit]
    linarith
  · -- `f² ≤ (1+t)|g|² + (1+1/t)|f+g|²`
    have hpt : ∀ y, fR y ^ 2 ≤ (1 + t) * ‖gW S y‖ ^ 2 + (1 + 1 / t) * ‖FF S y‖ ^ 2 := by
      intro y
      have h1 : |fR y| ≤ ‖gW S y‖ + ‖FF S y‖ := by
        have : (fR y : ℂ) = FF S y - gW S y := by rw [FF]; ring
        rw [← Real.norm_eq_abs, ← Complex.norm_real, this]
        exact (norm_sub_le _ _).trans (by rw [add_comm])
      have h2 : fR y ^ 2 ≤ (‖gW S y‖ + ‖FF S y‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      exact h2.trans (sq_add_le_weighted _ _ ht)
    have := integral_mono_on hX1 (ii_fR one_pos hX1)
      (((ii_gW S one_pos hX1).const_mul (1 + t)).add ((ii_FF S one_pos hX1).const_mul (1 + 1 / t)))
      fun y _ => hpt y
    rw [intervalIntegral.integral_add ((ii_gW S one_pos hX1).const_mul _)
      ((ii_FF S one_pos hX1).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at this
    exact this
  · -- `|g|² ≤ (1+t)f² + (1+1/t)|f+g|²`
    have hpt : ∀ y, ‖gW S y‖ ^ 2 ≤ (1 + t) * fR y ^ 2 + (1 + 1 / t) * ‖FF S y‖ ^ 2 := by
      intro y
      have h1 : ‖gW S y‖ ≤ |fR y| + ‖FF S y‖ := by
        have : gW S y = FF S y - (fR y : ℂ) := by rw [FF]; ring
        rw [this]
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, add_comm]
      have h2 : ‖gW S y‖ ^ 2 ≤ (|fR y| + ‖FF S y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have := sq_add_le_weighted |fR y| ‖FF S y‖ ht
      rw [sq_abs] at this
      exact h2.trans this
    have := integral_mono_on hX1 (ii_gW S one_pos hX1)
      (((ii_fR one_pos hX1).const_mul (1 + t)).add ((ii_FF S one_pos hX1).const_mul (1 + 1 / t)))
      fun y _ => hpt y
    rw [intervalIntegral.integral_add ((ii_fR one_pos hX1).const_mul _)
      ((ii_FF S one_pos hX1).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at this
    exact this

end Cramer.MeanSq
