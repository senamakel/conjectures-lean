import LLS.Defs

/-!
# Perron formulas for the logarithmic kernel `x^s / s²` on `Re s = 2`

* `perron_log`: `(1/2π) ∫ y^s/s² = log y` for `y ≥ 1`, `0` for `0 < y < 1`.
* `perron_lres`: `(1/2π) ∫ x^s/((s − w) s²) = x^w/w² − log x/w − 1/w²` (`x ≥ 1`, `Re w < 2`,
  `w ≠ 0`).
* `perron_cube`: `(1/2π) ∫ x^s/s³ = (log x)²/2` (`x ≥ 1`).
* `perron_log_weighted`: `Σ_{n ≤ N} a(n) log(N/n) = (1/2π) ∫ LSeries a (2+it) N^s/s² dt`.

All are proved by Mellin inversion through erdos-985's `PerronAux.perron_of_mellin` /
`perron_prof`; integrability comes from the erdos-985 kernels `x^s/(s(s+1))` and the bound
`|(s+1)/s| ≤ 3/2` on `Re s = 2`.
-/

namespace LLS.LogAux

open Complex MeasureTheory Set Filter Topology Erdos985.Analytic Erdos985.Analytic.PerronAux

/-- The point `2 + t i` of the line. -/
local notation "σ" t => ((2 : ℂ) + (t : ℝ) * I)

lemma line_ne_zero2 (t : ℝ) : ((2 : ℂ) + t * I) ≠ 0 := line_ne_zero two_pos t

lemma two_le_norm_line (t : ℝ) : (2 : ℝ) ≤ ‖(2 : ℂ) + t * I‖ := by
  have := c_le_norm_line (c := 2) (by norm_num) t
  simpa using this

/-- `|(s+1)/s| ≤ 3/2` on `Re s = 2`. -/
lemma norm_add_one_div_le (t : ℝ) : ‖((2 : ℂ) + t * I + 1) / ((2 : ℂ) + t * I)‖ ≤ 3 / 2 := by
  have h2 := two_le_norm_line t
  have hpos : 0 < ‖(2 : ℂ) + t * I‖ := by linarith
  rw [norm_div, div_le_iff₀ hpos]
  have := norm_add_le ((2 : ℂ) + t * I) 1
  rw [norm_one] at this
  linarith

/-- `|1/s| ≤ 1/2` on `Re s = 2`. -/
lemma norm_inv_line_le (t : ℝ) : ‖((2 : ℂ) + t * I)⁻¹‖ ≤ 1 / 2 := by
  rw [norm_inv]
  have := two_le_norm_line t
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) this

lemma integrable_of_le_mul {f g : ℝ → ℂ} (hg : Integrable g) (hf : Continuous f) (B : ℝ)
    (h : ∀ t, ‖f t‖ ≤ B * ‖g t‖) : Integrable f :=
  (hg.norm.const_mul B).mono' hf.aestronglyMeasurable (ae_of_all _ h)

lemma continuous_line : Continuous fun t : ℝ => (2 : ℂ) + t * I :=
  continuous_const.add (continuous_ofReal.mul continuous_const)

/-- The log kernel `x^s/s²` on `Re s = 2`. -/
noncomputable def lkern (x t : ℝ) : ℂ := (x : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 2

lemma lkern_eq (x t : ℝ) : lkern x t = IdentityAux.kern x t *
    (((2 : ℂ) + t * I + 1) / ((2 : ℂ) + t * I)) := by
  unfold lkern IdentityAux.kern
  have h0 := line_ne_zero2 t
  have h1 := line_add_one_ne_zero (c := 2) two_pos t
  push_cast at h1 ⊢
  field_simp

lemma continuous_lkern {x : ℝ} (hx : 0 < x) : Continuous (lkern x) := by
  unfold lkern
  exact (continuous_cpow_line hx 2 |>.congr fun t => by simp).div (continuous_line.pow 2)
    fun t => pow_ne_zero 2 (line_ne_zero2 t)

lemma integrable_lkern {x : ℝ} (hx : 0 < x) : Integrable (lkern x) := by
  refine integrable_of_le_mul (IdentityAux.integrable_kern hx) (continuous_lkern hx) (3 / 2)
    fun t => ?_
  rw [lkern_eq, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_add_one_div_le t) (norm_nonneg _)

lemma integrable_inv_sq : Integrable fun t : ℝ => 1 / ((2 : ℂ) + t * I) ^ 2 := by
  have := integrable_lkern (x := 1) one_pos
  refine this.congr (ae_of_all _ fun t => ?_)
  simp [lkern]

/-- Perron for the log kernel. -/
theorem perron_log (y : ℝ) (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 2
      = ((if 1 ≤ y then Real.log y else 0 : ℝ) : ℂ) := by
  have key := perron_prof (c := 2) hy (-1) 0 0 0 0 0 0 0 (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun _ => by ring) (F := fun s => 1 / s ^ 2)
    (fun t => by simp only [add_zero, zero_mul]; push_cast; ring)
    (by simpa using integrable_inv_sq)
  have e : (fun t : ℝ => (y : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 2)
      = fun t : ℝ => (y : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) * (fun s => 1 / s ^ 2)
          (((2 : ℝ) : ℂ) + t * I) := by
    funext t; push_cast; ring
  rw [e, key, prof]
  split_ifs with h
  · rw [indicator_of_mem (show y⁻¹ ∈ Ioc (0 : ℝ) 1 from ⟨inv_pos.2 hy, inv_le_one_of_one_le₀ h⟩),
      Real.log_inv]
    push_cast
    simp
  · rw [indicator_of_notMem]
    · simp
    · intro hm
      have := hm.2
      rw [inv_le_one₀ hy] at this
      exact h this

lemma integral_lkern {x : ℝ} (hx : 1 ≤ x) :
    ∫ t, lkern x t = 2 * Real.pi * (Real.log x : ℂ) := by
  have h := perron_log x (by linarith)
  rw [if_pos hx] at h
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have : ∫ t, lkern x t = ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 2 := rfl
  rw [this, ← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]

/-- The log kernel with an extra simple pole `w`. -/
noncomputable def lres (x : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - w) * ((2 : ℂ) + t * I) ^ 2)

lemma lres_eq (x : ℝ) (w : ℂ) (hw : w.re < 2) (t : ℝ) : lres x w t =
    (x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - w) * ((2 : ℂ) + t * I) *
      ((2 : ℂ) + t * I + 1)) * (((2 : ℂ) + t * I + 1) / ((2 : ℂ) + t * I)) := by
  unfold lres
  have h0 := line_ne_zero2 t
  have h1 := line_add_one_ne_zero (c := 2) two_pos t
  have h2 := line_sub_ne_zero (c := 2) t (w := w) (by simpa using hw)
  push_cast at h1 h2 ⊢
  field_simp

lemma integrable_lres {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : w.re < 2) : Integrable (lres x w) := by
  have hI := integrable_perron_kernel (x := x) (c := 2) hx two_pos (w := w) (by simpa using hw)
  have hc : Continuous (lres x w) := by
    unfold lres
    refine ((continuous_cpow_line hx 2).congr fun t => by simp).div
      ((continuous_line.sub continuous_const).mul (continuous_line.pow 2)) fun t => ?_
    exact mul_ne_zero (by simpa using line_sub_ne_zero (c := 2) t (w := w) (by simpa using hw))
      (pow_ne_zero 2 (line_ne_zero2 t))
  refine integrable_of_le_mul (hI.congr (ae_of_all _ fun t => by push_cast; rfl)) hc (3 / 2)
    fun t => ?_
  rw [lres_eq x w hw, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_add_one_div_le t) (norm_nonneg _)

/-- Residues of `x^s/((s − w)s²)` at `w` and `0`. -/
theorem perron_lres (x : ℝ) (hx : 1 ≤ x) (w : ℂ) (hw : w.re < 2) (hw0 : w ≠ 0) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, lres x w t
      = (x : ℂ) ^ w / w ^ 2 - (Real.log x : ℂ) / w - 1 / w ^ 2 := by
  have hx0 : 0 < x := by linarith
  have key := perron_prof (c := 2) hx0 (1 / w) 0 (1 / w ^ 2) (-1 / w ^ 2) 0 (-w) 0 0
    (by simp) (by simp) (by simp; linarith) (by simp) (by simp)
    (fun _ => by ring) (F := fun s => 1 / ((s - w) * s ^ 2))
    (fun t => by
      have h0 := line_ne_zero2 t
      have h2 := line_sub_ne_zero (c := 2) t (w := w) (by simpa using hw)
      push_cast at h2 ⊢
      simp only [add_zero, ← sub_eq_add_neg]
      field_simp
      ring)
    (by
      have := integrable_lres one_pos hw
      refine this.congr (ae_of_all _ fun t => ?_)
      simp [lres])
  have e : lres x w = fun t : ℝ => (x : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) *
      (fun s => 1 / ((s - w) * s ^ 2)) (((2 : ℝ) : ℂ) + t * I) := by
    funext t; simp [lres, div_eq_mul_inv]
  rw [e, key, prof, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), inv_ofReal_cpow_neg hx0, Real.log_inv]
  simp only [cpow_zero]
  push_cast
  ring

/-! ### The triple pole: Mellin transform of `log² t` on `(0, 1]` -/

lemma hasMellin_log_sq {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (Real.log t : ℂ) * ((Real.log t : ℂ) * P 0 t)) s (2 / s ^ 3) := by
  set g : ℝ → ℂ := fun t => (Real.log t : ℂ) * P 0 t with hg
  have hM1 := (hasMellin_log_P 0 (s := 1) (by simp) (by simp)).1
  have hloc : LocallyIntegrableOn g (Ioi 0) := by
    have : IntegrableOn g (Ioi 0) := by
      unfold MellinConvergent at hM1
      refine hM1.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp [g]
    exact this.locallyIntegrableOn
  have htop : g =O[atTop] (· ^ (-(s.re + 1))) := by
    refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [g, P, indicator_of_notMem (fun hm : t ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 ht))]
  have hbot : g =O[𝓝[>] 0] (· ^ (-(s.re / 2))) := by
    have hl := (isLittleO_log_rpow_nhdsGT_zero (r := -(s.re / 2)) (by linarith)).isBigO
    rw [← Asymptotics.isBigO_norm_left] at hl ⊢
    refine hl.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    simp [g, P, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht.1, ht.2.le⟩)]
  obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow hloc htop (by linarith) hbot
    (by linarith)
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hev : mellin g =ᶠ[𝓝 s] fun z => -1 / z ^ 2 := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [(hasMellin_log_P 0 (s := z) (by simp) (by simpa using hz)).2, add_zero]
  have h2 : HasDerivAt (fun z : ℂ => -1 / z ^ 2) (2 / s ^ 3) s := by
    have h := ((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs0)).neg
    convert h using 1
    · funext z; simp [div_eq_mul_inv]
    · simp only [Nat.cast_ofNat, show (2:ℕ) - 1 = 1 from rfl, pow_one]
      field_simp
  have h3 := (h2.congr_of_eventuallyEq hev).unique hder
  have hfe : (fun t : ℝ => Real.log t • g t)
      = fun t => (Real.log t : ℂ) * ((Real.log t : ℂ) * P 0 t) := by
    funext t; simp only [g, Complex.real_smul]
  rw [hfe] at hconv h3
  exact ⟨hconv, h3.symm⟩

lemma continuous_inv_cube : Continuous fun t : ℝ => 1 / ((2 : ℂ) + t * I) ^ 3 := by
  have h : Continuous fun t : ℝ => ((2 : ℂ) + t * I) ^ 3 := continuous_line.pow 3
  simp only [one_div]
  exact h.inv₀ fun t => pow_ne_zero 3 (line_ne_zero2 t)

lemma integrable_inv_cube : Integrable fun t : ℝ => 1 / ((2 : ℂ) + t * I) ^ 3 := by
  refine integrable_of_le_mul (g := fun t : ℝ => 1 / ((2 : ℂ) + t * I) ^ 2) integrable_inv_sq
    continuous_inv_cube (1 / 2) fun t => ?_
  · have e : 1 / ((2 : ℂ) + t * I) ^ 3 = ((2 : ℂ) + t * I)⁻¹ * (1 / ((2 : ℂ) + t * I) ^ 2) := by
      have := line_ne_zero2 t; field_simp
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_inv_line_le t) (norm_nonneg _)

/-- `(1/2π) ∫ x^s/s³ = (log x)²/2` for `x ≥ 1`. -/
theorem perron_cube (x : ℝ) (hx : 1 ≤ x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 3
      = (Real.log x : ℂ) ^ 2 / 2 := by
  have hx0 : 0 < x := by linarith
  set f : ℝ → ℂ := fun t => (1 / 2 : ℂ) • ((Real.log t : ℂ) * ((Real.log t : ℂ) * P 0 t))
  have hre : ∀ t : ℝ, (((2 : ℝ) : ℂ) + t * I).re = 2 := fun t => by simp
  have hM : ∀ z : ℂ, 0 < z.re → HasMellin f z (1 / z ^ 3) := fun z hz => by
    have h := hasMellin_log_sq hz
    have k := hasMellin_const_smul h.1 (1 / 2 : ℂ)
    refine ⟨k.1, ?_⟩
    rw [k.2, h.2, smul_eq_mul]; ring
  have hfeq : f = indicator (Ioc 0 1) (fun t : ℝ => (1 / 2 : ℂ) * ((Real.log t : ℂ) *
      (Real.log t : ℂ))) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [f, P, ht]
  have hcont : ContinuousAt f x⁻¹ := by
    rw [hfeq]
    refine continuousAt_indicator_Ioc (inv_pos.2 hx0) ?_ (fun _ => by simp)
    have hl : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) x⁻¹ :=
      continuous_ofReal.continuousAt.comp (Real.continuousAt_log (inv_pos.2 hx0).ne')
    exact continuousAt_const.mul (hl.mul hl)
  have h := perron_of_mellin (f := f) (F := fun s => 1 / s ^ 3) (c := 2) hx0
    (hM 2 (by simp)).1 (fun t => (hM _ (by rw [hre]; norm_num)).2)
    (by simpa using integrable_inv_cube) hcont
  have e : (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 3)
      = fun t : ℝ => (x : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) * (fun s => 1 / s ^ 3)
          (((2 : ℝ) : ℂ) + t * I) := by
    funext t; push_cast; ring
  rw [e, h, hfeq, indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from
    ⟨inv_pos.2 hx0, inv_le_one_of_one_le₀ hx⟩), Real.log_inv]
  push_cast
  ring

/-! ### The weighted Perron formula with weight `log(N/n)` -/

lemma norm_lkern (y t : ℝ) (hy : 0 < y) :
    ‖lkern y t‖ = y ^ (2 : ℝ) * ‖1 / ((2 : ℂ) + t * I) ^ 2‖ := by
  unfold lkern
  rw [div_eq_mul_one_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
  simp

lemma term_mul_lkern (a : ℕ → ℂ) (t : ℝ) (N n : ℕ) :
    LSeries.term a ((2 : ℂ) + t * I) n * lkern N t
      = if n = 0 then 0 else a n * lkern ((N : ℝ) / n) t := by
  rw [LSeries.term_def]
  split_ifs with hn
  · simp
  · unfold lkern
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hnc : (n : ℂ) ^ ((2 : ℂ) + t * I) ≠ 0 := by
      rw [cpow_ne_zero_iff]; left; exact_mod_cast hn
    rw [ofReal_div, div_eq_mul_inv ((N : ℝ) : ℂ), ← ofReal_inv, mul_cpow_ofReal_nonneg
      (by positivity) (by positivity), ofReal_inv, inv_cpow_ofReal_nonneg hn0.le, ofReal_natCast,
      ofReal_natCast]
    field_simp

theorem perron_log_weighted (a : ℕ → ℂ) (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (2 : ℝ))
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), a n * (Real.log ((N : ℝ) / n) : ℂ)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((2 : ℂ) + t * I) * lkern N t := by
  set C := ∫ t : ℝ, ‖1 / ((2 : ℂ) + t * I) ^ 2‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < (N : ℝ) / n := fun n hn =>
    div_pos hN0 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  let G : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * lkern ((N : ℝ) / n) t
  have hG_int : ∀ n, Integrable (G n) := by
    intro n
    by_cases hn : n = 0
    · simp only [G, hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [G, hn, ↓reduceIte]; exact (integrable_lkern (hpos n hn)).const_mul _
  have hG_norm : ∀ n, ∫ t, ‖G n t‖ = if n = 0 then 0 else ‖a n‖ * (((N : ℝ) / n) ^ (2 : ℝ) * C) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte, norm_mul]
      rw [integral_const_mul]
      simp_rw [norm_lkern _ _ (hpos n hn)]
      rw [integral_const_mul]
  have hsum : Summable fun n => ∫ t, ‖G n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (ha.mul_left ((N : ℝ) ^ (2 : ℝ) * C))
    rw [hG_norm]
    split_ifs with hn
    · have : 0 ≤ ‖a n‖ / (n : ℝ) ^ (2 : ℝ) := div_nonneg (norm_nonneg _) (by positivity)
      positivity
    · rw [Real.div_rpow hN0.le (Nat.cast_nonneg n)]
      apply le_of_eq
      ring
  have hfun : (fun t : ℝ => LSeries a ((2 : ℂ) + t * I) * lkern N t) = fun t => ∑' n, G n t := by
    funext t
    rw [LSeries, ← tsum_mul_right]
    congr 1
    funext n
    exact term_mul_lkern a t N n
  have hGint : ∀ n, ∫ t, G n t = if n = 0 then 0 else
      a n * (2 * Real.pi * ((if 1 ≤ (N : ℝ) / n then Real.log ((N : ℝ) / n) else 0 : ℝ) : ℂ)) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      rw [integral_const_mul]
      have h := perron_log _ (hpos n hn)
      have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
        mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
      congr 1
      have : ∫ t, lkern ((N : ℝ) / n) t = ∫ t : ℝ, (((N : ℝ) / n : ℝ) : ℂ) ^ ((2 : ℂ) + t * I) /
          ((2 : ℂ) + t * I) ^ 2 := rfl
      rw [this, ← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  rw [hfun, ← integral_tsum_of_summable_integral_norm hG_int hsum]
  simp_rw [hGint]
  rw [tsum_eq_sum (s := Finset.range (N + 1)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    by_cases hn0 : n = 0
    · subst hn0; simp
    have hle : 1 ≤ (N : ℝ) / n := by
      rw [one_le_div (Nat.cast_pos.2 (by omega))]; exact_mod_cast (by omega : n ≤ N)
    simp only [hn0, hle, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    field_simp
  · intro n hn
    rw [Finset.mem_range] at hn
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte]
    have hlt : ¬ 1 ≤ (N : ℝ) / n := by
      rw [not_le, div_lt_one (Nat.cast_pos.2 (by omega))]; exact_mod_cast (by omega : N < n)
    simp [hlt]

end LLS.LogAux
