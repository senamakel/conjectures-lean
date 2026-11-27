import Lindelof.BorelCaratheodory
import Lindelof.ThreeLines

/-!
# Step 8: assembly of RH ⇒ Lindelöf

For `0 < ε ≤ 1/2`: Step 4 gives `‖ζ(1/2+it)‖ ≤ C t^{ε/2} ‖ζ(1/2+ε+it)‖`; Steps 5–7 give
`‖ζ(1/2+ε+it)‖ ≤ 3 exp(C (log (t+2))^α)` with `α < 1`, which is `O(t^{ε/4})`.

The argument is stated once for any `f` satisfying `LogBounds f` (`isBigO_rpow_of_logBounds`);
`ζ` (`logBounds_riemannZeta`) and primitive Dirichlet L-functions (`logBounds_LFunction`) are
the two instances.
-/

namespace Lindelof

open Complex Filter Asymptotics

/-- `ζ` is controlled by the logarithm `M` of `zetaQ` away from the real axis. -/
theorem norm_riemannZeta_le_exp {M : ℂ → ℂ} (hexp : ∀ s ∈ halfPlane, exp (M s) = zetaQ s)
    {s : ℂ} (hs : s ∈ halfPlane) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 3 * Real.exp ‖M s‖ := by
  have hs1 : s ≠ 1 := by
    rintro rfl; simp at him; linarith
  have hsub : 1 ≤ ‖s - 1‖ := by
    calc (1 : ℝ) ≤ |s.im| := him
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := abs_im_le_norm _
  have hadd : ‖s + 1‖ ≤ 3 * ‖s - 1‖ := by
    calc ‖s + 1‖ = ‖(s - 1) + 2‖ := by ring_nf
      _ ≤ ‖s - 1‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * ‖s - 1‖ := by rw [show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
  have hplus : s + 1 ≠ 0 := by
    intro h
    have him0 : s.im = 0 := by simpa using congrArg Complex.im h
    rw [him0, abs_zero] at him; linarith
  have hz : riemannZeta s = (s - 1)⁻¹ * ((s + 1) * exp (M s)) := by
    rw [riemannZeta_eq_inv_sub_mul hs1, hexp s hs, zetaQ, mul_div_cancel₀ _ hplus]
  have hpos : 0 < ‖s - 1‖ := by linarith
  rw [hz, norm_mul, norm_inv, norm_mul, norm_exp]
  have hexp_le : Real.exp (M s).re ≤ Real.exp ‖M s‖ :=
    Real.exp_le_exp.mpr (re_le_norm _)
  calc ‖s - 1‖⁻¹ * (‖s + 1‖ * Real.exp (M s).re)
      ≤ ‖s - 1‖⁻¹ * (3 * ‖s - 1‖ * Real.exp ‖M s‖) := by
        gcongr
    _ = 3 * Real.exp ‖M s‖ := by field_simp

/-- For `α < 1` and any `C`, eventually `C (log (t+2))^α ≤ c log (t+2)` for `c > 0`. -/
theorem eventually_mul_log_rpow_le {α C c : ℝ} (hα : α < 1) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, C * Real.log (t + 2) ^ α ≤ c * Real.log (t + 2) := by
  have hlog : Tendsto (fun t : ℝ => Real.log (t + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 2 tendsto_id)
  have hdecay : Tendsto (fun x : ℝ => x ^ (-(1 - α))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hev : ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ |C| * x ^ (-(1 - α)) ≤ c := by
    refine (eventually_ge_atTop 1).and ?_
    have := (hdecay.const_mul |C|)
    simp only [mul_zero] at this
    exact (this.eventually (ge_mem_nhds hc))
  filter_upwards [hlog.eventually hev] with t ⟨h1, h2⟩
  set x := Real.log (t + 2)
  have hx0 : 0 < x := by linarith
  have hsplit : x ^ α = x ^ (-(1 - α)) * x := by
    rw [← Real.rpow_add_one hx0.ne']; ring_nf
  calc C * x ^ α ≤ |C| * x ^ α := by
        gcongr; exact le_abs_self C
    _ = (|C| * x ^ (-(1 - α))) * x := by rw [hsplit]; ring
    _ ≤ c * x := by gcongr

/-- The hypotheses of the generic Lindelöf argument (Steps 4–8) for a function `f`:
`M` is a holomorphic logarithm of `g` on `σ > 1/2`, `g` grows at most linearly on
`1/2 ≤ σ ≤ 5`, `M` is bounded on `2 ≤ σ ≤ 5`, `‖f‖ ≤ A exp ‖M‖` away from the real axis, and
`f` on the critical line is controlled by `f` slightly to the right (Step 4). -/
structure LogBounds (f : ℂ → ℂ) : Prop where
  exists_bounds : ∃ (g M : ℂ → ℂ) (A K C₀ C₁ : ℝ), 1 ≤ K ∧
    (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 → ‖g s‖ ≤ K * (|s.im| + 2)) ∧
    DifferentiableOn ℂ M halfPlane ∧ (∀ s ∈ halfPlane, exp (M s) = g s) ∧
    (∀ s : ℂ, 2 ≤ s.re → s.re ≤ 5 → ‖M s‖ ≤ C₀) ∧
    (∀ s ∈ halfPlane, 1 ≤ |s.im| → ‖f s‖ ≤ A * Real.exp ‖M s‖) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ t : ℝ, 1 ≤ t →
      ‖f (1 / 2 + t * I)‖ ≤ C₁ * t ^ (δ / 2) * ‖f ((1 / 2 + δ : ℝ) + t * I)‖)

/-- **Generic Step 8**, for `0 < ε ≤ 1/2`. -/
theorem isBigO_of_logBounds {f : ℂ → ℂ} (hf : LogBounds f) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε ≤ 1 / 2) :
    (fun t : ℝ => ‖f (1 / 2 + t * I)‖) =O[atTop] fun t : ℝ => t ^ ε := by
  obtain ⟨g, M, A, K, C₀, C₁, hK1, hKb, hMd, hexp, hC₀, hfM, hC₁⟩ := hf.exists_bounds
  obtain ⟨C₂, hC₂⟩ := norm_log_le_of_bounds hK1 hKb hMd hexp ⟨C₀, hC₀⟩ (ε / 2) (by positivity)
  set a : ℝ := 1 / 2 + ε / 2 with ha
  have hab : a < 2 := by linarith
  have hsub : {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} ⊆ halfPlane := fun s hs => by
    simp only [halfPlane, Set.mem_ofPred_eq]; linarith [hs.1]
  obtain ⟨C₃, hC₃⟩ := norm_le_log_rpow_of_strip (B := C₀) hab (hMd.mono hsub)
    (fun s h1 h2 => hC₂ s h1 h2) (fun s h => hC₀ s (by linarith) (by linarith))
  set σ : ℝ := 1 / 2 + ε with hσ
  set α : ℝ := (2 - σ) / (2 - a) with hα
  have hα1 : α < 1 := by
    rw [hα, div_lt_one (by linarith)]; linarith
  have hev := eventually_mul_log_rpow_le (C := C₃) hα1 (show 0 < ε / 4 by positivity)
  refine IsBigO.of_bound (3 * |A| * |C₁|) ?_
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with t hlog ht
  have ht0 : 0 < t := by linarith
  -- the bound at `σ + it`
  have hs : ((σ : ℂ) + t * I) ∈ halfPlane := by
    simp only [halfPlane, Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
    norm_num; linarith
  have him : 1 ≤ |((σ : ℂ) + t * I).im| := by
    simp [abs_of_pos ht0]; linarith
  have hfσ := hfM _ hs him
  have hMσ := hC₃ σ t (by linarith) (by linarith)
  rw [abs_of_pos ht0] at hMσ
  -- `exp (C₃ log(t+2)^α) ≤ (t+2)^{ε/4} ≤ 3 t^{ε/4}`
  have hexp_le : Real.exp ‖M ((σ : ℂ) + t * I)‖ ≤ 3 * t ^ (ε / 4) := by
    have h1 : Real.exp ‖M ((σ : ℂ) + t * I)‖ ≤ Real.exp ((ε / 4) * Real.log (t + 2)) :=
      Real.exp_le_exp.mpr (hMσ.trans hlog)
    have h2 : Real.exp ((ε / 4) * Real.log (t + 2)) = (t + 2) ^ (ε / 4) := by
      rw [Real.rpow_def_of_pos (by linarith), mul_comm]
    have h3 : (t + 2) ^ (ε / 4) ≤ (3 * t) ^ (ε / 4) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    have h4 : (3 * t) ^ (ε / 4) = 3 ^ (ε / 4) * t ^ (ε / 4) :=
      Real.mul_rpow (by norm_num) ht0.le
    have h5 : (3 : ℝ) ^ (ε / 4) ≤ 3 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by linarith)
    calc Real.exp ‖M ((σ : ℂ) + t * I)‖ ≤ (t + 2) ^ (ε / 4) := h1.trans h2.le
      _ ≤ 3 ^ (ε / 4) * t ^ (ε / 4) := h3.trans h4.le
      _ ≤ 3 * t ^ (ε / 4) := by gcongr
  have hhalf := hC₁ ε hε hε' t ht
  have hpow : t ^ (ε / 2) * t ^ (ε / 4) ≤ t ^ ε := by
    rw [← Real.rpow_add ht0]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, abs_of_pos (Real.rpow_pos_of_pos ht0 ε)]
  have hfσ' : ‖f ((1 / 2 + ε : ℝ) + t * I)‖ ≤ |A| * (3 * t ^ (ε / 4)) :=
    hfσ.trans (mul_le_mul (le_abs_self A) hexp_le (Real.exp_pos _).le (abs_nonneg A))
  calc ‖f (1 / 2 + t * I)‖
      ≤ C₁ * t ^ (ε / 2) * ‖f ((1 / 2 + ε : ℝ) + t * I)‖ := hhalf
    _ ≤ |C₁| * t ^ (ε / 2) * ‖f ((1 / 2 + ε : ℝ) + t * I)‖ := by
        gcongr; exact le_abs_self C₁
    _ ≤ |C₁| * t ^ (ε / 2) * (|A| * (3 * t ^ (ε / 4))) := by gcongr
    _ = 3 * |A| * |C₁| * (t ^ (ε / 2) * t ^ (ε / 4)) := by ring
    _ ≤ 3 * |A| * |C₁| * t ^ ε := by gcongr

/-- **Generic Step 8**: `LogBounds f` gives `f(1/2 + it) = O(t^ε)` for every `ε > 0`. -/
theorem isBigO_rpow_of_logBounds {f : ℂ → ℂ} (hf : LogBounds f) {ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => ‖f (1 / 2 + t * I)‖) =O[atTop] fun t : ℝ => t ^ ε := by
  have hε' : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  refine (isBigO_of_logBounds hf hε' (min_le_right _ _)).trans ?_
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _),
    abs_of_nonneg (Real.rpow_nonneg ht0 _), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le ht (min_le_left _ _)

/-- Under RH, `ζ` satisfies the hypotheses of the generic argument. -/
theorem logBounds_riemannZeta (hRH : RiemannHypothesis) : LogBounds riemannZeta := by
  obtain ⟨C₁, hC₁⟩ := norm_zeta_half_le hRH
  obtain ⟨M, hMd, hexp, C₀, hC₀⟩ := exists_log_zetaQ hRH
  obtain ⟨K, hK1, hKb⟩ := norm_zetaQ_le hRH
  exact ⟨zetaQ, M, 3, K, C₀, C₁, hK1, hKb, hMd, hexp, hC₀,
    fun s hs him => norm_riemannZeta_le_exp hexp hs him, hC₁⟩

/-- Lindelöf for `0 < ε ≤ 1/2`. -/
theorem lindelof_small (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖) =O[atTop] fun t : ℝ => t ^ ε :=
  isBigO_of_logBounds (logBounds_riemannZeta hRH) hε hε'

/-- **Littlewood's theorem**: RH implies the Lindelöf hypothesis. -/
theorem lindelof_of_RH (hRH : RiemannHypothesis) : LindelofHypothesis := fun _ hε =>
  isBigO_rpow_of_logBounds (logBounds_riemannZeta hRH) hε

/-- The big-O formulation gives the little-o formulation by applying it at half the exponent. -/
theorem lindelof_littleO_of_bigO (h : LindelofHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) =o[atTop]
        (fun t : ℝ => t ^ ε) := by
  intro ε hε
  apply (h (ε / 2) (half_pos hε)).of_norm_left.trans_isLittleO
  apply (isLittleO_iff_tendsto' ?_).mpr
  · apply (tendsto_rpow_neg_atTop (half_pos hε)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← Real.rpow_sub ht]
    congr 1
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht hz
    exact ((Real.rpow_pos_of_pos ht ε).ne' hz).elim

end Lindelof
