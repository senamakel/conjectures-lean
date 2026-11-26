import Cramer.Sharp.Majorant

/-!
# A centred bound for the second difference `D_ρ`

For `ρ = 1/2 + iγ`, `m > 0`, `0 < h`, `ε = h/m ≤ 1/2`:

`‖g(m+h) − 2g(m) + g(m−h)‖ ≤ m^{3/2} (4 sin²(γε/2) + 2(w + w²)) / γ²`,

`w = (3/2) ε/(1−ε) + |γ| (ε²/2 + ε³/(1−ε))`, provided `w ≤ 1`.

Writing `(1 ± ε)^{ρ+1} = e^{±iγε} e^{w±}` with `w± = (ρ+1) log(1±ε) ∓ iγε`, the bracket
`(1+ε)^{ρ+1} − 2 + (1−ε)^{ρ+1}` is `−4 sin²(γε/2)` plus `e^{iγε}(e^{w+} − 1) + e^{−iγε}(e^{w−} − 1)`.
Unlike `Cramer.Sharp.SecondDiff` (which compares with the left endpoint) the error here is
`O(ε/x)` relative to the main term in `x = γh/(2m)`, not `O(εx)`: the chirp `e^{−iγε²/2}` is
common to both ends and only costs `|γ|ε²`.
-/

namespace Cramer

open Complex

/-- `|log(1+e)| ≤ |e|/(1−|e|)` and `|log(1+e) − e| ≤ e²/2 + |e|³/(1−|e|)` for `|e| < 1`. -/
lemma log_one_add_bounds {e : ℝ} (he : |e| < 1) :
    |Real.log (1 + e)| ≤ |e| / (1 - |e|) ∧
      |Real.log (1 + e) - e| ≤ e ^ 2 / 2 + |e| ^ 3 / (1 - |e|) := by
  have he' : |(-e)| < 1 := by rwa [abs_neg]
  have h0 := Real.abs_log_sub_add_sum_range_le he' 0
  have h2 := Real.abs_log_sub_add_sum_range_le he' 2
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, abs_neg, sub_neg_eq_add, pow_one] at h0
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, abs_neg,
    sub_neg_eq_add] at h2
  refine ⟨by rw [add_comm]; simpa [add_comm] using h0, ?_⟩
  have e1 : Real.log (1 + e) - e = (0 + (-e) ^ (0 + 1) / (0 + 1) + (-e) ^ (1 + 1) / (1 + 1)
      + Real.log (e + 1)) - e ^ 2 / 2 := by
    rw [add_comm e 1]; push_cast; ring
  rw [e1]
  have : |e ^ 2 / 2| = e ^ 2 / 2 := abs_of_nonneg (by positivity)
  calc _ ≤ |0 + (-e) ^ (0 + 1) / (0 + 1) + (-e) ^ (1 + 1) / (1 + 1) + Real.log (e + 1)|
        + |e ^ 2 / 2| := abs_sub _ _
    _ ≤ |e| ^ (2 + 1) / (1 - |e|) + e ^ 2 / 2 := by
        rw [this]; gcongr; simpa [add_comm] using h2
    _ = _ := by ring

/-- `‖e^w − 1‖ ≤ ‖w‖ + ‖w‖²` for `‖w‖ ≤ 1`. -/
lemma norm_exp_sub_one_le_add_sq {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖exp w - 1‖ ≤ ‖w‖ + ‖w‖ ^ 2 := by
  have := Complex.norm_exp_sub_one_sub_id_le hw
  calc ‖exp w - 1‖ = ‖(exp w - 1 - w) + w‖ := by ring_nf
    _ ≤ ‖exp w - 1 - w‖ + ‖w‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The error of one end: `‖(1+e)^{ρ+1} − e^{iγe}‖ ≤ W + W²` whenever
`(3/2)|log(1+e)| + |γ||log(1+e) − e| ≤ W ≤ 1`. -/
lemma norm_one_add_cpow_sub_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) {e W : ℝ} (he : -1 < e)
    (hW : 3 / 2 * |Real.log (1 + e)| + |ρ.im| * |Real.log (1 + e) - e| ≤ W) (hW1 : W ≤ 1) :
    ‖(((1 + e : ℝ)) : ℂ) ^ (ρ + 1) - exp (I * ((ρ.im * e : ℝ) : ℂ))‖ ≤ W + W ^ 2 := by
  have hpos : (0 : ℝ) < 1 + e := by linarith
  have hne : (((1 + e : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  set ℓ := Real.log (1 + e)
  set γ := ρ.im
  set w : ℂ := ((3 / 2 * ℓ : ℝ) : ℂ) + I * ((γ * (ℓ - e) : ℝ) : ℂ)
  have hρ' : ρ = (1 / 2 : ℂ) + I * (γ : ℂ) := by apply Complex.ext <;> simp [hρ, γ]
  have hsplit : (((1 + e : ℝ)) : ℂ) ^ (ρ + 1) = exp (I * ((γ * e : ℝ) : ℂ)) * exp w := by
    rw [cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le, ← Complex.exp_add, hρ']
    congr 1
    simp only [w, ℓ]
    push_cast; ring
  rw [hsplit, show exp (I * ((γ * e : ℝ) : ℂ)) * exp w - exp (I * ((γ * e : ℝ) : ℂ))
      = exp (I * ((γ * e : ℝ) : ℂ)) * (exp w - 1) by ring, norm_mul,
    Complex.norm_exp_I_mul_ofReal, one_mul]
  have hwn : ‖w‖ ≤ W := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_mul]
    have : |(3 / 2 : ℝ)| = 3 / 2 := by norm_num
    linarith
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  refine (norm_exp_sub_one_le_add_sq (hwn.trans hW1)).trans ?_
  nlinarith

/-- The centred error parameter. -/
noncomputable def wCenter (ε γ : ℝ) : ℝ := 3 / 2 * (ε / (1 - ε)) + |γ| * (ε ^ 2 / 2 + ε ^ 3 / (1 - ε))

/-- **The centred bound.** -/
theorem norm_second_diff_center {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hγ : ρ.im ≠ 0) {m h : ℝ}
    (hm : 0 < m) (hh : 0 < h) (hε : h / m ≤ 1 / 2) (hw : wCenter (h / m) ρ.im ≤ 1) :
    ‖gρ ρ (m + h) - 2 * gρ ρ m + gρ ρ (m - h)‖
      ≤ m ^ (3 / 2 : ℝ) * (4 * Real.sin (ρ.im * (h / m) / 2) ^ 2
          + 2 * (wCenter (h / m) ρ.im + wCenter (h / m) ρ.im ^ 2)) / ρ.im ^ 2 := by
  set ε := h / m with hεdef
  set γ := ρ.im with hγdef
  set W := wCenter ε γ
  have hε0 : 0 < ε := div_pos hh hm
  have hε1 : ε < 1 := by linarith
  have hab : |ε| < 1 := by rw [abs_of_pos hε0]; exact hε1
  have hab' : |(-ε)| < 1 := by rwa [abs_neg]
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ; norm_num at hρ
  have hρ1 : ρ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hρ] at this; norm_num at this
  -- the two ends
  have hW : ∀ e : ℝ, |e| = ε → 3 / 2 * |Real.log (1 + e)| + |γ| * |Real.log (1 + e) - e| ≤ W := by
    intro e he
    have hb := log_one_add_bounds (e := e) (by rw [he]; exact hε1)
    rw [he] at hb
    have he2 : e ^ 2 = ε ^ 2 := by rw [← sq_abs, he]
    rw [he2] at hb
    simp only [W, wCenter]
    have := abs_nonneg γ
    have h1 : 3 / 2 * |Real.log (1 + e)| ≤ 3 / 2 * (ε / (1 - ε)) := by linarith [hb.1]
    have h2 : |γ| * |Real.log (1 + e) - e| ≤ |γ| * (ε ^ 2 / 2 + ε ^ 3 / (1 - ε)) :=
      mul_le_mul_of_nonneg_left hb.2 this
    linarith
  have hp := norm_one_add_cpow_sub_le hρ (e := ε) (by linarith) (hW ε (abs_of_pos hε0)) hw
  have hn := norm_one_add_cpow_sub_le hρ (e := -ε) (by linarith)
    (hW (-ε) (by rw [abs_neg, abs_of_pos hε0])) hw
  -- factor out `m^{ρ+1}`
  have hfac : ∀ e : ℝ, -1 < e → (((m * (1 + e) : ℝ)) : ℂ) ^ (ρ + 1)
      = ((m : ℝ) : ℂ) ^ (ρ + 1) * (((1 + e : ℝ)) : ℂ) ^ (ρ + 1) := by
    intro e he
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hm.le (by linarith)]
  have e1 : m + h = m * (1 + ε) := by rw [hεdef]; field_simp
  have e2 : m - h = m * (1 + -ε) := by rw [hεdef]; field_simp; ring
  have e3 : m = m * (1 + 0) := by ring
  set P := (((1 + ε : ℝ)) : ℂ) ^ (ρ + 1)
  set Q := (((1 + -ε : ℝ)) : ℂ) ^ (ρ + 1)
  have hD : gρ ρ (m + h) - 2 * gρ ρ m + gρ ρ (m - h)
      = ((m : ℝ) : ℂ) ^ (ρ + 1) * (P - 2 + Q) / (ρ * (ρ + 1)) := by
    unfold gρ
    rw [e1, e2, hfac ε (by linarith), hfac (-ε) (by linarith)]
    field_simp
    ring
  -- the main term
  set E := exp (I * ((γ * ε : ℝ) : ℂ))
  set E' := exp (I * ((γ * -ε : ℝ) : ℂ))
  have hmain : ‖E - 2 + E'‖ = 4 * Real.sin (γ * ε / 2) ^ 2 := by
    have hc : E - 2 + E' = ((-(4 * Real.sin (γ * ε / 2) ^ 2) : ℝ) : ℂ) := by
      have h2 : E + E' = 2 * Complex.cos ((γ * ε : ℝ) : ℂ) := by
        simp only [E, E', Complex.cos]
        push_cast
        ring_nf
      have hcos : Real.cos (γ * ε) = 1 - 2 * Real.sin (γ * ε / 2) ^ 2 := by
        rw [show γ * ε = 2 * (γ * ε / 2) by ring, Real.cos_two_mul, Real.cos_sq']
        ring_nf
      rw [show E - 2 + E' = (E + E') - 2 by ring, h2, ← Complex.ofReal_cos, hcos]
      push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  have hbr : ‖P - 2 + Q‖ ≤ 4 * Real.sin (γ * ε / 2) ^ 2 + 2 * (W + W ^ 2) := by
    have e : P - 2 + Q = (E - 2 + E') + (P - E) + (Q - E') := by ring
    rw [e]
    have h1 := norm_add_le (E - 2 + E' + (P - E)) (Q - E')
    have h2 := norm_add_le (E - 2 + E') (P - E)
    have hQ : ‖Q - E'‖ ≤ W + W ^ 2 := hn
    have hP : ‖P - E‖ ≤ W + W ^ 2 := hp
    linarith
  have hmn : ‖((m : ℝ) : ℂ) ^ (ρ + 1)‖ = m ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hm]
    simp [hρ]; norm_num
  have hden : γ ^ 2 ≤ ‖ρ * (ρ + 1)‖ := im_sq_le_norm_mul ρ
  have hγ2 : 0 < γ ^ 2 := by positivity
  rw [hD, norm_div, norm_mul, hmn]
  have hnum : 0 ≤ m ^ (3 / 2 : ℝ) * ‖P - 2 + Q‖ := by positivity
  calc m ^ (3 / 2 : ℝ) * ‖P - 2 + Q‖ / ‖ρ * (ρ + 1)‖
      ≤ m ^ (3 / 2 : ℝ) * ‖P - 2 + Q‖ / γ ^ 2 := div_le_div_of_nonneg_left hnum hγ2 hden
    _ ≤ m ^ (3 / 2 : ℝ) * (4 * Real.sin (γ * ε / 2) ^ 2 + 2 * (W + W ^ 2)) / γ ^ 2 := by
        gcongr

end Cramer
