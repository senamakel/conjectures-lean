import Cramer.Shift.Center
import Cramer.Shift.Check

/-!
# Each zero is bounded by the majorant

If every `y ≥ 0` satisfies `CellGood maj y` (the checked cells plus the tail), then for every
`ρ = 1/2 + iγ`, `m > 0` and `0 < h ≤ m/800`,

`‖g(m+h) − 2g(m) + g(m−h)‖ ≤ h² m^{−1/2} · M(γh/(2m))`.

The three envelopes of `Cramer.Shift.Check` come from three bounds for `D_ρ`:
`envT` from the trivial bound `4(m+h)^{3/2}/‖ρ(ρ+1)‖`, `envL` from the centred bound
(`Cramer.Shift.Center`), `envS` from the left-endpoint bound of `Cramer.Sharp.SecondDiff`.
-/

namespace Cramer.Shift

open Real

lemma lor_neg (σ y : ℝ) : lor σ (-y) = lor σ y := by unfold lor; ring_nf

lemma majF_neg (maj : List (ℕ × ℕ × ℕ)) (x : ℝ) : majF maj (-x) = majF maj x := by
  unfold majF
  congr 1
  apply List.map_congr_left
  intro c _
  rw [show -x - (c.2.2 : ℝ) / NN = -(x + (c.2.2 : ℝ) / NN) by ring,
    show -x + (c.2.2 : ℝ) / NN = -(x - (c.2.2 : ℝ) / NN) by ring, lor_neg, lor_neg]
  ring

lemma majF_abs (maj : List (ℕ × ℕ × ℕ)) (x : ℝ) : majF maj |x| = majF maj x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, majF_neg]

lemma Tpoly_pos (y : ℝ) : 0 < Tpoly y := by unfold Tpoly; nlinarith [sq_nonneg (y - 10)]

/-- `rpow` bookkeeping: `h² m^{−1/2} = h²/√m`, `m^{3/2} = m √m`. -/
lemma rpow_neg_half {m : ℝ} (hm : 0 < m) : m ^ (-(1 / 2 : ℝ)) = 1 / √m := by
  rw [Real.rpow_neg hm.le, Real.sqrt_eq_rpow, inv_eq_one_div]

lemma rpow_three_halves {m : ℝ} (hm : 0 < m) : m ^ (3 / 2 : ℝ) = m * √m := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm, Real.rpow_one, Real.sqrt_eq_rpow]

lemma wCenter_le {ε γ y : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 800) (hy : |γ| = 2 * y / ε) :
    wCenter ε γ ≤ wbx y := by
  have hy0 : 0 ≤ y := by
    by_contra hneg
    push_neg at hneg
    have : 2 * y / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε0
    linarith [abs_nonneg γ, hy]
  unfold wCenter wbx
  rw [hy]
  have h1 : ε / (1 - ε) ≤ 1 / 799 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have e : 2 * y / ε * (ε ^ 2 / 2 + ε ^ 3 / (1 - ε)) = y * ε + 2 * y * (ε * (ε / (1 - ε))) := by
    field_simp
  rw [e]
  have h2 : ε * (ε / (1 - ε)) ≤ 1 / 800 * (1 / 799) :=
    mul_le_mul hε h1 (div_nonneg hε0.le (by linarith)) (by norm_num)
  have : y * ε ≤ y * (1 / 800) := mul_le_mul_of_nonneg_left hε hy0
  have : 2 * y * (ε * (ε / (1 - ε))) ≤ 2 * y * (1 / 800 * (1 / 799)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have : 3 / 2 * (ε / (1 - ε)) ≤ 3 / 2 * (1 / 799) := by linarith
  linarith

/-- **The per-zero majorant bound.** -/
theorem norm_D_le_majF {maj : List (ℕ × ℕ × ℕ)} (hgood : ∀ y : ℝ, 0 ≤ y → CellGood maj y)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2) {m h : ℝ} (hm : 0 < m) (hh : 0 < h) (hε : h / m ≤ 1 / 800) :
    ‖gρ ρ (m + h) - 2 * gρ ρ m + gρ ρ (m - h)‖
      ≤ h ^ 2 * m ^ (-(1 / 2 : ℝ)) * majF maj (ρ.im * h / (2 * m)) := by
  set γ := ρ.im with hγdef
  set x := γ * h / (2 * m) with hx
  set y := |x| with hydef
  set ε := h / m with hεdef
  have hε0 : 0 < ε := div_pos hh hm
  have hhm : h ≤ m / 800 := by rw [hεdef, div_le_iff₀ hm] at hε; linarith
  set a := m - h with hadef
  have ha : 0 < a := by linarith
  have hsm : 0 < √m := Real.sqrt_pos.mpr hm
  have hsa : 0 < √a := Real.sqrt_pos.mpr ha
  have hA : h ^ 2 * m ^ (-(1 / 2 : ℝ)) = h ^ 2 / √m := by rw [rpow_neg_half hm]; ring
  rw [hA, ← majF_abs, ← hydef]
  have hy0 : 0 ≤ y := abs_nonneg x
  -- `γ² = (2 m y / h)²`
  have hγy : |γ| = 2 * m * y / h := by
    rw [hydef, hx, abs_div, abs_mul, abs_of_pos hh, abs_of_pos (by positivity : (0 : ℝ) < 2 * m)]
    field_simp
  have hγ2 : γ ^ 2 = 4 * m ^ 2 * y ^ 2 / h ^ 2 := by
    rw [← sq_abs, hγy]; field_simp; ring
  have ea : a + h = m := by rw [hadef]; ring
  have eb : a + 2 * h = m + h := by rw [hadef]; ring
  -- `√m / √a ≤ 800/799`
  have hma : m / a ≤ 800 / 799 := by
    rw [div_le_div_iff₀ ha (by norm_num)]; rw [hadef]; linarith
  have hsqa : √m / √a ≤ 800 / 799 := by
    rw [← Real.sqrt_div hm.le]
    have h1 : 1 ≤ m / a := by rw [le_div_iff₀ ha]; linarith
    have : √(m / a) ≤ m / a := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  have hAa : h ^ 2 * a ^ (-(1 / 2 : ℝ)) ≤ 800 / 799 * (h ^ 2 / √m) := by
    rw [rpow_neg_half ha]
    have : h ^ 2 * (1 / √a) = (h ^ 2 / √m) * (√m / √a) := by field_simp
    rw [this, mul_comm (800 / 799 : ℝ)]
    exact mul_le_mul_of_nonneg_left hsqa (by positivity)
  rcases hgood y hy0 with ⟨hyp, hT⟩ | ⟨hyp, hw, hL⟩ | ⟨-, hy1, hS⟩
  · -- the trivial bound
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hT (by positivity))
    have hγ0 : 0 < γ ^ 2 := by rw [hγ2]; positivity
    have h1 := norm_second_diff_gρ_le' hρ ha hh.le
    rw [ea, eb] at h1
    refine h1.trans ?_
    have hden : γ ^ 2 ≤ ‖ρ * (ρ + 1)‖ := im_sq_le_norm_mul ρ
    set b := m + h
    have hb : 0 < b := by positivity
    have hbm : b ≤ 801 / 800 * m := by simp only [b]; linarith
    have hsb : √b ≤ 1601 / 1600 * √m := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hm.le]; nlinarith
    rw [rpow_three_halves hb]
    calc 4 * (b * √b) / ‖ρ * (ρ + 1)‖ ≤ 4 * (b * √b) / γ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hγ0 hden
      _ ≤ h ^ 2 / √m * envT y := by
          unfold envT
          rw [hγ2]
          have hy2 : 0 < y ^ 2 := by positivity
          rw [div_le_iff₀ (by positivity)]
          have hbb : b * √b ≤ 801 / 800 * m * (1601 / 1600 * √m) :=
            mul_le_mul hbm hsb (Real.sqrt_nonneg _) (by positivity)
          have hsq : √m * √m = m := Real.mul_self_sqrt hm.le
          have e : h ^ 2 / √m * (802 / (800 * y ^ 2)) * (4 * m ^ 2 * y ^ 2 / h ^ 2)
              = 4 * (802 / 800) * m * √m := by
            field_simp
            simp only [Real.sq_sqrt hm.le]
          rw [e]
          nlinarith [Real.sqrt_nonneg m]
  · -- the centred bound
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hL (by positivity))
    have hγ0 : γ ≠ 0 := by
      intro h0; rw [h0] at hγy; simp at hγy
      have : 0 < 2 * m * y / h := by positivity
      linarith
    have hwc : wCenter ε γ ≤ wbx y :=
      wCenter_le hε0 hε (by rw [hγy, hεdef]; field_simp)
    have hwc0 : 0 ≤ wCenter ε γ := by
      unfold wCenter
      have : 0 < 1 - ε := by linarith
      positivity
    have key := norm_second_diff_center hρ hγ0 hm hh (by linarith) (hwc.trans hw)
    rw [← hadef] at key
    refine key.trans ?_
    have hsin : 4 * Real.sin (γ * ε / 2) ^ 2 = 2 * (1 - Real.cos (2 * y)) := by
      have e1 : γ * ε / 2 = x := by rw [hx, hεdef]; ring
      rw [e1]
      have e2 : Real.cos (2 * y) = Real.cos (2 * x) := by
        rw [hydef]
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
        · rw [abs_of_nonpos h0, mul_neg, Real.cos_neg]
      rw [e2, Real.cos_two_mul, Real.cos_sq']
      ring
    rw [hsin]
    have hW2 : wCenter ε γ + wCenter ε γ ^ 2 ≤ wbx y + wbx y ^ 2 := by
      have := pow_le_pow_left₀ hwc0 hwc 2; linarith
    have hyp2 : 0 < y ^ 2 := by positivity
    rw [rpow_three_halves hm, hγ2]
    unfold envL
    have hc : 0 ≤ 1 - Real.cos (2 * y) := by linarith [Real.cos_le_one (2 * y)]
    calc m * √m * (2 * (1 - Real.cos (2 * y)) + 2 * (wCenter ε γ + wCenter ε γ ^ 2))
          / (4 * m ^ 2 * y ^ 2 / h ^ 2)
        ≤ m * √m * (2 * (1 - Real.cos (2 * y)) + 2 * (wbx y + wbx y ^ 2))
          / (4 * m ^ 2 * y ^ 2 / h ^ 2) := by gcongr
      _ = h ^ 2 / √m * ((1 - Real.cos (2 * y) + wbx y + wbx y ^ 2) / (2 * y ^ 2)) := by
          have hsq : √m * √m = m := Real.mul_self_sqrt hm.le
          field_simp
          simp only [Real.sq_sqrt hm.le]
          ring
  · -- the left-endpoint bound
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hS (by positivity))
    have hT0 := Tpoly_pos (y ^ 2)
    have herr0 : 0 ≤ (799 + 3200 * y) / 638401 := by positivity
    rcases eq_or_ne γ 0 with hγ0 | hγ0
    · have h1 := norm_second_diff_gρ_le hρ ha hh.le
      rw [ea, eb] at h1
      refine h1.trans (hAa.trans ?_)
      have hy00 : y = 0 := by rw [hydef, hx, hγ0]; simp
      unfold envS
      rw [hy00]
      unfold Tpoly
      norm_num
      have : 0 ≤ h ^ 2 / √m := by positivity
      nlinarith
    · have h1 := norm_second_diff_gρ_sharp hρ hγ0 ha hh
      rw [ea, eb] at h1
      refine h1.trans ?_
      set xa := γ * h / (2 * a) with hxa
      have hxa_abs : |xa| = y * (m / a) := by
        have e1 : xa = x * (m / a) := by rw [hxa, hx]; field_simp
        rw [e1, abs_mul, abs_of_pos (div_pos hm ha), ← hydef]
      have hma1 : 1 ≤ m / a := by rw [le_div_iff₀ ha]; linarith
      have hxa_le : |xa| ≤ 800 / 799 * y := by
        rw [hxa_abs, mul_comm]; exact mul_le_mul_of_nonneg_right hma hy0
      have hxa_ge : y ≤ |xa| := by
        rw [hxa_abs]; exact le_mul_of_one_le_right hy0 hma1
      have hxa2 : xa ^ 2 ≤ 2 := by
        have h1 : |xa| ≤ 800 / 799 := by
          have : 800 / 799 * y ≤ 800 / 799 := by linarith
          linarith
        have h2 : |xa| ^ 2 ≤ (800 / 799) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rw [← sq_abs]; norm_num at h2 ⊢; linarith
      have hxa0 : xa ≠ 0 := by
        rw [hxa]; exact div_ne_zero (mul_ne_zero hγ0 hh.ne') (by linarith)
      have hs := sin_sq_div_sq_le hxa0 hxa2
      have hyx : y ^ 2 ≤ xa ^ 2 := by rw [← sq_abs xa]; exact pow_le_pow_left₀ hy0 hxa_ge 2
      have hTT : Tpoly (xa ^ 2) ≤ Tpoly (y ^ 2) := Tpoly_anti (by positivity) hyx (by linarith)
      have hTT2 : Tpoly (xa ^ 2) ^ 2 ≤ Tpoly (y ^ 2) ^ 2 :=
        pow_le_pow_left₀ (Tpoly_pos _).le hTT 2
      have hha : h / a ≤ 1 / 799 := by
        rw [div_le_div_iff₀ ha (by norm_num)]; rw [hadef]; linarith
      have hha0 : 0 ≤ h / a := by positivity
      have herr : h / a + 2 * |γ| * h ^ 2 / a ^ 2 ≤ (799 + 3200 * y) / 638401 := by
        have e : 2 * |γ| * h ^ 2 / a ^ 2 = 4 * |xa| * (h / a) := by
          rw [hxa, abs_div, abs_mul, abs_of_pos hh, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)]
          field_simp; ring
        rw [e]
        have : 4 * |xa| * (h / a) ≤ 4 * (800 / 799 * y) * (1 / 799) :=
          mul_le_mul (by linarith) hha hha0 (by positivity)
        have : (799 + 3200 * y) / 638401 = 1 / 799 + 4 * (800 / 799 * y) * (1 / 799) := by ring
        linarith
      have hbr : Real.sin xa ^ 2 / xa ^ 2 + h / a + 2 * |γ| * h ^ 2 / a ^ 2
          ≤ Tpoly (y ^ 2) ^ 2 + (799 + 3200 * y) / 638401 := by linarith
      have hbr0 : 0 ≤ Real.sin xa ^ 2 / xa ^ 2 + h / a + 2 * |γ| * h ^ 2 / a ^ 2 := by positivity
      calc h ^ 2 * a ^ (-(1 / 2 : ℝ)) * (Real.sin xa ^ 2 / xa ^ 2 + h / a + 2 * |γ| * h ^ 2 / a ^ 2)
          ≤ 800 / 799 * (h ^ 2 / √m) * (Tpoly (y ^ 2) ^ 2 + (799 + 3200 * y) / 638401) :=
            mul_le_mul hAa hbr hbr0 (by positivity)
        _ = h ^ 2 / √m * envS y := by unfold envS; ring

end Cramer.Shift
