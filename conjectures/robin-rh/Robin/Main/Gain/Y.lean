import Robin.Main.Gain.Basic

/-! # The splitting point `Y` with `Y² log Y = 1/ε` -/

namespace Robin.Gain

open Real

theorem exp30_ge {x : ℝ} (hx : Real.exp 30 ≤ x) : 10 ^ 12 ≤ x := by
  have h1 : (2.7182818283 : ℝ) ^ 30 ≤ Real.exp 1 ^ 30 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 30
  rw [Real.exp_one_pow] at h1
  have h2 : (10 : ℝ) ^ 12 ≤ (2.7182818283 : ℝ) ^ 30 := by norm_num
  have h3 : Real.exp ((30 : ℕ) : ℝ) = Real.exp 30 := by norm_num
  linarith

theorem log_one_add_inv_bounds {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (1 + 1 / x) ∧ Real.log (1 + 1 / x) ≤ 1 / x := by
  constructor
  · have h := Real.log_le_sub_one_of_pos (show 0 < x / (x + 1) by positivity)
    have e : 1 + 1 / x = (x / (x + 1))⁻¹ := by field_simp
    rw [e, Real.log_inv]
    have : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
    linarith
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by positivity)
    linarith

theorem exists_Y {x : ℝ} (hx : Real.exp 30 ≤ x) :
    ∃ Y, √x ≤ Y ∧ Y ≤ x ∧ Y ^ 2 * Real.log Y = 1 / epsR x ∧
      Real.log x / 2 ≤ Real.log Y ∧ Real.log Y ≤ (Real.log x + 0.6933) / 2 ∧
      0.7071 ≤ √x / Y := by
  have hx12 := exp30_ge hx
  have hx0 : 0 < x := by linarith
  have hL : 30 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  obtain ⟨hlo1, hlo2⟩ := log_one_add_inv_bounds hx0
  set lo := Real.log (1 + 1 / x) with hlo
  have hlo0 : 0 < lo := lt_of_lt_of_le (by positivity) hlo1
  set L := Real.log x with hLdef
  have heps : 1 / epsR x = L / lo := by
    unfold epsR; rw [← hlo, ← hLdef]; field_simp
  set a := √x with ha
  set b := √(2 * (x + 1)) with hb
  have ha0 : 0 < a := Real.sqrt_pos.2 hx0
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
  have hb2 : b ^ 2 = 2 * (x + 1) := Real.sq_sqrt (by linarith)
  have hloga : Real.log a = L / 2 := Real.log_sqrt hx0.le
  have hlogb : Real.log b = Real.log (2 * (x + 1)) / 2 := Real.log_sqrt (by linarith)
  set f : ℝ → ℝ := fun t => t ^ 2 * Real.log t with hf
  have hfc : ContinuousOn f (Set.Icc a b) := by
    apply ContinuousOn.mul (continuousOn_pow 2)
    exact Real.continuousOn_log.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  have hfa : f a ≤ L / lo := by
    simp only [hf, ha2, hloga]
    rw [le_div_iff₀ hlo0]
    have : lo * x ≤ 1 := by rw [one_div] at hlo2; calc lo * x ≤ x⁻¹ * x := by gcongr
      _ = 1 := inv_mul_cancel₀ hx0.ne'
    nlinarith
  have hfb : L / lo ≤ f b := by
    simp only [hf, hb2, hlogb]
    rw [div_le_iff₀ hlo0]
    have h1 : L ≤ Real.log (2 * (x + 1)) := Real.log_le_log hx0 (by linarith)
    have h2 : 1 ≤ (x + 1) * lo := by
      rw [div_le_iff₀ (by linarith)] at hlo1; linarith
    have h3 : 0 ≤ L := by linarith
    nlinarith
  obtain ⟨Y, ⟨hYa, hYb⟩, hYf⟩ := intermediate_value_Icc hab hfc ⟨hfa, hfb⟩
  have hY0 : 0 < Y := lt_of_lt_of_le ha0 hYa
  have hY2 : Y ^ 2 ≤ 2 * (x + 1) := by rw [← hb2]; gcongr
  refine ⟨Y, hYa, ?_, ?_, ?_, ?_, ?_⟩
  · have : b ≤ x := by
      rw [hb, Real.sqrt_le_left]
      · nlinarith
      · linarith
    linarith
  · rw [heps]; exact hYf
  · rw [← hloga]; exact Real.log_le_log ha0 hYa
  · have h1 : Real.log Y ≤ Real.log b := Real.log_le_log hY0 hYb
    have h2 : Real.log (2 * (x + 1)) = Real.log 2 + (L + lo) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : x + 1 = x * (1 + 1 / x) := by field_simp
      rw [this, Real.log_mul hx0.ne' (by positivity)]
    have h3 : 1 / x ≤ 0.0001 := by
      rw [div_le_iff₀ hx0]; linarith
    have := Real.log_two_lt_d9
    rw [hlogb, h2] at h1
    linarith
  · have hr0 : 0 ≤ √x / Y := by positivity
    have hr2 : (√x / Y) ^ 2 = x / Y ^ 2 := by rw [div_pow, ← ha, ha2]
    have h1 : x / (2 * (x + 1)) ≤ x / Y ^ 2 :=
      div_le_div_of_nonneg_left hx0.le (by positivity) hY2
    have h2 : (0.7071 : ℝ) ^ 2 ≤ x / (2 * (x + 1)) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    nlinarith

end Robin.Gain
