import Robin.Mertens.Identity

/-!
# Mertens' third theorem as an identity, with the tail of `K` bounded

If `θ(t) − t = O(t^{3/4})`, then for `x ≥ 2`
`Σ_{p≤x} c_p = γ + log log x + (θ(x) − x)/(x log x) − ∫_x^∞ (θ(t) − t) w(t) dt − T(x)`,
where `T(x) = Σ_{p>x}(c_p − 1/p) ∈ [0, 4/x]`. robin-rh's `mertens_RH` keeps only the upper
bound (it drops `T`); Nicolas' inequality needs the lower bound, hence the identity here. The
proof reuses robin-rh's Abel summation (`D1_eq`) and `mertens_const_eq_gamma`.
-/

namespace Nicolas

open Filter Topology Real Chebyshev MeasureTheory Set Robin

/-- `T(x) = Σ_{p>x}(c_p − 1/p) = K − Σ_{p≤x}(c_p − 1/p)`. -/
noncomputable def tailK (x : ℝ) : ℝ := ∑' n, aK n - ∑ n ∈ Finset.range (⌊x⌋₊ + 1), aK n

theorem mertens_eq (hθ : ∃ C, ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4))
    {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun t => (θ t - t) * wM t) (Set.Ioi x) ∧
    primeSum cp x = Real.eulerMascheroniConstant + Real.log (Real.log x)
      + (θ x - x) / (x * Real.log x) - (∫ t in Set.Ioi x, (θ t - t) * wM t) - tailK x := by
  obtain ⟨C, hC⟩ := hθ
  refine ⟨integrableOn_err hC hx, ?_⟩
  have hlim : Tendsto (fun X => primeSum cp X - Real.log (Real.log X)) atTop
      (𝓝 (D1 x + ∑' n, aK n)) := by
    have h1 := ((tendsto_const_nhds (x := D1 x)).add tendsto_primeSum_aK).add
      (tendsto_err_div hC) |>.sub (tendsto_integral_err hC)
    rw [add_zero, sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop x] with X hX
    rw [← D1_eq hC hx hX]
    unfold D1; rw [primeSum_cp_split]; ring
  have hγ := mertens_const_eq_gamma hlim
  have hx' : primeSum cp x = D1 x + Real.log (Real.log x) + (θ x - x) / (x * Real.log x)
      - (∫ t in Ioi x, (θ t - t) * wM t) + primeSum (fun p => cp p - 1 / (p : ℝ)) x := by
    unfold D1; rw [primeSum_cp_split]; ring
  rw [primeSum_aK] at hx'
  unfold tailK
  linarith

lemma tailK_eq (x : ℝ) : tailK x = ∑' n, aK (n + (⌊x⌋₊ + 1)) := by
  unfold tailK
  rw [← summable_aK.sum_add_tsum_nat_add (⌊x⌋₊ + 1)]
  ring

/-- `0 ≤ T(x) ≤ 4/(⌊x⌋ + 1)`. -/
theorem tailK_le (x : ℝ) : 0 ≤ tailK x ∧ tailK x ≤ 4 / ((⌊x⌋₊ : ℝ) + 1) := by
  rw [tailK_eq]
  set N := ⌊x⌋₊
  refine ⟨tsum_nonneg fun n => aK_nonneg _, ?_⟩
  refine Real.tsum_le_of_sum_range_le (fun n => aK_nonneg _) fun n => ?_
  calc ∑ i ∈ Finset.range n, aK (i + (N + 1))
      ≤ ∑ i ∈ Finset.range n, 2 * (((i + (N + 1) : ℕ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun i _ => by
          have := aK_le (i + (N + 1)); simpa [one_div] using this
    _ = 2 * ∑ j ∈ Finset.Ioo N (N + 1 + n), ((j : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.mul_sum, ← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range]
        congr 1
        rw [show N + 1 + n - (N + 1) = n by omega]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 2; push_cast; ring
    _ ≤ 2 * (2 / ((N : ℝ) + 1)) := by
        gcongr; exact sum_Ioo_inv_sq_le _ _
    _ = 4 / ((N : ℝ) + 1) := by ring

theorem tailK_le_div {x : ℝ} (hx : 0 < x) : tailK x ≤ 4 / x := by
  refine (tailK_le x).2.trans ?_
  apply div_le_div_of_nonneg_left (by norm_num) hx
  exact (Nat.lt_floor_add_one x).le

/-- `θ(3) = log 6 > 1`. -/
lemma one_lt_theta {x : ℝ} (hx : 3 ≤ x) : 1 < θ x := by
  have h3 : θ 3 = Real.log 6 := by
    rw [theta_eq_log_primorial]
    norm_num [Nat.floor_ofNat]
    rfl
  have h6 : 1 < Real.log 6 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have := theta_mono hx
  linarith

/-- `log log θ(x) ≤ log log x + (θ(x) − x)/(x log x)` for `x ≥ 3`. -/
theorem loglog_theta_le {x : ℝ} (hx : 3 ≤ x) :
    Real.log (Real.log (θ x)) ≤ Real.log (Real.log x) + (θ x - x) / (x * Real.log x) := by
  have hθ1 := one_lt_theta hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hlθ : 0 < Real.log (θ x) := Real.log_pos hθ1
  have h1 : Real.log (Real.log (θ x)) - Real.log (Real.log x)
      ≤ Real.log (θ x) / Real.log x - 1 := by
    rw [← Real.log_div hlθ.ne' hL.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hlθ hL)
  have h2 : Real.log (θ x) - Real.log x ≤ θ x / x - 1 := by
    rw [← Real.log_div (by linarith) hx0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hx0)
  have e1 : Real.log (θ x) / Real.log x - 1 = (Real.log (θ x) - Real.log x) / Real.log x := by
    field_simp
  have e2 : (θ x - x) / (x * Real.log x) = (θ x / x - 1) / Real.log x := by
    field_simp
  rw [e1] at h1
  rw [e2]
  have := div_le_div_of_nonneg_right h2 hL.le
  linarith

end Nicolas
