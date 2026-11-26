import Erdos233.Gaps
import Erdos233.Statement2

/-!
# Selberg 1943: primes in almost all short intervals under RH

The argument of `Erdos233/Gaps.lean`, read the other way round. Fix `X`, and `δ` with
`16 log²(5X)/log 2 ≤ δX` and `δ ≤ 1/8`.

1. `window_forces`: if `(y, y(1+2δ))` contains no prime, with `X ≤ y ≤ 4X`, then
   `y^{3/2} |F δ (log y)| ≥ (δX)²/2` (the `D2_le` / `D2_bound` step of `gap_sum`).
2. `large_wave_measure`: by Chebyshev's inequality and `mean_square`, the set of `y ∈ [X, 2X]`
   with `y^{3/2}|F δ (log y)| ≥ t` has measure `≤ C X⁴ δ³ log²(2/δ) / t²`.
3. `primeless_measure_le`: with `δ = H/(4X)` and `t = (H/4)²/2` the `y ∈ [X, 2X]` with no prime in
   `(y, y + H]` have measure `≤ C X log² X / H`, for `64 log²(5X)/log 2 ≤ H ≤ X/2`.
4. `selberg_almost_all_of_RH`: `SelbergAlmostAllStatement`, taking `H = K log² X` with `K → ∞`.
5. `smoothed_asymptotic_of_RH`: the smoothed count `D2 δ y` is `(1 + o(1)) δ²y²` for almost all
   `y ∈ [X, 2X]`, with `δ = H(X)/X` and `H / log² → ∞` (a weaker, smoothed form of
   `SelbergAsymptoticStatement`, which is proved in `Erdos233/Selberg/Asymptotic.lean`).
6. `large_gaps_of_RH`: `Σ_{X ≤ p_n < 2X, d_n ≥ h} d_n ≪ X log² X / h` (`gap_sum`, restated).
-/

namespace Erdos233

open Complex Erdos985.Analytic MeasureTheory intervalIntegral Chebyshev ArithmeticFunction
  Filter Topology

/-- A prime-free window `(y, y(1+2δ))` forces the zero contribution to be large. -/
lemma window_forces (hRH : RiemannHypothesis) {X δ y : ℝ} (hX5 : 5 ≤ X)
    (hsqrt : 16 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ Real.sqrt X)
    (hδ0 : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hhL : 16 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ δ * X)
    (hyX : X ≤ y) (hy4 : y ≤ 4 * X)
    (hnp : ∀ m : ℕ, y < m → (m : ℝ) < y * (1 + 2 * δ) → ¬ m.Prime) :
    (δ * X) ^ 2 / 2 ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hX0 : 0 < X := by linarith
  set Lx := Real.log (5 * X) ^ 2 / Real.log 2 with hLx
  have hl5 : 1 ≤ Real.log (5 * X) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hLx1 : 1 ≤ Lx := by
    rw [hLx, le_div_iff₀ hl2]; nlinarith
  set h := δ * X with hhdef
  have hh16 : 16 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  have hy0 : 0 < y := by linarith
  have hHh : h ≤ δ * y := mul_le_mul_of_nonneg_left hyX hδ0.le
  have hB5 : y * (1 + 2 * δ) ≤ 5 * X := by nlinarith
  have hyB : y ≤ y * (1 + 2 * δ) := by nlinarith
  have hD2 := D2_le hy0 hδ0 hnp
  have hwin := psi_sub_theta_window (A := y) (B := y * (1 + 2 * δ)) (by linarith) hyB
  have hDb := D2_bound hRH hδ0 (show 1 ≤ y by linarith)
  have hBy : y * (1 + 2 * δ) - y = 2 * (δ * y) := by ring
  set B := y * (1 + 2 * δ) with hBdef
  set H := δ * y with hHdef
  clear_value H B
  have hlB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hlB5 : Real.log B ≤ Real.log (5 * X) := Real.log_le_log (by linarith) hB5
  have hLw : Real.log B / Real.log 2 * Real.log B ≤ Lx := by
    rw [hLx, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2, sq]
    exact mul_le_mul hlB5 hlB5 hlB (hlB.trans hlB5)
  have hsy : Real.sqrt X ≤ Real.sqrt y := Real.sqrt_le_sqrt hyX
  have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hT : (B - y) / Real.sqrt y = 2 * H / Real.sqrt y := by rw [hBy]
  set T := 2 * H / Real.sqrt y with hTdef
  have hT0 : 0 ≤ T := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hHT : H * Lx * T ≤ H ^ 2 / 8 := by
    rw [hTdef]
    have : H * Lx * (2 * H / Real.sqrt y) = 2 * Lx * H ^ 2 / Real.sqrt y := by ring
    rw [this, div_le_iff₀ hsy0]
    have hH2 : 0 ≤ H ^ 2 := sq_nonneg H
    have := mul_le_mul_of_nonneg_left (hsqrt.trans hsy) hH2
    linarith
  have hP : (ψ B - θ B) - (ψ y - θ y) ≤ Lx * (T + 1) := by
    rw [← hT]
    refine hwin.trans ?_
    have : 0 ≤ (B - y) / Real.sqrt y + 1 := by
      have : 0 ≤ (B - y) / Real.sqrt y := div_nonneg (by linarith) (Real.sqrt_nonneg _)
      linarith
    exact mul_le_mul_of_nonneg_right hLw this
  have hH0 : 0 < H := by linarith
  have hDle : D2 δ y ≤ H * (Lx * (T + 1)) := hD2.trans (mul_le_mul_of_nonneg_left hP hH0.le)
  have hHL : H * Lx ≤ H ^ 2 / 8 := by
    have := mul_le_mul_of_nonneg_left (show 8 * Lx ≤ H by linarith) hH0.le
    have hsq : H ^ 2 = H * H := sq H
    linarith
  have hab := (abs_le.1 hDb).1
  have hWy : H ^ 2 / 2 ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖ := by
    have e : δ ^ 2 * y ^ 2 = H ^ 2 := by rw [hHdef]; ring
    rw [e] at hab
    have e2 : H * (Lx * (T + 1)) = H * Lx * T + H * Lx := by ring
    have h16 : 16 ≤ H := by linarith
    have h256 : 256 ≤ H ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) h16 2; norm_num at this; linarith
    linarith
  have hh2 : h ^ 2 / 2 ≤ H ^ 2 / 2 := by
    have := pow_le_pow_left₀ hh0.le hHh 2; linarith
  linarith

/-- Chebyshev's inequality for the mean square of `mean_square`. -/
theorem large_wave_measure (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ t : ℝ, 0 < t →
    volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖}
      ≤ C * X ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 / t ^ 2 := by
  obtain ⟨C, hC, hms⟩ := mean_square hRH
  refine ⟨C, hC, fun X hX δ hδ hδ' t ht => ?_⟩
  obtain ⟨hII, hMS⟩ := hms X hX δ hδ hδ'
  set W : ℝ → ℝ := fun y => (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2 with hW
  have hX4 : X ≤ 4 * X := by linarith
  have hint : Integrable W (volume.restrict (Set.Ioc X (4 * X))) := hII.1
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc X (4 * X))] W :=
    ae_of_all _ fun y => by simp only [Pi.zero_apply, hW]; positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn hint (t ^ 2)
  have hI : ∫ y, W y ∂(volume.restrict (Set.Ioc X (4 * X))) = ∫ y in X..4 * X, W y :=
    (integral_of_le hX4).symm
  set E := {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖} with hE
  set A := {y | t ^ 2 ≤ W y} ∩ Set.Ioc X (4 * X) with hA
  have hsub : E ⊆ A ∪ {X} := by
    rintro y ⟨⟨h1, h2⟩, h3⟩
    rcases eq_or_lt_of_le h1 with h | h
    · right; exact h.symm
    · left
      refine ⟨?_, h, by linarith⟩
      show t ^ 2 ≤ (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2
      exact pow_le_pow_left₀ ht.le h3 2
  have hμ : (volume.restrict (Set.Ioc X (4 * X))).real {y | t ^ 2 ≤ W y} = volume.real A := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply' measurableSet_Ioc]
  have hfin : volume (A ∪ {X}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 4 * X)).ne (measure_mono ?_)
    rintro y (⟨-, h1, h2⟩ | h)
    · exact ⟨h1.le, h2⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨le_rfl, hX4⟩
  have hEA : volume.real E ≤ volume.real A := by
    calc volume.real E ≤ volume.real (A ∪ {X}) := measureReal_mono hsub hfin
      _ ≤ volume.real A + volume.real ({X} : Set ℝ) := measureReal_union_le _ _
      _ = volume.real A := by simp [Measure.real]
  rw [le_div_iff₀ (by positivity)]
  calc volume.real E * t ^ 2 ≤ t ^ 2 * volume.real A := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hEA (by positivity)
    _ = t ^ 2 * (volume.restrict (Set.Ioc X (4 * X))).real {y | t ^ 2 ≤ W y} := by rw [hμ]
    _ ≤ ∫ y, W y ∂(volume.restrict (Set.Ioc X (4 * X))) := hmk
    _ = ∫ y in X..4 * X, W y := hI
    _ ≤ _ := hMS

/-- **Selberg's measure bound.** Under RH, for `64 log²(5X)/log 2 ≤ H ≤ X/2`, the `y ∈ [X, 2X]`
with no prime in `(y, y + H]` have measure `≤ C X log² X / H`. -/
theorem primeless_measure_le (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ X : ℝ, X₀ ≤ X → ∀ H : ℝ, 64 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ H → H ≤ X / 2 →
    volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
        ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + H}
      ≤ C * X * Real.log X ^ 2 / H := by
  obtain ⟨C, hC, hW⟩ := large_wave_measure hRH
  obtain ⟨X₁, hX₁⟩ := eventually_log_sq_le_sqrt
  refine ⟨64 * C, max X₁ 5, by positivity, fun X hX H hH hHX => ?_⟩
  have hX5 : 5 ≤ X := le_of_max_le_right hX
  have hX0 : 0 < X := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl5 : 1 ≤ Real.log (5 * X) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hLx1 : 1 ≤ Real.log (5 * X) ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hl2]; nlinarith
  have hH64 : 64 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  set δ := H / (4 * X) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ8 : δ ≤ 1 / 8 := by rw [hδdef, div_le_iff₀ (by positivity)]; linarith
  have hδX : δ * X = H / 4 := by rw [hδdef]; field_simp
  set t := (δ * X) ^ 2 / 2 with htdef
  have ht0 : 0 < t := by positivity
  have hsub : {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + H}
      ⊆ {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖} := by
    rintro y ⟨hy, hnp⟩
    refine ⟨hy, ?_⟩
    refine window_forces hRH hX5 (hX₁ X (le_of_max_le_left hX)) hδ0 hδ8
      (by rw [hδX]; linarith) hy.1 (by linarith [hy.2]) fun m h1 h2 hm => hnp ⟨m, hm, h1, ?_⟩
    have : y * (1 + 2 * δ) ≤ y + H := by
      have : y * δ ≤ 2 * X * δ := mul_le_mul_of_nonneg_right hy.2 hδ0.le
      nlinarith
    linarith
  have hfin : volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      t ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖} ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 2 * X)).ne
      (measure_mono fun y hy => hy.1)
  refine (measureReal_mono hsub hfin).trans ((hW X (by linarith) δ hδ0 (by linarith) t ht0).trans ?_)
  set L := Real.log (2 / δ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hL2 : L ≤ 2 * Real.log X := by
    have : 2 / δ ≤ X ^ 2 := by
      rw [div_le_iff₀ hδ0, hδdef]
      field_simp
      nlinarith
    calc L ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
  have hLsq : L ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  have e : C * X ^ 4 * δ ^ 3 * L ^ 2 / t ^ 2 = 16 * C * X * L ^ 2 / H := by
    rw [htdef, hδX, hδdef]
    field_simp
    ring
  rw [e]
  rw [div_le_div_iff_of_pos_right hH0]
  have := mul_le_mul_of_nonneg_left hLsq (by positivity : (0 : ℝ) ≤ 16 * C * X)
  linarith

/-- **Selberg 1943 (existence form), under RH.** -/
theorem selberg_almost_all_of_RH (hRH : RiemannHypothesis) : SelbergAlmostAllStatement := by
  intro h hh
  obtain ⟨C, X₀, hC, hb⟩ := primeless_measure_le hRH
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := max 512 (2 * C / ε) with hK
  have hK512 : 512 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hKC : C / K ≤ ε / 2 := by
    rw [div_le_iff₀ hK0]
    have := le_max_right 512 (2 * C / ε)
    rw [← hK, div_le_iff₀ hε] at this
    linarith
  -- eventually `h y ≥ K log² y`
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.1 (hh.eventually_ge_atTop K)
  -- eventually `K log² X ≤ X / 2`
  have ho := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show 0 < 1 / (2 * K) by positivity)
  obtain ⟨Y₂, hY₂⟩ := eventually_atTop.1 ho
  refine ⟨max (max X₀ 5) (max Y₁ Y₂), fun X hX => ?_⟩
  have hX5 : 5 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXY₁ : Y₁ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXY₂ : Y₂ ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  have hlX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; have := Real.exp_one_lt_d9; linarith
  set H := K * Real.log X ^ 2 with hHdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hH1 : 64 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ H := by
    have h5 : Real.log (5 * X) ≤ 2 * Real.log X := by
      rw [Real.log_mul (by norm_num) hX0.ne']
      have : Real.log 5 ≤ Real.log X := Real.log_le_log (by norm_num) hX5
      linarith
    have h5' : 0 ≤ Real.log (5 * X) := Real.log_nonneg (by linarith)
    have hsq : Real.log (5 * X) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
    rw [mul_div_assoc', div_le_iff₀ hl2, hHdef]
    have : 0 ≤ Real.log X ^ 2 := sq_nonneg _
    have hK2 : 256 ≤ K * Real.log 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hK2 this
    nlinarith
  have hH2 : H ≤ X / 2 := by
    have := hY₂ X hXY₂
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), id,
      abs_of_nonneg hX0.le] at this
    rw [hHdef]
    have e : 1 / (2 * K) * X * K = X / 2 := by field_simp
    nlinarith
  have hH0 : 0 < H := by positivity
  have hsub : primelessSet h X ⊆
      {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + H} := by
    rintro y ⟨hy, hnp⟩
    refine ⟨hy, fun ⟨p, hp, h1, h2⟩ => hnp ⟨p, hp, h1, ?_⟩⟩
    have hyX := hy.1
    have hy0 : 0 < y := by linarith
    have hly : Real.log X ≤ Real.log y := Real.log_le_log hX0 hyX
    have hly0 : 0 < Real.log y := by linarith
    have hKy := hY₁ y (by linarith)
    rw [le_div_iff₀ (by positivity)] at hKy
    have : H ≤ K * Real.log y ^ 2 := by
      rw [hHdef]; gcongr
    linarith
  have hfin : volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + H} ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 2 * X)).ne
      (measure_mono fun y hy => hy.1)
  have hm := (measureReal_mono hsub hfin).trans (hb X hXX₀ H hH1 hH2)
  have hq : C * X * Real.log X ^ 2 / H = C / K * X := by
    rw [hHdef]; field_simp
  rw [hq] at hm
  have hnn : 0 ≤ (volume (primelessSet h X)).toReal / X := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ hX0]
  have : (volume (primelessSet h X)).toReal = volume.real (primelessSet h X) := rfl
  rw [this]
  nlinarith

/-- The smoothed form of Selberg's asymptotic (the sharp form is
`SelbergAsymptoticStatement`). With `δ = H(X)/X`, `D2 δ y = Σ_n Λ(n) w_y(n)` where `w_y` is the
tent of height `δy` on `(y, y(1+2δ))` (`Erdos233/Basic.lean`), whose expected value is `δ²y²`.
For almost all `y ∈ [X, 2X]` it is `(1 + O(ε)) δ²y²`, as soon as `H / log² X → ∞`. -/
def SmoothedSelbergStatement : Prop :=
  ∀ H : ℝ → ℝ, Tendsto (fun X => H X / Real.log X ^ 2) atTop atTop →
    Tendsto (fun X => H X / X) atTop (𝓝 0) → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun X => (volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
        ε * (H X / X * y) ^ 2 < |D2 (H X / X) y - (H X / X * y) ^ 2|}).toReal / X)
      atTop (𝓝 0)

/-- **Smoothed Selberg asymptotic, under RH.** -/
theorem smoothed_asymptotic_of_RH (hRH : RiemannHypothesis) : SmoothedSelbergStatement := by
  intro H hH hHx ε hε
  obtain ⟨C, hC, hW⟩ := large_wave_measure hRH
  rw [Metric.tendsto_atTop]
  intro η hη
  set K : ℝ := max 12 (32 * C / (ε ^ 2 * η)) with hK
  have hK12 : 12 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hKC : 16 * C / ε ^ 2 / K ≤ η / 2 := by
    rw [div_le_iff₀ hK0]
    have := le_max_right 12 (32 * C / (ε ^ 2 * η))
    rw [← hK, div_le_iff₀ (by positivity)] at this
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.1 (hH.eventually_ge_atTop (K / ε + K))
  obtain ⟨Y₂, hY₂⟩ := eventually_atTop.1
    ((hHx.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))))
  refine ⟨max 5 (max Y₁ Y₂), fun X hX => ?_⟩
  have hX5 : 5 ≤ X := le_trans (le_max_left _ _) hX
  have hXY₁ : Y₁ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXY₂ : Y₂ ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  have hlX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; have := Real.exp_one_lt_d9; linarith
  have hl0 : 0 < Real.log X ^ 2 := by positivity
  have hHK0 : (K / ε + K) * Real.log X ^ 2 ≤ H X := by
    have := hY₁ X hXY₁; rwa [le_div_iff₀ hl0] at this
  have hKe : 0 ≤ K / ε * Real.log X ^ 2 := by positivity
  have hKl : 0 ≤ K * Real.log X ^ 2 := by positivity
  have hHK : K / ε * Real.log X ^ 2 ≤ H X := by nlinarith
  have hHK'' : K * Real.log X ^ 2 ≤ H X := by nlinarith
  have hHK' : K * Real.log X ^ 2 ≤ ε * H X := by
    have := mul_le_mul_of_nonneg_left hHK hε.le
    have e : ε * (K / ε * Real.log X ^ 2) = K * Real.log X ^ 2 := by field_simp
    linarith
  have hεH : 12 ≤ ε * H X := by nlinarith
  have hH12 : 12 ≤ H X := by nlinarith
  have hHpos : 0 < H X := by linarith
  set δ := H X / X with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := (hY₂ X hXY₂).le
  have hδX : δ * X = H X := by rw [hδdef]; field_simp
  set t := ε * (δ * X) ^ 2 / 2 with htdef
  have ht0 : 0 < t := by positivity
  have hsub : {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ ε * (δ * y) ^ 2 < |D2 δ y - (δ * y) ^ 2|}
      ⊆ {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖} := by
    rintro y ⟨hy, hbad⟩
    refine ⟨hy, ?_⟩
    have hyX := hy.1
    have hb := D2_bound hRH hδ0 (show 1 ≤ y by linarith)
    have e : δ ^ 2 * y ^ 2 = (δ * y) ^ 2 := by ring
    rw [e] at hb
    have hXy : (δ * X) ^ 2 ≤ (δ * y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hyX hδ0.le) 2
    have h12 : 12 ≤ ε * (δ * X) ^ 2 := by
      rw [hδX]
      have : ε * H X ≤ ε * H X ^ 2 := by
        have : H X ≤ H X ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this hε.le
      linarith
    have := mul_le_mul_of_nonneg_left hXy hε.le
    rw [htdef]
    linarith
  have hfin : volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      t ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖} ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 2 * X)).ne
      (measure_mono fun y hy => hy.1)
  have hm := (measureReal_mono hsub hfin).trans (hW X (by linarith) δ hδ0 hδ2 t ht0)
  set L := Real.log (2 / δ) with hL
  have hH1 : 1 ≤ H X := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hL2 : L ≤ 2 * Real.log X := by
    have : 2 / δ ≤ X ^ 2 := by
      rw [div_le_iff₀ hδ0, hδdef]
      field_simp
      nlinarith
    calc L ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
  have hLsq : L ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  have e : C * X ^ 4 * δ ^ 3 * L ^ 2 / t ^ 2 = 4 * C * X * L ^ 2 / (ε ^ 2 * H X) := by
    rw [htdef, hδX, hδdef]
    field_simp
    ring
  rw [e] at hm
  have hm2 : volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      ε * (δ * y) ^ 2 < |D2 δ y - (δ * y) ^ 2|} ≤ η / 2 * X := by
    refine hm.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hLsq (by positivity : (0 : ℝ) ≤ 4 * C * X)
    have h2 : 16 * C / ε ^ 2 * Real.log X ^ 2 ≤ η / 2 * K * Real.log X ^ 2 := by
      have := mul_le_mul_of_nonneg_right hKC hK0.le
      rw [div_mul_cancel₀ _ hK0.ne'] at this
      exact mul_le_mul_of_nonneg_right this hl0.le
    have h3 : η / 2 * K * Real.log X ^ 2 ≤ η / 2 * H X := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hHK'' (by positivity)
    have e2 : 16 * C / ε ^ 2 * Real.log X ^ 2 * (ε ^ 2 * X) = 16 * C * X * Real.log X ^ 2 := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_right (h2.trans h3) (by positivity : (0 : ℝ) ≤ ε ^ 2 * X)
    rw [e2] at h4
    have e3 : η / 2 * H X * (ε ^ 2 * X) = η / 2 * X * (ε ^ 2 * H X) := by ring
    linarith
  have hnn : 0 ≤ (volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      ε * (H X / X * y) ^ 2 < |D2 (H X / X) y - (H X / X * y) ^ 2|}).toReal / X := by
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ hX0]
  have : (volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      ε * (H X / X * y) ^ 2 < |D2 (H X / X) y - (H X / X * y) ^ 2|}).toReal
      = volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      ε * (δ * y) ^ 2 < |D2 δ y - (δ * y) ^ 2|} := rfl
  rw [this]
  have : 0 < η * X := by positivity
  linarith

/-- **Large gaps, under RH**: `Σ_{X ≤ p_n < 2X, d_n ≥ h} d_n ≤ C X log² X / h` for
`256 log²(5X)/log 2 ≤ h ≤ 2X` (`gap_sum` with `h/16`). -/
theorem large_gaps_of_RH (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x →
    ∀ h : ℝ, 256 * (Real.log (5 * x) ^ 2 / Real.log 2) ≤ h → h ≤ 2 * x →
    ∑ n ∈ (block x).filter (fun n => h ≤ primeGap n), (primeGap n : ℝ)
      ≤ C * x * Real.log x ^ 2 / h := by
  obtain ⟨C, X₀, hC, hg⟩ := gap_sum hRH
  refine ⟨16 * C, max X₀ 1, by positivity, fun x hx h hh1 hh2 => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx1 : (1 : ℝ) ≤ x := le_of_max_le_right hx
  have hl5 : 0 < Real.log (5 * x) := Real.log_pos (by linarith)
  have hh0 : 0 < h := by
    have : 0 < Real.log (5 * x) ^ 2 / Real.log 2 := by positivity
    linarith
  have h1 := hg x (le_of_max_le_left hx) (h / 16) (by linarith) (by linarith)
  have e : (fun n => 16 * (h / 16) ≤ (primeGap n : ℝ)) = fun n => h ≤ (primeGap n : ℝ) := by
    funext n; rw [show 16 * (h / 16) = h by ring]
  simp only [e] at h1
  refine h1.trans (le_of_eq ?_)
  field_simp

end Erdos233
