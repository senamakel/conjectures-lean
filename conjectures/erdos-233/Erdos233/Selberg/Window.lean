import Erdos233.Selberg.TrapCoeff

/-!
# Primes in `(y, y(1+δ)]` for almost all `y ∈ [X, 2X]`, under RH

Fix `0 < κ ≤ 1/8` and `δ ≤ κ` with `δX ≥ K₀ log² X`. Put `σ = κδ` and take the two trapezoids

* `trap (1−σ) σ (δ+σ) y` (plateau `[y, y(1+δ)]`, `psi_window_le_trap`), and
* `trap 1 σ (δ−σ) y` (support `(y, y(1+δ))`, `trap_le_psi_window`).

1. `psi_window_of_waves`: when both waves are below `t = κσδX²`,
   `|ψ(y(1+δ)) − ψ(y) − δy| ≤ 3κδy` (`trap_bound`, main term `σD y²`).
2. `waves_measure`: by `wave_large_measure` and `tcoef_sums`, the `y ∈ [X, 2X]` where one wave
   reaches `t` have measure `≤ C log² X / (κ²δ)`; `σ` cancels.
3. `pi_window_of_psi`: from `ψ` to `θ` (`psi_sub_theta_window`) and to `π` (`log p ∈ [log y,
   log y + δ]`): `(1−6κ) δy/log y ≤ π(y(1+δ)) − π(y) ≤ (1+3κ) δy/log y`.
4. `pi_window_measure`: the `y ∈ [X, 2X]` where step 3 fails have measure `≤ C log² X / δ`.
-/

namespace Erdos233

open Complex Erdos985.Analytic MeasureTheory Chebyshev ArithmeticFunction Filter Topology

/-- Eventually `log²(5x)/log 2 ≤ c √x`. -/
lemma eventually_log_sq_le_c_sqrt {c : ℝ} (hc : 0 < c) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → Real.log (5 * X) ^ 2 / Real.log 2 ≤ c * Real.sqrt X := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho := (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show 0 < c * Real.log 2 / 4 by positivity)
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 ho
  refine ⟨max X₁ 5, fun X hX => ?_⟩
  have hX5 : 5 ≤ X := le_of_max_le_right hX
  have hX0 : 0 < X := by linarith
  have h := hX₁ X (le_of_max_le_left hX)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlX _),
    abs_of_nonneg (Real.rpow_nonneg hX0.le _), Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have h5 : Real.log (5 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 5 ≤ Real.log X := Real.log_le_log (by norm_num) hX5
    linarith
  have h5' : 0 ≤ Real.log (5 * X) := Real.log_nonneg (by linarith)
  have hsq : Real.log (5 * X) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  rw [div_le_iff₀ hl2]
  nlinarith

/-- Step 1: off the two large-wave sets, `ψ(y(1+δ)) − ψ(y) = δy (1 + O(κ))`. -/
lemma psi_window_of_waves (hRH : RiemannHypothesis) {X y δ κ : ℝ} (hX : 3 ≤ X) (hyX : X ≤ y)
    (hκ : 0 < κ) (hκ8 : κ ≤ 1 / 8) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (h3 : 3 ≤ κ ^ 2 * δ ^ 2 * X ^ 2)
    (hup : y ^ (3 / 2 : ℝ) * ‖TW (1 - κ * δ) (κ * δ) (δ + κ * δ) (Real.log y)‖
      < κ * (κ * δ) * δ * X ^ 2)
    (hlo : y ^ (3 / 2 : ℝ) * ‖TW 1 (κ * δ) (δ - κ * δ) (Real.log y)‖
      < κ * (κ * δ) * δ * X ^ 2) :
    |ψ (y * (1 + δ)) - ψ y - δ * y| ≤ 3 * κ * δ * y := by
  set σ := κ * δ with hσ
  have hy0 : 0 < y := by linarith
  have hσ0 : 0 < σ := by positivity
  have hσδ : σ ≤ δ / 8 := by rw [hσ]; nlinarith
  have hXy2 : X ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by linarith) hyX 2
  have ht : κ * σ * δ * X ^ 2 ≤ κ * σ * δ * y ^ 2 :=
    mul_le_mul_of_nonneg_left hXy2 (by positivity)
  have h3y : 3 ≤ σ ^ 2 * y ^ 2 := by
    have : κ ^ 2 * δ ^ 2 * X ^ 2 ≤ κ ^ 2 * δ ^ 2 * y ^ 2 :=
      mul_le_mul_of_nonneg_left hXy2 (by positivity)
    rw [hσ]; nlinarith
  -- upper trapezoid
  have hu1 := psi_window_le_trap (a := 1 - σ) (D := δ + σ) hy0 (by linarith) hσ0.le (by linarith)
  rw [show 1 - σ + (δ + σ) = 1 + δ by ring, show 1 - σ + σ = 1 by ring, mul_one] at hu1
  have hu2 := trap_bound hRH (a := 1 - σ) (σ := σ) (D := δ + σ) (y := y) (by linarith) hσ0.le
    (by linarith) (by nlinarith)
  have hu3 := (abs_le.1 hu2).2
  -- lower trapezoid
  have hl1 := trap_le_psi_window (a := 1) (D := δ - σ) hy0 one_pos hσ0.le (by linarith)
  rw [show 1 + (δ - σ) + σ = 1 + δ by ring, mul_one] at hl1
  have hl2 := trap_bound hRH (a := 1) (σ := σ) (D := δ - σ) (y := y) one_pos hσ0.le
    (by linarith) (by linarith)
  have hl3 := (abs_le.1 hl2).1
  have hsy : 0 < σ * y := by positivity
  rw [abs_le]
  constructor
  · have key : σ * y * (δ * y - 3 * κ * δ * y) ≤ σ * y * (ψ (y * (1 + δ)) - ψ y) := by
      have : σ * y * (δ * y - 3 * κ * δ * y) ≤ σ * (δ - σ) * y ^ 2 - 3
          - κ * σ * δ * y ^ 2 := by
        have e : κ * σ * δ * y ^ 2 = σ ^ 2 * y ^ 2 := by rw [hσ]; ring
        nlinarith
      linarith
    have := le_of_mul_le_mul_left key hsy
    linarith
  · have key : σ * y * (ψ (y * (1 + δ)) - ψ y) ≤ σ * y * (δ * y + 3 * κ * δ * y) := by
      have : σ * (δ + σ) * y ^ 2 + 3 + κ * σ * δ * y ^ 2 ≤ σ * y * (δ * y + 3 * κ * δ * y) := by
        have e : κ * σ * δ * y ^ 2 = σ ^ 2 * y ^ 2 := by rw [hσ]; ring
        nlinarith
      linarith
    have := le_of_mul_le_mul_left key hsy
    linarith

/-- Step 2: the two large-wave sets have measure `≪ log² X / (κ²δ)`. -/
theorem waves_measure (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    ∀ δ κ : ℝ, 0 < κ → κ ≤ 1 / 8 → 0 < δ → δ ≤ 1 / 4 → 1 / X ≤ δ →
    volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      (κ * (κ * δ) * δ * X ^ 2 ≤ y ^ (3 / 2 : ℝ) * ‖TW (1 - κ * δ) (κ * δ) (δ + κ * δ) (Real.log y)‖ ∨
       κ * (κ * δ) * δ * X ^ 2 ≤ y ^ (3 / 2 : ℝ) * ‖TW 1 (κ * δ) (δ - κ * δ) (Real.log y)‖)}
      ≤ C * Real.log X ^ 2 / (κ ^ 2 * δ) := by
  obtain ⟨Cm, hCm, hW⟩ := wave_large_measure
  obtain ⟨Ct, hCt, hT⟩ := tcoef_sums hRH
  refine ⟨2 * (1280 * Cm * Ct), by positivity, fun X hX δ κ hκ hκ8 hδ hδ4 hXδ => ?_⟩
  set σ := κ * δ with hσ
  have hσ0 : 0 < σ := by positivity
  have hσδ : σ ≤ δ / 8 := by rw [hσ]; nlinarith
  set t := κ * σ * δ * X ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have hX0 : 0 < X := by linarith
  have hlX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; have := Real.exp_one_lt_d9; linarith
  -- one wave
  have one : ∀ a D : ℝ, 3 / 4 ≤ a → a ≤ 1 → σ ≤ D → 3 * δ / 4 ≤ D → D ≤ 5 * δ / 4 →
      volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖TW a σ D (Real.log y)‖}
        ≤ 1280 * Cm * Ct * Real.log X ^ 2 / (κ ^ 2 * δ) := by
    intro a D ha ha1 hσD hD1 hD2
    have hD0 : 0 < D := by linarith
    have hDh : D ≤ 1 / 2 := by linarith
    obtain ⟨s1, s2, sb⟩ := hT a σ D ha ha1 hσ0 hσD hDh
    have hm := hW (fun ρ => tcoef a σ D ρ) s1 s2 X (by linarith) t ht0
    refine hm.trans ?_
    set L := Real.log (2 / D) with hL
    have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hD0]; linarith)
    have hL2 : L ≤ 2 * Real.log X := by
      have : 2 / D ≤ X ^ 2 := by
        rw [div_le_iff₀ hD0]
        have : 3 / (4 * X) ≤ D := by
          have : 3 / (4 * X) = 3 / 4 * (1 / X) := by field_simp
          rw [this]; linarith
        rw [div_le_iff₀ (by positivity)] at this
        nlinarith
      calc L ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) this
        _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
    have hLsq : L ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
    have hS : ∑' ρ : Zeros, (mult ρ : ℝ) * ‖tcoef a σ D ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
        ≤ Ct * σ ^ 2 * (5 * δ / 4) * (4 * Real.log X ^ 2) := by
      refine sb.trans ?_
      have : Ct * σ ^ 2 * D * L ^ 2 ≤ Ct * σ ^ 2 * (5 * δ / 4) * L ^ 2 := by gcongr
      refine this.trans ?_
      gcongr
    calc 256 * Cm * X ^ 4 * (∑' ρ : Zeros, (mult ρ : ℝ) * ‖tcoef a σ D ρ‖ ^ 2 *
          Real.log (|(ρ : ℂ).im| + 2)) / t ^ 2
        ≤ 256 * Cm * X ^ 4 * (Ct * σ ^ 2 * (5 * δ / 4) * (4 * Real.log X ^ 2)) / t ^ 2 := by
          gcongr
      _ = 1280 * Cm * Ct * Real.log X ^ 2 / (κ ^ 2 * δ) := by
          rw [ht, hσ]; field_simp; ring
  have hfin : ∀ S : Set ℝ, S ⊆ Set.Icc X (2 * X) → volume S ≠ ⊤ := fun S hS =>
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 2 * X)).ne (measure_mono hS)
  have hsub : {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      (t ≤ y ^ (3 / 2 : ℝ) * ‖TW (1 - σ) σ (δ + σ) (Real.log y)‖ ∨
       t ≤ y ^ (3 / 2 : ℝ) * ‖TW 1 σ (δ - σ) (Real.log y)‖)} ⊆
      {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖TW (1 - σ) σ (δ + σ) (Real.log y)‖}
      ∪ {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖TW 1 σ (δ - σ) (Real.log y)‖} := by
    rintro y ⟨hy, h | h⟩
    · left; exact ⟨hy, h⟩
    · right; exact ⟨hy, h⟩
  have hδ1 : δ ≤ 1 / 4 := hδ4
  refine (measureReal_mono hsub (measure_union_ne_top (hfin _ fun y hy => hy.1)
    (hfin _ fun y hy => hy.1))).trans ((measureReal_union_le _ _).trans ?_)
  have h1 := one (1 - σ) (δ + σ) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have h2 := one 1 (δ - σ) (by norm_num) le_rfl (by linarith) (by linarith) (by linarith)
  have e : 2 * (1280 * Cm * Ct) * Real.log X ^ 2 / (κ ^ 2 * δ)
      = 1280 * Cm * Ct * Real.log X ^ 2 / (κ ^ 2 * δ)
        + 1280 * Cm * Ct * Real.log X ^ 2 / (κ ^ 2 * δ) := by ring
  rw [e]
  exact add_le_add h1 h2

end Erdos233
