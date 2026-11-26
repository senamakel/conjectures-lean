import Cramer.Statement2
import Cramer.MeanSquare.Block

/-!
# Cramér's mean-square theorem under RH (Round 5 headline theorems)

From `block_bound` (`∫_Y^{4Y} (ψ − y)² ≤ C Y²` for `Y ≥ 2`):

* the dyadic form directly;
* `∫_2^X (ψ − y)² ≤ C X²` by splitting off `[X/4, X]` and inducting on `X ≤ 8·4^n`;
* `∫_2^X ((ψ − y)/y)² ≤ C + (C / log 4) log X` the same way, since each block contributes at
  most `C`.
-/

namespace Cramer

open MeasureTheory intervalIntegral Chebyshev Cramer.MeanSq

/-- Induction along `X ↦ X/4`. -/
lemma quarter_induction (I B : ℝ → ℝ) (hbase : ∀ X, 2 ≤ X → X ≤ 8 → I X ≤ B X)
    (hstep : ∀ X, 8 < X → I (X / 4) ≤ B (X / 4) → I X ≤ B X) :
    ∀ X, 2 ≤ X → I X ≤ B X := by
  have key : ∀ n : ℕ, ∀ X, 2 ≤ X → X ≤ 8 * 4 ^ n → I X ≤ B X := by
    intro n
    induction n with
    | zero => intro X h1 h2; exact hbase X h1 (by simpa using h2)
    | succ n ih =>
      intro X h1 h2
      by_cases h8 : X ≤ 8
      · exact hbase X h1 h8
      · push_neg at h8
        refine hstep X h8 (ih (X / 4) (by linarith) ?_)
        rw [pow_succ] at h2
        linarith
  intro X hX
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 4)
  exact key n X hX (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) n])

lemma intervalIntegrable_sq_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => ((ψ x - x) / x) ^ 2) volume a b := by
  have hc : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.uIcc a b) := by
    refine ContinuousOn.inv₀ (continuous_pow 2).continuousOn fun x hx => ?_
    rw [Set.uIcc_of_le hab] at hx
    have : 0 < x := lt_of_lt_of_le ha hx.1
    exact pow_ne_zero 2 this.ne'
  have := (intervalIntegrable_sq a b).continuousOn_mul hc
  refine this.congr fun x _ => ?_
  simp only [div_pow]
  ring

/-- **Dyadic form** (Cramér 1922; Brent–Platt–Trudgian 2022, eq. (1)):
`∫_X^{2X} (ψ(x) − x)² dx ≪ X²` under RH. -/
theorem dyadicMeanSquare_of_RH (hRH : RiemannHypothesis) : CramerDyadicMeanSquare := by
  obtain ⟨C, hC, hb⟩ := block_bound hRH
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with X hX
  have hX0 : 0 ≤ X := by linarith
  have hnn : 0 ≤ ∫ x in X..2 * X, (ψ x - x) ^ 2 :=
    integral_nonneg (by linarith) fun x _ => sq_nonneg _
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (sq_nonneg X)]
  calc ∫ x in X..2 * X, (ψ x - x) ^ 2 ≤ ∫ x in X..4 * X, (ψ x - x) ^ 2 :=
        integral_mono_interval le_rfl (by linarith) (by linarith)
          (Filter.Eventually.of_forall fun x => sq_nonneg _) (intervalIntegrable_sq _ _)
    _ ≤ C * X ^ 2 := hb X hX

/-- **Cramér (1922)**: `∫_1^X (ψ(x) − x)² dx ≪ X²` under RH. -/
theorem meanSquare_of_RH (hRH : RiemannHypothesis) : CramerMeanSquare := by
  obtain ⟨C, hC, hb⟩ := block_bound hRH
  set I : ℝ → ℝ := fun X => ∫ x in (2 : ℝ)..X, (ψ x - x) ^ 2 with hI
  have hmain : ∀ X, 2 ≤ X → I X ≤ C * X ^ 2 := by
    refine quarter_induction I (fun X => C * X ^ 2) (fun X h1 h2 => ?_) (fun X h8 ih => ?_)
    · calc I X ≤ ∫ x in (2 : ℝ)..4 * 2, (ψ x - x) ^ 2 :=
            integral_mono_interval le_rfl h1 (by linarith)
              (Filter.Eventually.of_forall fun x => sq_nonneg _) (intervalIntegrable_sq _ _)
        _ ≤ C * 2 ^ 2 := hb 2 le_rfl
        _ ≤ C * X ^ 2 := by gcongr
    · have hsplit : I X = I (X / 4) + ∫ x in X / 4..4 * (X / 4), (ψ x - x) ^ 2 := by
        simp only [hI]
        rw [show 4 * (X / 4) = X by ring]
        exact (integral_add_adjacent_intervals (intervalIntegrable_sq _ _)
          (intervalIntegrable_sq _ _)).symm
      have := hb (X / 4) (by linarith)
      rw [hsplit]
      nlinarith
  set K0 := ∫ x in (1 : ℝ)..2, (ψ x - x) ^ 2 with hK0
  have hK00 : 0 ≤ K0 := integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  refine Asymptotics.IsBigO.of_bound (K0 + C) ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with X hX
  have hnn : 0 ≤ ∫ x in (1 : ℝ)..X, (ψ x - x) ^ 2 :=
    integral_nonneg (by linarith) fun x _ => sq_nonneg _
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (sq_nonneg X)]
  have hsplit : ∫ x in (1 : ℝ)..X, (ψ x - x) ^ 2 = K0 + I X :=
    (integral_add_adjacent_intervals (intervalIntegrable_sq _ _)
      (intervalIntegrable_sq _ _)).symm
  have hX1 : 1 ≤ X ^ 2 := by nlinarith
  rw [hsplit]
  nlinarith [hmain X hX]

/-- **Logarithmic form**: `∫_1^X ((ψ(x) − x)/x)² dx ≪ log X` under RH. -/
theorem logMeanSquare_of_RH (hRH : RiemannHypothesis) : CramerLogMeanSquare := by
  obtain ⟨C, hC, hb⟩ := block_bound hRH
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hblock : ∀ Y : ℝ, 2 ≤ Y → ∫ y in Y..4 * Y, ((ψ y - y) / y) ^ 2 ≤ C := by
    intro Y hY
    have hY0 : 0 < Y := by linarith
    calc ∫ y in Y..4 * Y, ((ψ y - y) / y) ^ 2
        ≤ ∫ y in Y..4 * Y, (Y ^ 2)⁻¹ * (ψ y - y) ^ 2 := by
          refine integral_mono_on (by linarith) (intervalIntegrable_sq_div hY0 (by linarith))
            ((intervalIntegrable_sq _ _).const_mul _) fun y hy => ?_
          have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
          rw [div_pow, div_eq_inv_mul]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hY0.le hy.1 2)
      _ = (Y ^ 2)⁻¹ * ∫ y in Y..4 * Y, (ψ y - y) ^ 2 := integral_const_mul _ _
      _ ≤ (Y ^ 2)⁻¹ * (C * Y ^ 2) := by gcongr; exact hb Y hY
      _ = C := by field_simp
  set J : ℝ → ℝ := fun X => ∫ x in (2 : ℝ)..X, ((ψ x - x) / x) ^ 2 with hJ
  set C2 := C / Real.log 4 with hC2
  have hC2l : C2 * Real.log 4 = C := by rw [hC2]; field_simp
  have hC20 : 0 ≤ C2 := by positivity
  have hmain : ∀ X, 2 ≤ X → J X ≤ C + C2 * Real.log X := by
    refine quarter_induction J (fun X => C + C2 * Real.log X) (fun X h1 h2 => ?_)
      (fun X h8 ih => ?_)
    · have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
      calc J X ≤ ∫ x in (2 : ℝ)..4 * 2, ((ψ x - x) / x) ^ 2 :=
            integral_mono_interval le_rfl h1 (by linarith)
              (Filter.Eventually.of_forall fun x => sq_nonneg _)
              (intervalIntegrable_sq_div (by norm_num) (by norm_num))
        _ ≤ C := hblock 2 le_rfl
        _ ≤ C + C2 * Real.log X := by nlinarith
    · have hX4 : 0 < X / 4 := by linarith
      have hsplit : J X = J (X / 4) + ∫ x in X / 4..4 * (X / 4), ((ψ x - x) / x) ^ 2 := by
        simp only [hJ]
        rw [show 4 * (X / 4) = X by ring]
        exact (integral_add_adjacent_intervals
          (intervalIntegrable_sq_div (by norm_num) (by linarith))
          (intervalIntegrable_sq_div hX4 (by linarith))).symm
      have hlog : Real.log (X / 4) = Real.log X - Real.log 4 :=
        Real.log_div (by linarith) (by norm_num)
      have := hblock (X / 4) (by linarith)
      rw [hsplit]
      rw [hlog] at ih
      nlinarith
  set K1 := ∫ x in (1 : ℝ)..2, ((ψ x - x) / x) ^ 2 with hK1
  have hK10 : 0 ≤ K1 := integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  refine Asymptotics.IsBigO.of_bound (K1 + C + C2) ?_
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hX
  have hX2 : 2 ≤ X := le_trans he2 hX
  have hlX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hX
  have hnn : 0 ≤ ∫ x in (1 : ℝ)..X, ((ψ x - x) / x) ^ 2 :=
    integral_nonneg (by linarith) fun x _ => sq_nonneg _
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by linarith)]
  have hsplit : ∫ x in (1 : ℝ)..X, ((ψ x - x) / x) ^ 2 = K1 + J X :=
    (integral_add_adjacent_intervals (intervalIntegrable_sq_div (by norm_num) (by norm_num))
      (intervalIntegrable_sq_div (by norm_num) hX2)).symm
  rw [hsplit]
  nlinarith [hmain X hX2]

end Cramer
