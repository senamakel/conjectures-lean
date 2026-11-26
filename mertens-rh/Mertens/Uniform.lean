import Mertens.Statement

/-!
# The Mertens bound at every integer

`MertensBound` is an `O`-statement as `x → ∞`. For partial summation it is used in the form
`|M(n)| ≤ K (n+1)^β` for **every** `n : ℕ`, which follows from the trivial bound `|M(n)| ≤ n`
below the threshold.
-/

namespace Mertens

open Filter Finset Asymptotics
open scoped ArithmeticFunction.Moebius

lemma sum_range_succ_moebius_int (n : ℕ) : ∑ k ∈ range (n + 1), μ k = mertens n := by
  rw [sum_range_succ', ArithmeticFunction.map_zero, add_zero, mertens, Nat.floor_natCast,
    Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => μ j) 0 n 1]
  rfl

lemma abs_mertens_nat_le_self (n : ℕ) : |(mertens n : ℝ)| ≤ n := by
  rw [mertens, Nat.floor_natCast]
  push_cast
  calc |∑ k ∈ Icc 1 n, (μ k : ℝ)| ≤ ∑ k ∈ Icc 1 n, |(μ k : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 1 n, (1 : ℝ) := sum_le_sum fun k _ => by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = n := by simp

/-- From `MertensBound`: for every `β > 1/2` there is `K` with `|M(n)| ≤ K (n+1)^β` for all `n`. -/
theorem abs_mertens_le_of_mertensBound (hMB : MertensBound) {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, |(mertens n : ℝ)| ≤ K * ((n : ℝ) + 1) ^ β := by
  obtain ⟨C, hC⟩ := (hMB (β - 1 / 2) (by linarith)).bound
  obtain ⟨X, hX⟩ := eventually_atTop.1 hC
  set Y : ℝ := max X 1
  refine ⟨|C| + Y, by positivity, fun n => ?_⟩
  have hβ0 : 0 ≤ β := by linarith
  have hp1 : 1 ≤ ((n : ℝ) + 1) ^ β := Real.one_le_rpow (by linarith [n.cast_nonneg (α := ℝ)]) hβ0
  by_cases hn : Y ≤ n
  · have hnX : X ≤ n := le_trans (le_max_left _ _) hn
    have h := hX n hnX
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [show 1 / 2 + (β - 1 / 2) = β by ring, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn0 _)] at h
    have h2 : (n : ℝ) ^ β ≤ ((n : ℝ) + 1) ^ β := Real.rpow_le_rpow hn0 (by linarith) hβ0
    calc |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ β := h
      _ ≤ |C| * ((n : ℝ) + 1) ^ β := by
          gcongr
          · exact le_abs_self C
      _ ≤ (|C| + Y) * ((n : ℝ) + 1) ^ β := by
          gcongr; linarith [le_max_right X 1]
  · push Not at hn
    calc |(mertens n : ℝ)| ≤ n := abs_mertens_nat_le_self n
      _ ≤ Y := hn.le
      _ ≤ (|C| + Y) * 1 := by linarith [abs_nonneg C]
      _ ≤ (|C| + Y) * ((n : ℝ) + 1) ^ β := by
          gcongr

end Mertens
