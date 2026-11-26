import Abundant.Gronwall
import Robin.Statement

/-!
# Infinitely many extremely abundant numbers

Nazardonyavi–Yakubovich, Theorem 2.4, "necessity" (RH ⇒ `#XA = ∞`). If `XA` were finite, every
`n ≥ 10080` would satisfy `f(n) ≤ f(m)` for some `m` in a fixed finite range `[10080, B]`
(strong induction: a non-XA `n > 10080` has some `10080 ≤ m < n` with `f(m) ≥ f(n)`). Robin's
inequality puts each such `f(m)` below `e^γ`, and Gronwall's lower bound
(`exists_mul_robinRatio_gt`, from Nicolas' inequality) gives an `n ≥ 10080` above all of them.
-/

namespace Abundant

open Real ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Robin's inequality in ratio form: `f(n) < e^γ` for `n > 5040`. -/
lemma robinRatio_lt_of_robin (hR : Robin.RobinStatement) {n : ℕ} (hn : 5040 < n) :
    robinRatio n < Real.exp Real.eulerMascheroniConstant := by
  have h := hR n hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hlog : 1 < Real.log n := by
    have := Real.exp_one_lt_d9
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith)
  have hpos : (0 : ℝ) < n * Real.log (Real.log n) :=
    mul_pos (by linarith) (Real.log_pos hlog)
  rw [robinRatio, div_lt_iff₀ hpos]
  linarith [h]

/-- If every extremely abundant number is at most `B`, then each `n ≥ 10080` has
`f(n) ≤ f(m)` for some `10080 ≤ m ≤ B`. -/
lemma exists_le_of_bounded {B : ℕ} (hB : ∀ n, IsExtremelyAbundant n → n ≤ B) :
    ∀ n, 10080 ≤ n → ∃ m, 10080 ≤ m ∧ m ≤ B ∧ robinRatio n ≤ robinRatio m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hxa : IsExtremelyAbundant n
    · exact ⟨n, hn, hB n hxa, le_rfl⟩
    · have hne : n ≠ 10080 := fun h ↦ hxa (Or.inl h)
      have hgt : 10080 < n := lt_of_le_of_ne hn (Ne.symm hne)
      have : ¬ ∀ m : ℕ, 10080 ≤ m → m < n → robinRatio m < robinRatio n :=
        fun h ↦ hxa (Or.inr ⟨hgt, h⟩)
      push Not at this
      obtain ⟨m, hm1, hm2, hm3⟩ := this
      obtain ⟨m', hm'1, hm'2, hm'3⟩ := ih m hm2 hm1
      exact ⟨m', hm'1, hm'2, hm3.trans hm'3⟩

/-- **Nazardonyavi–Yakubovich** (2014): Robin's inequality and Nicolas' inequality imply that
there are infinitely many extremely abundant numbers. -/
theorem extremelyAbundantInfinite_of_robin_of_nicolas (hR : Robin.RobinStatement)
    (hN : Nicolas.NicolasStatement) : ExtremelyAbundantInfinite := by
  intro hfin
  obtain ⟨B₀, hB₀⟩ := hfin.bddAbove
  set B := max B₀ 10080
  have hB : ∀ n, IsExtremelyAbundant n → n ≤ B := fun n hn ↦ le_trans (hB₀ hn) (le_max_left _ _)
  obtain ⟨m₀, hm₀, hmax⟩ := (Finset.Icc 10080 B).exists_max_image robinRatio
    ⟨10080, Finset.mem_Icc.mpr ⟨le_rfl, le_max_right _ _⟩⟩
  have hm₀lt : robinRatio m₀ < Real.exp Real.eulerMascheroniConstant :=
    robinRatio_lt_of_robin hR (by have := (Finset.mem_Icc.mp hm₀).1; omega)
  obtain ⟨a, _, ha, hgt⟩ := exists_mul_robinRatio_gt hN le_rfl hm₀lt 10080
  rw [mul_one] at ha hgt
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_le_of_bounded hB a ha
  have := hmax m (Finset.mem_Icc.mpr ⟨hm1, hm2⟩)
  linarith

end Abundant
