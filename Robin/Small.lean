import Robin.Defs

/-!
# Robin's inequality in the range `5040 < n ≤ exp(e^{30})` (cited computation)

Morrill and Platt (*Robin's inequality for 20-free integers*, Integers 21 (2021), A28;
arXiv:1809.10813, Theorem 1) verified Robin's inequality unconditionally for all
`5040 < n ≤ 10^{10^{13.11485}}`, extending Briggs (Experiment. Math. 15 (2006)), who checked
every colossally abundant number up to `10^{10^{10}}`. Since `e^{30} < 1.07·10^{13}`,
`log n ≤ e^{30}` gives `n ≤ 10^{4.64·10^{12}}`, well inside that range.

This is a finite computation (in the sense that it reduces, via colossally abundant numbers, to
finitely many explicit checks), but far too large to replay in Lean; it is left as a cited `sorry`.
-/

namespace Robin

open ArithmeticFunction Real
open scoped ArithmeticFunction.sigma

/-- **Cited (Morrill–Platt 2021, Theorem 1).** Robin's inequality for `5040 < n ≤ exp(e^{30})`. -/
theorem robin_small_range (n : ℕ) (h1 : 5040 < n) (h2 : Real.log n ≤ Real.exp 30) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  sorry

end Robin
