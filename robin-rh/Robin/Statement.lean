import Erdos985.Statement

/-!
# Robin's inequality (target statements — do not change the definitions)

Robin (1984): if RH holds, then `σ(n) < e^γ n log log n` for every `n > 5040` (and conversely).
`RiemannHypothesis` is Mathlib's statement; leanprover-community/riemann-hypothesis proves it
as `riemannHypothesis : RiemannHypothesis`.
-/

namespace Robin

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Robin's inequality. -/
def RobinStatement : Prop :=
  ∀ n : ℕ, 5040 < n →
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

/-- Lagarias's equivalent form (stretch goal): `σ(n) ≤ H_n + exp(H_n) log H_n` for `n ≥ 1`. -/
def LagariasStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (σ 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n)

-- The main theorem `Robin.robin_of_RH : RiemannHypothesis → RobinStatement` is proved in
-- `Robin/Main.lean` (moved there so that it can import the proof modules).

end Robin
