import Erdos985.Analytic.ExplicitFormula.Identity
import Erdos985.Analytic.ExplicitFormula.Bounds
import Erdos985.Analytic.ExplicitFormula.ZeroSum

/-! # Assembly of Bach's non-principal bound (see `ExplicitFormula/Basic.lean` for the plan) -/

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step D: assembly -/

/-- MTT Lemma 1, non-principal part: the statement of `Erdos985.bach_nonprincipal`. -/
theorem bach_nonprincipal_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    ‖bachSum χ x‖ ≤ bachC p x * √x * Real.log p := by
  sorry

end Erdos985.Analytic
