import Erdos985.Analytic.Principal.Identity
import Erdos985.Analytic.Principal.Bounds

/-! # Assembly of Bach's principal bound -/

namespace Erdos985.Analytic

open Complex ArithmeticFunction

/-- MTT Lemma 1, principal part: the statement of `Erdos985.bach_principal`. -/
theorem bach_principal_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (x : ℕ) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) - x / 2| ≤ √x / 20 + 3 := by
  sorry

end Erdos985.Analytic
