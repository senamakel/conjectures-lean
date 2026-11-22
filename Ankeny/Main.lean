import Ankeny.Numerics
import Ankeny.Compute
import Ankeny.LeastNonresidue

/-!
# Bach's bound under GRH, with constant `5`

* `q ≥ 2^14`: the analytic argument (`Ankeny.bach_of_numericOK`, `Ankeny.numericOK_of_ge`).
* `q < 2^14`: the verified finite computation (`Ankeny.bach_of_allOK`, `Ankeny.allOK_Q₀`).

Bach's constant `2` is not reached: see the README for why the constant is `5`.
-/

namespace Ankeny

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- Bach's theorem under GRH, with constant `5` (Bach: `2`). -/
theorem bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : BachSubgroupBound 5 := by
  intro q _ H hH
  by_cases hq : q < 2 ^ 14
  · exact bach_of_allOK allOK_Q₀ q hq H hH
  · exact bach_of_numericOK hGRH q (numericOK_of_ge q (not_lt.1 hq)) H hH

theorem leastNonresidue_of_bach {c : ℝ} (h : BachSubgroupBound c) : LeastNonresidueBound c :=
  leastNonresidue_of_bach' h

theorem leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBound 5 :=
  leastNonresidue_of_bach (bach_of_GRH hGRH)

end Ankeny
