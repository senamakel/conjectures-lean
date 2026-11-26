import Ankeny.Numerics
import Ankeny.Compute
import Ankeny.LeastNonresidue

/-!
# Bach's bound under GRH, with constant `21/5`

* `q ≥ 2^17`: the analytic argument (`Ankeny.bach_of_numericOK`, `Ankeny.numericOK_of_ge`).
* `q < 2^17`: the verified finite computation (`Ankeny.bach_small`).

Bach's constant `2` is not reached: see the README for why the constant is `21/5`.
-/

namespace Ankeny

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- Bach's theorem under GRH, with constant `21/5` (Bach: `2`). -/
theorem bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : BachSubgroupBound (21 / 5) := by
  intro q _ H hH
  by_cases hq : q < 2 ^ 17
  · exact bach_small q hq H hH
  · exact bach_of_numericOK hGRH q (numericOK_of_ge q (not_lt.1 hq)) H hH

theorem leastNonresidue_of_bach {c : ℝ} (h : BachSubgroupBound c) : LeastNonresidueBound c :=
  leastNonresidue_of_bach' h

theorem leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBound (21 / 5) :=
  leastNonresidue_of_bach (bach_of_GRH hGRH)

end Ankeny
