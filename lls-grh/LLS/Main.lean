import LLS.Bach114
import LLS.Finite114
import Ankeny.LeastNonresidue
import Miller.Reduction

/-!
# Headline results under GRH: Bach's subgroup bound with constant `11/4`

* `LLS.bach_of_GRH : BachSubgroupBound (11/4)` (ankeny-grh's target definition, constant `11/4`
  instead of Bach's `2`; ankeny-grh proves `21/5`). For `q ≥ 2^18` this is the
  Lamzouri–Li–Soundararajan argument (`LLS.bach_large114`); for `q < 2^18` it is the verified
  finite computation (`LLS.bach_small114`).
* `LLS.leastNonresidue_of_GRH : LeastNonresidueBound (11/4)`.
* `LLS.miller_of_GRH : MillerStatement (11/4)` (miller-grh's target, via `Miller.miller_of_bach`).
-/

namespace LLS

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- Bach's subgroup bound under GRH with constant `11/4`. -/
theorem bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Ankeny.BachSubgroupBound (11 / 4) := by
  intro q _ H hH
  by_cases hq : q < 2 ^ 18
  · exact bach_small114 q hq H hH
  · exact bach_large114 hGRH q (not_lt.1 hq) H hH

/-- The least quadratic non-residue mod an odd prime `p` is at most `(11/4) log² p`, under GRH. -/
theorem leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.LeastNonresidueBound (11 / 4) :=
  Ankeny.leastNonresidue_of_bach' (bach_of_GRH hGRH)

/-- Miller's deterministic primality test under GRH, with witnesses `a ≤ (11/4) log² n`. -/
theorem miller_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Miller.MillerStatement (11 / 4) :=
  Miller.miller_of_bach (bach_of_GRH hGRH)

end LLS
