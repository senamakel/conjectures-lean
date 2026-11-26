import BachSorenson.Numerics
import BachSorenson.Compute

/-!
# The Bach–Sorenson bound under GRH, with constant `7/2`

* `q ≥ 2^15`: the analytic argument (`BachSorenson.bachSorenson_of_numericOK`,
  `BachSorenson.numericOK_of_ge`).
* `2 ≤ q < 2^15`: the verified finite computation (`BachSorenson.bachSorenson_small`).

This Cesàro-weight argument stops at `7/2`; Bach–Sorenson's constant `2` is
`BachSorenson.bachSorenson_two_of_GRH` (`BachSorenson/Two/Main.lean`).
-/

namespace BachSorenson

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- The least prime `p ≡ a (mod q)` is below `(7/2) (q log q)²`, under GRH
(Bach–Sorenson: `2 (q log q)²`). -/
theorem bachSorenson_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    BachSorensonBound (7 / 2) := by
  intro q a hq ha
  by_cases hq' : q < 2 ^ 15
  · exact bachSorenson_small hq hq' ha
  · exact bachSorenson_of_numericOK hGRH (by norm_num) hq (numericOK_of_ge q (not_lt.1 hq')) ha

end BachSorenson
