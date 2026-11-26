import BachSorenson.Two.Numerics
import BachSorenson.Compute2

/-!
# The Bach–Sorenson bound under GRH, with their constant `2`

* `q ≥ 2^15`: the analytic argument with the kernel `x^s/s²` (`BachSorenson.Two.
  exists_prime_of_numericOK2`, `BachSorenson.Two.numericOK2_of_ge`).
* `2 ≤ q < 2^15`: the verified finite computation (`BachSorenson.bachSorenson_two_small`).
-/

namespace BachSorenson

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- Bach–Sorenson (1996): under GRH, the least prime `p ≡ a (mod q)` is below `2 (q log q)²`. -/
theorem bachSorenson_two_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    BachSorensonBound 2 := by
  intro q a hq ha
  by_cases hq' : q < 2 ^ 15
  · exact bachSorenson_two_small hq hq' ha
  · obtain ⟨p, hp, hpa, hpx⟩ := Two.exists_prime_of_numericOK2 hGRH (by omega)
      (Two.numericOK2_of_ge q (not_lt.1 hq')) a ha
    refine ⟨p, hp, hpa, ?_⟩
    have : (p : ℝ) < xOf 2 q := by exact_mod_cast hpx
    linarith [xOf_le 2 q (by norm_num)]

end BachSorenson
