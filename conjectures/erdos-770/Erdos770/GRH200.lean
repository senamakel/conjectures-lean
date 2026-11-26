import Erdos770.Main200
import LLS.Bach2.Main2

/-!
# Erdős 770 (iii) under GRH with constant 200

`LLS.bach2_of_GRH` (lls-grh) gives `Ankeny.BachSubgroupBound 2` from
`Erdos985.DirichletLNonvanishingRightOfHalf`. It carries lls-grh's 15 `native_decide`
(`chunk2_ok`, a proved-sound checker) for the finite range of moduli.
-/

namespace Erdos770

open Erdos985 (DirichletLNonvanishingRightOfHalf)

theorem explicitBound200_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    ExplicitBound200 :=
  explicitBound200_of_bach (LLS.bach2_of_GRH hGRH)

end Erdos770
