import Erdos770.Main
import Ankeny.Main

/-!
# Erdős 770 (iii) under GRH

`Ankeny.bach_of_GRH` (ankeny-grh) gives `BachSubgroupBound (21/5)` from
`Erdos985.DirichletLNonvanishingRightOfHalf`. This file imports `Ankeny.Main`, which carries
ankeny-grh's `native_decide` computation for moduli below `2^17`.
-/

namespace Erdos770

open Erdos985 (DirichletLNonvanishingRightOfHalf)

theorem explicitBound_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    ExplicitBound 420 2 :=
  explicitBound_of_bach (Ankeny.bach_of_GRH hGRH)

theorem erdos_770_iii_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Erdos770Part3 :=
  erdos_770_iii_of_bach (Ankeny.bach_of_GRH hGRH)

end Erdos770
