import Erdos770.Sharp.Main
import LLS.Thm11.Main

/-!
# Erdős 770 (iii) under GRH with constant 5

`LLS.Thm11.leastPrimeOutsideSubgroup_of_GRH` (lls-grh, LLS Theorem 1.1 with the paper's `B(q)`,
standard axioms only, no `native_decide`) supplies the hypothesis of `explicitBound5_of_lls`.

Not imported by the default target `Erdos770`: build it with `lake build Erdos770.Sharp.GRH`
once lls-grh's `LLS.Thm11` modules are built.
-/

namespace Erdos770.Sharp

open Erdos985 (DirichletLNonvanishingRightOfHalf)

theorem explicitBound5_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : ExplicitBound5 :=
  explicitBound5_of_lls (LLS.Thm11.leastPrimeOutsideSubgroup_of_GRH hGRH)

theorem erdos_770_iii_of_GRH5 (hGRH : DirichletLNonvanishingRightOfHalf) : Erdos770Part3 :=
  erdos_770_iii_of_lls (LLS.Thm11.leastPrimeOutsideSubgroup_of_GRH hGRH)

end Erdos770.Sharp
