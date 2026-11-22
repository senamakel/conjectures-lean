import Lindelof.Statement

/-!
# Stretch goal: Lindelöf for Dirichlet L-functions in the `t`-aspect, from GRH

The same argument as for `ζ` (Steps 1–8 of `docs/BLUEPRINT.md`), with `ξ` replaced by the
completed L-function of the primitive character inducing `χ`.
-/

namespace Lindelof

/-- GRH for Dirichlet L-functions implies the Lindelöf hypothesis for them. -/
theorem dirichletLindelof_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    DirichletLindelofHypothesis := by
  sorry

end Lindelof
