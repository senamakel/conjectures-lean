import LLS.Bach2.Core
import LLS.Bach2.Finite2
import Ankeny.LeastNonresidue
import Miller.Reduction

/-!
# Bach's constant `2` under GRH

* `LLS.bach2_of_GRH : Ankeny.BachSubgroupBound 2`: every proper subgroup of `(ZMod q)ˣ` omits a
  unit of residue `≤ 2 log² q` (Bach, Math. Comp. 55 (1990), with his constant). For
  `3 ≤ q < 2^2500` the checker of `LLSCheck` certifies each modulus (generation of `(ZMod q)ˣ`
  by small units, or a positive GRH budget with the actual prime factors of `q`, or a positive
  budget uniform in `q`); for `q ≥ 2^2500` the uniform budget `LLS.Phi` is positive
  (`LLS.goodQ_tail2`).
* `LLS.leastNonresidue2_of_GRH : Ankeny.LeastNonresidueBound 2`.
* `LLS.miller2_of_GRH : Miller.MillerStatement 2`.
-/

namespace LLS

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- **Bach's subgroup bound with Bach's constant `2`, under GRH.** -/
theorem bach2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Ankeny.BachSubgroupBound 2 := by
  intro q _ H hH
  rcases lt_or_ge q 3 with h3 | h3
  · exact absurd (Ankeny.subgroup_eq_top_of_le_two (by omega) H) hH
  rcases lt_or_ge q (2 ^ 2500) with h | h
  · exact bach_of_good2 hGRH q (good2_range q h3 h) H hH
  · exact bach_tail2 hGRH q h H hH

/-- The least quadratic non-residue mod an odd prime `p` is at most `2 log² p`, under GRH. -/
theorem leastNonresidue2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.LeastNonresidueBound 2 :=
  Ankeny.leastNonresidue_of_bach' (bach2_of_GRH hGRH)

/-- Miller's deterministic primality test under GRH, with witnesses `a ≤ 2 log² n`. -/
theorem miller2_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Miller.MillerStatement 2 :=
  Miller.miller_of_bach (bach2_of_GRH hGRH)

end LLS
