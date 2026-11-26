import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Abundant
import Robin     -- robin-rh, for `Robin.robin_of_RH` (its full build includes the verified-range sieve)

/-!
# The abundant-rh theorems, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs riemann-hypothesis's compiled modules and robin-rh's
full build (about 54 core-hours for its verified-range sieve). Run
`scripts/check-unconditional.sh`.

Nicolas' inequality comes from `Nicolas.nicolas_of_RH` inside the main-library theorems; Robin's
inequality is supplied here by `Robin.robin_of_RH riemannHypothesis`, the proof of robin-rh's
`robin_unconditional`.
-/

theorem solePlanat_unconditional : Abundant.SolePlanatStatement :=
  Abundant.solePlanat_of_RH riemannHypothesis

theorem extremelyAbundantInfinite_unconditional : Abundant.ExtremelyAbundantInfinite :=
  Abundant.extremelyAbundantInfinite_of_RH riemannHypothesis (Robin.robin_of_RH riemannHypothesis)

theorem fourOnlyExtraordinary_unconditional : Abundant.FourOnlyExtraordinary :=
  Abundant.fourOnlyExtraordinary_of_RH riemannHypothesis (Robin.robin_of_RH riemannHypothesis)

#print axioms solePlanat_unconditional
#print axioms extremelyAbundantInfinite_unconditional
#print axioms fourOnlyExtraordinary_unconditional
