import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
-- riemann-hypothesis: the class number formula `GlobalTheory.LFunction_one_and_mean_log_eta`
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import LLS

/-!
# The LLS results with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`. Each theorem closes the GRH hypothesis in one line.

`classNumberFormula` discharges the tier-H hypothesis `LLS.ClassNumberFormula` (Dirichlet's class
number formula, a theorem not involving RH) from riemann-hypothesis's
`GlobalTheory.LFunction_one_and_mean_log_eta`. That theorem also asks for an embedding
`σ : K →+* ℂ` and, for each ideal class, a point `τ c` of the upper half-plane representing it
(`IsIdealClassPoint`); the bridge supplies both, from Mathlib's `Nonempty (K →+* ℂ)` and the
repository's `exists_isIdealClassPoint`. Its `IsKroneckerChar χ` is, by definition, the
condition `∀ n, Odd n → χ n = J(−q | n)` of `LLS.ClassNumberFormula`, for every `q`, odd or
even; the same discharge serves the round-5 bounds (odd discriminants) and the round-6 bounds
`ClassNumberUpperBoundWith 5`, `ClassNumberLowerBoundWith 5` (every imaginary quadratic field).
-/

theorem leastNonresidueBelowLogSq_unconditional : LLS.LeastNonresidueBelowLogSq :=
  LLS.leastNonresidueBelowLogSq_of_GRH LFunction_ne_zero_of_half_lt_re

theorem bach_unconditional : Ankeny.BachSubgroupBound (11 / 4) :=
  LLS.bach_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastNonresidue_unconditional : Ankeny.LeastNonresidueBound (11 / 4) :=
  LLS.leastNonresidue_of_GRH LFunction_ne_zero_of_half_lt_re

theorem miller_unconditional : Miller.MillerStatement (11 / 4) :=
  LLS.miller_of_GRH LFunction_ne_zero_of_half_lt_re

theorem bach2_unconditional : Ankeny.BachSubgroupBound 2 :=
  LLS.bach2_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastNonresidue2_unconditional : Ankeny.LeastNonresidueBound 2 :=
  LLS.leastNonresidue2_of_GRH LFunction_ne_zero_of_half_lt_re

theorem miller2_unconditional : Miller.MillerStatement 2 :=
  LLS.miller2_of_GRH LFunction_ne_zero_of_half_lt_re

theorem l1UpperBoundWith_unconditional : LLS.L1UpperBoundWith 5 :=
  LLS.l1UpperBoundWith_of_GRH LFunction_ne_zero_of_half_lt_re

theorem l1LowerBoundWith_unconditional : LLS.L1LowerBoundWith 5 :=
  LLS.l1LowerBoundWith_of_GRH LFunction_ne_zero_of_half_lt_re

theorem classNumberFormula : LLS.ClassNumberFormula := by
  intro K _ _ q _ h2 hD hq χ hχ
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  choose τ hτ using fun c => GlobalTheory.exists_isIdealClassPoint h2 hD σ c
  exact (GlobalTheory.LFunction_one_and_mean_log_eta h2 hD hq hχ σ hτ).1

theorem classNumberUpperBoundOddWith_unconditional : LLS.ClassNumberUpperBoundOddWith 5 :=
  LLS.classNumberUpperBoundOddWith_of_GRH_of_formula LFunction_ne_zero_of_half_lt_re
    classNumberFormula

theorem classNumberLowerBoundOddWith_unconditional : LLS.ClassNumberLowerBoundOddWith 5 :=
  LLS.classNumberLowerBoundOddWith_of_GRH_of_formula LFunction_ne_zero_of_half_lt_re
    classNumberFormula

theorem classNumberUpperBoundWith_unconditional : LLS.ClassNumberUpperBoundWith 5 :=
  LLS.classNumberUpperBoundWith_of_GRH_of_formula LFunction_ne_zero_of_half_lt_re
    classNumberFormula

theorem classNumberLowerBoundWith_unconditional : LLS.ClassNumberLowerBoundWith 5 :=
  LLS.classNumberLowerBoundWith_of_GRH_of_formula LFunction_ne_zero_of_half_lt_re
    classNumberFormula

theorem l1UpperBound_unconditional : LLS.L1UpperBound :=
  LLS.Sharp.l1UpperBound_of_GRH LFunction_ne_zero_of_half_lt_re

theorem l1LowerBound_unconditional : LLS.L1LowerBound :=
  LLS.Sharp.l1LowerBound_of_GRH LFunction_ne_zero_of_half_lt_re

theorem classNumberUpperBound_unconditional : LLS.ClassNumberUpperBound :=
  LLS.Sharp.classNumberUpperBound_of_GRH_of_formula LFunction_ne_zero_of_half_lt_re
    classNumberFormula

theorem classNumberLowerBound_unconditional : LLS.ClassNumberLowerBound :=
  LLS.Sharp.classNumberLowerBound_of_GRH_of_formula LFunction_ne_zero_of_half_lt_re
    classNumberFormula

#print axioms leastNonresidueBelowLogSq_unconditional
#print axioms bach_unconditional
#print axioms leastNonresidue_unconditional
#print axioms miller_unconditional
#print axioms l1UpperBoundWith_unconditional
#print axioms l1LowerBoundWith_unconditional
#print axioms classNumberFormula
#print axioms classNumberUpperBoundOddWith_unconditional
#print axioms classNumberLowerBoundOddWith_unconditional
#print axioms classNumberUpperBoundWith_unconditional
#print axioms classNumberLowerBoundWith_unconditional
#print axioms bach2_unconditional
#print axioms leastNonresidue2_unconditional
#print axioms miller2_unconditional
#print axioms l1UpperBound_unconditional
#print axioms l1LowerBound_unconditional
#print axioms classNumberUpperBound_unconditional
#print axioms classNumberLowerBound_unconditional
