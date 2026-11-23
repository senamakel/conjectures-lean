import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Grosswald.Main

/-!
# Grosswald's conjecture, with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

The range `409 < p ≤ 2.5·10^15` remains the hypothesis `VerifiedUpTo` (the computation of
Cohen, Oliveira e Silva and Trudgian); above it the result is unconditional.
-/

theorem prime_primitive_root_large_unconditional :
    ∀ p : ℕ, p.Prime → 2500000000000000 < p → Grosswald.HasSmallPrimePrimitiveRoot p :=
  Grosswald.prime_primitive_root_of_GRH_large LFunction_ne_zero_of_half_lt_re

theorem grosswald_of_verified (hcomp : Grosswald.VerifiedUpTo 2500000000000000) :
    Grosswald.GrosswaldStatement :=
  Grosswald.grosswald_of_GRH LFunction_ne_zero_of_half_lt_re hcomp

#print axioms prime_primitive_root_large_unconditional
#print axioms grosswald_of_verified
