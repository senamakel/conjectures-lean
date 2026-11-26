import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Grosswald.Main

/-!
# Grosswald's conjecture, given the riemann-hypothesis repository's proof of GRH

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`. The proof of GRH in leanprover-community/riemann-hypothesis has
not been independently verified.
-/

theorem grosswald : Grosswald.GrosswaldStatement :=
  Grosswald.grosswald_of_GRH LFunction_ne_zero_of_half_lt_re

theorem prime_primitive_root_large_unconditional :
    ∀ p : ℕ, p.Prime → 10000000000000 < p → Grosswald.HasSmallPrimePrimitiveRoot p :=
  Grosswald.prime_primitive_root_of_GRH_above LFunction_ne_zero_of_half_lt_re

#print axioms grosswald
#print axioms prime_primitive_root_large_unconditional
