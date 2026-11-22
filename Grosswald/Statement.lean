import Erdos985.Statement

/-!
# Grosswald's conjecture (target statements — do not change the definitions)

Grosswald (1981): the least primitive root `g(p)` satisfies `g(p) < √p - 2` for every prime
`p > 409`. McGown, Treviño and Trudgian (arXiv:1508.05182, Theorem 1) prove under GRH that
the least *prime* primitive root is below `√p - 2` for `p > 2.5·10^15`; Cohen, Oliveira e Silva
and Trudgian verified `g(p) < √p - 2` computationally for `409 < p ≤ 2.5·10^15`.
-/

namespace Grosswald

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- `p` has a primitive root `g` with `0 < g < √p - 2`. -/
def HasSmallPrimitiveRoot (p : ℕ) : Prop :=
  ∃ g : ℕ, 0 < g ∧ (g : ℝ) < Real.sqrt p - 2 ∧ orderOf (g : ZMod p) = p - 1

/-- `p` has a prime primitive root `q < √p - 2`. -/
def HasSmallPrimePrimitiveRoot (p : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ (q : ℝ) < Real.sqrt p - 2 ∧ orderOf (q : ZMod p) = p - 1

/-- Grosswald's conjecture. -/
def GrosswaldStatement : Prop :=
  ∀ p : ℕ, p.Prime → 409 < p → HasSmallPrimitiveRoot p

/-- The finite range covered by an external computation (Cohen–Oliveira e Silva–Trudgian). -/
def VerifiedUpTo (B : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → 409 < p → p ≤ B → HasSmallPrimitiveRoot p

/-- MTT Theorem 1, GRH part: the main deliverable. -/
theorem prime_primitive_root_of_GRH_large (hGRH : DirichletLNonvanishingRightOfHalf) :
    ∀ p : ℕ, p.Prime → 2500000000000000 < p → HasSmallPrimePrimitiveRoot p := by
  sorry

theorem grosswald_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (hcomp : VerifiedUpTo 2500000000000000) : GrosswaldStatement := by
  sorry

end Grosswald
