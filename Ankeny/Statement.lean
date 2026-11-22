import Erdos985.Statement

/-!
# Bach's theorem (target statements — do not change the definitions)

Bach, *Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990):
under GRH every proper subgroup of `(ℤ/q)ˣ` omits a residue below `2 log² q`. In particular
the least quadratic non-residue mod an odd prime `p` is at most `2 log² p` (Ankeny's theorem
with Bach's constant). Unconditionally only `p^{1/(4√e)+ε}` (Burgess) is known.
-/

namespace Ankeny

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- Every proper subgroup of `(ZMod q)ˣ` omits a unit whose least residue is `≤ c log² q`. -/
def BachSubgroupBound (c : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ c * Real.log q ^ 2

/-- The least quadratic non-residue mod an odd prime `p` is at most `c log² p`. -/
def LeastNonresidueBound (c : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ c * Real.log p ^ 2 ∧ ¬ IsSquare (n : ZMod p)

/-- Bach's theorem with Bach's constant: the main deliverable. -/
theorem bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : BachSubgroupBound 2 := by
  sorry

theorem leastNonresidue_of_bach {c : ℝ} (h : BachSubgroupBound c) : LeastNonresidueBound c := by
  sorry

theorem leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBound 2 :=
  leastNonresidue_of_bach (bach_of_GRH hGRH)

end Ankeny
