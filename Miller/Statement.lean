import Erdos985.Statement

/-!
# Miller's test is deterministic under GRH (target statements — do not change the definitions)

Miller (1976), with Bach's constant (Math. Comp. 55, 1990): under GRH every odd composite `n`
has a strong-pseudoprime witness `a ≤ 2 log² n`. The proof: the strong liars lie in a proper
subgroup of `(ℤ/n)ˣ`, and Bach's theorem gives a small unit outside any proper subgroup.

`BachSubgroupBound` is copied verbatim from the `ankeny-grh` repository so that the two
definitions are the same term; `Unconditional/` will connect them.
-/

namespace Miller

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- Copied verbatim from `Ankeny.BachSubgroupBound` (ankeny-grh). -/
def BachSubgroupBound (c : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ c * Real.log q ^ 2

/-- `n` is a strong probable prime to base `a`: writing `n - 1 = 2^s d` with `d` odd,
`a^d = 1` or `a^(2^r d) = -1` for some `r < s`, in `ZMod n`. -/
def IsStrongProbablePrime (n a : ℕ) : Prop :=
  let s := (n - 1).factorization 2
  let d := (n - 1) / 2 ^ s
  (a : ZMod n) ^ d = 1 ∨ ∃ r < s, (a : ZMod n) ^ (2 ^ r * d) = -1

/-- Every odd composite `n` has a witness `a ≤ c log² n`. -/
def MillerStatement (c : ℝ) : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → ¬ n.Prime →
    ∃ a : ℕ, 0 < a ∧ (a : ℝ) ≤ c * Real.log n ^ 2 ∧ ¬ IsStrongProbablePrime n a

/-- Unconditional group theory: the main deliverable of this repository. -/
theorem miller_of_bach {c : ℝ} (h : BachSubgroupBound c) : MillerStatement c := by
  sorry

/-- The resulting primality test is correct: for odd `n > 1`, `n` is prime iff it is a strong
probable prime to every base `1 ≤ a ≤ c log² n` with `a < n`. -/
theorem prime_iff_of_bach {c : ℝ} (h : BachSubgroupBound c) (n : ℕ) (hn : Odd n) (h1 : 1 < n) :
    n.Prime ↔ ∀ a : ℕ, 0 < a → a < n → (a : ℝ) ≤ c * Real.log n ^ 2 → IsStrongProbablePrime n a := by
  sorry

end Miller
