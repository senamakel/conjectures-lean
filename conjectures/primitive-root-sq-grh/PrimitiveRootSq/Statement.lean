import Erdos985.Statement

/-!
# Prime primitive roots modulo `p²` and modulo every power of `p`

Erdős Problem 985 (<https://www.erdosproblems.com/985>, formal-conjectures
`ErdosProblems/985.lean`) asks for a prime `q < p` that is a primitive root modulo the odd
prime `p`. The statements below ask for more: the same `q` must be a primitive root modulo
`p²`, and therefore modulo `p ^ k` for every `k ≥ 1`.

They are phrased like `Erdos985.Erdos985Statement` (which is formal-conjectures' `erdos_985`
verbatim): "`q` is a primitive root modulo `m`" is `orderOf (q : ZMod m) = φ(m)`, with
`φ(p) = p - 1`, `φ(p²) = p * (p - 1)` and `φ(p ^ k) = (p ^ k).totient`.

GRH for Dirichlet L-functions is `Erdos985.DirichletLNonvanishingRightOfHalf`, which
erdos-985 copies word for word from `src/Statements.lean` of
<https://github.com/leanprover-community/riemann-hypothesis>. We use that same constant, so
the riemann-hypothesis theorem `LFunction_ne_zero_of_half_lt_re` discharges it, and so do
not restate it here.

These definitions are the fixed targets: do not edit them to make a proof go through.
-/

namespace PrimitiveRootSq

/-- Every odd prime `p` has a prime `q < p` that is a primitive root modulo `p²`. -/
def PrimitiveRootSqStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod (p ^ 2)) = p * (p - 1)

/-- Every odd prime `p` has a prime `q < p` that is a primitive root modulo `p ^ k` for every
`k ≥ 1`. -/
def PrimitiveRootPowStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q : ℕ, q.Prime ∧ q < p ∧
    ∀ k : ℕ, 1 ≤ k → orderOf (q : ZMod (p ^ k)) = (p ^ k).totient

end PrimitiveRootSq
