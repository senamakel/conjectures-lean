import Erdos985.Statement

/-!
# Sun's Conjecture 3.25 (first part), OEIS A243164

*Source.* Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641 (v12),
Conjecture 3.25 (2014-06-01); also in Proc. 7th China–Japan Seminar, Ser. Number Theory Appl. 11,
World Sci. 2015, 169–187. OEIS A243164, comment "Conjecture: (i) a(n) > 0 for all n > 6", where
`a(n)` is the number of primes `p < n` such that `p*n` is a primitive root modulo `prime(n)`.

*Statement (Sun).* Let `n > 6` be an integer. Then there is a prime `p < n` such that `pn` is a
primitive root modulo `p_n`, the `n`-th prime.

No formal-conjectures statement exists (checked 2026-11-26). Here `p_n = Nat.nth Nat.Prime (n - 1)`
(Mathlib's `Nat.nth` is 0-indexed, `Nat.nth Nat.Prime 0 = 2`), the prime is called `q` to keep
`p` for the modulus, and "primitive root modulo `p`" is `orderOf = p - 1` in `ZMod p`, as in
`Erdos985.Erdos985Statement`.

GRH enters as `Erdos985.DirichletLNonvanishingRightOfHalf`, copied verbatim in erdos-985 from
leanprover-community/riemann-hypothesis `src/Statements.lean`.
-/

namespace SunA243164

/-- The `n`-th prime, 1-indexed: `nthPrime 1 = 2`. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- **Sun's Conjecture 3.25 (first part), OEIS A243164.** For every `n > 6` there is a prime
`q < n` such that `q * n` is a primitive root modulo the `n`-th prime. -/
def SunA243164Statement : Prop :=
  ∀ n : ℕ, 6 < n → ∃ q : ℕ, q.Prime ∧ q < n ∧
    orderOf ((q * n : ℕ) : ZMod (Nat.nth Nat.Prime (n - 1))) = Nat.nth Nat.Prime (n - 1) - 1

end SunA243164
