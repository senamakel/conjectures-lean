import Erdos985

/-!
# Target statements for this project

Fixed once written (see the conjectures tracker, rule 3).

* `TernaryGoldbachStatement` is the body of `TernaryGoldbachConjecture.ternaryGoldbach` in
  google-deepmind/formal-conjectures (`FormalConjectures/Wikipedia/GoldbachConjecture.lean`,
  commit `86a2f58a4d7a3a0637d15d5b2ce627592b54b956`), copied verbatim with its binders turned
  into a `∀`.
* `TernaryGoldbachUpTo`, `BinaryGoldbachUpTo` are the finite ranges this repository checks.
* `ZinovievTheorem` is the analytic half of Deshouillers–Effinger–te Riele–Zinoviev (1997), the
  large-`n` theorem of D. Zinoviev, *On Vinogradov's constant in Goldbach's ternary problem*,
  J. Number Theory 65 (1997) 334–358: under GRH, every odd `n > 10²⁰` is a sum of three primes.
  It is a cited hypothesis (tier H): it is not proved here.
* The GRH hypothesis is `Erdos985.DirichletLNonvanishingRightOfHalf`, which erdos-985 copied
  verbatim from leanprover-community/riemann-hypothesis (`src/Statements.lean`).
-/

namespace Goldbach

open Erdos985

/-- **Ternary Goldbach** (formal-conjectures `TernaryGoldbachConjecture.ternaryGoldbach`):
every odd integer greater than `5` is a sum of three primes (a prime may be used more than
once). -/
def TernaryGoldbachStatement : Prop :=
  ∀ (n : ℕ) (_hn : 5 < n) (_hn_odd : Odd n),
    ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-- Ternary Goldbach for the odd `n` with `5 < n ≤ N`. -/
def TernaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ (n : ℕ), 5 < n → Odd n → n ≤ N →
    ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-- Binary Goldbach for the even `n` with `2 < n ≤ N`. -/
def BinaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ (n : ℕ), 2 < n → Even n → n ≤ N → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- **Zinoviev's theorem** (1997), the analytic half of DETZ, as a cited hypothesis: GRH
implies that every odd `n > 10²⁰` is a sum of three primes. -/
def ZinovievTheorem : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (n : ℕ), 10 ^ 20 < n → Odd n →
      ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

end Goldbach
