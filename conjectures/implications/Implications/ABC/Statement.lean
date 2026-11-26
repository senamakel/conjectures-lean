import Mathlib

/-!
# Statements for the abc consequences

Every definition below is copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (Apache-2.0, © 2025 The Formal Conjectures Authors).
A theorem `foo (args) : P := by sorry` there becomes `def Foo : Prop := ∀ args, P` here, with
`args` and `P` unchanged.

* `ABC.radical`: `FormalConjectures/Wikipedia/ABC.lean`, `ABC.radical`.
* `ABC.ABCConjecture`: `FormalConjectures/Wikipedia/ABC.lean`, theorem `ABC.abc`.
* `Nat.Full`, `Nat.Powerful`: `FormalConjecturesForMathlib/Data/Nat/Full.lean`.
* `Erdos936.EventuallyNotPowerful` and the four `Erdos936.*` propositions:
  `FormalConjectures/ErdosProblems/936.lean`, theorems `erdos_936.variants.*`.
* `Erdos977.Factorial`: `FormalConjectures/ErdosProblems/977.lean`, theorem
  `erdos_977.variants.factorial`. That file uses `Nat.maxPrimeFac` from
  `FormalConjecturesForMathlib/Data/Nat/MaxPrimeFac.lean`. Our Mathlib pin already has a
  `Nat.maxPrimeFac` (with `getLastD n` in place of formal-conjectures' `if n = 1 then 1 else
  getLastI`), so the copied definition is named `Erdos977.fcMaxPrimeFac` and
  `Erdos977.fcMaxPrimeFac_eq` proves the two agree at every `n`.
-/

namespace ABC

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

/-- The abc conjecture, `ABC.abc` in formal-conjectures (`FormalConjectures/Wikipedia/ABC.lean`):
For every positive real number `ε`, there exist only finitely many triples `(a, b, c)` of coprime
positive integers, with `a + b = c`, such that `c > rad(abc)^(1+ε)`. -/
def ABCConjecture : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε),
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite

end ABC

namespace Nat

/--
A natural number $n$ is said to be $k$-full (or $k$-powerful) if for every prime factor $p$ of $n$,
the $k$-th power $p^k$ also divides $n$.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

/--
A [Powerful number](https://en.wikipedia.org/wiki/Powerful_number) is a natural number $n$ where
for every prime divisor $p$, $p^2$ divides $n$.
Powerful numbers are also known as "squareful", "square-full", or "$2$-full".
-/
abbrev Powerful : ℕ → Prop := (2).Full

end Nat

namespace Erdos936

open Filter Nat

/--
The predicate that `a n` is only powerful for finitely many `n`.
-/
def EventuallyNotPowerful (a : ℕ → ℕ) : Prop := atTop.Eventually (fun n => ¬ (a n).Powerful)

/-- `erdos_936.variants.two_pow_add_one`: Is $2^n + 1$ powerful for finitely many $n$? -/
def TwoPowAddOne : Prop :=
   EventuallyNotPowerful (2 ^ · + 1)

/-- `erdos_936.variants.two_pow_sub_one`: Is $2^n - 1$ powerful for finitely many $n$? -/
def TwoPowSubOne : Prop :=
   EventuallyNotPowerful (2 ^ · - 1)

/-- `erdos_936.variants.factorial_add_one`: Is $n! + 1$ powerful for finitely many $n$? -/
def FactorialAddOne : Prop :=
   EventuallyNotPowerful (·! + 1)

/-- `erdos_936.variants.factorial_sub_one`: Is $n! - 1$ powerful for finitely many $n$? -/
def FactorialSubOne : Prop :=
   EventuallyNotPowerful (·! - 1)

end Erdos936

namespace Erdos977

open Filter

/-- `Nat.maxPrimeFac` from `FormalConjecturesForMathlib/Data/Nat/MaxPrimeFac.lean`, renamed.

The greatest prime divisor of a natural number `n > 1`.

Takes the junk value `0` for `n = 0` and `1` for `n = 1`. -/
def fcMaxPrimeFac (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactorsList.getLastI

/-- The formal-conjectures definition agrees with Mathlib's `Nat.maxPrimeFac` everywhere. -/
theorem fcMaxPrimeFac_eq (n : ℕ) : fcMaxPrimeFac n = Nat.maxPrimeFac n := by
  unfold fcMaxPrimeFac Nat.maxPrimeFac
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · obtain rfl : n = 0 := by omega
      simp [List.getLastI]
    · have hne : n.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil n).2 (by omega)
      rw [List.getLastI_eq_getLast?_getD, List.getLast?_eq_getLast_of_ne_nil hne,
        List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne]
      rfl

/-- `erdos_977.variants.factorial`: is it true that $P(n!+1)/n\to\infty$? (`Nat.maxPrimeFac` is
Mathlib's, equal to formal-conjectures' by `fcMaxPrimeFac_eq`.) -/
def Factorial : Prop :=
    Tendsto (fun n : ℕ ↦ (Nat.maxPrimeFac (n.factorial + 1) : ℝ) / n) atTop atTop

end Erdos977
