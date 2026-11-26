import Mathlib

/-!
# Dickson's conjecture, Schinzel's hypothesis H and Bunyakovsky's conjecture: statements

Every definition below is copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `9097e2f`.
The two conditions are `def`s there and are copied as they stand. The three conjectures are
`theorem ... := by sorry` there; here each is the `Prop` that the theorem asserts, with the
binders of the source theorem kept in the same order and with the same types, so that
`type_of% Dickson.dickson_conjecture` in formal-conjectures is this `DicksonConjecture`.

The definitions live in the namespace `Implications.Dickson` so they cannot clash with copies of
the same definitions elsewhere in this package.
-/

open Polynomial

namespace Implications.Dickson

/-- Source: `FormalConjecturesForMathlib/Algebra/Polynomial/Basic.lean`, `BunyakovskyCondition`,
formal-conjectures `9097e2f`, verbatim.

**Bunyakovsky condition**
A condition on polynomials in the Schinzel and Bunyakovsky conjectures.
Holds for nonconstant irreducible polynomial with positive leading coefficient. -/
def BunyakovskyCondition (f : ℤ[X]) : Prop :=
  1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff

/-- Source: `FormalConjecturesForMathlib/Algebra/Polynomial/Basic.lean`, `SchinzelCondition`,
formal-conjectures `9097e2f`, verbatim.

**Schinzel condition**
A condition on sets of polynomials in the Schinzel and Bunyakovsky conjectures.
Holds if for every prime $p$ there exists a natural $n$ such that for every polynomial $f$ in the
set, $p$ does not divide $f(n)$. -/
def SchinzelCondition (fs : Finset ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ f ∈ fs, ¬(p : ℤ) ∣ f.eval (n : ℤ)

/-- Source: `FormalConjectures/Wikipedia/Dickson.lean`, `Dickson.dickson_conjecture`,
formal-conjectures `9097e2f` (research open). The statement of the theorem, verbatim:

**Dickson's conjecture**
If a finite set of linear integer forms $f_i(n) = a_i n+b_i$ satisfies Schinzel condition,
there exist infinitely many natural numbers $m$ such that $f_i(m)$ are primes for all $i$. -/
def DicksonConjecture : Prop :=
  ∀ (fs : Finset ℤ[X]) (_hfs : ∀ f ∈ fs, f.degree = 1 ∧ BunyakovskyCondition f)
    (_hfs' : SchinzelCondition fs), Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

/-- Source: `FormalConjectures/Wikipedia/Schinzel.lean`, `Schinzel.schinzel_conjecture`,
formal-conjectures `9097e2f` (research open). The statement of the theorem, verbatim:

**Schinzel conjecture (H hypothesis)**
If a finite set of polynomials $f_i$ satisfies both Schinzel and Bunyakovsky conditions,
there exist infinitely many natural numbers $n$ such that $f_i(n)$ are primes for all $i$. -/
def SchinzelConjecture : Prop :=
  ∀ (fs : Finset ℤ[X]) (_hfs : ∀ f ∈ fs, BunyakovskyCondition f)
    (_hfs' : SchinzelCondition fs), Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

/-- Source: `FormalConjectures/Wikipedia/Bunyakovsky.lean`, `Bunyakovsky.bunyakovsky_conjecture`,
formal-conjectures `9097e2f` (research open). The statement of the theorem, verbatim:

**Bunyakovsky conjecture**
If a polynomial $f$ over integers satisfies both Schinzel and Bunyakovsky conditions,
there exist infinitely many natural numbers $m$ such that $f(m)$ is prime. -/
def BunyakovskyConjecture : Prop :=
  ∀ (f : ℤ[X]),
    BunyakovskyCondition f ∧ SchinzelCondition {f} →
    Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}

end Implications.Dickson
