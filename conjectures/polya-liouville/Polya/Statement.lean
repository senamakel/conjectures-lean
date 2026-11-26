import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Statements: Pólya's conjecture and von Sterneck's conjecture

No formal-conjectures statement exists for either conjecture (searched at formal-conjectures
`9097e2f`: Pólya, Liouville, Sterneck, `906150257`, `7725038629`). The definitions below are
written here, in the summation style of formal-conjectures'
`Wikipedia/ChowlaLiouvilleConjecture.lean` (`∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.liouville n`).

* **Pólya (1919).** `L(n) = ∑_{k=1}^{n} λ(k) ≤ 0` for every `n ≥ 2`, where `λ` is Liouville's
  function (`λ(k) = (-1)^Ω(k)`, so `λ(1) = 1`).
* **von Sterneck.** `|M(x)| < ½ √x` for every integer `x > 200`, where
  `M(x) = ∑_{k=1}^{x} μ(k)` is the Mertens function. `VonSterneckConjecture` is the real-valued
  form; `VonSterneckConjectureInt` is the same inequality squared, `4 M(x)² < x`.

These files are fixed: do not edit them to make a proof go through.
-/

namespace Polya

open ArithmeticFunction

/-- The summatory Liouville function `L(n) = ∑_{k=1}^{n} λ(k)`. -/
def liouvilleSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.liouville k

/-- The Mertens function `M(x) = ∑_{k=1}^{x} μ(k)`. -/
def mertens (x : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 x, ArithmeticFunction.moebius k

/-- Pólya's conjecture (1919): `L(n) ≤ 0` for every `n ≥ 2`. -/
def PolyaConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → liouvilleSum n ≤ 0

/-- Von Sterneck's conjecture: `|M(x)| < ½ √x` for every integer `x > 200`. -/
def VonSterneckConjecture : Prop :=
  ∀ x : ℕ, 200 < x → |(mertens x : ℝ)| < Real.sqrt x / 2

/-- Von Sterneck's conjecture squared and in integers: `4 M(x)² < x` for every `x > 200`. -/
def VonSterneckConjectureInt : Prop :=
  ∀ x : ℕ, 200 < x → 4 * mertens x ^ 2 < x

end Polya
