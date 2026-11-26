import Mathlib

/-!
# Erdős Problem 770 (iii): target statements (do not change the definitions)

The definition of `h` and the body of `Erdos770Part3` are copied word for word from
formal-conjectures, `FormalConjectures/ErdosProblems/770.lean`, at commit
`86a2f58a4d7a3a0637d15d5b2ce627592b54b956`
(<https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/ErdosProblems/770.lean>),
Apache-2.0, Copyright 2026 The Formal Conjectures Authors.

In formal-conjectures the statement reads `theorem erdos_770.parts.iii : <body>` with the
`@[category research open, question, AMS 11]` attribute; that machinery needs
`FormalConjecturesUtil`, so here the body is stated as a `Prop` (`Erdos770Part3`).

`ExplicitBound` is not from formal-conjectures: it is the explicit form
`h(n) ≤ max(P(n), ⌈C log² n⌉)` proved in this repo, with `P n` the same `sSup` that appears in
`erdos_770.parts.iii`.
-/

open Set ENat Filter

namespace Erdos770

/-- Let $h n$ be the minimal number such that $2 ^ n - 1, \dots, h(n) ^ n - 1$
are collectively coprime. -/
noncomputable def h (n : ℕ) : ℕ∞ := sInf {m | 2 < m ∧
  ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}

/-- Is it true that if `p` is the greatest prime such that `p - 1 ∣ n` and `p > n ^ ε`, then
`h n = p`?

This is the body of formal-conjectures' `erdos_770.parts.iii`, copied verbatim. -/
def Erdos770Part3 : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop,
    let p := sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}
    p > (n : ℝ) ^ (ε : ℝ) → h n = p

/-- `P n` is the greatest prime `p` with `p - 1 ∣ n`: the same `sSup` as in
`erdos_770.parts.iii`. For `n ≥ 1` the set contains `2` and is bounded by `n + 1`. -/
noncomputable def P (n : ℕ) : ℕ := sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}

/-- The explicit bound `h n ≤ max (P n) ⌈C (log n)²⌉` for every `n ≥ n₀`. -/
def ExplicitBound (C : ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, h n ≤ ((max (P n) ⌈C * Real.log n ^ 2⌉₊ : ℕ) : ℕ∞)

end Erdos770
