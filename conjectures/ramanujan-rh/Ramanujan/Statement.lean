import Schoenfeld.Statement

/-!
# Target statements (fixed; see the conjectures tracker, rule 3)

Ramanujan's prime-counting inequality (Ramanujan's notebooks; B. C. Berndt, *Ramanujan's
Notebooks, Part IV*, Springer 1994, pp. 112–114, as cited by Johnston 2022; the book itself was
not read):

  `π(x)² < (e x / log x) · π(x / e)`  for all sufficiently large `x`.

A. W. Dudek and D. J. Platt, *On solving a curious inequality of Ramanujan*, Exp. Math. 24
(2015), 289–294, arXiv:1407.1901, Theorem 1.3: "Assuming the Riemann Hypothesis, the largest
integer counter-example to inequality (1) is that at x = 38,358,837,682." `RamanujanStatement`
is the real-variable form, every real `x ≥ 38,358,837,683`, as D. R. Johnston, *Improving bounds
on prime counting functions by partial verification of the Riemann hypothesis*, Ramanujan J.
(2022), arXiv:2109.02249, Theorem 5.1, states its range. (Both sides are monotone in the right
way: `π(x)` is constant on `[n, n+1)` and the right-hand side is non-decreasing for `x > e`, so
the integer and real forms agree for `x ≥ 38,358,837,683`.)

`π(x)` is `π(⌊x⌋)` for real `x`, the convention of `Schoenfeld.PiBound`. No formal-conjectures
statement exists (searched at commit 9097e2f, 2026-11-26), so the statements are written here.
-/

namespace Ramanujan

open Real

/-- Ramanujan's inequality at the real number `x`:
`π(x)² < (e x / log x) · π(x / e)`, with `π(y) = π(⌊y⌋)`. -/
def RamanujanAt (x : ℝ) : Prop :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ) ^ 2 <
    Real.exp 1 * x / Real.log x * (Nat.primeCounting ⌊x / Real.exp 1⌋₊ : ℝ)

/-- Ramanujan's inequality for every real `x ≥ X₀`. -/
def RamanujanInequalityFrom (X₀ : ℝ) : Prop :=
  ∀ x : ℝ, X₀ ≤ x → RamanujanAt x

/-- Dudek–Platt's Theorem 1.3 (the conclusion; they prove it under RH): Ramanujan's inequality
for every real `x ≥ 38,358,837,683`. -/
def RamanujanStatement : Prop := RamanujanInequalityFrom 38358837683

/-- The finite range `[38,358,837,683, e⁴⁰]` (`e⁴⁰ ≈ 2.354·10¹⁷`), a cited hypothesis (tier H).
Johnston 2022, Theorem 5.1: "For 38,358,837,683 ≤ x ≤ exp(103), Ramanujan's inequality holds
unconditionally" (its proof uses Axler 2018 below `e⁴³` and the Platt–Trudgian verification of
RH to height `3·10¹²` above). Dudek–Platt 2015 cover `[10¹¹, 1.15·10¹⁶]` by computation
(Lemma 3.4) and `x ≥ 1.15·10¹⁶` under RH with `π(x) < li(x)` for `x ≤ 1.2·10¹⁷` (Lemma 3.2). -/
def RamanujanVerifiedRange : Prop :=
  ∀ x : ℝ, 38358837683 ≤ x → x ≤ Real.exp 40 → RamanujanAt x

end Ramanujan
