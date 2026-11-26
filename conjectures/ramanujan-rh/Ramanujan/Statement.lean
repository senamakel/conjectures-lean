import Schoenfeld.Statement

/-!
# Target statements (fixed; see the conjectures tracker, rule 3)

Ramanujan's prime-counting inequality (Ramanujan's notebooks; B. C. Berndt, *Ramanujan's
Notebooks, Part IV*, Springer 1994, p. 112–114 (unverified)):

  `π(x)² < (e x / log x) · π(x / e)`  for all sufficiently large `x`.

A. W. Dudek and D. J. Platt, *On solving a curious inequality of Ramanujan*, Exp. Math. 24
(2015), 289–294, arXiv:1407.1901, Theorem 1.3: under RH the inequality holds for every
`x ≥ 38,358,837,683`; the largest integer counterexample is `38,358,837,682`.

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

/-- The finite range `[38,358,837,683, e⁴⁰]` (`e⁴⁰ ≈ 2.35·10¹⁷`), a cited hypothesis (tier H):
the computations of Dudek–Platt 2015 (Lemma 3.4, with Platt–Trudgian's `π(x) < li(x)` for
`x ≤ 1.2·10¹⁷` in Lemma 3.2) and Johnston 2022 (Ramanujan J., Theorem 5.1, unconditional for
`38,358,837,683 ≤ x ≤ e¹⁰³`) cover it. -/
def RamanujanVerifiedRange : Prop :=
  ∀ x : ℝ, 38358837683 ≤ x → x ≤ Real.exp 40 → RamanujanAt x

end Ramanujan
