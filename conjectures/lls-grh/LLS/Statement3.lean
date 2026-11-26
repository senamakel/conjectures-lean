import Mathlib

/-!
# Target statements, round 6: class-number bounds for every imaginary quadratic field (fixed
once written; do not edit to make a proof go through)

Source: Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic
non-residue and related problems*, Math. Comp. 84 (2015), 2391–2412, arXiv:1309.3595,
Corollary 1.3 (`LLS.ClassNumberUpperBound`, `LLS.ClassNumberLowerBound` in
`LLS/Statement2.lean`). These are the same bounds with the paper's lower-order terms replaced by
an additive constant `C`, and the lower bound's leading constant `π/(12e^γ)` by `1/(2πe^γ)`:

* `h(−q) ≤ (2e^γ/π) √q (log log q + C)`;
* `h(−q) ≥ √q / (2πe^γ (log log q + C))`.

As in Corollary 1.3 they are stated for every number field `K` of degree `2` with
`NumberField.discr K = −q`, `q ≥ 10¹⁰`, with no further hypothesis on `q`: every negative
fundamental discriminant, odd or even, is the discriminant of such a field. The round-5
statements `LLS.ClassNumberUpperBoundOddWith`, `LLS.ClassNumberLowerBoundOddWith`
(`LLS/ClassNumber.lean`) also assumed `q ≡ 3 (mod 4)` and `Squarefree q`.
-/

namespace LLS

open Real NumberField Module

/-- Upper bound of LLS Corollary 1.3's shape with additive constant `C`, for every imaginary
quadratic field of discriminant `−q`, `q ≥ 10¹⁰`. -/
def ClassNumberUpperBoundWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      (classNumber K : ℝ) ≤ 2 * exp eulerMascheroniConstant / π * √q * (log (log q) + C)

/-- Lower bound of LLS Corollary 1.3's shape (leading constant `1/(2πe^γ)`, LLS: `π/(12e^γ)`)
with additive constant `C`, for every imaginary quadratic field of discriminant `−q`,
`q ≥ 10¹⁰`. -/
def ClassNumberLowerBoundWith (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      √q / (2 * π * exp eulerMascheroniConstant * (log (log q) + C)) ≤ classNumber K

end LLS
