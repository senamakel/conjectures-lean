import Mathlib

/-!
# Li's criterion (target statements — do not change the definitions)

Copied word for word from google-deepmind/formal-conjectures,
[`FormalConjectures/Paper/RiemannHypothesisEquivalents.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Paper/RiemannHypothesisEquivalents.lean)
at commit `86a2f58a4d7a3a0637d15d5b2ce627592b54b956` (Apache-2.0, © 2026 The Formal Conjectures
Authors). Only the file header changes: `module` / `public import FormalConjecturesUtil` /
`@[expose] public section` become `import Mathlib`, and the `@[category …]` attributes, which
come from `FormalConjecturesUtil`, are dropped. The two theorems there,

```
theorem li_criterion : RiemannHypothesis ↔ ∀ n > 0, 0 < lambda n
theorem li_criterion_rhs {n : ℕ} (hn : 0 < n) : 0 < lambda n
```

are recorded below as the `Prop`s `LiCriterion` and `LiCriterionRHS` (same statements, bound
`n` universally quantified). The deliverable is `RiemannHypothesis.li_criterion_rhs_of_RH`
(`LiCriterion/Main.lean`), i.e. `RiemannHypothesis → LiCriterionRHS`, the forward direction of
`li_criterion`.

`RiemannHypothesis` is Mathlib's statement.
-/

open Real

namespace RiemannHypothesis

/-- The nontrivial zeros of the Riemann zeta function with positive imaginary part. Since the
nontrivial zeros are closed under complex conjugation, these determine all nontrivial zeros. -/
def nontrivialPosZeros : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ riemannZeta z = 0}

/-- The numbers
$$
  \lambda_n := \sum_{\rho}\left(1 - \left(1 - \frac{1}{\rho}\right)^n\right)
$$
appearing in Li's criterion, summing over the nontrivial zeros $\rho$ of the
Riemann zeta function.

This is a real number because nontrivial zeros always come in conjugate pairs.
Note that, as stated, the sum is only conditionally convergent, however it is absolutely convergent
when taken in conjugate pairs, since $1/\rho + 1/\bar\rho = 2\Re\rho/|\rho|^2$. Hence we sum
over the zeros with positive imaginary part with summand `2 * (_).re`, which makes the unordered
sum `∑'` meaningful. -/
noncomputable def lambda (n : ℕ) : ℝ := ∑' ρ : nontrivialPosZeros, 2 * (1 - (1 - 1 / ρ.1) ^ n).re

/-- formal-conjectures `li_criterion` (`research solved`), as a `Prop`. -/
def LiCriterion : Prop := RiemannHypothesis ↔ ∀ n > 0, 0 < lambda n

/-- formal-conjectures `li_criterion_rhs` (`research open`), as a `Prop`. -/
def LiCriterionRHS : Prop := ∀ {n : ℕ} (_hn : 0 < n), 0 < lambda n

end RiemannHypothesis
