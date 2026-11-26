import Implications.PrimeGaps.Erdos382

/-!
# Granville's prime-gap conjecture and the conjectures it contradicts: statements

Every definition here is copied word for word from google-deepmind/formal-conjectures at commit
`9097e2f` (Apache-2.0), with the source file and declaration named at each definition. A theorem
with binders becomes a `Prop` whose binders are `∀`. `primeGap`, `CramerConjecture.cramerRatio`,
`CramerConjecture.StrictBound` and `Firoozbakht.FiroozbakhtConjecture` are the copies already in
`Implications.PrimeGaps.Erdos382`.

All four conjectures are `research open` in formal-conjectures. Nothing here proves or disproves
any of them.
-/

open Filter

set_option linter.dupNamespace false

namespace Implications.PrimeGaps

/-- Copied verbatim from formal-conjectures
`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`, `sup_primeGap` (commit `9097e2f`).

The maximal prime gap starting strictly below $x$, i.e.,
$\max_{p_n < x} (p_{n+1} - p_n)$ ($0$ when $x \le 2$). -/
noncomputable def sup_primeGap (x : ℝ) : ℕ :=
  (Finset.range (Nat.primeCounting' ⌈x⌉₊)).sup primeGap

namespace CramerConjecture

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/CramerConjecture.lean`,
`CramerConjecture.cramer_conjecture.variants.limsup_eq_one` (commit `9097e2f`,
`research open`), copied verbatim as a `Prop`.

**Cramér's Heuristic Limit-Superior Prediction**: $\limsup_{n \to \infty} g_n / (\log p_n)^2 =
1$. -/
def LimsupEqOne : Prop :=
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, cramerRatio n ≤ 1 + ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ᶠ n in Filter.atTop, 1 - ε ≤ cramerRatio n)

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/CramerConjecture.lean`,
`CramerConjecture.cramer_conjecture.variants.granville` (commit `9097e2f`, `research open`),
copied verbatim as a `Prop` (its binders `(c : ℝ) (hc : …)` become `∀`).

**Cramér–Granville Conjecture** [Gr95]: $\limsup_{n \to \infty} g_n / (\log p_n)^2 \ge
2 e^{-\gamma}$, stated without conditional `ℝ`-suprema as infinitely many $n$ satisfying
$\operatorname{cramerRatio}(n) \ge c$ for each $c < 2 e^{-\gamma}$. -/
def Granville : Prop :=
    ∀ (c : ℝ) (_hc : c < 2 * Real.exp (-Real.eulerMascheroniConstant)),
      ∃ᶠ n : ℕ in Filter.atTop, c ≤ cramerRatio n

end CramerConjecture

namespace MaximalPrimeGap

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/MaximalPrimeGap.lean`,
`MaximalPrimeGap.shanks_maximal_prime_gap_conjecture` (commit `9097e2f`, `research open`),
copied verbatim as a `Prop`.

Shanks's maximal prime gap conjecture (1964): the maximal prime gap $G(x)$ starting below $x$
satisfies $G(x) \sim (\log x)^2$ as $x \to \infty$. -/
def ShanksConjecture : Prop :=
    (fun x : ℝ => (sup_primeGap x : ℝ)) ~[Filter.atTop]
      (fun x : ℝ => (Real.log x) ^ 2)

end MaximalPrimeGap

namespace Firoozbakht

open Real

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/Firoozbakht.lean`,
`Firoozbakht.firoozbakht_conjecture_consequence` (commit `9097e2f`, `research solved`), copied
verbatim as a `Prop` (its binders become `∀`; `type_of% firoozbakht_conjecture` is
`FiroozbakhtConjecture`). `Prime` is `_root_.Prime`, as in the source.

The inequality $p_{n+1}-p_n < (\log p_n)^2-\log p_n$ holds for all $n>4$.
A consequence of Firuzbakht's conjecture. -/
def FiroozbakhtConsequence : Prop :=
    ∀ (n : ℕ) (_hn : 3 < n) (_P : FiroozbakhtConjecture),
      (n+1).nth Prime - n.nth Prime < (log (n.nth Prime))^2 - log (n.nth Prime)

end Firoozbakht

end Implications.PrimeGaps
