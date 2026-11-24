import Mathlib

/-!
# Selberg 1943: primes in almost all short intervals (target statements: do not change)

Source: A. Selberg, *On the normal density of primes in small intervals, and the difference
between consecutive primes*, Arch. Math. Naturvid. **47** (6) (1943), 87–105. Under RH:

* almost all intervals `(x, x + Φ(x) log² x]` contain a prime, for any `Φ(x) → ∞`
  (as quoted by Huang–Liu–Rudnick, arXiv:1903.04005, and by Cully-Hugill–Dudek,
  arXiv:2206.00433, who state it for increasing `h = o(x)` with `h / log² x → ∞`);
* in the same range, `π(x + h) − π(x) ~ h / log x` for almost all `x` (as quoted by Maier's
  foreword to *Irregularities in the Distribution of Prime Numbers*, Springer 2018, with the
  hypothesis `y / log² x → ∞`).

The paper itself was not read; the statements follow these secondary sources.

"Almost all" is Selberg's: the exceptional set has measure `o(X)` (Cully-Hugill–Dudek cite
footnote 4, p. 161 of the paper). We measure it inside `[X, 2X]`; summing dyadic blocks gives
the same statement inside `[1, X]`. formal-conjectures has no statement of this theorem
(searched 2026-11-24), so these definitions are this repository's own.

`RiemannHypothesis` is not mentioned here: the theorems take Mathlib's `RiemannHypothesis` as
an explicit hypothesis.
-/

open Filter MeasureTheory Topology

namespace Erdos233

/-- The `x ∈ [X, 2X]` for which `(x, x + h x]` contains no prime. -/
def primelessSet (h : ℝ → ℝ) (X : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + h x}

/-- **Selberg 1943, existence form.** If `h(x) / log² x → ∞`, the set of `x ∈ [X, 2X]` with no
prime in `(x, x + h(x)]` has measure `o(X)`. No monotonicity or `h = o(x)` is assumed: a
larger `h` only makes the statement easier. -/
def SelbergAlmostAllStatement : Prop :=
  ∀ h : ℝ → ℝ, Tendsto (fun x => h x / Real.log x ^ 2) atTop atTop →
    Tendsto (fun X => (volume (primelessSet h X)).toReal / X) atTop (𝓝 0)

/-- The `x ∈ [X, 2X]` at which `π(x + h x) − π(x)` is not within a factor `1 ± ε` of
`h x / log x`. -/
def selbergBadSet (h : ℝ → ℝ) (ε X : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Icc X (2 * X) ∧
    ε * (h x / Real.log x) <
      |((Nat.primeCounting ⌊x + h x⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊) - h x / Real.log x|}

/-- **Selberg 1943, asymptotic form.** If `h` is increasing, `h(x) / log² x → ∞` and
`h(x) = o(x)`, then `π(x + h) − π(x) ~ h / log x` for almost all `x`. -/
def SelbergAsymptoticStatement : Prop :=
  ∀ h : ℝ → ℝ, Monotone h → Tendsto (fun x => h x / Real.log x ^ 2) atTop atTop →
    Tendsto (fun x => h x / x) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → Tendsto (fun X => (volume (selbergBadSet h ε X)).toReal / X) atTop (𝓝 0)

end Erdos233
