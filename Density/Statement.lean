import Mathlib

/-!
# The density hypothesis (target statements — do not change the definitions)

The deliverables are `DensityHypothesis.densityHypothesis_of_RH` and
`DensityHypothesis.guthMaynard_of_RH` (`Density/Main.lean`).

Everything below is copied word for word from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
at commit `86a2f58a4d7a3a0637d15d5b2ce627592b54b956` (Apache-2.0, see `NOTICE.md`):

* `Complex.zeroCountOn` and its two basic lemmas from
  [`FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean);
* `DensityHypothesis.zetaZeroCount` and the statements of
  `DensityHypothesis.density_hypothesis_zeta_zeros` (`research open` there) and
  `DensityHypothesis.guth_maynard_zero_density` (a known result, `sorry` there) from
  [`FormalConjectures/Wikipedia/DensityHypothesis.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/DensityHypothesis.lean).

The only changes are mechanical: the `module` / `public import` / `@[expose] public section`
header and the `@[category …, AMS …]` attributes (which come from `FormalConjecturesUtil`) are
dropped, and the statements of the theorems `density_hypothesis_zeta_zeros` and
`guth_maynard_zero_density`, which end in `sorry` there, become the bodies of the `Prop`s
`DensityHypothesis.Statement` and `DensityHypothesis.GuthMaynardStatement` here, with their binders
`(ε : ℝ) (hε : 0 < ε)` turned into `∀ ε : ℝ, 0 < ε →`.

For `1/2 ≤ σ ≤ 1` and `T ≥ 2`, `zetaZeroCount σ T` counts the zeros `ρ` of `ζ` with
multiplicity in `σ ≤ Re ρ ≤ 1`, `0 < Im ρ ≤ T`. The density hypothesis says
`N(σ, T) ≤ C_ε T^{2(1-σ)+ε}`, with `C_ε` uniform in `σ ∈ [1/2, 1]` and `T ≥ 2`.
-/

namespace Complex

/-- The multiplicity-weighted count of zeros of `f : ℂ → ℂ` in `S : Set ℂ`, summing
`analyticOrderNatAt f s` over `s ∈ S`. Points where `f s ≠ 0` or `f` is not analytic contribute
`0`. -/
noncomputable def zeroCountOn (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ s ∈ S, analyticOrderNatAt f s

theorem analyticOrderNatAt_eq_zero_of_ne_zero {f : ℂ → ℂ} {s : ℂ} (h : f s ≠ 0) :
    analyticOrderNatAt f s = 0 := by
  simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (.inr h)]

theorem zeroCountOn_eq_zero_of_forall_ne_zero {f : ℂ → ℂ} {S : Set ℂ}
    (h : ∀ s ∈ S, f s ≠ 0) : zeroCountOn f S = 0 :=
  finsum_mem_eq_zero_of_forall_eq_zero fun _ hs =>
    analyticOrderNatAt_eq_zero_of_ne_zero (h _ hs)

end Complex

namespace DensityHypothesis

/-- Multiplicity-weighted count $N(\sigma, T)$ of zeros of $\zeta(s)$ inside
$\{s \in \mathbb{C} \mid \sigma \le \operatorname{Re}(s) \le 1 \text{ and } 0 <
\operatorname{Im}(s) \le T\}$ (half the symmetric count $|\operatorname{Im}(s)| \le T$). -/
noncomputable abbrev zetaZeroCount (σ T : ℝ) : ℕ :=
  Complex.zeroCountOn riemannZeta
    {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T}

/-- Density Hypothesis: for every $\varepsilon > 0$, there exists $C > 0$ such that
$N(\sigma, T) \le C \, T^{2(1 - \sigma) + \varepsilon}$ for all $\frac{1}{2} \le \sigma \le 1$
and $T \ge 2$. -/
def Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε)

/-- Guth–Maynard zero-density bound (2024): for every $\varepsilon > 0$, there exists $C > 0$ such
that $N(\sigma, T) \le C \, T^{\frac{30}{13}(1 - \sigma) + \varepsilon}$ for all
$\frac{1}{2} \le \sigma \le 1$ and $T \ge 2$. -/
def GuthMaynardStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ ((30 / 13 : ℝ) * (1 - σ) + ε)

end DensityHypothesis
