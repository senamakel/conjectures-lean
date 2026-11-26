import Mathlib

/-!
# Artin's primitive root conjecture under Hooley's hypothesis (target statement)

Do not change the definitions in this file. They are copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`c8dd64f723c3aa2a953011c6c951014694540432` (Apache-2.0):

* `Set.partialDensity`, `Set.HasDensity` from `FormalConjecturesForMathlib/Data/Set/Density.lean`;
* `IsDedekindZeta`, `DedekindZetaRH`, `HooleyHypothesis`, `S`, `ArtinConstant` from
  `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`.

The target is that file's theorem `conditional_artin_primitive_roots.parts.i`, proved as
`Artin.Unconditional.conditional_artin_primitive_roots_parts_i` in
`Unconditional/ArtinUnconditional.lean`; the main library proves it with Hecke's continuation as
an extra hypothesis (`Artin/MainContinuation.lean`). Hooley (1967), *On Artin's conjecture*, J. reine angew. Math. 225,
209–220.
-/

open Filter
open scoped Topology Nat

namespace Set

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace ArtinPrimitiveRootsConjecture

/-- `Z` is a Dedekind zeta function of the number field `K`: it is holomorphic away from $s = 1$
and agrees with the Dedekind zeta series of `K` on $\operatorname{Re} s > 1$, where that series
converges. Such a `Z` is uniquely determined on $\mathbb{C} \setminus \{1\}$. -/
def IsDedekindZeta (K : Type*) [Field K] [NumberField K] (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta K s

/-- The **Riemann hypothesis for the Dedekind zeta function** $\zeta_K$ of a number field $K$:
every zero of (the analytic continuation of) $\zeta_K$ in the critical strip
$0 < \operatorname{Re} s < 1$ has real part $\frac{1}{2}$. -/
def DedekindZetaRH (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Z : ℂ → ℂ, IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → s.re = 1 / 2

open Polynomial in
/-- **Hooley's hypothesis** for $a$: the Riemann hypothesis holds for the Dedekind zeta function
of the Kummer field $\mathbb{Q}(\zeta_k, a^{1/k})$, the splitting field of $X^k - a$ over
$\mathbb{Q}$, for every squarefree $k$. This is the hypothesis under which Hooley [Ho67] proved
Artin's conjecture. -/
def HooleyHypothesis (a : ℤ) : Prop :=
  ∀ k : ℕ, Squarefree k →
    letI := NumberField.of_module_finite ℚ (X ^ k - C (a : ℚ)).SplittingField
    DedekindZetaRH (X ^ k - C (a : ℚ)).SplittingField

/-- Let $S(a)$ be the set of primes such that $a$ is a primitive root modulo $p$. -/
abbrev S (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ orderOf (a : ZMod p) = (p-1 : ℕ)}

/--
**Artin's Constant** is defined to be the product
$$\prod_{p\ \text{prime}} \left(1 - \frac{1}{p(p - 1)}\right)$$.
-/
noncomputable def ArtinConstant : ℝ :=
  ∏' p : Nat.Primes, (1 - 1 / (p * (p - 1)) : ℝ)

end ArtinPrimitiveRootsConjecture
