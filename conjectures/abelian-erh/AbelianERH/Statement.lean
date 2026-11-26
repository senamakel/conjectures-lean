import Mathlib

/-!
# The extended Riemann hypothesis for abelian number fields (target statements)

Do not change the definitions in this file to make a proof go through.

* `ERH.IsDedekindZeta` and `ERH.ExtendedRiemannHypothesis` are copied word for word from
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
  `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (Apache-2.0),
  `FormalConjectures/Millennium/RiemannHypothesis.lean`, namespace `ERH`. formal-conjectures states
  `ERH.extended_riemann_hypothesis` for every number field (open); it has no abelian version.
* `AbelianERH.DirichletLZerosOnLine` is copied word for word from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
  `src/Statements.lean` at commit `507a75d91d`, where it is the type of `LFunction_eq_zero_re`.
  It is GRH for every Dirichlet L-function, primitive or not, in the critical strip.
* `AbelianERH.KroneckerWeberStatement` is the type of `UpperTheory.V.CF.kwHom` in the same
  repository (file `.../GaloisLibrary/ClassFieldRamification/KwHom.lean`), the Kronecker–Weber
  theorem: every finite abelian extension of `ℚ` embeds in a cyclotomic field. It is a known
  theorem (Kronecker 1853, Weber 1886, Hilbert 1896), not an RH-type hypothesis.

The targets are `AbelianERHStatement` (every finite abelian `K/ℚ`) and, as the first stage,
`CyclotomicERHStatement` (every cyclotomic field `ℚ(ζ_N)`).
-/

namespace ERH

/-- `Z` is a Dedekind zeta function of the number field `K`: it is holomorphic away from $s = 1$
and agrees with the Dedekind zeta series of `K` on $\operatorname{Re} s > 1$, where that series
converges. Such a `Z` is uniquely determined on $\mathbb{C} \setminus \{1\}$.

Mathlib's `NumberField.dedekindZeta` is only the Dirichlet series. Outside
$\operatorname{Re} s > 1$ it takes the junk value $0$, so we quantify over continuations
instead. -/
def IsDedekindZeta (K : Type*) [Field K] [NumberField K] (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta K s

/-- The **Extended Riemann Hypothesis** for a number field $K$: every zero of (the analytic
continuation of) the Dedekind zeta function $\zeta_K$ in the critical strip
$0 < \operatorname{Re} s < 1$ has real part $\frac{1}{2}$. -/
def ExtendedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Z : ℂ → ℂ, IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → s.re = 1 / 2

end ERH

namespace AbelianERH

/-- GRH for all Dirichlet L-functions (any modulus, imprimitive characters included) in the
critical strip. Copied from riemann-hypothesis `src/Statements.lean`. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- The Kronecker–Weber theorem, in the form of riemann-hypothesis's `UpperTheory.V.CF.kwHom`. -/
def KroneckerWeberStatement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L],
    ∃ N : ℕ, 0 < N ∧ Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ)

/-- **Target.** ERH for every finite abelian extension of `ℚ`. -/
def AbelianERHStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K], ERH.ExtendedRiemannHypothesis K

/-- **Stage 1 target.** ERH for every cyclotomic field `ℚ(ζ_N)`. -/
def CyclotomicERHStatement : Prop :=
  ∀ (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K],
    ERH.ExtendedRiemannHypothesis K

end AbelianERH
