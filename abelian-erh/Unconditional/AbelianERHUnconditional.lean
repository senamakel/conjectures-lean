import Main  -- leanprover-community/riemann-hypothesis: `LFunction_eq_zero_re`
import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation  -- same repository
-- same repository: `UpperTheory.V.CF.kwHom`, the Kronecker–Weber theorem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom
import AbelianERH

/-!
# ERH for abelian fields, with GRH and Kronecker–Weber supplied by riemann-hypothesis

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

* `abelianERH` closes both hypotheses of `abelianERH_of_GRH` in one line: `DirichletLZerosOnLine`
  with riemann-hypothesis's `LFunction_eq_zero_re` (its GRH claim), and `KroneckerWeberStatement`
  with its `UpperTheory.V.CF.kwHom` (Kronecker–Weber, a known theorem, no RH involved).
* `kroneckerWeber` alone is tier U₀.
* `cyclotomicERH` closes the hypothesis `DirichletLZerosOnLine` of `cyclotomicERH_of_GRH` with
  `LFunction_eq_zero_re`, in one line.
* `isDedekindZeta_continuedDedekindZeta` shows that `ERH.ExtendedRiemannHypothesis K` is not
  vacuous: the Tate-thesis continuation `GroundTheory.Global.continuedDedekindZeta K` of that
  repository is an `ERH.IsDedekindZeta K`. It uses no RH or GRH claim.
* `cyclotomic_continuedDedekindZeta_zero` combines the two for that continuation.

Nothing is copied from riemann-hypothesis (it has no licence); only its theorems are used.
-/

namespace AbelianERH.Unconditional

open AbelianERH

/-- The Tate-thesis continuation of `ζ_K` is a Dedekind zeta function in the sense of
formal-conjectures, for every number field `K`. -/
theorem isDedekindZeta_continuedDedekindZeta (K : Type*) [Field K] [NumberField K] :
    ERH.IsDedekindZeta K (GroundTheory.Global.continuedDedekindZeta K) :=
  ⟨GroundTheory.Global.differentiableOn_continuedDedekindZeta K,
    fun _ hs => GroundTheory.Global.continuedDedekindZeta_eq K hs⟩

/-- The Kronecker–Weber theorem, from riemann-hypothesis's class field theory. -/
theorem kroneckerWeber : KroneckerWeberStatement := UpperTheory.V.CF.kwHom

/-- ERH for every finite abelian extension of `ℚ`, given the Lean proof of GRH in
riemann-hypothesis (and its Kronecker–Weber theorem). -/
theorem abelianERH : AbelianERHStatement :=
  abelianERH_of_GRH LFunction_eq_zero_re UpperTheory.V.CF.kwHom

/-- The zeros of the continued `ζ_K` of an abelian field `K` in the critical strip lie on
`Re s = 1/2`. -/
theorem abelian_continuedDedekindZeta_zero (K : Type) [Field K] [NumberField K]
    [IsAbelianGalois ℚ K] (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hs : GroundTheory.Global.continuedDedekindZeta K s = 0) : s.re = 1 / 2 :=
  abelianERH K _ (isDedekindZeta_continuedDedekindZeta K) s h0 h1 hs

/-- ERH for every cyclotomic field, given the Lean proof of GRH in riemann-hypothesis. -/
theorem cyclotomicERH : CyclotomicERHStatement :=
  cyclotomicERH_of_GRH LFunction_eq_zero_re

/-- The zeros of the continued `ζ_{ℚ(ζ_N)}` in the critical strip lie on `Re s = 1/2`. -/
theorem cyclotomic_continuedDedekindZeta_zero (N : ℕ) [NeZero N] (K : Type) [Field K]
    [NumberField K] [IsCyclotomicExtension {N} ℚ K] (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hs : GroundTheory.Global.continuedDedekindZeta K s = 0) : s.re = 1 / 2 :=
  cyclotomicERH N K _ (isDedekindZeta_continuedDedekindZeta K) s h0 h1 hs

end AbelianERH.Unconditional

#print axioms AbelianERH.Unconditional.kroneckerWeber
#print axioms AbelianERH.Unconditional.abelianERH
#print axioms AbelianERH.Unconditional.abelian_continuedDedekindZeta_zero
#print axioms AbelianERH.Unconditional.cyclotomicERH
#print axioms AbelianERH.Unconditional.isDedekindZeta_continuedDedekindZeta
#print axioms AbelianERH.Unconditional.cyclotomic_continuedDedekindZeta_zero
