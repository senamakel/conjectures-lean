import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation  -- leanprover-community/riemann-hypothesis
import Artin

/-!
# Hecke's continuation supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.

leanprover-community/riemann-hypothesis contains a formalisation of Tate's thesis
(`src/GroundTheory/GlobalFields/TateThesis/`). For the trivial Hecke character it gives the
completed Dedekind zeta function `completedDedekindZeta K` as `π^{-r₂} |d_K|^{s/2} Λ_P(s)` for a
Mathlib `WeakFEPair` `P` (`thetaPair`), its functional equation `completedDedekindZeta_one_sub`,
and a continuation `continuedDedekindZeta K` of `ζ_K` to `ℂ ∖ {1}`. It does not state a bound in
vertical strips; `Artin.Analytic.dedekindContinuation_of_weakFEPair` (main library, Mathlib only)
derives it from the FE-pair. Only Tate-thesis modules are imported here: none of the RH or GRH
claims of that repository is used, and nothing is copied from it (it has no licence).

What remains is `HooleyHypothesis a`, RH for `ζ_{K_k}` with `K_k = ℚ(ζ_k, a^{1/k})`, which that
repository does not prove (see the README, "This result stays conditional").
-/

namespace Artin.Unconditional

open Complex Artin.Analytic ArtinPrimitiveRootsConjecture

/-- Hecke's continuation, functional equation and strip bound for `ζ_K`, for every number field. -/
theorem dedekindContinuation (K : Type*) [Field K] [NumberField K] : DedekindContinuation K := by
  classical
  have hF := (1 : GroundTheory.Global.HeckeCharacter K).testFunction_mem
  have harch : GroundTheory.Global.archExponent
      (Classical.arbitrary (NumberField.InfinitePlace K)) (1 : GroundTheory.Global.HeckeCharacter K)
      = 0 :=
    GroundTheory.Global.archExponent_eq_of_forall
      GroundTheory.Global.HeckeCharacter.one_toIdele_eq_cpow _
  refine dedekindContinuation_of_weakFEPair K
    (GroundTheory.Global.thetaPair (Classical.arbitrary _) hF 1) rfl rfl
    ((Real.pi : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces K)⁻¹
    (GroundTheory.Global.completedDedekindZeta K) (GroundTheory.Global.continuedDedekindZeta K)
    ?_ (fun s h0 h1 => GroundTheory.Global.completedDedekindZeta_one_sub K h0 h1)
    ⟨GroundTheory.Global.differentiableOn_continuedDedekindZeta K,
      fun s hs => GroundTheory.Global.continuedDedekindZeta_eq K hs⟩ ?_
  · intro s _ _
    rw [GroundTheory.Global.completedDedekindZeta,
      GroundTheory.Global.HeckeCharacter.completedLFunction,
      GroundTheory.Global.HeckeCharacter.discrNormConductor_one, GroundTheory.Global.tateZeta,
      GroundTheory.Global.tateZetaAt_eq _ hF, harch]
    simp
  · intro s hs h1
    have h0 : s ≠ 0 := by rintro rfl; simp at hs
    have hγ := gammaFactorK_ne_zero (K := K) hs
    rw [completedOf, GroundTheory.Global.continuedDedekindZeta_of_ne_zero K h0,
      GroundTheory.Global.normalizedDedekindZeta, cpow_neg]
    unfold gammaFactorK at hγ ⊢
    have hD : ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2) ≠ 0 := by
      intro h; apply hγ; rw [h]; ring
    have hΓ : Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
        Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
      intro h; apply hγ; rw [mul_assoc, h, mul_zero]
    field_simp
    exact mul_div_cancel_left₀ _ hΓ

/-- The formal-conjectures statement `conditional_artin_primitive_roots.parts.i`, word for word:
Hooley's theorem from `HooleyHypothesis` alone, with Hecke's continuation discharged by the
Tate-thesis formalisation of the riemann-hypothesis repository. -/
theorem conditional_artin_primitive_roots_parts_i (a : ℤ) (ha : ¬IsSquare a) (ha' : a ≠ -1)
    (h : HooleyHypothesis a) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime} :=
  conditional_artin_primitive_roots.parts.i_of_continuation a ha ha' h
    fun _ _ => dedekindContinuation _

end Artin.Unconditional

#print axioms Artin.Unconditional.dedekindContinuation
#print axioms Artin.Unconditional.conditional_artin_primitive_roots_parts_i
