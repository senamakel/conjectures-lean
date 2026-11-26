import Hironaka.Statement
import Hironaka.SmoothReduced

/-!
# Hironaka's theorem from a smooth modification
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Hironaka

/-- Hironaka's theorem in the formal-conjectures form, given a smooth modification that is an
isomorphism over the smooth locus. -/
theorem hironaka_of_smoothModification (h : SmoothModification.{u}) : HironakaStatement.{u} := by
  intro k _ _ X sX _ _ _ _
  obtain ⟨Y, π, hsm, hprop, hiso, hdense⟩ := h k X sX
  let U := sX.smoothLocus
  have hUd : Dense (U : Set X) := sX.dense_smoothLocus_of_perfectField
  have hUne : Nonempty U := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy⟩ := hUd.nonempty
    exact ⟨⟨y, hy⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let e : (π ⁻¹ᵁ U).toScheme ≅ U.toScheme := asIso (π ∣_ U)
  have : Nonempty (π ⁻¹ᵁ U).toScheme := ⟨e.inv.base (Classical.arbitrary _)⟩
  have : IsIntegral (π ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion e.hom
  have hirr : IrreducibleSpace Y := by
    have h1 : IsIrreducible (Set.range (π ⁻¹ᵁ U).ι.base) := by
      rw [← Set.image_univ]
      exact ((irreducibleSpace_def _).mp inferInstance).image _
        (π ⁻¹ᵁ U).ι.continuous.continuousOn
    rw [Scheme.Opens.range_ι] at h1
    have h2 := h1.closure
    rw [Scheme.Hom.coe_preimage, hdense.closure_eq] at h2
    exact (irreducibleSpace_def _).mpr (by simpa using h2)
  have : IsReduced Y := isReduced_of_smooth_of_isIntegral (π ≫ sX)
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  refine ⟨Y, π, this, hprop, hsm, ?_⟩
  refine ⟨⟨π ⁻¹ᵁ U, hdense, U, hUd, e⟩, ?_⟩
  simp [Scheme.PartialIso.IsOver, e]
