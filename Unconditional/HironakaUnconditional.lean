import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing  -- leanprover-community/riemann-hypothesis
import Hironaka

/-!
# Hironaka's theorem, with the smooth modification supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.

leanprover-community/riemann-hypothesis proves `FunctorialResolution.functorialResolutionCharZero`
(functorial resolution of singularities in characteristic 0, by a sequence of blowups). Its first
conjunct, `IsResolutionRuleCharZero`, gives for every reduced scheme `X` of finite type over a field
of characteristic 0 the top `Y` of a blowup tower with `Smooth (topMap ≫ f)`, `IsProper topMap`,
`IsIso (morphismRestrict topMap f.smoothLocus)` and a dense preimage of the smooth locus. That is
`Hironaka.SmoothModification` with the tower forgotten. Only that one module is imported: no RH or
GRH theorem is used, and nothing is copied from the repository (it has no licence).
-/

namespace Hironaka.Unconditional

/-- The input of `hironaka_of_smoothModification`, from `IsResolutionRuleCharZero`. -/
theorem smoothModification : SmoothModification.{u} := fun k _ _ X f _ _ _ =>
  have h := FunctorialResolution.functorialResolutionCharZero.{u}
  let R := h.choose
  ⟨(R k X f).top, (R k X f).topMap, ((h.choose_spec.1 k X f).1), (h.choose_spec.1 k X f).2.1,
    (h.choose_spec.1 k X f).2.2.1, (h.choose_spec.1 k X f).2.2.2.1⟩

/-- Hironaka's theorem in the formal-conjectures form, with no hypothesis left. -/
theorem resolution_of_singularities_of_charZero : HironakaStatement.{u} :=
  hironaka_of_smoothModification smoothModification

end Hironaka.Unconditional

#print axioms Hironaka.Unconditional.smoothModification
#print axioms Hironaka.Unconditional.resolution_of_singularities_of_charZero
