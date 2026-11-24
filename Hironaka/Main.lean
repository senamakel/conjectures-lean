import Hironaka.Statement

/-!
# Hironaka's theorem from a smooth modification
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Hironaka

/-- Hironaka's theorem in the formal-conjectures form, given a smooth modification that is an
isomorphism over the smooth locus. -/
theorem hironaka_of_smoothModification (h : SmoothModification.{u}) : HironakaStatement.{u} := by
  sorry

end Hironaka
