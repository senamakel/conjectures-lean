import Artin.SieveHalf

/-! # Artin's conjecture under Hooley's hypothesis, assembled from the two halves -/

namespace ArtinPrimitiveRootsConjecture

/--
**Artin's Conjecture on Primitive Roots**, first half, conditional on the Riemann hypothesis
for the Dedekind zeta functions of the fields $\mathbb{Q}(\zeta_k, a^{1/k})$, $k$ squarefree
[Ho67]. Same statement as `conditional_artin_primitive_roots.parts.i` in formal-conjectures.
-/
theorem conditional_artin_primitive_roots.parts.i (a : ℤ) (ha : ¬IsSquare a) (ha' : a ≠ -1)
    (h : HooleyHypothesis a) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime} := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  exact Artin.artin_of_effectiveKummerChebotarev a ha ha'
    (Artin.effectiveKummerChebotarev_of_hooley a ha0 h)

end ArtinPrimitiveRootsConjecture
