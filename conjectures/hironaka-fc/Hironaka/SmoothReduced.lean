import Mathlib

/-!
# Smooth over an integral base implies reduced

Mathlib (at this pin) has no lemma saying a scheme smooth over a field is reduced. We prove it
here: a smooth morphism is locally standard smooth, a standard smooth algebra is étale over a
polynomial ring, and an étale algebra over a domain `R` embeds (by flatness) into its base change
to `Frac R`, which is unramified over a field and hence reduced.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Hironaka

/-- An étale algebra over a domain is reduced. -/
theorem isReduced_of_etale_of_isDomain {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : IsReduced S := by
  let K := FractionRing R
  have : Algebra.FormallyUnramified K (K ⊗[R] S) := inferInstance
  have : Algebra.EssFiniteType K (K ⊗[R] S) := inferInstance
  have := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] S)
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- A scheme smooth over an integral scheme is reduced. -/
theorem isReduced_of_smooth_of_isIntegral {Y S : Scheme.{u}} (g : Y ⟶ S) [Smooth g]
    [IsIntegral S] : IsReduced Y := by
  have H : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨U, hU, V, hV, hyV, e, hst⟩ := Smooth.exists_isStandardSmooth g y
    have : Nonempty U := ⟨⟨g y, e hyV⟩⟩
    obtain ⟨n, φ, -, hφ⟩ := hst.exists_etale_mvPolynomial
    algebraize [φ]
    have hred : _root_.IsReduced Γ(Y, V) :=
      isReduced_of_etale_of_isDomain (R := MvPolynomial (Fin n) Γ(S, U))
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyV⟩ : V)
    have := hV.isLocalization_stalk ⟨y, hyV⟩
    exact isReduced_localizationPreserves (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl _ hred
  exact isReduced_of_isReduced_stalk Y

end Hironaka
