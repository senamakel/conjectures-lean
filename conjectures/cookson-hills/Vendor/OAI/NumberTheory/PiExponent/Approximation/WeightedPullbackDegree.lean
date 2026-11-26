import OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveIntrinsicCoefficientLaw
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface
import OAI.NumberTheory.PiExponent.Polynomials.GlobalPolynomialWeightedBound
import OAI.NumberTheory.PiExponent.Polynomials.WeightedHomogeneousSubstitution

namespace OAI

noncomputable section
namespace PiExponent.WeightedPullbackDegree
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetPolynomial PiExponent.AffineJetCoefficientFrame
open PiExponent.AffineJetCoefficientInterface
variable {K ι σ : Type} [Field K]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  WeightedCompactification.affineChartMap
  AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  ProjectiveO1.lineBundle ProjectiveO1.coordinateSection ProjectiveO1.scalars
  ProjectiveO1.coordinateCocycle PiExponentSeshadri.Projective.sectionsMorphism
  PiExponentSeshadri.Projective.CoordinateAtlas.morphism PiExponentSeshadri.Projective.atlasOfFramedSections
  ProjectiveO1.globalSectionChartPolynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv

theorem pullback_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
    (e : Frame (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (lineBundle (R := K) a))
    (s : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n)
    (p : MvPolynomial.homogeneousSubmodule σ K n)
    (hp : dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) (σ := σ) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s)) :
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient (affineChartMap (R := K) a z hz coordinate hcoordinate)
        (lineBundle (R := K) a) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ))
          (projectiveMonomialMap (R := K) a) n s)) := by
  -- Ported to Lean v4.36.0 / Mathlib fc4f59e5: the original proof went through
  -- `ProjectiveIntrinsicCoefficientLaw.intrinsicData` and the `rfl` lemmas
  -- `intrinsic_polynomial` / `intrinsic_ringEquiv`, which the kernel can no longer check in
  -- reasonable time on this pin. This proof feeds the same ambient data to
  -- `coefficient_bound` directly, with `coordinate_law` in place of `intrinsic_law`.
  let ev : MvPolynomial (ChartVariables z) K →+* MvPolynomial ι K :=
    (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
      MvPolynomial.monomial (a j.val) (1 : K))).toRingHom
  have hbound : SupportBound ρ ((n : ℝ) * B) (ev (ProjectiveGlobalPolynomials.coordinateChartPolynomial
      (X := ProjectiveO1.projectiveSpace K σ) (R := K) (σ := σ)
      (ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf (ProjectiveO1.coordinateSection (R := K) (σ := σ))
      (ProjectiveO1.scalars (R := K) (σ := σ)) (ProjectiveO1.coordinateSection_cover (R := K) (σ := σ))
      (Iso.refl (ProjectiveO1.projectiveSpace K σ))
      (ProjectiveO1.coordinate_sectionsMorphism_identity (R := K) (σ := σ)) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s))) := by
    have hp' := hp
    unfold ProjectiveO1.globalSectionChartPolynomial at hp'
    rw [← hp']
    change SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K)) (dehomogenize z p.val))
    rw [WeightedHomogeneousSubstitution.dehomogenize_substitution a z hz]
    exact WeightedHomogeneousSubstitution.supportBound_substitution ρ B a ha n p
  exact GlobalPolynomialWeightedBound.coefficient_bound
    (X := Proj (imageGrade (R := K) a)) (Y := ProjectiveO1.projectiveSpace K σ) (K := K) (ι := ι)
    (B := MvPolynomial (ChartVariables z) K)
    (ProjectiveO1.lineBundle (R := K) (σ := σ))
    (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate)
    (WeightedChartRingEvaluation.ambientOpen (R := K) z)
    (WeightedChartRingEvaluation.chartFactor (R := K) a z hz coordinate hcoordinate)
    (WeightedChartRingEvaluation.chartFactor_comp (R := K) a z hz coordinate hcoordinate) n
    (coordinatePowerFrame (ProjectiveO1.coordinateSection (R := K) (σ := σ) z) n)
    (WeightedChartRingEvaluation.ambientRingEquiv (R := K) z)
    (ProjectiveGlobalPolynomials.coordinateChartPolynomial
      (X := ProjectiveO1.projectiveSpace K σ) (R := K) (σ := σ)
      (ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf (ProjectiveO1.coordinateSection (R := K) (σ := σ))
      (ProjectiveO1.scalars (R := K) (σ := σ)) (ProjectiveO1.coordinateSection_cover (R := K) (σ := σ))
      (Iso.refl (ProjectiveO1.projectiveSpace K σ))
      (ProjectiveO1.coordinate_sectionsMorphism_identity (R := K) (σ := σ)) n z)
    (GlobalPolynomialCoefficientLaw.coordinate_law
      (ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf (ProjectiveO1.coordinateSection (R := K) (σ := σ))
      (ProjectiveO1.scalars (R := K) (σ := σ)) (ProjectiveO1.coordinateSection_cover (R := K) (σ := σ))
      (Iso.refl (ProjectiveO1.projectiveSpace K σ))
      (ProjectiveO1.coordinate_sectionsMorphism_identity (R := K) (σ := σ)) n z) ev
    (fun q => WeightedChartRingEvaluation.chartFactor_pullback (R := K) a z hz coordinate hcoordinate q)
    ρ ((n : ℝ) * B) e s hbound

end PiExponent.WeightedPullbackDegree
end

end OAI
