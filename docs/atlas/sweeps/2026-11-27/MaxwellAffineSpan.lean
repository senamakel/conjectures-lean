import Mathlib.LinearAlgebra.AffineSpace.Independent
import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

open scoped BigOperators

namespace MaxwellAffineSpan

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- A vanishing weighted force for affinely independent sites gives an affine
combination of the sites. All weights may have either sign. -/
theorem mem_affineSpan_of_force_zero (a : ι → E) (w : ι → ℝ) (x : E)
    (ha : AffineIndependent ℝ a) (hw : ∃ i, w i ≠ 0)
    (hforce : ∑ i, w i • (x -ᵥ a i) = 0) :
    x ∈ affineSpan ℝ (Set.range a) := by
  let total := ∑ i, w i
  have htotal : total ≠ 0 := by
    intro hz
    have he := Finset.sum_smul_const_vsub_eq_neg_weightedVSub
      Finset.univ w a x hz
    rw [hforce, eq_comm, neg_eq_zero] at he
    obtain ⟨i, hi⟩ := hw
    exact hi ((affineIndependent_iff_of_fintype ℝ a).1 ha w hz he i)
  let u (i : ι) := total⁻¹ * w i
  have hu : ∑ i, u i = 1 := by
    simp only [u, ← Finset.mul_sum]
    exact inv_mul_cancel₀ htotal
  have hscaled : ∑ i, u i • (x -ᵥ a i) = 0 := by
    simp only [u, mul_smul, ← Finset.smul_sum, hforce, smul_zero]
  have he := Finset.sum_smul_const_vsub_eq_vsub_affineCombination
    Finset.univ u a x hu
  rw [hscaled] at he
  have hx := vsub_eq_zero_iff_eq.mp he.symm
  rw [hx]
  exact affineCombination_mem_affineSpan hu a

open Arxiv.«2607.27197» InnerProductSpace
open scoped Gradient RealInnerProductSpace

abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Differentiate a single Coulomb term away from its source. -/
private theorem coulomb_hasGradient (q : ℝ) {a x : E3} (hne : x ≠ a) :
    HasGradientAt (fun y : E3 => q / dist y a)
      ((-q / ‖x - a‖ ^ 3) • (x - a)) x := by
  have hn : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hs := ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : E3 => ‖y - a‖)
      (‖x - a‖⁻¹ • innerSL ℝ (x - a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp
      <;> norm_num
  have hderiv := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hderiv using 1
  · funext y
    simp [dist_eq_norm, div_eq_mul_inv]
  · ext v
    simp [toDual_apply_apply, inner_smul_left, div_eq_mul_inv, smul_smul]
    field_simp [hn]
    <;> simp
    <;> ring

/-- Every equilibrium of three noncollinear charges lies in their plane.
The theorem uses the registry's exact equilibrium definition. -/
theorem equilibrium_mem_plane (q : Fin 3 → ℝ) (a : Fin 3 → E3)
    (ha : AffineIndependent ℝ a) (hq : ∀ i, q i ≠ 0)
    {x : E3} (hx : x ∈ equilibria q a) : x ∈ affineSpan ℝ (Set.range a) := by
  let w (i : Fin 3) := -q i / ‖x - a i‖ ^ 3
  have hne (i : Fin 3) : x ≠ a i := fun h => hx.1 ⟨i, h.symm⟩
  have hd : HasGradientAt (potential q a) (∑ i, w i • (x - a i)) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    unfold potential
    rw [map_sum]
    exact HasFDerivAt.fun_sum fun i _ => (coulomb_hasGradient (q i) (hne i)).hasFDerivAt
  apply mem_affineSpan_of_force_zero a w x ha
  · exact ⟨0, div_ne_zero (neg_ne_zero.mpr (hq 0))
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne 0))))⟩
  · exact hd.gradient.symm.trans hx.2

end MaxwellAffineSpan

#print axioms MaxwellAffineSpan.mem_affineSpan_of_force_zero

#print axioms MaxwellAffineSpan.equilibrium_mem_plane
