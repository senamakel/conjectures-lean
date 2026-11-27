import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Basic.Real.Basic

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

end MaxwellAffineSpan

#print axioms MaxwellAffineSpan.mem_affineSpan_of_force_zero
