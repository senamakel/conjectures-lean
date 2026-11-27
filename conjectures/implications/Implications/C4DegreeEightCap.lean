import Mathlib.Algebra.Order.Chebyshev

/-!
# A degree-eight cap from C4 codegree moments

In a 42-vertex C4-free graph with all degrees at least six, let `k` be the
number of degree-eight vertices and let `a x` count their neighbors at an
outside vertex `x`.  The graph argument gives `∑ a = 8k` and
`∑ (a² - a) ≤ k(k - 1)`: each ordered pair of distinct degree-eight vertices
has at most one common neighbor.  Cauchy–Schwarz then rules out `k ≥ 8`.

This module formalizes the moment-to-cap reduction.  Its hypotheses are the
two codegree-counting conclusions, so it can be checked independently of the
graph-theoretic bridge that supplies them.
-/

namespace C4DegreeEightCap

/-- The first and second codegree moments for degree-eight vertices in a
42-vertex C4-free graph force their count to be at most seven.

Here `n` is the number of vertices outside the degree-eight set and `a x` is
the number of degree-eight neighbors of outside vertex `x`. -/
theorem count_le_seven_of_codegree_moments
    (k n : ℕ) (a : Fin n → ℝ)
    (hk : 0 < k)
    (hsize : n + k = 42)
    (hfirst : ∑ x, a x = 8 * (k : ℝ))
    (hsecond : ∑ x, (a x ^ 2 - a x) ≤ (k : ℝ) * ((k : ℝ) - 1)) :
    k ≤ 7 := by
  have hsumSq : ∑ x, a x ^ 2 ≤ (k : ℝ) * ((k : ℝ) + 7) := by
    have hsecond' := hsecond
    rw [← Finset.sum_sub_distrib] at hsecond'
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [hfirst] at hcs
  have hcs' : (8 * (k : ℝ)) ^ 2 ≤ (n : ℝ) * ((k : ℝ) * ((k : ℝ) + 7)) := by
    exact hcs.trans (mul_le_mul_of_nonneg_left hsumSq (Nat.cast_nonneg n))
  have hcancel : (k : ℝ) * (64 * (k : ℝ)) ≤
      (k : ℝ) * ((n : ℝ) * ((k : ℝ) + 7)) := by
    nlinarith [hcs']
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hlinear : 64 * (k : ℝ) ≤ (n : ℝ) * ((k : ℝ) + 7) :=
    (mul_le_mul_left hkpos).mp hcancel
  have hkn : (n : ℝ) + (k : ℝ) = 42 := by exact_mod_cast hsize
  have hk8 : ¬ 8 ≤ k := by
    intro hk8
    have hk8' : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk8
    nlinarith
  omega

end C4DegreeEightCap

#print axioms C4DegreeEightCap.count_le_seven_of_codegree_moments
