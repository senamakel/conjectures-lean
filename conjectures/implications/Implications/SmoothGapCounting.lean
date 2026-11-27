import Mathlib

/-!
# Finite counting bounds for smooth integers in prime gaps

The first estimate in the elementary cutoff argument for Erdős #932: gaps of
size at least `B` among the first `N` consecutive prime gaps have total count
at most `p_N / B`. The proof is the disjoint-interval argument expressed by
telescoping the consecutive prime gaps.
-/

namespace Implications.SmoothGapCounting

/-- The `n`th prime, in the indexing convention used by formal-conjectures. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The gap between the `n`th prime and its successor. -/
noncomputable def primeGap (n : ℕ) : ℕ := primeAt (n + 1) - primeAt n

private theorem primeAt_strictMono : StrictMono primeAt := by
  intro a b hab
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime hab

/-- For every cutoff `B`, each of the first `N` gaps of size at least `B`
contributes at least `B` to the telescoping sum of all gaps. Consequently,
their count is at most the `N`th prime divided by `B` (in the cross-multiplied
form, which also covers `B = 0`). -/
theorem largeGapCount (N B : ℕ) :
    (B : ℝ) * (((Finset.range N).filter (fun r => B ≤ primeGap r)).card : ℝ) ≤
      (primeAt N : ℝ) := by
  let L := (Finset.range N).filter (fun r => B ≤ primeGap r)
  change (B : ℝ) * (L.card : ℝ) ≤ (primeAt N : ℝ)
  calc
    _ = ∑ _r ∈ L, (B : ℝ) := by simp [mul_comm]
    _ ≤ ∑ r ∈ L, (primeGap r : ℝ) :=
      Finset.sum_le_sum fun r hr => Nat.cast_le.mpr (Finset.mem_filter.mp hr).2
    _ ≤ ∑ r ∈ Finset.range N, (primeGap r : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) 
        fun r _ _ => Nat.cast_nonneg _
    _ = (primeAt N : ℝ) - (primeAt 0 : ℝ) := by
      have hcast (r : ℕ) : (primeGap r : ℝ) =
          (primeAt (r + 1) : ℝ) - (primeAt r : ℝ) := by
        rw [primeGap, Nat.cast_sub (primeAt_strictMono (by omega)).le]
      simp_rw [hcast]
      exact Finset.sum_range_sub (fun i => (primeAt i : ℝ)) N
    _ ≤ (primeAt N : ℝ) := by
      exact sub_le_self _ (by positivity)

end Implications.SmoothGapCounting
