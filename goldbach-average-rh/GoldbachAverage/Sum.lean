import GoldbachAverage.Statement

/-!
# The convolution identity

`S(N) = Σ_{a ≤ N} Λ(a) ψ(N − a)` and `Σ_{a ≤ N} Λ(a) (N − a) = Σ_{k < N} ψ(k)`.
-/

namespace GoldbachAverage

open ArithmeticFunction Chebyshev

lemma psi_natCast (M : ℕ) : ψ (M : ℝ) = ∑ m ∈ Finset.range (M + 1), (Λ m : ℝ) := by
  rw [psi_eq_sum_Icc, Nat.floor_natCast]
  congr 1
  ext m
  simp [Finset.mem_Icc, Finset.mem_range]

lemma goldbachWeight_zero : goldbachWeight 0 = 0 := by
  simp [goldbachWeight]

lemma goldbachWeight_eq_sum_range (n : ℕ) :
    goldbachWeight n = ∑ k ∈ Finset.range (n + 1), (Λ k : ℝ) * (Λ (n - k) : ℝ) := by
  unfold goldbachWeight
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => (Λ p.1 : ℝ) * (Λ p.2 : ℝ)) n

lemma goldbachSum_natCast (N : ℕ) :
    goldbachSum (N : ℝ) = ∑ n ∈ Finset.range (N + 1), goldbachWeight n := by
  unfold goldbachSum
  rw [Nat.floor_natCast, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    goldbachWeight_zero, zero_add]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

lemma goldbachSum_eq_convolution (N : ℕ) :
    goldbachSum (N : ℝ) = ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ψ ((N - a : ℕ) : ℝ) := by
  rw [goldbachSum_natCast]
  simp_rw [goldbachWeight_eq_sum_range, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_Ico_comm (f := fun i j => (Λ i : ℝ) * (Λ (j - i) : ℝ))]
  refine Finset.sum_congr rfl fun a ha => ?_
  have haN : a ≤ N := by simpa [Nat.lt_succ_iff] using ha
  rw [psi_natCast, ← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
  congr 1
  have : N + 1 - a = (N - a) + 1 := by omega
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- `Σ_{a ≤ N} Λ(a) (N − a) = Σ_{k < N} ψ(k)`. -/
lemma sum_vonMangoldt_mul_sub (N : ℕ) :
    ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ((N : ℝ) - a) =
      ∑ k ∈ Finset.range N, ψ (k : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ _ N, ← ih, Finset.sum_range_succ _ (N + 1), psi_natCast]
    have : ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * (((N + 1 : ℕ) : ℝ) - a) =
        ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) * ((N : ℝ) - a) +
          ∑ a ∈ Finset.range (N + 1), (Λ a : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast; ring
    rw [this]
    simp

end GoldbachAverage
