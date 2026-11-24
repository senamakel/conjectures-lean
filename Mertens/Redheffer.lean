import Mertens.Statement

/-!
# Redheffer's determinant `det R_n = M(n)` (tier D)

Let `V_{ij} = μ(j/i)` if `i ∣ j` and `0` otherwise (1-indexed). `V` is upper triangular with
`1` on the diagonal, so `det V = 1`. For a column `k ≥ 2`, `R_{jk} = [j ∣ k]`, so
`(V R)_{ik} = ∑_{i ∣ j ∣ k} μ(j/i) = [i = k]` by Möbius inversion
(`moebius_mul_coe_zeta`). Column `1` of `R` is all ones, so `(V R)_{11} = ∑_{j ≤ n} μ(j) = M(n)`.
Hence `V R` is lower triangular with diagonal `(M(n), 1, …, 1)`, and
`det R = det (V R) = M(n)`.
-/

namespace Mertens

open Matrix ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- The Möbius matrix: entry `(i, j)` (1-indexed) is `μ(j/i)` if `i ∣ j`, else `0`. -/
def moebiusMat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then μ (((j : ℕ) + 1) / ((i : ℕ) + 1)) else 0

lemma sum_divisors_moebius (q : ℕ) : ∑ d ∈ q.divisors, μ d = if q = 1 then 1 else 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f q) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply] at this
  rw [this, ArithmeticFunction.one_apply]

/-- `∑_{i ∣ b ∣ c} μ(b/i) = [i = c]`. -/
lemma sum_dvd_moebius {a c : ℕ} (ha : 0 < a) (hc : 0 < c) :
    ∑ b ∈ c.divisors, (if a ∣ b then μ (b / a) else 0) = if a = c then 1 else 0 := by
  by_cases hac : a ∣ c
  · obtain ⟨q, rfl⟩ := hac
    have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
    rw [← Finset.sum_filter]
    have key : ∑ b ∈ (a * q).divisors with a ∣ b, μ (b / a) = ∑ d ∈ q.divisors, μ d := by
      refine Finset.sum_nbij' (fun b => b / a) (fun d => a * d) ?_ ?_ ?_ ?_ ?_
      · intro b hb
        simp only [Finset.mem_filter, Nat.mem_divisors] at hb ⊢
        obtain ⟨⟨hbd, -⟩, e, rfl⟩ := hb
        rw [Nat.mul_div_cancel_left e ha]
        exact ⟨Nat.dvd_of_mul_dvd_mul_left ha hbd, hq.ne'⟩
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
        exact ⟨⟨mul_dvd_mul_left a hd.1, by positivity⟩, dvd_mul_right a d⟩
      · intro b hb
        simp only [Finset.mem_filter] at hb
        exact Nat.mul_div_cancel' hb.2
      · intro d _
        exact Nat.mul_div_cancel_left d ha
      · intro b _
        rfl
    rw [key, sum_divisors_moebius]
    by_cases hq1 : q = 1
    · subst hq1; simp
    · rw [if_neg hq1, if_neg]
      intro h
      apply hq1
      have : a * 1 = a * q := by rw [mul_one]; exact h
      exact (Nat.eq_of_mul_eq_mul_left ha this).symm
  · rw [Finset.sum_eq_zero, if_neg]
    · rintro rfl; exact hac dvd_rfl
    · intro b hb
      rw [if_neg]
      intro hab
      exact hac (hab.trans (Nat.dvd_of_mem_divisors hb))

/-- A sum over `Fin n` of a function supported on divisors of `c ≤ n` is a divisor sum. -/
lemma sum_fin_dvd {n c : ℕ} (hc : 0 < c) (hcn : c ≤ n) (h : ℕ → ℤ) :
    ∑ j : Fin n, (if ((j : ℕ) + 1) ∣ c then h ((j : ℕ) + 1) else 0) =
      ∑ b ∈ c.divisors, h b := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if (j + 1) ∣ c then h (j + 1) else 0) n,
    ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun j => j + 1) (fun b => b - 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors] at hj ⊢
    exact ⟨hj.2, hc.ne'⟩
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors] at hb ⊢
    have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb.1 hc
    have hbc : b ≤ c := Nat.le_of_dvd hc hb.1
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel hb0]
    exact hb.1
  · intro j _
    simp
  · intro b hb
    simp only [Nat.mem_divisors] at hb
    have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb.1 hc
    omega
  · intro j _
    rfl

/-- `(V R)_{ik} = [i = k]` for columns `k ≥ 2` (index `k ≠ 0`). -/
lemma moebiusMat_mul_redheffer_of_ne {n : ℕ} (i k : Fin n) (hk : (k : ℕ) ≠ 0) :
    (moebiusMat n * redheffer n) i k = if i = k then 1 else 0 := by
  rw [Matrix.mul_apply]
  have hrw : ∀ j : Fin n, moebiusMat n i j * redheffer n j k =
      if ((j : ℕ) + 1) ∣ ((k : ℕ) + 1) then
        (if ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then μ (((j : ℕ) + 1) / ((i : ℕ) + 1)) else 0)
      else 0 := by
    intro j
    simp only [moebiusMat, redheffer, hk, false_or]
    split_ifs <;> simp
  simp_rw [hrw]
  rw [sum_fin_dvd (h := fun b => if ((i : ℕ) + 1) ∣ b then μ (b / ((i : ℕ) + 1)) else 0)
    (by omega) (by omega)]
  rw [sum_dvd_moebius (by omega) (by omega)]
  simp only [Nat.add_right_cancel_iff, Fin.val_inj]

lemma moebiusMat_upper (n : ℕ) : (moebiusMat n).IsUpperTriangular := by
  intro i j hij
  simp only [moebiusMat]
  rw [if_neg]
  intro h
  have := Nat.le_of_dvd (by omega) h
  have : (j : ℕ) < i := hij
  omega

lemma det_moebiusMat (n : ℕ) : (moebiusMat n).det = 1 := by
  rw [det_of_isUpperTriangular (moebiusMat_upper n)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [moebiusMat]

lemma moebiusMat_mul_redheffer_lower (n : ℕ) :
    (moebiusMat n * redheffer n).IsLowerTriangular := by
  intro i k hik
  have hik' : (i : ℕ) < k := hik
  rw [moebiusMat_mul_redheffer_of_ne i k (by omega), if_neg]
  intro h
  rw [h] at hik'
  exact lt_irrefl _ hik'

/-- **Redheffer (1977)**: `det R_n = M(n)` for `n ≥ 1`. -/
theorem det_redheffer (n : ℕ) (hn : 1 ≤ n) : (redheffer n).det = mertens n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := det_mul (moebiusMat (m + 1)) (redheffer (m + 1))
  rw [det_moebiusMat, one_mul,
    det_of_isLowerTriangular _ (moebiusMat_mul_redheffer_lower (m + 1)), Fin.prod_univ_succ] at h
  rw [← h]
  have hsucc : ∀ i : Fin m, (moebiusMat (m + 1) * redheffer (m + 1)) i.succ i.succ = 1 := by
    intro i
    rw [moebiusMat_mul_redheffer_of_ne _ _ (by simp), if_pos rfl]
  simp only [hsucc, Finset.prod_const_one, mul_one]
  rw [Matrix.mul_apply]
  have h0 : ∀ j : Fin (m + 1), moebiusMat (m + 1) 0 j * redheffer (m + 1) j 0 = μ ((j : ℕ) + 1) := by
    intro j
    simp [moebiusMat, redheffer]
  simp_rw [h0]
  rw [mertens, Nat.floor_natCast,
    Fin.sum_univ_eq_sum_range (fun j => μ (j + 1)) (m + 1), Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun j => μ j) 0 (m + 1) 1]
  rfl

end Mertens
