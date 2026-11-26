import GMUBinaryPartitions.Statement

/-!
# The series behind `b m n`

* `one_sub_mul_geomPow2`: `(1 − X^{2^i}) · ∑_j X^{2^i j} = 1`.
* `prod_mul_truncatedSeries`: `∏_{i<N} (1 − X^{2^i})^m · truncatedSeries m N = 1`.
* `coeff_truncatedSeries`: the coefficient of `X^n` is the same for every `N` with `n < 2^N`.
* `b_eq_coeff_of_mul_eq_one`: `b m n` is the `n`-th coefficient of the inverse of
  `∏_{i<N} (1 − X^{2^i})^m` for every such `N`.
-/

namespace GMU

open PowerSeries

theorem one_sub_mul_geomPow2 (i : ℕ) : (1 - X ^ (2 ^ i)) * geomPow2 i = 1 := by
  ext n
  have hd : 0 < 2 ^ i := Nat.pow_pos (by norm_num)
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', geomPow2, coeff_mk, coeff_one]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg hn]
    by_cases hle : 2 ^ i ≤ n
    · rw [if_pos hle, coeff_mk]
      have : 2 ^ i ∣ n ↔ 2 ^ i ∣ n - 2 ^ i := by
        rw [Nat.dvd_sub_iff_left hle (dvd_refl _)]
      by_cases h : 2 ^ i ∣ n
      · rw [if_pos h, if_pos (this.mp h), sub_self]
      · rw [if_neg h, if_neg (fun h' => h (this.mpr h')), sub_self]
    · rw [if_neg hle, if_neg, sub_zero]
      intro h
      exact hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h)

/-- `∑_j X^{2^i j} = 1 + X^{2^i} · ∑_j X^{2^i j}`. -/
theorem geomPow2_eq (i : ℕ) : geomPow2 i = 1 + X ^ (2 ^ i) * geomPow2 i := by
  have h := one_sub_mul_geomPow2 i
  calc geomPow2 i = (1 - X ^ (2 ^ i)) * geomPow2 i + X ^ (2 ^ i) * geomPow2 i := by ring
    _ = 1 + X ^ (2 ^ i) * geomPow2 i := by rw [h]

theorem prod_mul_truncatedSeries (m N : ℕ) :
    (∏ i ∈ Finset.range N, (1 - X ^ (2 ^ i) : PowerSeries ℤ) ^ m) * truncatedSeries m N = 1 := by
  rw [truncatedSeries, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← mul_pow, one_sub_mul_geomPow2, one_pow]

/-- Multiplying by a series `≡ 1 (mod X^d)` does not change the coefficients below `d`. -/
theorem coeff_mul_of_dvd_sub_one {A B : PowerSeries ℤ} {d n : ℕ} (hB : X ^ d ∣ B - 1)
    (hn : n < d) : coeff n (A * B) = coeff n A := by
  obtain ⟨E, hE⟩ := hB
  have : A * B = A + X ^ d * (A * E) := by
    rw [show B = 1 + X ^ d * E by rw [← hE]; ring]; ring
  rw [this, map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]

theorem coeff_truncatedSeries_succ (m N n : ℕ) (hn : n < 2 ^ N) :
    coeff n (truncatedSeries m (N + 1)) = coeff n (truncatedSeries m N) := by
  rw [truncatedSeries, Finset.prod_range_succ, ← truncatedSeries]
  refine coeff_mul_of_dvd_sub_one ?_ hn
  have h1 : X ^ (2 ^ N) ∣ geomPow2 N - 1 :=
    ⟨geomPow2 N, by conv_lhs => rw [geomPow2_eq N]
                    ring⟩
  calc X ^ (2 ^ N) ∣ geomPow2 N - 1 := h1
    _ ∣ geomPow2 N ^ m - 1 ^ m := sub_dvd_pow_sub_pow _ _ _
    _ = geomPow2 N ^ m - 1 := by rw [one_pow]

theorem coeff_truncatedSeries_le (m n : ℕ) {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) (hn : n < 2 ^ N₁) :
    coeff n (truncatedSeries m N₂) = coeff n (truncatedSeries m N₁) := by
  induction N₂, h using Nat.le_induction with
  | base => rfl
  | succ N hle ih =>
    rw [coeff_truncatedSeries_succ m N n
      (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hle)), ih]

/-- The coefficient of `X^n` in `∏_{i<N} (∑_j X^{2^i j})^m` is `b m n` whenever `n < 2^N`. -/
theorem coeff_truncatedSeries (m n N : ℕ) (hn : n < 2 ^ N) :
    coeff n (truncatedSeries m N) = b m n := by
  have hn' : n < 2 ^ min N (n + 1) := by
    rcases min_choice N (n + 1) with h | h <;> rw [h]
    · exact hn
    · exact Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))
  rw [b, coeff_truncatedSeries_le m n (min_le_left _ _) hn',
    coeff_truncatedSeries_le m n (min_le_right _ _) hn']

/-- `b m n` is the `n`-th coefficient of the inverse of `∏_{i<N} (1 − X^{2^i})^m`, for every `N`
with `n < 2^N`. -/
theorem b_eq_coeff_of_mul_eq_one (m n N : ℕ) (hn : n < 2 ^ N) (S : PowerSeries ℤ)
    (hS : (∏ i ∈ Finset.range N, (1 - X ^ (2 ^ i) : PowerSeries ℤ) ^ m) * S = 1) :
    coeff n S = b m n := by
  have : S = truncatedSeries m N := by
    have h2 := prod_mul_truncatedSeries m N
    calc S = (truncatedSeries m N * ∏ i ∈ Finset.range N, (1 - X ^ (2 ^ i) : PowerSeries ℤ) ^ m)
          * S := by rw [mul_comm (truncatedSeries m N), h2, one_mul]
      _ = truncatedSeries m N := by rw [mul_assoc, hS, mul_one]
  rw [this, coeff_truncatedSeries m n N hn]

end GMU
