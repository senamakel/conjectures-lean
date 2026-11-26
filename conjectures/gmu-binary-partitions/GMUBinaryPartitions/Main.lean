import GMUBinaryPartitions.Values

/-!
# Conjecture 5.6 of Gawron–Miska–Ulas is false

Each `…_fails_at_…` theorem is the negation of one instance of `GMUConjecture56`, written
exactly as the instance reads (`b (2^m − 1) (2^(k+1) n) ≡ b (2^m − 1) (2^(k−1) n)
[ZMOD 2^(4⌊(k+1)/2⌋ − 2)]` with `n = 1`).
-/

namespace GMU

/-- `m = 1, k = 3, n = 1`: `b₁(16) − b₁(4) = 32`, not divisible by `2^6`. -/
theorem gmu_conjecture_5_6_fails_at_m1_k3 :
    ¬ b (2 ^ 1 - 1) (2 ^ (3 + 1) * 1) ≡ b (2 ^ 1 - 1) (2 ^ (3 - 1) * 1)
      [ZMOD 2 ^ (4 * ((3 + 1) / 2) - 2)] := by
  show ¬ b 1 16 ≡ b 1 4 [ZMOD 2 ^ 6]
  rw [b_1_16, b_1_4, Int.ModEq]; norm_num

/-- `m = 1, k = 5, n = 1`: `b₁(64) − b₁(16) = 1792 = 2^8 · 7`, not divisible by `2^10`. -/
theorem gmu_conjecture_5_6_fails_at_m1_k5 :
    ¬ b (2 ^ 1 - 1) (2 ^ (5 + 1) * 1) ≡ b (2 ^ 1 - 1) (2 ^ (5 - 1) * 1)
      [ZMOD 2 ^ (4 * ((5 + 1) / 2) - 2)] := by
  show ¬ b 1 64 ≡ b 1 16 [ZMOD 2 ^ 10]
  rw [b_1_64, b_1_16, Int.ModEq]; norm_num

/-- `m = 3, k = 5, n = 1`: `b₇(64) − b₇(16) = 346264414943104`, of 2-adic valuation `7 < 10`. -/
theorem gmu_conjecture_5_6_fails_at_m3 :
    ¬ b (2 ^ 3 - 1) (2 ^ (5 + 1) * 1) ≡ b (2 ^ 3 - 1) (2 ^ (5 - 1) * 1)
      [ZMOD 2 ^ (4 * ((5 + 1) / 2) - 2)] := by
  show ¬ b 7 64 ≡ b 7 16 [ZMOD 2 ^ 10]
  rw [b_7_64, b_7_16, Int.ModEq]; norm_num

/-- `m = 4, k = 6, n = 1`: `b₁₅(128) − b₁₅(32)` has 2-adic valuation `8 < 10`. -/
theorem gmu_conjecture_5_6_fails_at_m4 :
    ¬ b (2 ^ 4 - 1) (2 ^ (6 + 1) * 1) ≡ b (2 ^ 4 - 1) (2 ^ (6 - 1) * 1)
      [ZMOD 2 ^ (4 * ((6 + 1) / 2) - 2)] := by
  show ¬ b 15 128 ≡ b 15 32 [ZMOD 2 ^ 10]
  rw [b_15_128, b_15_32, Int.ModEq]; norm_num

/-- `m = 5, k = 7, n = 1`: `b₃₁(256) − b₃₁(64)` has 2-adic valuation `9 < 14`. -/
theorem gmu_conjecture_5_6_fails_at_m5 :
    ¬ b (2 ^ 5 - 1) (2 ^ (7 + 1) * 1) ≡ b (2 ^ 5 - 1) (2 ^ (7 - 1) * 1)
      [ZMOD 2 ^ (4 * ((7 + 1) / 2) - 2)] := by
  show ¬ b 31 256 ≡ b 31 64 [ZMOD 2 ^ 14]
  rw [b_31_256, b_31_64, Int.ModEq]; norm_num

/-- **Conjecture 5.6 of Gawron–Miska–Ulas is false** (witness `m = 1`, `k = 3`, `n = 1`). -/
theorem gmu_conjecture_5_6_false : ¬ GMUConjecture56 := fun h =>
  gmu_conjecture_5_6_fails_at_m1_k3 (h 1 one_pos 1 3 (by norm_num))

/-- The conjecture fails for every `m ∈ {1, 3, 4, 5}`: for each of them some instance is false. -/
theorem gmu_conjecture_5_6_fails_for_m_1_3_4_5 :
    ∀ m ∈ ({1, 3, 4, 5} : Finset ℕ), ∃ n k : ℕ, m + 2 ≤ k ∧
      ¬ b (2 ^ m - 1) (2 ^ (k + 1) * n) ≡ b (2 ^ m - 1) (2 ^ (k - 1) * n)
        [ZMOD 2 ^ (4 * ((k + 1) / 2) - 2)] := by
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨1, 3, by norm_num, gmu_conjecture_5_6_fails_at_m1_k3⟩
  · exact ⟨1, 5, by norm_num, gmu_conjecture_5_6_fails_at_m3⟩
  · exact ⟨1, 6, by norm_num, gmu_conjecture_5_6_fails_at_m4⟩
  · exact ⟨1, 7, by norm_num, gmu_conjecture_5_6_fails_at_m5⟩

end GMU
