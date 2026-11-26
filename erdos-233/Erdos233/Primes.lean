import Erdos233.Basic

/-!
# Elementary facts about `p_n = nth Nat.Prime n` and the index blocks
-/

namespace Erdos233

open Nat

lemma nth_lt_of_lt_idx {n m : ℕ} (h : n < idx m) : nth Nat.Prime n < m :=
  Nat.nth_lt_of_lt_count h

lemma le_nth_of_idx_le {n m : ℕ} (h : idx m ≤ n) : m ≤ nth Nat.Prime n :=
  (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).1 h

lemma mem_block {x n : ℕ} (h : n ∈ block x) :
    x ≤ nth Nat.Prime n ∧ nth Nat.Prime n < 2 * x := by
  rw [Finset.mem_Ico] at h
  exact ⟨le_nth_of_idx_le h.1, nth_lt_of_lt_idx h.2⟩

lemma not_prime_between {n m : ℕ} (h1 : nth Nat.Prime n < m) (h2 : m < nth Nat.Prime (n + 1)) :
    ¬ m.Prime := by
  intro hm
  have e := Nat.nth_count hm
  rw [← e] at h1 h2
  rw [Nat.nth_lt_nth Nat.infinite_setOfPred_prime] at h1 h2
  omega

lemma nth_succ_le_two_mul (n : ℕ) : nth Nat.Prime (n + 1) ≤ 2 * nth Nat.Prime n := by
  have h0 : nth Nat.Prime n ≠ 0 := (Nat.prime_nth_prime n).ne_zero
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul _ h0
  have e := Nat.nth_count hq
  rw [← e] at hlt hle
  rw [Nat.nth_lt_nth Nat.infinite_setOfPred_prime] at hlt
  exact le_trans ((Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hlt) hle

lemma nth_le_nth_succ (n : ℕ) : nth Nat.Prime n ≤ nth Nat.Prime (n + 1) :=
  (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (Nat.le_succ n)

lemma primeGap_cast (n : ℕ) :
    (primeGap n : ℝ) = (nth Nat.Prime (n + 1) : ℝ) - nth Nat.Prime n := by
  unfold primeGap
  rw [Nat.cast_sub (nth_le_nth_succ n)]

lemma sum_Ico_primeGap (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (primeGap n : ℝ) = (nth Nat.Prime b : ℝ) - nth Nat.Prime a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Finset.sum_Ico_eq_sum_range, show a + k - a = k by omega]
  simp_rw [primeGap_cast, show ∀ i, a + i + 1 = a + (i + 1) from fun i => by ring]
  exact Finset.sum_range_sub (fun i => (nth Nat.Prime (a + i) : ℝ)) k

lemma sum_block_primeGap_le (x : ℕ) :
    ∑ n ∈ block x, (primeGap n : ℝ) ≤ 4 * x := by
  by_cases hab : idx x < idx (2 * x)
  · rw [sum_Ico_primeGap _ _ hab.le]
    have hb : idx (2 * x) - 1 ∈ block x := by
      rw [Finset.mem_Ico]; omega
    have h1 := (mem_block hb).2
    have h2 := nth_succ_le_two_mul (idx (2 * x) - 1)
    rw [show idx (2 * x) - 1 + 1 = idx (2 * x) by omega] at h2
    have h3 : (nth Nat.Prime (idx (2 * x)) : ℝ) ≤ 4 * x := by
      exact_mod_cast (by omega : nth Nat.Prime (idx (2 * x)) ≤ 4 * x)
    have h4 : (0 : ℝ) ≤ nth Nat.Prime (idx x) := Nat.cast_nonneg _
    linarith
  · rw [block, Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity

end Erdos233
