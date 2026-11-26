import BachSorenson.Checker
import BachSorensonCheck2

/-!
# Soundness of the finite check for the constant `2`

`checkRange2 N lo n = true` implies: for every `q ∈ [lo, lo + n)` with `q ≥ 2` and every `a`
coprime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ bound2 q < 2 (q log q)²`. The proof is
that of `BachSorenson.Checker.exists_prime_of_checkRange`, with `bound2` for `bound`.
-/

namespace BachSorenson.Checker

theorem exists_prime_of_checkRange2 {N lo n : ℕ} (h : checkRange2 N lo n = true) {q : ℕ}
    (hq1 : lo ≤ q) (hq2 : q < lo + n) (hq : 2 ≤ q) {a : ℕ} (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ p ≤ bound2 q := by
  unfold checkRange2 at h
  have hq' := List.all_eq_true.1 h q (List.mem_range'_1.2 ⟨hq1, hq2⟩)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hq'
  rcases hq' with hlt | hchk
  · omega
  unfold checkQ2 at hchk
  have hq0 : 0 < q := by omega
  have ha' := List.all_eq_true.1 hchk (a % q) (List.mem_range.2 (Nat.mod_lt a hq0))
  have hg : Nat.gcd (a % q) q = 1 := by
    rw [← Nat.gcd_rec q a, Nat.gcd_comm]; exact ha
  simp only [hg, bne_self_eq_false, Bool.false_or] at ha'
  obtain ⟨k, hk1, hk2⟩ := findFrom_sound _ _ _ _ _ ha'
  refine ⟨a % q + k * q, prime_of_marked hk1, ?_, by omega⟩
  unfold Nat.ModEq
  rw [Nat.add_mul_mod_self_right, Nat.mod_mod]

lemma bound2_lt (q : ℕ) (hq : 2 ≤ q) :
    (bound2 q : ℝ) < 2 * ((q : ℝ) * Real.log q) ^ 2 := by
  set k := Nat.log 2 (q ^ 8)
  have hk : Nat.log2 (q ^ 8) = k := Nat.log2_eq_log_two
  have hpow : 2 ^ k ≤ q ^ 8 := Nat.pow_log_le_self 2 (pow_ne_zero 8 (by omega))
  have hk8 : 8 ≤ k := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact Nat.pow_le_pow_left hq 8
  have hl2 := Real.log_two_gt_d9
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hk0 : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hlog : (k : ℝ) * 0.6931471803 / 8 < Real.log q := by
    have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((q : ℝ) ^ 8) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    rw [Real.log_pow, Real.log_pow] at h1
    have : (k : ℝ) * 0.6931471803 < k * Real.log 2 :=
      mul_lt_mul_of_pos_left hl2 (by linarith)
    push_cast at h1
    linarith
  have h0 : (0 : ℝ) ≤ (k : ℝ) * 0.6931471803 / 8 := by positivity
  unfold bound2
  rw [hk]
  calc (((2 * q * q * k ^ 2 * 6931471803 ^ 2 / (64 * 10 ^ 20) : ℕ)) : ℝ)
        ≤ ((2 * q * q * k ^ 2 * 6931471803 ^ 2 : ℕ) : ℝ) / ((64 * 10 ^ 20 : ℕ) : ℝ) :=
        Nat.cast_div_le
    _ = 2 * ((q : ℝ) * ((k : ℝ) * 0.6931471803 / 8)) ^ 2 := by
        push_cast; field_simp; ring
    _ < 2 * ((q : ℝ) * Real.log q) ^ 2 := by gcongr

end BachSorenson.Checker
