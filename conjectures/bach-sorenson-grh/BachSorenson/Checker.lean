import Mathlib
import BachSorensonCheck

/-!
# Step 7: soundness of the finite check

`checkRange N lo n = true` implies: for every `q ∈ [lo, lo + n)` with `q ≥ 2` and every `a`
coprime to `q` there is a prime `p ≡ a (mod q)` with `p < bound q ≤ (7/2) (q log q)²`.

Soundness uses only that a marked table entry is a prime (`isPrime_of_isPrimeB`, by trial
division up to `√n`) and that the walk visits `a % q + k q`. The table size, the fuel and the
order of the walk matter only for completeness.
-/

namespace BachSorenson.Checker

lemma trialFrom_sound (n : ℕ) :
    ∀ fuel d, trialFrom n d fuel = true → ∀ m, d ≤ m → m * m ≤ n → n % m ≠ 0
  | 0, d, h => by simp [trialFrom] at h
  | fuel + 1, d, h => by
    intro m hdm hmn
    unfold trialFrom at h
    by_cases h1 : n < d * d
    · exfalso
      have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · simp only [h1, ite_false] at h
      by_cases h2 : n % d = 0
      · simp [h2] at h
      · simp only [h2, beq_iff_eq, ite_false] at h
        rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
        · exact h2
        · exact trialFrom_sound n fuel (d + 1) h m hlt hmn

lemma isPrime_of_isPrimeB {n : ℕ} (h : isPrimeB n = true) : n.Prime := by
  unfold isPrimeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, ht⟩ := h
  by_contra hnp
  have hn1 : n ≠ 1 := by omega
  have hm := Nat.minFac_prime hn1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have := trialFrom_sound n n 2 ht n.minFac hm.two_le (by nlinarith)
  exact this (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))

lemma prime_of_marked {N p : ℕ} (h : marked (primeTable N) p = true) : p.Prime := by
  unfold marked primeTable at h
  rw [Array.getElem?_ofFn] at h
  split_ifs at h with hp
  · exact isPrime_of_isPrimeB (by simpa using h)
  · simp at h

lemma findFrom_sound (arr : Array Bool) (q B : ℕ) :
    ∀ fuel p, findFrom arr q B p fuel = true → ∃ k, marked arr (p + k * q) = true ∧ p + k * q < B
  | 0, p, h => by simp [findFrom] at h
  | fuel + 1, p, h => by
    unfold findFrom at h
    by_cases h1 : B ≤ p
    · simp [h1] at h
    · simp only [h1, ite_false] at h
      by_cases h2 : marked arr p = true
      · exact ⟨0, by simpa using h2, by simpa using (Nat.lt_of_not_le h1)⟩
      · simp only [h2, ite_false, Bool.false_eq_true] at h
        obtain ⟨k, hk1, hk2⟩ := findFrom_sound arr q B fuel (p + q) h
        exact ⟨k + 1, by rwa [show p + (k + 1) * q = p + q + k * q by ring],
          by rwa [show p + (k + 1) * q = p + q + k * q by ring]⟩

theorem exists_prime_of_checkRange {N lo n : ℕ} (h : checkRange N lo n = true) {q : ℕ}
    (hq1 : lo ≤ q) (hq2 : q < lo + n) (hq : 2 ≤ q) {a : ℕ} (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ p < bound q := by
  unfold checkRange at h
  have hq' := List.all_eq_true.1 h q (List.mem_range'_1.2 ⟨hq1, hq2⟩)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hq'
  rcases hq' with hlt | hchk
  · omega
  unfold checkQ at hchk
  have hq0 : 0 < q := by omega
  have ha' := List.all_eq_true.1 hchk (a % q) (List.mem_range.2 (Nat.mod_lt a hq0))
  have hg : Nat.gcd (a % q) q = 1 := by
    rw [← Nat.gcd_rec q a, Nat.gcd_comm]; exact ha
  simp only [hg, bne_self_eq_false, Bool.false_or] at ha'
  obtain ⟨k, hk1, hk2⟩ := findFrom_sound _ _ _ _ _ ha'
  refine ⟨a % q + k * q, prime_of_marked hk1, ?_, hk2⟩
  unfold Nat.ModEq
  rw [Nat.add_mul_mod_self_right, Nat.mod_mod]

lemma bound_le (q : ℕ) (hq : q ≠ 0) :
    (bound q : ℝ) ≤ 7 / 2 * ((q : ℝ) * Real.log q) ^ 2 := by
  set k := Nat.log 2 (q ^ 8)
  have hk : Nat.log2 (q ^ 8) = k := Nat.log2_eq_log_two
  have hpow : 2 ^ k ≤ q ^ 8 := Nat.pow_log_le_self 2 (pow_ne_zero 8 hq)
  have hl2 := Real.log_two_gt_d9
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hlog : (k : ℝ) * 0.6931471803 / 8 ≤ Real.log q := by
    have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((q : ℝ) ^ 8) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    rw [Real.log_pow, Real.log_pow] at h1
    have : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
    push_cast at h1
    linarith
  have h0 : (0 : ℝ) ≤ (k : ℝ) * 0.6931471803 / 8 := by positivity
  unfold bound
  rw [hk]
  calc (((7 * q * q * k ^ 2 * 6931471803 ^ 2 / (2 * 64 * 10 ^ 20) : ℕ)) : ℝ)
        ≤ ((7 * q * q * k ^ 2 * 6931471803 ^ 2 : ℕ) : ℝ) / ((2 * 64 * 10 ^ 20 : ℕ) : ℝ) :=
        Nat.cast_div_le
    _ = 7 / 2 * ((q : ℝ) * ((k : ℝ) * 0.6931471803 / 8)) ^ 2 := by
        push_cast; field_simp; ring
    _ ≤ 7 / 2 * ((q : ℝ) * Real.log q) ^ 2 := by gcongr

end BachSorenson.Checker
