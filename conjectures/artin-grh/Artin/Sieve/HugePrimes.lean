import Artin.Interfaces

/-!
# Huge primes `q > √x log x` (blueprint B4)

If a prime `q > √x · log x` divides `p - 1` and `a^((p-1)/q) = 1` mod `p`, then
`m = (p - 1)/q` satisfies `1 ≤ m < √x / log x` and `a^m ≡ 1 (mod p)`. So `p` is a prime factor of
one of the nonzero integers `a^m - 1`, `1 ≤ m ≤ M = ⌊√x / log x⌋`. The integer `a^m - 1` has at
most `(|a| + 1) · m` distinct prime factors, so there are at most `(|a| + 1) M² ≤ (|a| + 1) x / log² x`
such primes `p`. Unconditional and elementary.
-/

namespace Artin

open Finset

open Classical in
/-- The number of primes `p < x`, `p ∤ a`, sifted out by some prime `q > √x · log x`:
`q ∣ p - 1` and `a^((p-1)/q) = 1` in `ZMod p`. -/
noncomputable def hugePrimeCount (a : ℤ) (x : ℕ) : ℕ :=
  ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
    ∃ q : ℕ, q.Prime ∧ Real.sqrt x * Real.log x < q ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1).card

lemma pow_add_one_le_add_one_pow (c : ℕ) {m : ℕ} (hm : 1 ≤ m) : c ^ m + 1 ≤ (c + 1) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le (c ^ m), Nat.zero_le c]

/-- A positive integer `n ≤ B^m` has at most `B · m` distinct prime factors. -/
lemma card_primeFactors_le_of_le_pow {n B m : ℕ} (hn : n ≠ 0) (h : n ≤ B ^ m) :
    n.primeFactors.card ≤ B * m := by
  have h1 : 2 ^ n.primeFactors.card ≤ n :=
    (Finset.pow_card_le_prod _ id 2 fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))
  have h2 : B ^ m ≤ 2 ^ (B * m) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le m
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h1.trans (h.trans h2))

/-- `|a^m - 1|` is nonzero and at most `(|a| + 1)^m` when `|a| ≥ 2` and `m ≥ 1`. -/
lemma natAbs_pow_sub_one {a : ℤ} (ha : 2 ≤ a.natAbs) {m : ℕ} (hm : 1 ≤ m) :
    (a ^ m - 1).natAbs ≠ 0 ∧ (a ^ m - 1).natAbs ≤ (a.natAbs + 1) ^ m := by
  constructor
  · intro h
    rw [Int.natAbs_eq_zero, sub_eq_zero] at h
    have := congrArg Int.natAbs h
    rw [Int.natAbs_pow, Int.natAbs_one] at this
    have h2 : 2 ^ m ≤ a.natAbs ^ m := Nat.pow_le_pow_left ha m
    have h3 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  · calc (a ^ m - 1).natAbs ≤ (a ^ m).natAbs + (1 : ℤ).natAbs := Int.natAbs_sub_le _ _
      _ = a.natAbs ^ m + 1 := by rw [Int.natAbs_pow, Int.natAbs_one]
      _ ≤ (a.natAbs + 1) ^ m := pow_add_one_le_add_one_pow _ hm

/-- **Huge primes (blueprint B4).** For `a ∉ {0, 1, -1}` and `x ≥ 2`, at most
`(|a| + 1) · x / log² x` primes `p < x` are sifted out by a prime `q > √x · log x`. -/
theorem hugePrimeCount_le (a : ℤ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ -1) (x : ℕ)
    (hx : 2 ≤ x) :
    (hugePrimeCount a x : ℝ) ≤ (a.natAbs + 1 : ℝ) * x / Real.log x ^ 2 := by
  classical
  have ha : 2 ≤ a.natAbs := by
    rcases Int.natAbs_eq a with h | h <;> omega
  set B := a.natAbs + 1 with hB
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  set M : ℝ := Real.sqrt x / Real.log x with hM
  have hM0 : 0 ≤ M := div_nonneg hsqrt.le hlog.le
  set M' := ⌊M⌋₊ with hM'
  -- every counted prime divides some `a^m - 1` with `1 ≤ m ≤ M'`
  have hsub : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∃ q : ℕ, q.Prime ∧ Real.sqrt x * Real.log x < q ∧ q ∣ p - 1 ∧
        (a : ZMod p) ^ ((p - 1) / q) = 1) ⊆
      (Icc 1 M').biUnion fun m => (a ^ m - 1).natAbs.primeFactors := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hp, -, q, hq, hqbig, hqd, hpow⟩ := hp
    set m := (p - 1) / q with hmdef
    have hqm : q * m = p - 1 := Nat.mul_div_cancel' hqd
    have hp1 := hp.one_lt
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hqm; omega
      · exact h
    have hmM : m ≤ M' := by
      refine Nat.le_floor ?_
      rw [hM, le_div_iff₀ hlog]
      have hqmR : (q : ℝ) * m < x := by
        have : q * m < x := by omega
        exact_mod_cast this
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      have h1 : (m : ℝ) * (Real.sqrt x * Real.log x) < Real.sqrt x * Real.sqrt x := by
        rw [Real.mul_self_sqrt (by linarith)]
        calc (m : ℝ) * (Real.sqrt x * Real.log x) < m * q := mul_lt_mul_of_pos_left hqbig hmR
          _ = q * m := mul_comm _ _
          _ < x := hqmR
      have h2 : Real.sqrt x * ((m : ℝ) * Real.log x) < Real.sqrt x * Real.sqrt x := by
        linarith
      exact (lt_of_mul_lt_mul_left h2 hsqrt.le).le
    simp only [Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨m, ⟨hm1, hmM⟩, ?_⟩
    obtain ⟨hne, -⟩ := natAbs_pow_sub_one ha hm1
    refine Nat.mem_primeFactors.mpr ⟨hp, ?_, hne⟩
    rw [← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hpow, sub_self]
  -- count prime factors
  have hcard : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∃ q : ℕ, q.Prime ∧ Real.sqrt x * Real.log x < q ∧ q ∣ p - 1 ∧
        (a : ZMod p) ^ ((p - 1) / q) = 1).card ≤ B * (M' * M') := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ m ∈ Icc 1 M', (a ^ m - 1).natAbs.primeFactors.card
        ≤ ∑ _m ∈ Icc 1 M', B * M' := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.mem_Icc] at hm
          obtain ⟨hne, hle⟩ := natAbs_pow_sub_one ha hm.1
          exact (card_primeFactors_le_of_le_pow hne hle).trans (Nat.mul_le_mul_left _ hm.2)
      _ = B * (M' * M') := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
          simp only [Nat.add_sub_cancel]
          ring
  have hM'R : (M' : ℝ) ≤ M := Nat.floor_le hM0
  have hMsq : M ^ 2 = x / Real.log x ^ 2 := by
    rw [hM, div_pow, Real.sq_sqrt (by linarith)]
  have hBR : (0 : ℝ) ≤ B := by positivity
  calc (hugePrimeCount a x : ℝ) ≤ (B * (M' * M') : ℕ) := by
        rw [hugePrimeCount]; exact_mod_cast hcard
    _ = (B : ℝ) * (M' : ℝ) ^ 2 := by push_cast; ring
    _ ≤ (B : ℝ) * M ^ 2 := by
        gcongr
    _ = (a.natAbs + 1 : ℝ) * x / Real.log x ^ 2 := by
        rw [hMsq, hB]; push_cast; ring

end Artin
