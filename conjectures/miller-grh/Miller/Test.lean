import Miller.Reduction

/-!
# An executable deterministic Miller test

`millerTest n` checks the strong-probable-prime condition for every base
`1 ≤ a ≤ min (n - 1) (millerBound n)`, where `millerBound n = (Nat.log 2 n + 1)^2` is an integer
upper bound for `2 log² n` (because `2 (log 2)² < 1`). Under `BachSubgroupBound 2` the test is
correct for every odd `n > 1` (`millerTest_iff_prime`).
-/

namespace Miller

/-- Binary modular exponentiation: `powMod b e m ≡ b^e (mod m)`. -/
def powMod (b e m : ℕ) : ℕ :=
  if e = 0 then 1 % m
  else
    let h := powMod b (e / 2) m
    if e % 2 = 0 then h * h % m else h * h % m * b % m
termination_by e
decreasing_by omega

theorem powMod_cast (b e m : ℕ) : (powMod b e m : ZMod m) = (b : ZMod m) ^ e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [powMod]
    split_ifs with h0 h2
    · simp [h0]
    · have he : e = 2 * (e / 2) := by omega
      simp only [ZMod.natCast_mod, Nat.cast_mul, ih (e / 2) (by omega)]
      conv_rhs => rw [he]
      ring
    · have he : e = 2 * (e / 2) + 1 := by omega
      simp only [ZMod.natCast_mod, Nat.cast_mul, ih (e / 2) (by omega)]
      conv_rhs => rw [he]
      ring

/-- The exponent of `2` in `m`, computed by repeated halving. -/
def twoVal (m : ℕ) : ℕ :=
  if m ≠ 0 ∧ m % 2 = 0 then twoVal (m / 2) + 1 else 0
termination_by m
decreasing_by omega

theorem twoVal_eq (m : ℕ) : twoVal m = m.factorization 2 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [twoVal]
    split_ifs with h
    · obtain ⟨hm0, hm2⟩ := h
      have hk : m = 2 * (m / 2) := by omega
      have hk0 : m / 2 ≠ 0 := by omega
      rw [ih (m / 2) (by omega)]
      conv_rhs => rw [hk, Nat.factorization_mul two_ne_zero hk0]
      rw [Finsupp.add_apply, Nat.prime_two.factorization_self, add_comm]
    · by_cases hm0 : m = 0
      · simp [hm0]
      · rw [Nat.factorization_eq_zero_of_not_dvd]
        omega

/-- Decides `IsStrongProbablePrime n a` (for `n > 0`) using modular exponentiation. -/
def sppBool (n a : ℕ) : Bool :=
  let s := twoVal (n - 1)
  let d := (n - 1) / 2 ^ s
  powMod a d n % n == 1 % n ||
    (List.range s).any fun r => powMod a (2 ^ r * d) n % n == (n - 1) % n

theorem sppBool_iff {n : ℕ} (hn : 0 < n) (a : ℕ) :
    sppBool n a = true ↔ IsStrongProbablePrime n a := by
  have hneg : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hn, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [isStrongProbablePrime_iff, sppBool, twoVal_eq]
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range]
  refine or_congr ?_ (exists_congr fun r => and_congr Iff.rfl ?_)
  · rw [← powMod_cast]
    exact_mod_cast (ZMod.natCast_eq_natCast_iff' _ 1 n).symm
  · rw [← powMod_cast, ← hneg]
    exact (ZMod.natCast_eq_natCast_iff' _ _ n).symm

/-- An integer upper bound for `2 log² n`. -/
def millerBound (n : ℕ) : ℕ := (Nat.log 2 n + 1) ^ 2

theorem two_mul_log_sq_le_millerBound (n : ℕ) : 2 * Real.log n ^ 2 ≤ millerBound n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [millerBound]
  set k := Nat.log 2 n
  have hlt : (n : ℝ) < 2 ^ (k + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two n
  have hL : Real.log n < (k + 1) * Real.log 2 := by
    rw [← Nat.cast_succ, ← Real.log_pow]
    exact Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hlt)
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hl2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hl20 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : Real.log n ^ 2 ≤ ((k + 1) * Real.log 2) ^ 2 := pow_le_pow_left₀ hL0 hL.le 2
  have h2 : Real.log 2 ^ 2 ≤ 0.49 := by nlinarith
  simp only [millerBound, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ((k : ℝ) + 1))]

/-- The deterministic Miller test: `n` passes the strong test for every base
`1 ≤ a ≤ min (n - 1) (millerBound n)`. -/
def millerTest (n : ℕ) : Bool :=
  (List.range' 1 (min (n - 1) (millerBound n))).all (sppBool n)

/-- Under Bach's bound with constant `2`, the deterministic Miller test is correct for odd
`n > 1`. -/
theorem millerTest_iff_prime (h : BachSubgroupBound 2) {n : ℕ} (hn : Odd n) (h1 : 1 < n) :
    millerTest n = true ↔ n.Prime := by
  have hall : millerTest n = true ↔
      ∀ a, 1 ≤ a → a ≤ min (n - 1) (millerBound n) → IsStrongProbablePrime n a := by
    rw [millerTest, List.all_eq_true]
    simp only [List.mem_range'_1, sppBool_iff (by omega : 0 < n)]
    exact ⟨fun H a ha1 ha2 => H a ⟨ha1, by omega⟩, fun H a ha => H a ha.1 (by omega)⟩
  rw [hall]
  constructor
  · intro H
    refine (prime_iff_of_bach h n hn h1).mpr fun a ha0 han hac => H a ha0 ?_
    have : (a : ℝ) ≤ millerBound n := hac.trans (two_mul_log_sq_le_millerBound n)
    exact le_min (by omega) (by exact_mod_cast this)
  · intro hp a ha1 ha2
    exact isStrongProbablePrime_of_prime hp ha1 (by omega)

/-! ### Sanity checks (evaluated by the compiler; they add no axioms) -/

-- Carmichael numbers and strong pseudoprimes to small bases are rejected.
#guard millerTest 561 = false
#guard millerTest 1105 = false
#guard millerTest 2047 = false          -- strong pseudoprime to base 2
#guard millerTest 1373653 = false       -- strong pseudoprime to bases 2, 3
#guard millerTest 25326001 = false      -- strong pseudoprime to bases 2, 3, 5
#guard millerTest 3215031751 = false    -- strong pseudoprime to bases 2, 3, 5, 7
#guard millerTest 9 = false
#guard millerTest 15 = false
-- Primes are accepted.
#guard millerTest 3 = true
#guard millerTest 97 = true
#guard millerTest 7919 = true
#guard millerTest 2147483647 = true     -- 2^31 - 1
#guard millerTest 1000000007 = true
-- Agreement with `Nat.Prime` on all odd numbers below 3000.
#guard (List.range 1500).all fun k =>
  let n := 2 * k + 3
  millerTest n == decide n.Prime

end Miller
