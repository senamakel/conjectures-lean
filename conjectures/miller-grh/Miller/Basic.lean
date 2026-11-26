import Miller.Statement

/-!
# Basic facts about strong probable primes

For odd `n > 1` write `n - 1 = 2^s d` with `d` odd. This file records the arithmetic of `s` and
`d`, translates `IsStrongProbablePrime` for a unit base into a statement in `(ZMod n)ˣ`, and
proves that primes are strong probable primes to every base `0 < a < p`.
-/

namespace Miller

/-- The 2-adic valuation `s` of `n - 1`, as in `IsStrongProbablePrime`. -/
abbrev sPart (n : ℕ) : ℕ := (n - 1).factorization 2

/-- The odd part `d` of `n - 1`, as in `IsStrongProbablePrime`. -/
abbrev dPart (n : ℕ) : ℕ := (n - 1) / 2 ^ sPart n

theorem two_pow_sPart_mul_dPart (n : ℕ) : 2 ^ sPart n * dPart n = n - 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2

theorem odd_dPart {n : ℕ} (h1 : 1 < n) : Odd (dPart n) :=
  Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (by omega))

theorem sPart_pos {n : ℕ} (hn : Odd n) (h1 : 1 < n) : 0 < sPart n := by
  have h2 : 2 ∣ n - 1 := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨k, by omega⟩
  exact (Nat.prime_two.dvd_iff_one_le_factorization (by omega)).mp h2

/-- The strong-liar condition on a unit. -/
def IsLiar (n : ℕ) (u : (ZMod n)ˣ) : Prop :=
  u ^ dPart n = 1 ∨ ∃ r < sPart n, u ^ (2 ^ r * dPart n) = -1

theorem isStrongProbablePrime_iff (n a : ℕ) :
    IsStrongProbablePrime n a ↔
      (a : ZMod n) ^ dPart n = 1 ∨ ∃ r < sPart n, (a : ZMod n) ^ (2 ^ r * dPart n) = -1 :=
  Iff.rfl

theorem isStrongProbablePrime_val_iff {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    IsStrongProbablePrime n (u : ZMod n).val ↔ IsLiar n u := by
  rw [isStrongProbablePrime_iff, ZMod.natCast_zmod_val, IsLiar]
  simp only [← Units.val_pow_eq_pow_val, Units.val_eq_one]
  refine or_congr Iff.rfl (exists_congr fun r => and_congr Iff.rfl ?_)
  rw [Units.ext_iff, Units.val_neg, Units.val_one]

/-- In a ring without zero divisors, an element whose `2^s`-th power is `1` is `1`, or one of its
`2^r`-th powers with `r < s` is `-1`. -/
theorem eq_one_or_pow_eq_neg_one {R : Type*} [Ring R] [NoZeroDivisors R] {x : R} :
    ∀ {s : ℕ}, x ^ 2 ^ s = 1 → x = 1 ∨ ∃ r < s, x ^ 2 ^ r = -1
  | 0, h => Or.inl (by simpa using h)
  | s + 1, h => by
    have h' : x ^ 2 ^ s * x ^ 2 ^ s = 1 := by rw [← pow_add, ← two_mul, ← pow_succ']; exact h
    rcases mul_self_eq_one_iff.mp h' with h1 | h1
    · rcases eq_one_or_pow_eq_neg_one h1 with h2 | ⟨r, hr, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨r, by omega, h2⟩
    · exact Or.inr ⟨s, by omega, h1⟩

/-- A prime is a strong probable prime to every base `0 < a < p`. -/
theorem isStrongProbablePrime_of_prime {p : ℕ} (hp : p.Prime) {a : ℕ} (ha0 : 0 < a)
    (hap : a < p) : IsStrongProbablePrime p a := by
  have := Fact.mk hp
  have hne : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)
  have hF := ZMod.pow_card_sub_one_eq_one hne
  rw [← two_pow_sPart_mul_dPart, mul_comm, pow_mul] at hF
  rw [isStrongProbablePrime_iff]
  rcases eq_one_or_pow_eq_neg_one hF with h | ⟨r, hr, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, hr, by rw [mul_comm, pow_mul]; exact h⟩

end Miller
