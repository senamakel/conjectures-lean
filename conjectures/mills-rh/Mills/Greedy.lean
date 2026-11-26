import Mathlib
import Mills.Statement

/-!
# The greedy sequence `2, 11, 1361, 2521008887, …` and the lower bound (no RH)

`g n` is the greedy sequence indexed from `0`, so `g n` is the `(n+1)`-st term `P_{n+1}`:
`g 0 = 2` and `g (n+1)` is the least prime `≥ (g n)^3`.  It is defined for every `n`
unconditionally, because there are infinitely many primes.

Every Mills number `A > 1` satisfies `g n ≤ ⌊A^(3^(n+1))⌋₊` (`g_le_floor`), hence
`A^81 ≥ 2521008887`, hence `A > 1.3063778838` (`lower_bound`).  This part needs no hypothesis.
-/

set_option linter.constructorNameAsVariable false  -- the linter overflows on the large `norm_num` proof terms

namespace Mills

lemma exists_prime_ge (x : ℕ) : ∃ p, p.Prime ∧ x ≤ p := by
  obtain ⟨p, hp, hq⟩ := Nat.exists_infinite_primes x
  exact ⟨p, hq, hp⟩

/-- The least prime `≥ x^3`. -/
noncomputable def nextPrime (x : ℕ) : ℕ := Nat.find (exists_prime_ge (x ^ 3))

lemma nextPrime_prime (x : ℕ) : (nextPrime x).Prime :=
  (Nat.find_spec (exists_prime_ge (x ^ 3))).1

lemma pow_le_nextPrime (x : ℕ) : x ^ 3 ≤ nextPrime x :=
  (Nat.find_spec (exists_prime_ge (x ^ 3))).2

lemma nextPrime_le {x p : ℕ} (hp : p.Prime) (h : x ^ 3 ≤ p) : nextPrime x ≤ p :=
  Nat.find_min' (exists_prime_ge (x ^ 3)) ⟨hp, h⟩

lemma nextPrime_eq {x p : ℕ} (hp : p.Prime) (h : x ^ 3 ≤ p)
    (hmin : ∀ q, x ^ 3 ≤ q → q < p → ¬ q.Prime) : nextPrime x = p := by
  refine le_antisymm (nextPrime_le hp h) ?_
  by_contra hlt
  exact hmin _ (pow_le_nextPrime x) (not_le.mp hlt) (nextPrime_prime x)

/-- The greedy sequence: `g 0 = 2`, `g (n+1) = ` least prime `≥ (g n)^3`. -/
noncomputable def g : ℕ → ℕ
  | 0 => 2
  | n + 1 => nextPrime (g n)

lemma g_zero : g 0 = 2 := rfl
lemma g_succ (n : ℕ) : g (n + 1) = nextPrime (g n) := rfl

lemma g_one : g 1 = 11 := by
  rw [g_succ, g_zero]
  refine nextPrime_eq (by norm_num) (by norm_num) ?_
  intro q h1 h2
  have h1' : 8 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_two : g 2 = 1361 := by
  rw [g_succ, g_one]
  refine nextPrime_eq (by norm_num) (by norm_num) ?_
  intro q h1 h2
  have h1' : 1331 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

/-- A Pratt/Lucas primality certificate: `5` is a primitive root mod `2521008887`, and
`2521008886 = 2 · 11 · 23 · 4982231` with `4982231` prime.  The modular powers are evaluated by
`reduce_mod_char` (repeated squaring); no `native_decide`. -/
lemma prime_2521008887 : Nat.Prime 2521008887 := by
  have hp4 : Nat.Prime 4982231 := by norm_num
  have hfac : (2521008887 - 1 : ℕ) = 2 * 11 * 23 * 4982231 := by norm_num
  apply lucas_primality 2521008887 (5 : ZMod 2521008887)
  · show (5 : ZMod 2521008887) ^ 2521008886 = 1
    reduce_mod_char
  · intro q hq hdvd
    rw [hfac] at hdvd
    have key : q = 2 ∨ q = 11 ∨ q = 23 ∨ q = 4982231 := by
      rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
          · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq hp4).mp h
    rcases key with rfl | rfl | rfl | rfl
    · show (5 : ZMod 2521008887) ^ 1260504443 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 229182626 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 109609082 ≠ 1
      reduce_mod_char; decide
    · show (5 : ZMod 2521008887) ^ 506 ≠ 1
      reduce_mod_char; decide

/-- `2521008887` is prime, and it is the least prime above `1361^3 = 2521008881`. -/
lemma g_three : g 3 = 2521008887 := by
  rw [g_succ, g_two]
  refine nextPrime_eq prime_2521008887 (by norm_num) ?_
  intro q h1 h2
  have h1' : 2521008881 ≤ q := by norm_num at h1; exact h1
  interval_cases q <;> norm_num

lemma g_prime (n : ℕ) : (g n).Prime := by
  cases n with
  | zero => rw [g_zero]; exact Nat.prime_two
  | succ n => rw [g_succ]; exact nextPrime_prime _

lemma g_cube_le (n : ℕ) : g n ^ 3 ≤ g (n + 1) := pow_le_nextPrime _

lemma g_mono : Monotone g := by
  refine monotone_nat_of_le_succ fun n => ?_
  have := g_cube_le n
  have h2 := (g_prime n).two_le
  calc g n ≤ g n ^ 3 := Nat.le_self_pow (by norm_num) _
    _ ≤ _ := this

/-- Any Mills number `A > 1` has `g n ≤ ⌊A^(3^(n+1))⌋₊`: the greedy sequence is minimal. -/
theorem g_le_floor {A : ℝ} (hA : 1 < A) (hM : IsMills A) (n : ℕ) :
    g n ≤ ⌊A ^ 3 ^ (n + 1)⌋₊ := by
  have hA0 : 0 ≤ A := by linarith
  have hprime : ∀ n : ℕ, (⌊A ^ 3 ^ (n + 1)⌋₊).Prime :=
    fun n => Nat.prime_iff.mpr (hM n.succPNat)
  induction n with
  | zero => rw [g_zero]; exact (hprime 0).two_le
  | succ n ih =>
    have hq : ⌊A ^ 3 ^ (n + 1)⌋₊ ^ 3 ≤ ⌊A ^ 3 ^ (n + 1 + 1)⌋₊ := by
      apply Nat.le_floor
      push_cast
      have h1 : ((⌊A ^ 3 ^ (n + 1)⌋₊ : ℕ) : ℝ) ≤ A ^ 3 ^ (n + 1) := Nat.floor_le (by positivity)
      calc ((⌊A ^ 3 ^ (n + 1)⌋₊ : ℕ) : ℝ) ^ 3 ≤ (A ^ 3 ^ (n + 1)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h1 3
        _ = A ^ 3 ^ (n + 1 + 1) := by rw [← pow_mul, ← pow_succ]
    rw [g_succ]
    exact nextPrime_le (hprime (n + 1)) (le_trans (Nat.pow_le_pow_left ih 3) hq)

theorem g_le_pow {A : ℝ} (hA : 1 < A) (hM : IsMills A) (n : ℕ) :
    (g n : ℝ) ≤ A ^ 3 ^ (n + 1) :=
  le_trans (Nat.cast_le.mpr (g_le_floor hA hM n)) (Nat.floor_le (by positivity))

/-- **Lower bound, no hypotheses**: every Mills number `A > 1` exceeds `1.3063778838`. -/
theorem lower_bound {A : ℝ} (hA : 1 < A) (hM : IsMills A) : (1.3063778838 : ℝ) < A := by
  have h := g_le_pow hA hM 3
  rw [g_three] at h
  norm_num at h
  by_contra hle
  push Not at hle
  have : A ^ 81 ≤ (1.3063778838 : ℝ) ^ 81 := pow_le_pow_left₀ (by linarith) hle 81
  have h2 : (1.3063778838 : ℝ) ^ 81 < 2521008887 := by norm_num
  linarith

end Mills
