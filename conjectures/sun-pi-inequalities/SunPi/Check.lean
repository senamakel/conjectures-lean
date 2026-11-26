import Mathlib.NumberTheory.PrimeCounting

/-!
# A proved-sound prime-counting checker

`primeTD m` tests primality by trial division by every `d ≥ 2` with `d² ≤ m`, and
`cnt a len` counts the primes in `(a, a + len]`. `primeTD_iff` and `primeCounting_add_cnt`
tie them to Mathlib's `Nat.Prime` and `Nat.primeCounting`. The two loops `checkA` and `checkB`
walk the finite ranges of Sun's two inequalities, carrying `π` incrementally; their soundness
theorems `checkA_sound` and `checkB_sound` say what a `true` result means.
-/

namespace SunPi.Check

open Nat
open scoped Nat.Prime

/-- `true` iff no `e` with `d ≤ e < d + fuel` and `e² ≤ m` divides `m`. -/
def noDivFrom (m : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | d, f + 1 => if m < d * d then true else if m % d = 0 then false else noDivFrom m (d + 1) f

theorem noDivFrom_iff (m : ℕ) : ∀ (f d : ℕ),
    noDivFrom m d f = true ↔ ∀ e, d ≤ e → e < d + f → e * e ≤ m → ¬ e ∣ m := by
  intro f
  induction f with
  | zero => intro d; simp [noDivFrom]; intro e h1 h2; omega
  | succ f ih =>
    intro d
    simp only [noDivFrom]
    by_cases h : m < d * d
    · simp only [h, ite_true, true_iff]
      intro e hde _ hee
      have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [h, ite_false]
      by_cases hm : m % d = 0
      · simp only [hm, ite_true, Bool.false_eq_true, false_iff, not_forall]
        exact ⟨d, le_refl d, by omega, by omega, fun hn => hn (Nat.dvd_of_mod_eq_zero hm)⟩
      · simp only [hm, ite_false, ih]
        constructor
        · intro H e hde hlt hee
          rcases Nat.eq_or_lt_of_le hde with rfl | hlt'
          · exact fun hd => hm (Nat.mod_eq_zero_of_dvd hd)
          · exact H e hlt' (by omega) hee
        · intro H e hde hlt hee
          exact H e (by omega) (by omega) hee

/-- Trial-division primality test. -/
def primeTD (m : ℕ) : Bool := decide (2 ≤ m) && noDivFrom m 2 m

theorem primeTD_iff (m : ℕ) : primeTD m = true ↔ m.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [primeTD, Bool.and_eq_true, decide_eq_true_eq, noDivFrom_iff]
  apply and_congr_right
  intro h2
  constructor
  · intro H e he hes
    have hee : e * e ≤ m := Nat.le_sqrt.mp hes
    have : e ≤ m := le_trans (Nat.le_mul_self e) hee
    exact H e he (by omega) hee
  · intro H e he _ hee
    exact H e he (Nat.le_sqrt.mpr hee)

/-- The number of primes in `(a, a + len]`. -/
def cnt (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | l + 1 => cnt a l + if primeTD (a + l + 1) then 1 else 0

theorem primeCounting_add_cnt (a : ℕ) : ∀ len, π (a + len) = π a + cnt a len := by
  intro len
  induction len with
  | zero => simp [cnt]
  | succ l ih =>
    have hs : π (a + (l + 1)) = π (a + l) + if (a + l + 1).Prime then 1 else 0 := by
      simp only [Nat.primeCounting, Nat.primeCounting', ← add_assoc]
      exact Nat.count_succ (p := Nat.Prime) _
    rw [hs, ih, cnt, add_assoc]
    congr 2
    by_cases hp : (a + l + 1).Prime
    · rw [if_pos hp, if_pos ((primeTD_iff _).mpr hp)]
    · have : primeTD (a + l + 1) = false := by
        cases h : primeTD (a + l + 1)
        · rfl
        · exact absurd ((primeTD_iff _).mp h) hp
      rw [if_neg hp, this]; rfl

/-! ## Sun's 2.14(ii): `π((n+1)²)^n < π(n²)^(n+1)` -/

/-- Walk `n, n+1, …` (`fuel` steps), carrying `c = π(n²)`. -/
def checkB (n c : ℕ) : ℕ → Bool
  | 0 => true
  | f + 1 =>
    let d := c + cnt (n * n) (2 * n + 1)
    decide (d ^ n < c ^ (n + 1)) && checkB (n + 1) d f

theorem checkB_sound : ∀ (f n : ℕ), checkB n (π (n * n)) f = true →
    ∀ m, n ≤ m → m < n + f → π ((m + 1) * (m + 1)) ^ m < π (m * m) ^ (m + 1) := by
  intro f
  induction f with
  | zero => intro n _ m h1 h2; omega
  | succ f ih =>
    intro n h m h1 h2
    simp only [checkB, Bool.and_eq_true, decide_eq_true_eq] at h
    have hsq : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by ring
    have hd : π (n * n) + cnt (n * n) (2 * n + 1) = π ((n + 1) * (n + 1)) := by
      rw [hsq, primeCounting_add_cnt]
    rw [hd] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (n + 1) h.2 m hlt (by omega)

/-! ## Sun's 2.7(i): `π((k+1)n)^k < π(kn)^(k+1)` -/

/-- For fixed `n`, walk `k, k+1, …` while `k ≤ n` and `k n < bound`, carrying `c = π(kn)`. -/
def checkAk (n bound k c : ℕ) : ℕ → Bool
  | 0 => true
  | f + 1 =>
    if n < k ∨ bound ≤ k * n then true else
    let d := c + cnt (k * n) n
    decide (d ^ k < c ^ (k + 1)) && checkAk n bound (k + 1) d f

theorem checkAk_sound (n bound : ℕ) : ∀ (f k : ℕ), checkAk n bound k (π (k * n)) f = true →
    ∀ j, k ≤ j → j < k + f → j ≤ n → j * n < bound →
      π ((j + 1) * n) ^ j < π (j * n) ^ (j + 1) := by
  intro f
  induction f with
  | zero => intro k _ j h1 h2; omega
  | succ f ih =>
    intro k h j h1 h2 h3 h4
    simp only [checkAk] at h
    have hkn : ¬ (n < k ∨ bound ≤ k * n) := by
      intro H; rcases H with H | H
      · omega
      · have : k * n ≤ j * n := Nat.mul_le_mul_right n h1; omega
    simp only [hkn, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
    have hd : π (k * n) + cnt (k * n) n = π ((k + 1) * n) := by
      rw [← primeCounting_add_cnt]; congr 1; ring
    rw [hd] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (k + 1) h.2 j hlt (by omega) h3 h4

/-- Walk `n, n+1, …` (`fuel` steps), running `checkAk` from `k = 1` for each. -/
def checkA (bound n : ℕ) : ℕ → Bool
  | 0 => true
  | f + 1 => checkAk n bound 1 (cnt 0 n) n && checkA bound (n + 1) f

theorem checkA_sound (bound : ℕ) : ∀ (f n : ℕ), checkA bound n f = true →
    ∀ m, n ≤ m → m < n + f → ∀ j, 1 ≤ j → j ≤ m → j * m < bound →
      π ((j + 1) * m) ^ j < π (j * m) ^ (j + 1) := by
  intro f
  induction f with
  | zero => intro n _ m h1 h2; omega
  | succ f ih =>
    intro n h m h1 h2 j hj1 hj2 hj3
    simp only [checkA, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have h0 : cnt 0 n = π (1 * n) := by
        have := primeCounting_add_cnt 0 n
        simp only [zero_add, Nat.primeCounting_zero] at this
        rw [one_mul, this]
      rw [h0] at h
      exact checkAk_sound n bound n 1 h.1 j hj1 (by omega) hj2 hj3
    · exact ih (n + 1) h.2 m hlt (by omega) j hj1 hj2 hj3

end SunPi.Check
