import Mathlib

/-!
The multiplicative recurrence underlying Bill McEachen's OEIS A135508 conjecture.

The recurrence and prime-modulo-three argument are supporting infrastructure for the density-one
deduction. The prime-modulo-three argument is already present in OMA reduction PR
[#1354](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1354); this file gives a
reusable recurrence statement, not a new proof of that argument.
-/

namespace Implications.McEachenStock

/-- Auxiliary sequence from the OEIS A135508 recurrence used in OMA PR #1354. -/
def x : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => 2 * x n + Nat.lcm (x n) (n + 1)

/-- The multiplier in `x (n + 1) = x n * (a n + 2)`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n + 1) / Nat.gcd (x n) (n + 1)

lemma x_pos (n : ℕ) (hn : 1 ≤ n) : 0 < x n := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => decide
    | succ n ih =>
      change 0 < 2 * x (n + 1) + Nat.lcm (x (n + 1)) (n + 2)
      omega

lemma x_succ_fact (n : ℕ) (hn : 1 ≤ n) :
    x (n + 1) = x n * (2 + (n + 1) / Nat.gcd (x n) (n + 1)) := by
  cases n with
  | zero => omega
  | succ k =>
    change 2 * x (k + 1) + Nat.lcm (x (k + 1)) (k + 2) = _
    rw [Nat.lcm_eq_mul_div, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
    ring

lemma a_eq_div_gcd (n : ℕ) (hn : 1 ≤ n) :
    a n = (n + 1) / Nat.gcd (x n) (n + 1) := by
  rw [a, if_neg (by omega), x_succ_fact n hn]
  simp [x_pos n hn]

lemma x_dvd_succ (n : ℕ) (hn : 1 ≤ n) : x n ∣ x (n + 1) := by
  rw [x_succ_fact n hn]
  exact Nat.dvd_mul_right _ _

lemma x_succ_mul_a (n : ℕ) (hn : 1 ≤ n) : x (n + 1) = x n * (a n + 2) := by
  rw [x_succ_fact n hn, a_eq_div_gcd n hn, Nat.add_comm 2]

lemma prime_not_dvd_x_before {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n)
    (hsmall : n + 2 < p) : ¬ p ∣ x n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · omega
    · simp [x, hp.not_dvd_one]
    · rw [x_succ_fact (k + 1) (by omega)]
      intro hd
      rcases hp.dvd_mul.mp hd with hleft | hright
      · exact ih (k + 1) (by omega) (by omega) (by omega) hleft
      · have hpos : 0 < (2 + (k + 2) / Nat.gcd (x (k + 1)) (k + 2) : ℕ) := by
          positivity
        have hle := Nat.div_le_self (k + 2) (Nat.gcd (x (k + 1)) (k + 2))
        exact Nat.not_dvd_of_pos_of_lt hpos (by omega) hright

lemma prime_mod_three_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2)
    (h11 : 11 ≤ p) : a (p - 1) = p := by
  have hthree : ∀ n : ℕ, 4 ≤ n → 3 ∣ x n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ k hk ih => exact ih.trans (x_dvd_succ k (by omega))
  have hprev : a (p - 3) ≠ p - 2 := by
    intro ha
    have hd := hthree (p - 3) (by omega)
    have hm : 3 ∣ (p - 3) + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hg : 3 ∣ Nat.gcd (x (p - 3)) ((p - 3) + 1) := Nat.dvd_gcd hd hm
    have hmul : a (p - 3) * Nat.gcd (x (p - 3)) ((p - 3) + 1) = (p - 3) + 1 := by
      rw [a_eq_div_gcd _ (by omega)]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hgpos := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
    have hrel : p - 2 = (p - 3) + 1 := by omega
    rw [ha, hrel] at hmul
    have hb := Nat.mul_le_mul_left ((p - 3) + 1) hgpos
    rw [hmul] at hb
    omega
  have hiff : p ∣ x (p - 1) ↔ a (p - 3) = p - 2 := by
    have he : p - 2 = (p - 3) + 1 := by omega
    rw [he, x_succ_mul_a _ (by omega), hp.dvd_mul]
    have hbefore := prime_not_dvd_x_before hp (p - 3) (by omega) (by omega)
    rw [or_iff_right hbefore]
    constructor
    · intro hd
      have ha := Nat.div_le_self ((p - 3) + 1) (Nat.gcd (x (p - 3)) ((p - 3) + 1))
      rw [a_eq_div_gcd _ (by omega)] at ha
      have hl := Nat.le_of_dvd (by omega : 0 < a (p - 3) + 2) hd
      omega
    · intro ha
      have heq : a (p - 3) + 2 = p := by omega
      rw [heq]
  have hnot : ¬ p ∣ x (p - 1) := by
    exact prime_not_dvd_x_before hp (p - 1) (by omega) (by omega)
  rw [a_eq_div_gcd _ (by have := hp.two_le; omega), Nat.sub_add_cancel hp.one_le]
  rw [if_neg hnot]
  have hc : Nat.Coprime (x (p - 1)) p := (hp.coprime_iff_not_dvd.mpr hnot).symm
  rw [hc.gcd_eq_one, Nat.div_one]

/-- For a prime `r ≥ 11` with `r ≡ 2 (mod 3)`, the recurrence inserts `r + 2`
into `x r`; divisibility monotonicity keeps it in every later state. -/
theorem prime_factor_persists {r n : ℕ} (hr : r.Prime) (hr11 : 11 ≤ r)
    (hmod : r % 3 = 2) (hrn : r ≤ n) : r + 2 ∣ x n := by
  have hmult : a (r - 1) = r := prime_mod_three_two hr hmod hr11
  have hstep := x_succ_mul_a (r - 1) (by omega)
  rw [show r - 1 + 1 = r by omega, hmult] at hstep
  have hbase : r + 2 ∣ x r := by
    rw [hstep]
    exact dvd_mul_of_dvd_right (dvd_refl (r + 2)) (x (r - 1))
  induction n, hrn using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih => exact ih.trans (x_dvd_succ k (by omega))

end Implications.McEachenStock

#print axioms Implications.McEachenStock.prime_factor_persists
