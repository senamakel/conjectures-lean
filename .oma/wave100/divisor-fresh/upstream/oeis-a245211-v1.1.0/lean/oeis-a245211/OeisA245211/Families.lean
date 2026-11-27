/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/
import OeisA245211.Basic
import OeisA245211.Dominance

/-!
# OEIS A245211 — Infinite Family Exclusions and Semiprime / Multiple-of-3 Uniqueness

This module proves unconditional structural and Diophantine theorems for the
first-moment proper-divisor sequence

$$a(n) = \sum_{d \mid n,\, d < n} d \cdot \tau(d)$$

(OEIS A245211), including:
1. **Primes**: For every prime $p$, $\tau(p) = 2$ and $a(p) = 1 < p$ (Krizek's
   2014 OEIS formula), together with the decidable characterization
   $\text{IsPrime}(p) \iff 2 \le p \wedge \tau(p) = 2$.
2. **Prime powers**: For every prime $p$ and exponent $k \ge 1$,
   $a(p^k) \equiv 1 \pmod p$, whereas $p^k \equiv 0 \pmod p$, so $a(p^k) \ne p^k$.
3. **Semiprimes**: For distinct primes $p < q$, $a(pq) = 1 + 2p + 2q$. In
   particular, $a(2p) = 2p + 5$ for every odd prime $p$ (Krizek's second 2014 OEIS
   formula), $a(3p) = 2p + 7$ for every prime $p > 3$, and among all semiprimes
   $p \cdot q$ ($p \le q$ primes), $n = 21 = 3 \cdot 7$ is the unique fixed point.
4. **Multiples of 3**: Among all positive multiples of $3$, $n = 21$ is
   unconditionally the unique fixed point of $a(n)$.
5. **Three-prime-factor families ($\Omega(n) = 3$)**: Exact polynomial and
   Diophantine exclusion identities for $n = p^2 q$ (explaining the closest odd
   composite near-miss $a(725) = 724$) and $n = p q r$ (showing
   $(2p+1)(2q+1)(2r+1) \ne 9pqr$ for all primes $p < q < r$).
-/

namespace OeisA245211

/-! ## Range Sum Evaluation Lemmas -/

/-- If `f` vanishes at every positive index in `[1, m]`, then `sumUpTo f m = 0`. -/
theorem sumUpTo_eq_zero (f : Nat → Nat) (m : Nat)
    (h : ∀ d : Nat, 1 ≤ d → d ≤ m → f d = 0) :
    sumUpTo f m = 0 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [sumUpTo_succ]
    have ih' : sumUpTo f k = 0 := ih (fun d hd1 hdk => h d hd1 (by omega))
    have hk : f (k + 1) = 0 := h (k + 1) (by omega) (by omega)
    omega

/-- If `f` vanishes strictly above `m₀` up to `m`, then `sumUpTo f m = sumUpTo f m₀`. -/
theorem sumUpTo_eq_of_gt_zero (f : Nat → Nat) (m₀ m : Nat)
    (hle : m₀ ≤ m)
    (h : ∀ d : Nat, m₀ < d → d ≤ m → f d = 0) :
    sumUpTo f m = sumUpTo f m₀ := by
  induction m with
  | zero =>
    have hm0 : m₀ = 0 := by omega
    subst hm0
    rfl
  | succ k ih =>
    by_cases hk : m₀ = k + 1
    · subst hk; rfl
    · have hle' : m₀ ≤ k := by omega
      rw [sumUpTo_succ, ih hle' (fun d hd1 hd2 => h d hd1 (by omega))]
      have hfk : f (k + 1) = 0 := h (k + 1) (by omega) (by omega)
      omega

/-- Evaluating `sumUpTo f m` when `f` is supported only at `d = 1`. -/
theorem sumUpTo_eq_single (f : Nat → Nat) (m : Nat)
    (hm : 1 ≤ m)
    (h : ∀ d : Nat, 1 ≤ d → d ≤ m → d ≠ 1 → f d = 0) :
    sumUpTo f m = f 1 := by
  have h1 : sumUpTo f m = sumUpTo f 1 :=
    sumUpTo_eq_of_gt_zero f 1 m hm (fun d hd1 hd2 => h d (by omega) hd2 (by omega))
  rw [h1]
  simp

/-- Evaluating `sumUpTo f m` when `f` is supported only at `{1, a}` with `1 < a ≤ m`. -/
theorem sumUpTo_eq_pair (f : Nat → Nat) (a m : Nat)
    (ha1 : 1 < a) (ham : a ≤ m)
    (h : ∀ d : Nat, 1 ≤ d → d ≤ m → d ≠ 1 → d ≠ a → f d = 0) :
    sumUpTo f m = f 1 + f a := by
  have h1 : sumUpTo f m = sumUpTo f a :=
    sumUpTo_eq_of_gt_zero f a m ham (fun d hd1 hd2 => h d (by omega) hd2 (by omega) (by omega))
  rw [h1]
  cases a with
  | zero => omega
  | succ a' =>
    rw [sumUpTo_succ]
    have h2 : sumUpTo f a' = f 1 :=
      sumUpTo_eq_single f a' (by omega) (fun d hd1 hd2 hdne1 =>
        h d hd1 (by omega) hdne1 (by omega))
    rw [h2]

/-- Evaluating `sumUpTo f m` when `f` is supported only at `{1, a, b}` with `1 < a < b ≤ m`. -/
theorem sumUpTo_eq_triple (f : Nat → Nat) (a b m : Nat)
    (ha1 : 1 < a) (hab : a < b) (hbm : b ≤ m)
    (h : ∀ d : Nat, 1 ≤ d → d ≤ m → d ≠ 1 → d ≠ a → d ≠ b → f d = 0) :
    sumUpTo f m = f 1 + f a + f b := by
  have h1 : sumUpTo f m = sumUpTo f b :=
    sumUpTo_eq_of_gt_zero f b m hbm
      (fun d hd1 hd2 => h d (by omega) hd2 (by omega) (by omega) (by omega))
  rw [h1]
  cases b with
  | zero => omega
  | succ b' =>
    rw [sumUpTo_succ]
    have h2 : sumUpTo f b' = f 1 + f a :=
      sumUpTo_eq_pair f a b' ha1 (by omega)
        (fun d hd1 hd2 hdne1 hdnea => h d hd1 (by omega) hdne1 hdnea (by omega))
    rw [h2]

/-- Modulo `p`, if every term `f d` for `d > 1` is a multiple of `p`, then
    `sumUpTo f m % p = f 1 % p`. -/
theorem sumUpTo_mod_eq_first (f : Nat → Nat) (m p : Nat)
    (hm : 1 ≤ m)
    (h : ∀ d : Nat, 1 < d → d ≤ m → f d % p = 0) :
    sumUpTo f m % p = f 1 % p := by
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      simp
    · rw [sumUpTo_succ]
      have ih' : sumUpTo f k % p = f 1 % p :=
        ih (by omega) (fun d hd1 hd2 => h d hd1 (by omega))
      have hfk : f (k + 1) % p = 0 := h (k + 1) (by omega) (by omega)
      rw [Nat.add_mod, ih', hfk, Nat.add_zero, Nat.mod_mod]

/-! ## Primality, Decidable Characterization, and Krizek's Prime Formula -/

/-- Arithmetic primality predicate on `Nat`: `p ≥ 2` and every divisor of `p`
    is `1` or `p`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Every prime has `1 < p`. -/
theorem one_lt_of_isPrime {p : Nat} (hp : IsPrime p) : 1 < p := by
  have h2 := hp.1
  omega

/-- Every prime has no proper divisor `d` with `1 < d < p`. -/
theorem not_proper_dvd_of_isPrime {p d : Nat} (hp : IsPrime p)
    (hd1 : 1 < d) (hdp : d < p) : ¬ (d ∣ p) := by
  intro hdvd
  rcases hp.2 d hdvd with rfl | rfl <;> omega

/-- For every prime `p`, `tau p = 2`. -/
theorem tau_of_isPrime {p : Nat} (hp : IsPrime p) : tau p = 2 := by
  unfold tau sumDiv sumDivUpTo
  have hp1 : 1 < p := one_lt_of_isPrime hp
  have hpair := sumUpTo_eq_pair
    (fun d => if dividesB d p then 1 else 0) p p hp1 (Nat.le_refl p)
    (by
      intro d hd1 hdp hdne1 hdnep
      have hndvd : ¬ (d ∣ p) := not_proper_dvd_of_isPrime hp (by omega) (by omega)
      have hb : dividesB d p = false := by
        cases h : dividesB d p
        · rfl
        · exfalso; exact hndvd (((dividesB_eq_true d p).mp h).2)
      rw [hb]
      rfl)
  rw [hpair, dividesB_one, dividesB_self (by omega)]
  rfl

/-- An integer `p` is prime if and only if `2 ≤ p` and `tau p = 2`. -/
theorem isPrime_iff_tau_eq_two (p : Nat) :
    IsPrime p ↔ 2 ≤ p ∧ tau p = 2 := by
  constructor
  · intro hp
    exact ⟨hp.1, tau_of_isPrime hp⟩
  · rintro ⟨hp2, htau⟩
    refine ⟨hp2, ?_⟩
    intro d hdvd
    have hdp : d ≤ p := Nat.le_of_dvd (by omega) hdvd
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    by_cases h1 : d = 1
    · exact Or.inl h1
    · by_cases hp : d = p
      · exact Or.inr hp
      · exfalso
        have h3 : 3 ≤ tau p :=
          tau_ge_three_of_proper_divisor (by omega) (by omega) hdvd
        omega

/-- Decidability of `IsPrime p` via `2 ≤ p ∧ tau p = 2`. -/
instance instDecidableIsPrime (p : Nat) : Decidable (IsPrime p) :=
  decidable_of_iff (2 ≤ p ∧ tau p = 2) (isPrime_iff_tau_eq_two p).symm

/-- **Krizek's Prime Formula (2014)**: For every prime $p$, $a(p) = 1$. -/
theorem a_of_isPrime {p : Nat} (hp : IsPrime p) : a p = 1 := by
  unfold a sumProperDiv sumDivUpTo
  have hp2 : 2 ≤ p := hp.1
  have hsingle := sumUpTo_eq_single
    (fun d => if dividesB d p then d * tau d else 0) (p - 1) (by omega)
    (by
      intro d hd1 hdp hdne1
      have hndvd : ¬ (d ∣ p) := not_proper_dvd_of_isPrime hp (by omega) (by omega)
      have hb : dividesB d p = false := by
        cases h : dividesB d p
        · rfl
        · exfalso; exact hndvd (((dividesB_eq_true d p).mp h).2)
      rw [hb]
      rfl)
  rw [hsingle, dividesB_one]
  rfl

/-- For every prime $p$, $a(p) < p$. -/
theorem a_lt_self_of_isPrime {p : Nat} (hp : IsPrime p) : a p < p := by
  rw [a_of_isPrime hp]
  exact one_lt_of_isPrime hp

/-- No prime $p$ satisfies $a(p) = p$. -/
theorem ne_self_of_isPrime {p : Nat} (hp : IsPrime p) : a p ≠ p := by
  have h := a_lt_self_of_isPrime hp
  omega

/-- No prime $p$ is a fixed point of $a$. -/
theorem not_isFixedPoint_of_isPrime {p : Nat} (hp : IsPrime p) :
    ¬ IsFixedPoint p := by
  intro ⟨_, hfp⟩
  exact ne_self_of_isPrime hp hfp

/-- Concrete primality certificates. -/
theorem isPrime_2 : IsPrime 2 := by decide
theorem isPrime_3 : IsPrime 3 := by decide
theorem isPrime_5 : IsPrime 5 := by decide
theorem isPrime_7 : IsPrime 7 := by decide
theorem isPrime_11 : IsPrime 11 := by decide
theorem isPrime_29 : IsPrime 29 := by decide

/-! ## Coprimality and Prime Power Exclusion -/

/-- If `p` is prime, `Nat.gcd d p` is either `1` or `p`. -/
theorem gcd_eq_one_or_self_of_isPrime {p d : Nat} (hp : IsPrime p) :
    Nat.gcd d p = 1 ∨ Nat.gcd d p = p :=
  hp.2 (Nat.gcd d p) (Nat.gcd_dvd_right d p)

/-- If `p` is prime, every `d` is either coprime to `p` or divisible by `p`. -/
theorem coprime_or_dvd_of_isPrime {p d : Nat} (hp : IsPrime p) :
    Nat.Coprime d p ∨ p ∣ d := by
  rcases gcd_eq_one_or_self_of_isPrime (d := d) hp with h1 | hp'
  · exact Or.inl h1
  · right
    rw [← hp']
    exact Nat.gcd_dvd_left d p

/-- If `Nat.Coprime d p` and `d ∣ p ^ k`, then `d = 1`. -/
theorem eq_one_of_coprime_of_dvd_pow {p d k : Nat}
    (hcop : Nat.Coprime d p) (hdvd : d ∣ p ^ k) : d = 1 := by
  induction k with
  | zero =>
    exact Nat.eq_one_of_dvd_one hdvd
  | succ k' ih =>
    rw [Nat.pow_succ] at hdvd
    have hdvd' : d ∣ p ^ k' := hcop.dvd_of_dvd_mul_right hdvd
    exact ih hdvd'

/-- Every divisor `d > 1` of a prime power `p ^ k` is divisible by `p`. -/
theorem dvd_of_dvd_prime_pow {p d k : Nat} (hp : IsPrime p)
    (hd1 : 1 < d) (hdvd : d ∣ p ^ k) : p ∣ d := by
  rcases coprime_or_dvd_of_isPrime (d := d) hp with hcop | hp_dvd
  · exfalso
    have heq : d = 1 := eq_one_of_coprime_of_dvd_pow hcop hdvd
    omega
  · exact hp_dvd

/-- For every prime $p$ and $k \ge 1$, $a(p^k) \equiv 1 \pmod p$. -/
theorem a_prime_pow_mod_p {p k : Nat} (hp : IsPrime p) (hk : 1 ≤ k) :
    a (p ^ k) % p = 1 := by
  unfold a sumProperDiv sumDivUpTo
  have hp2 : 2 ≤ p := hp.1
  have hpk_ge_p : p ≤ p ^ k := by
    rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
    rw [Nat.pow_add, Nat.pow_one]
    have hpm : 1 ≤ p ^ m := Nat.one_le_pow m p (by omega)
    exact Nat.le_mul_of_pos_right p hpm
  have hmod := sumUpTo_mod_eq_first
    (fun d => if dividesB d (p ^ k) then d * tau d else 0) (p ^ k - 1) p (by omega)
    (by
      intro d hd1 hdpk
      cases hb : dividesB d (p ^ k)
      · exact Nat.zero_mod p
      · have hdvd : d ∣ p ^ k := ((dividesB_eq_true d (p ^ k)).mp hb).2
        have hp_dvd_d : p ∣ d := dvd_of_dvd_prime_pow hp hd1 hdvd
        have hp_dvd_mul : p ∣ d * tau d := Nat.dvd_mul_right_of_dvd hp_dvd_d (tau d)
        exact Nat.mod_eq_zero_of_dvd hp_dvd_mul)
  rw [hmod, dividesB_one]
  change (1 * tau 1) % p = 1
  have ht1 : 1 * tau 1 = 1 := rfl
  rw [ht1]
  exact Nat.mod_eq_of_lt hp2

/-- For every prime $p$ and $k \ge 1$, $p^k \equiv 0 \pmod p$. -/
theorem prime_pow_mod_p (p k : Nat) (hk : 1 ≤ k) : (p ^ k) % p = 0 := by
  rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
  rw [Nat.pow_add, Nat.pow_one]
  exact Nat.mul_mod_right p (p ^ m)

/-- **Prime Power Exclusion**: For every prime $p$ and $k \ge 1$, $a(p^k) \ne p^k$. -/
theorem ne_self_of_prime_pow {p k : Nat} (hp : IsPrime p) (hk : 1 ≤ k) :
    a (p ^ k) ≠ p ^ k := by
  intro heq
  have h1 : a (p ^ k) % p = 1 := a_prime_pow_mod_p hp hk
  have h2 : (p ^ k) % p = 0 := prime_pow_mod_p p k hk
  rw [heq] at h1
  omega

/-- No prime power $p^k$ ($k \ge 1$) is a fixed point of $a$. -/
theorem not_isFixedPoint_prime_pow {p k : Nat} (hp : IsPrime p) (hk : 1 ≤ k) :
    ¬ IsFixedPoint (p ^ k) := by
  intro ⟨_, hfp⟩
  exact ne_self_of_prime_pow hp hk hfp

/-! ## Semiprime Closed-Form Formula and Fixed-Point Uniqueness -/

/-- Classification of all divisors of a product of two primes $p \cdot q$. -/
theorem dvd_mul_primes {p q d : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hdvd : d ∣ p * q) :
    d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  rcases coprime_or_dvd_of_isPrime (d := d) hp with hcop | ⟨k, rfl⟩
  · have hdvd_q : d ∣ q := hcop.dvd_of_dvd_mul_left hdvd
    rcases hq.2 d hdvd_q with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have hp_pos : 0 < p := by have := hp.1; omega
    have hk_dvd_q : k ∣ q := Nat.dvd_of_mul_dvd_mul_left hp_pos hdvd
    rcases hq.2 k hk_dvd_q with rfl | rfl
    · exact Or.inr (Or.inl (Nat.mul_one p))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- Classification of all proper divisors of $p \cdot q$ for primes $p < q$. -/
theorem proper_dvd_mul_primes {p q d : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hd_lt : d < p * q) (hdvd : d ∣ p * q) :
    d = 1 ∨ d = p ∨ d = q := by
  rcases dvd_mul_primes hp hq hdvd with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

/-- **Semiprime Closed-Form Formula**: For primes $p < q$,
    $a(p \cdot q) = 1 + 2p + 2q$. -/
theorem a_semiprime {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (hpq : p < q) :
    a (p * q) = 1 + 2 * p + 2 * q := by
  unfold a sumProperDiv sumDivUpTo
  have hp2 : 2 ≤ p := hp.1
  have hqp : q ≤ p * q - 1 := by
    have hmul : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp2
    omega
  have htriple := sumUpTo_eq_triple
    (fun d => if dividesB d (p * q) then d * tau d else 0) p q (p * q - 1)
    (by omega) hpq hqp
    (by
      intro d hd1 hdpq hdne1 hdnep hdneq
      cases hb : dividesB d (p * q)
      · rfl
      · exfalso
        have hdvd : d ∣ p * q := ((dividesB_eq_true d (p * q)).mp hb).2
        rcases proper_dvd_mul_primes hp hq (by omega) hdvd with rfl | rfl | rfl <;> omega)
  rw [htriple]
  have hb1 : dividesB 1 (p * q) = true := dividesB_one (p * q)
  have hbp : dividesB p (p * q) = true :=
    (dividesB_eq_true p (p * q)).mpr ⟨by omega, Nat.dvd_mul_right p q⟩
  have hbq : dividesB q (p * q) = true :=
    (dividesB_eq_true q (p * q)).mpr ⟨by omega, Nat.dvd_mul_left q p⟩
  have ht1 : (if dividesB 1 (p * q) = true then 1 * tau 1 else 0) = 1 := by
    rw [hb1, tau_1]
    rfl
  have htp : (if dividesB p (p * q) = true then p * tau p else 0) = 2 * p := by
    rw [hbp, tau_of_isPrime hp]
    exact Nat.mul_comm p 2
  have htq : (if dividesB q (p * q) = true then q * tau q else 0) = 2 * q := by
    rw [hbq, tau_of_isPrime hq]
    exact Nat.mul_comm q 2
  rw [ht1, htp, htq]

/-- **Krizek's Even Semiprime Formula (2014)**: For every odd prime $p > 2$,
    $a(2p) = 2p + 5$. -/
theorem a_two_mul_odd_prime {p : Nat} (hp : IsPrime p) (hp2 : 2 < p) :
    a (2 * p) = 2 * p + 5 := by
  have h := a_semiprime isPrime_2 hp hp2
  omega

/-- For every prime $p > 3$, $a(3p) = 2p + 7$. -/
theorem a_three_mul_prime {p : Nat} (hp : IsPrime p) (hp3 : 3 < p) :
    a (3 * p) = 2 * p + 7 := by
  have h := a_semiprime isPrime_3 hp hp3
  omega

/-- Diophantine factorization for distinct-prime semiprime fixed points:
    if $2 \le p < q$ and $1 + 2p + 2q = pq$, then $p = 3$ and $q = 7$. -/
theorem semiprime_diophantine_eq {p q : Nat} (hp2 : 2 ≤ p) (hpq : p < q)
    (heq : 1 + 2 * p + 2 * q = p * q) :
    p = 3 ∧ q = 7 := by
  have hp_not_2 : p ≠ 2 := by
    intro h
    subst h
    omega
  have hp_lt_5 : p < 5 := by
    by_cases hlt : p < 5
    · exact hlt
    · exfalso
      have h1 : 5 * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
      have h2 : 2 * p < 2 * q := by omega
      omega
  have hp_ne_4 : p ≠ 4 := by
    intro h
    subst h
    omega
  have hp3 : p = 3 := by omega
  subst hp3
  exact ⟨rfl, by omega⟩

/-- **Semiprime Fixed-Point Uniqueness**: Among all semiprimes $p \cdot q$ with
    primes $p \le q$, $a(p \cdot q) = p \cdot q$ holds if and only if $p = 3$ and $q = 7$
    ($n = 21$). -/
theorem semiprime_fixedPoint_iff {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hpq : p ≤ q) :
    IsFixedPoint (p * q) ↔ p = 3 ∧ q = 7 := by
  constructor
  · intro hfp
    rcases Nat.eq_or_lt_of_le hpq with rfl | hlt
    · exfalso
      have hpow : p * p = p ^ 2 := by
        rw [Nat.pow_succ, Nat.pow_one]
      rw [hpow] at hfp
      exact not_isFixedPoint_prime_pow hp (by omega) hfp
    · have ha : a (p * q) = 1 + 2 * p + 2 * q := a_semiprime hp hq hlt
      have heq : 1 + 2 * p + 2 * q = p * q := by
        rw [← ha]
        exact hfp.2
      exact semiprime_diophantine_eq hp.1 hlt heq
  · rintro ⟨rfl, rfl⟩
    exact isFixedPoint_21

/-! ## Unconditional Uniqueness Among Multiples of 3 -/

/-- Every integer $m \ge 2$ that is not prime has a proper divisor $1 < d < m$. -/
theorem exists_proper_divisor_of_not_isPrime {m : Nat} (hm2 : 2 ≤ m)
    (hnp : ¬ IsPrime m) :
    ∃ d : Nat, 1 < d ∧ d < m ∧ d ∣ m := by
  exact Classical.byContradiction fun hno =>
    hnp ⟨hm2, fun d hdvd => by
      have hdm : d ≤ m := Nat.le_of_dvd (by omega) hdvd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      by_cases h1 : d = 1
      · exact Or.inl h1
      · by_cases hm : d = m
        · exact Or.inr hm
        · exfalso
          exact hno ⟨d, by omega, by omega, hdvd⟩⟩

/-- **Multiples-of-3 Fixed-Point Uniqueness**: Among all multiples of $3$,
    $n = 21$ is unconditionally the unique fixed point of $a(n)$. -/
theorem three_dvd_fixedPoint_iff_eq_21 (n : Nat) (h3 : 3 ∣ n) :
    IsFixedPoint n ↔ n = 21 := by
  constructor
  · intro hfp
    rcases h3 with ⟨m, rfl⟩
    have hm_pos : 1 ≤ m := by
      have hn_pos := hfp.1
      omega
    by_cases hm1 : m = 1
    · subst hm1
      exfalso; exact not_isFixedPoint_3 hfp
    · have hm2 : 2 ≤ m := by omega
      by_cases hpm : IsPrime m
      · by_cases hm2' : m = 2
        · subst hm2'
          exfalso; exact not_isFixedPoint_6 hfp
        · by_cases hm3 : m = 3
          · subst hm3
            exfalso; exact not_isFixedPoint_9 hfp
          · have hm_gt_3 : 3 < m := by omega
            have hsemi := (semiprime_fixedPoint_iff isPrime_3 hpm (by omega)).mp hfp
            rcases hsemi with ⟨_, rfl⟩
            rfl
      · exfalso
        rcases exists_proper_divisor_of_not_isPrime hm2 hpm with ⟨d, hd1, hdm, hdvd⟩
        exact not_isFixedPoint_three_mul_of_proper_divisor hd1 hdm hdvd hfp
  · rintro rfl
    exact isFixedPoint_21

/-! ## Three-Prime-Factor ($\Omega(n) = 3$) Diophantine Identities and Exclusions -/

/-- Exact polynomial identity governing $a(p^2 q)$ for primes $p \ne q$:
    $(p^2 - 4p - 2)(q - 3) + (1 + 2p + 3p^2 + 2q + 4pq) = p^2 q + 7(2p + 1)$.
    When $p = 5$ ($p^2 - 4p - 2 = 3$) and $q = 29$ ($q - 3 = 26$),
    $3 \cdot 26 = 78 = 7 \cdot 11 + 1$, giving $a(725) = 724 = 725 - 1$. -/
theorem p2q_near_miss_identity (p q : Nat) (hp : 5 ≤ p) (hq : 3 ≤ q) :
    (p * p - 4 * p - 2) * (q - 3) + (1 + 2 * p + 3 * p * p + 2 * q + 4 * p * q) =
      p * p * q + 7 * (2 * p + 1) := by
  rcases Nat.exists_eq_add_of_le hp with ⟨a, rfl⟩
  rcases Nat.exists_eq_add_of_le hq with ⟨b, rfl⟩
  have hsub1 : (5 + a) * (5 + a) - 4 * (5 + a) - 2 = 3 + 6 * a + a * a := by
    have hmul : (5 + a) * (5 + a) = 25 + 10 * a + a * a := by grind
    omega
  have hsub2 : 3 + b - 3 = b := by omega
  rw [hsub1, hsub2]
  grind

/-- Parity obstruction for odd $p^2 q$: for all odd $p$ and odd $q$,
    $1 + 2p + 3p^2 + 2q + 4pq$ is even while $p^2 q$ is odd, so they are never equal. -/
theorem odd_p2q_formula_ne_self (p q : Nat) (hp_odd : p % 2 = 1) (hq_odd : q % 2 = 1) :
    1 + 2 * p + 3 * p * p + 2 * q + 4 * p * q ≠ p * p * q := by
  intro heq
  have hp_div : p = 2 * (p / 2) + 1 := by omega
  have hq_div : q = 2 * (q / 2) + 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, hp_div⟩
  obtain ⟨m, hm⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, hq_div⟩
  subst hk hm
  have hmod1 : (1 + 2 * (2 * k + 1) + 3 * (2 * k + 1) * (2 * k + 1) +
      2 * (2 * m + 1) + 4 * (2 * k + 1) * (2 * m + 1)) % 2 = 0 := by
    have heven : 1 + 2 * (2 * k + 1) + 3 * (2 * k + 1) * (2 * k + 1) +
        2 * (2 * m + 1) + 4 * (2 * k + 1) * (2 * m + 1) =
        2 * (4 + 8 * k + 6 * k * k + 4 * m + 8 * k * m + 2 * m + 2 * k) := by grind
    rw [heven]
    omega
  have hmod2 : ((2 * k + 1) * (2 * k + 1) * (2 * m + 1)) % 2 = 1 := by
    have hodd : (2 * k + 1) * (2 * k + 1) * (2 * m + 1) =
        2 * (4 * k * k * m + 2 * k * k + 4 * k * m + 2 * k + m) + 1 := by grind
    rw [hodd]
    omega
  rw [heq] at hmod1
  omega

/-- Auxiliary growth bound for three distinct primes $11 \le p < q < r$:
    $2431 (2p + 1)(2q + 1)(2r + 1) \le 21735 p q r < 2431 \cdot 9 p q r$. -/
theorem three_prime_growth_bound (p q r : Nat)
    (hp : 11 ≤ p) (hq : 13 ≤ q) (hr : 17 ≤ r) :
    2431 * ((2 * p + 1) * (2 * q + 1) * (2 * r + 1)) ≤ 21735 * (p * q * r) := by
  have h1 : 11 * (2 * p + 1) ≤ 23 * p := by omega
  have h2 : 13 * (2 * q + 1) ≤ 27 * q := by omega
  have h3 : 17 * (2 * r + 1) ≤ 35 * r := by omega
  have h12 : (11 * (2 * p + 1)) * (13 * (2 * q + 1)) ≤ (23 * p) * (27 * q) :=
    Nat.mul_le_mul h1 h2
  have h123 : ((11 * (2 * p + 1)) * (13 * (2 * q + 1))) * (17 * (2 * r + 1)) ≤
      ((23 * p) * (27 * q)) * (35 * r) :=
    Nat.mul_le_mul h12 h3
  have lhs_eq : ((11 * (2 * p + 1)) * (13 * (2 * q + 1))) * (17 * (2 * r + 1)) =
      2431 * ((2 * p + 1) * (2 * q + 1) * (2 * r + 1)) := by grind
  have rhs_eq : ((23 * p) * (27 * q)) * (35 * r) = 21735 * (p * q * r) := by grind
  rw [lhs_eq, rhs_eq] at h123
  exact h123

/-- **Squarefree Three-Prime Exclusion**: For all primes $p < q < r$, the
    full first-moment product $(2p + 1)(2q + 1)(2r + 1)$ never equals
    $9 p q r = p q r (\tau(pqr) + 1)$. -/
theorem three_prime_moment_ne {p q r : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hpq : p < q) (hqr : q < r) :
    (2 * p + 1) * (2 * q + 1) * (2 * r + 1) ≠ 9 * p * q * r := by
  intro heq
  have hp2 : 2 ≤ p := hp.1
  by_cases hp11 : 11 ≤ p
  · have hq13 : 13 ≤ q := by
      by_cases hq12 : q = 12
      · exfalso
        have h2 : ¬ IsPrime 12 := by decide
        exact h2 (hq12 ▸ hq)
      · omega
    have hr17 : 17 ≤ r := by
      by_cases hr14 : r = 14
      · exfalso; exact (by decide : ¬ IsPrime 14) (hr14 ▸ hr)
      · by_cases hr15 : r = 15
        · exfalso; exact (by decide : ¬ IsPrime 15) (hr15 ▸ hr)
        · by_cases hr16 : r = 16
          · exfalso; exact (by decide : ¬ IsPrime 16) (hr16 ▸ hr)
          · omega
    have hbound := three_prime_growth_bound p q r hp11 hq13 hr17
    have heq' : (2 * p + 1) * (2 * q + 1) * (2 * r + 1) = 9 * (p * q * r) := by
      calc (2 * p + 1) * (2 * q + 1) * (2 * r + 1) = 9 * p * q * r := heq
      _ = 9 * (p * q * r) := by grind
    rw [heq'] at hbound
    have hpqr_pos : 0 < p * q * r := by
      have hp_pos : 0 < p := by omega
      have hq_pos : 0 < q := by omega
      have hr_pos : 0 < r := by omega
      exact Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos
    omega
  · -- Now `2 ≤ p < 11`, so `p ∈ {2, 3, 5, 7}` since `p` is prime
    have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      by_cases h4 : p = 4
      · exfalso; exact (by decide : ¬ IsPrime 4) (h4 ▸ hp)
      · by_cases h6 : p = 6
        · exfalso; exact (by decide : ¬ IsPrime 6) (h6 ▸ hp)
        · by_cases h8 : p = 8
          · exfalso; exact (by decide : ¬ IsPrime 8) (h8 ▸ hp)
          · by_cases h9 : p = 9
            · exfalso; exact (by decide : ¬ IsPrime 9) (h9 ▸ hp)
            · by_cases h10 : p = 10
              · exfalso; exact (by decide : ¬ IsPrime 10) (h10 ▸ hp)
              · omega
    rcases hp_cases with rfl | rfl | rfl | rfl
    · -- Case `p = 2`: `5 * (2q + 1)(2r + 1) = 18 q r` (odd = even, impossible)
      have hmod : ((2 * 2 + 1) * (2 * q + 1) * (2 * r + 1)) % 2 = 1 := by
        have hodd : (2 * 2 + 1) * (2 * q + 1) * (2 * r + 1) =
            2 * (10 * q * r + 5 * q + 5 * r + 2) + 1 := by grind
        rw [hodd]
        omega
      have hmod2 : (9 * 2 * q * r) % 2 = 0 := by
        have hev : 9 * 2 * q * r = 2 * (9 * q * r) := by grind
        rw [hev]
        omega
      rw [heq] at hmod
      omega
    · -- Case `p = 3`: `7 * (2q + 1)(2r + 1) = 27 q r`
      have hdvd7 : 7 ∣ 27 * (q * r) := ⟨(2 * q + 1) * (2 * r + 1), by grind⟩
      have hcop27 : Nat.Coprime 7 27 := by decide
      have hdvd_qr : 7 ∣ q * r := hcop27.dvd_of_dvd_mul_left hdvd7
      rcases coprime_or_dvd_of_isPrime (d := q) isPrime_7 with hcop7q | h7q
      · have h7r : 7 ∣ r := hcop7q.symm.dvd_of_dvd_mul_left hdvd_qr
        rcases hr.2 7 h7r with h1 | rfl <;> omega
      · rcases hq.2 7 h7q with h1 | rfl
        · omega
        · grind
    · -- Case `p = 5`: `11 * (2q + 1)(2r + 1) = 45 q r`, so `11 ∣ q * r`
      have hdvd11 : 11 ∣ 45 * (q * r) := ⟨(2 * q + 1) * (2 * r + 1), by grind⟩
      have hcop45 : Nat.Coprime 11 45 := by decide
      have hdvd_qr : 11 ∣ q * r := hcop45.dvd_of_dvd_mul_left hdvd11
      rcases coprime_or_dvd_of_isPrime (d := q) isPrime_11 with hcop11q | h11q
      · have h11r : 11 ∣ r := hcop11q.symm.dvd_of_dvd_mul_left hdvd_qr
        rcases hr.2 11 h11r with h1 | rfl <;> omega
      · rcases hq.2 11 h11q with h1 | rfl
        · omega
        · grind
    · -- Case `p = 7`: `15 * (2q + 1)(2r + 1) = 63 q r`, so `5 ∣ 63 q r`
      have hdvd5 : 5 ∣ 63 * (q * r) := ⟨3 * (2 * q + 1) * (2 * r + 1), by grind⟩
      have hcop63 : Nat.Coprime 5 63 := by decide
      have hdvd_qr : 5 ∣ q * r := hcop63.dvd_of_dvd_mul_left hdvd5
      rcases coprime_or_dvd_of_isPrime (d := q) isPrime_5 with hcop5q | h5q
      · have h5r : 5 ∣ r := hcop5q.symm.dvd_of_dvd_mul_left hdvd_qr
        rcases hr.2 5 h5r with h1 | rfl <;> omega
      · rcases hq.2 5 h5q with h1 | rfl <;> omega

end OeisA245211
