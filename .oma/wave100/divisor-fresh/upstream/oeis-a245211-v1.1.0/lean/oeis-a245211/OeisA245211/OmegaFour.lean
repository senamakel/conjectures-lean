/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/
import OeisA245211.Basic
import OeisA245211.Dominance
import OeisA245211.Families
import OeisA245211.Parity

/-!
# OEIS A245211: Complete Classification of $\Omega(n) \le 4$ and Partial $\Omega(n) = 5$ Exclusions

This module proves the unconditional exclusion of all integers with $\Omega(n) = 4$ prime factors
counted with multiplicity, establishes `omegaBig n` ($\Omega(n)$), proves that every fixed point
`n ≠ 21` satisfies `Nat.gcd n 6 = 1` and `5 ≤ omegaBig n`, and proves the closed exclusions for
$\Omega(n) = 5$ (all non-squarefree families `p^5`, `p^4 q`, `p^3 q^2`, `p^3 q r`, `p^2 q^2 r`,
`p^2 q r s`, plus the lower bound `17 ≤ p` on the smallest prime factor of any squarefree 5-prime
fixed point `p q r s t`).
-/

namespace OeisA245211

/-! ## Prime-Factor Multiplicity Function `omegaBig` ($\Omega(n)$) -/

section OmegaBig

/-- Smallest divisor helper searching downwards from `n - 1` to `n - k`. -/
def leastFactorAux (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 =>
    let d := n - (k + 1)
    if 2 ≤ d ∧ d ∣ n then d else leastFactorAux n k

/-- Smallest divisor `≥ 2` of `n` (equals `n` if `n ≤ 1`). -/
def minFac (n : Nat) : Nat :=
  if n ≤ 1 then n else leastFactorAux n (n - 2)

theorem leastFactorAux_spec (n : Nat) (hn : 2 ≤ n) :
    ∀ k, k ≤ n - 2 →
      (∀ x, 2 ≤ x → x < n - k → ¬ (x ∣ n)) →
      2 ≤ leastFactorAux n k ∧ leastFactorAux n k ∣ n ∧
      (∀ x, 2 ≤ x → x < leastFactorAux n k → ¬ (x ∣ n))
  | 0, _, hno => by
    unfold leastFactorAux
    refine ⟨hn, Nat.dvd_refl n, fun x hx1 hx2 => hno x hx1 (by omega)⟩
  | k + 1, hk, hno => by
    unfold leastFactorAux
    dsimp only
    split
    · next hyes =>
      refine ⟨hyes.1, hyes.2, fun x hx1 hx2 => hno x hx1 ?_⟩
      omega
    · next hnot =>
      apply leastFactorAux_spec n hn k (by omega)
      intro x hx1 hx2
      by_cases heq : x = n - (k + 1)
      · subst heq
        intro hdvd
        exact hnot ⟨hx1, hdvd⟩
      · exact hno x hx1 (by omega)

theorem minFac_isPrime {n : Nat} (hn : 2 ≤ n) : IsPrime (minFac n) := by
  unfold minFac
  have hnot : ¬ (n ≤ 1) := by omega
  split
  · next hle => exact absurd hle hnot
  · have hspec := leastFactorAux_spec n hn (n - 2) (Nat.le_refl _) (fun x hx1 hx2 => by omega)
    refine ⟨hspec.1, fun d hdvd => ?_⟩
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · have hd2 : 2 ≤ d := by omega
      have hle : d ≤ leastFactorAux n (n - 2) := Nat.le_of_dvd (by omega) hdvd
      by_cases heq : d = leastFactorAux n (n - 2)
      · exact Or.inr heq
      · exfalso
        exact hspec.2.2 d hd2 (by omega) (Nat.dvd_trans hdvd hspec.2.1)

theorem minFac_dvd (n : Nat) : minFac n ∣ n := by
  unfold minFac
  split
  · exact Nat.dvd_refl n
  · next hnot =>
    have hn : 2 ≤ n := by omega
    exact (leastFactorAux_spec n hn (n - 2) (Nat.le_refl _) (fun x hx1 hx2 => by omega)).2.1

theorem minFac_le_of_dvd {n d : Nat} (hd2 : 2 ≤ d) (hdvd : d ∣ n) (hn : 2 ≤ n) :
    minFac n ≤ d := by
  unfold minFac
  have hnot : ¬ (n ≤ 1) := by omega
  split
  · next hle => exact absurd hle hnot
  · have hspec := leastFactorAux_spec n hn (n - 2) (Nat.le_refl _) (fun x hx1 hx2 => by omega)
    by_cases hlt : d < leastFactorAux n (n - 2)
    · exfalso; exact hspec.2.2 d hd2 hlt hdvd
    · omega

/-- Total prime factor count with multiplicity $\Omega(n)$ (OEIS A001222), defined by
    well-founded division by `minFac n`. -/
def omegaBig : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    let p := minFac (n + 2)
    1 + omegaBig ((n + 2) / p)
termination_by n => n
decreasing_by
  have hp_ge2 : 2 ≤ minFac (n + 2) := (minFac_isPrime (by omega)).1
  exact Nat.div_lt_self (by omega) hp_ge2

@[simp]
theorem omegaBig_zero : omegaBig 0 = 0 := by simp [omegaBig]

@[simp]
theorem omegaBig_one : omegaBig 1 = 0 := by simp [omegaBig]

theorem omegaBig_eq_succ_div_minFac {n : Nat} (hn : 2 ≤ n) :
    omegaBig n = 1 + omegaBig (n / minFac n) := by
  match n, hn with
  | k + 2, _ =>
    rw [omegaBig]

/-- Distinct primes are coprime. -/
theorem coprime_primes_ne {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (hne : p ≠ q) :
    Nat.Coprime p q := by
  rcases coprime_or_dvd_of_isPrime (d := p) hq with hcop | hdvd
  · exact hcop
  · rcases hp.2 q hdvd with h1 | heq
    · have := hq.1; omega
    · exact absurd heq.symm hne

theorem omegaBig_prime_mul_aux :
    ∀ k p m : Nat, p * m ≤ k → IsPrime p → 0 < m →
      omegaBig (p * m) = 1 + omegaBig m
  | 0, p, m, hle, hp, hm => by
    have := hp.1
    have : 2 ≤ p * m := by
      have : 2 * 1 ≤ p * m := Nat.mul_le_mul this hm
      omega
    omega
  | k + 1, p, m, hle, hp, hm => by
    have hp2 : 2 ≤ p := hp.1
    have hpm_ge2 : 2 ≤ p * m := by
      have : 2 * 1 ≤ p * m := Nat.mul_le_mul hp2 hm
      omega
    rw [omegaBig_eq_succ_div_minFac hpm_ge2]
    have hq_prime : IsPrime (minFac (p * m)) := minFac_isPrime hpm_ge2
    have hq_dvd : minFac (p * m) ∣ p * m := minFac_dvd (p * m)
    by_cases hqp : minFac (p * m) = p
    · rw [hqp, Nat.mul_div_right m (by omega)]
    · have hcop : Nat.Coprime (minFac (p * m)) p := coprime_primes_ne hq_prime hp hqp
      have hq_dvd_m : minFac (p * m) ∣ m := hcop.dvd_of_dvd_mul_left hq_dvd
      obtain ⟨m', hm_eq⟩ := hq_dvd_m
      have hm'_pos : 0 < m' := by
        by_cases hm0 : m' = 0
        · subst hm0; omega
        · omega
      have hq2 : 2 ≤ minFac (p * m) := hq_prime.1
      have hpm'_lt : p * m' < p * m := by
        rw [hm_eq]
        have : 1 * m' < minFac (p * m) * m' := Nat.mul_lt_mul_of_pos_right (by omega) hm'_pos
        have : m' < minFac (p * m) * m' := by omega
        exact Nat.mul_lt_mul_of_pos_left this (by omega)
      have hdiv_eq : (p * m) / minFac (p * m) = p * m' := by
        have hpm_eq : p * m = minFac (p * m) * (p * m') := by grind
        calc (p * m) / minFac (p * m)
            = (minFac (p * m) * (p * m')) / minFac (p * m) := by rw [← hpm_eq]
          _ = minFac (p * m) * (p * m') / minFac (p * m) := rfl
          _ = p * m' := Nat.mul_div_right (p * m') (by omega)
      have ih1 : omegaBig (p * m') = 1 + omegaBig m' :=
        omegaBig_prime_mul_aux k p m' (by omega) hp hm'_pos
      have hm_lt : minFac (p * m) * m' < p * m := by
        rw [← hm_eq]
        have : 1 * m < p * m := Nat.mul_lt_mul_of_pos_right (by omega) hm
        omega
      have ih2 : omegaBig (minFac (p * m) * m') = 1 + omegaBig m' :=
        omegaBig_prime_mul_aux k (minFac (p * m)) m' (by omega) hq_prime hm'_pos
      rw [hdiv_eq, ih1]
      have hrhs_eq : omegaBig m = omegaBig (minFac (p * m) * m') := congrArg omegaBig hm_eq
      rw [hrhs_eq, ih2]

theorem omegaBig_prime_mul {p m : Nat} (hp : IsPrime p) (hm : 0 < m) :
    omegaBig (p * m) = 1 + omegaBig m :=
  omegaBig_prime_mul_aux (p * m) p m (Nat.le_refl _) hp hm

theorem omegaBig_of_isPrime {p : Nat} (hp : IsPrime p) :
    omegaBig p = 1 := by
  have h := omegaBig_prime_mul hp (by decide : 0 < 1)
  simpa using h

theorem omegaBig_prime_pow {p : Nat} (hp : IsPrime p) :
    ∀ e : Nat, omegaBig (p ^ e) = e
  | 0 => by simp
  | e + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm, omegaBig_prime_mul hp (Nat.pow_pos (by have := hp.1; omega)),
      omegaBig_prime_pow hp e]
    omega

theorem omegaBig_mul_aux :
    ∀ k u v : Nat, u ≤ k → 0 < u → 0 < v →
      omegaBig (u * v) = omegaBig u + omegaBig v
  | 0, u, _, hu_le, hu_pos, _ => by omega
  | k + 1, u, v, hu_le, hu_pos, hv_pos => by
    by_cases hu1 : u = 1
    · subst hu1; simp
    · have hu2 : 2 ≤ u := by omega
      have hp : IsPrime (minFac u) := minFac_isPrime hu2
      obtain ⟨u', hu_eq⟩ := minFac_dvd u
      have hu'_pos : 0 < u' := by
        by_cases hm0 : u' = 0
        · subst hm0; omega
        · omega
      have hp2 : 2 ≤ minFac u := hp.1
      have hu'_lt : u' < u := by
        have hlt : 1 * u' < minFac u * u' := Nat.mul_lt_mul_of_pos_right (by omega) hu'_pos
        rw [← hu_eq] at hlt
        omega
      have ih : omegaBig (u' * v) = omegaBig u' + omegaBig v :=
        omegaBig_mul_aux k u' v (by omega) hu'_pos hv_pos
      have h1 : omegaBig (u * v) = 1 + omegaBig (u' * v) := by
        have huv : u * v = minFac u * (u' * v) := by
          calc u * v = (minFac u * u') * v := by rw [← hu_eq]
            _ = minFac u * (u' * v) := Nat.mul_assoc _ _ _
        rw [huv]
        exact omegaBig_prime_mul hp (Nat.mul_pos hu'_pos hv_pos)
      have h2 : omegaBig u = 1 + omegaBig u' := by
        calc omegaBig u = omegaBig (minFac u * u') := congrArg omegaBig hu_eq
          _ = 1 + omegaBig u' := omegaBig_prime_mul hp hu'_pos
      rw [h1, h2, ih]
      omega

theorem omegaBig_mul {u v : Nat} (hu : 0 < u) (hv : 0 < v) :
    omegaBig (u * v) = omegaBig u + omegaBig v :=
  omegaBig_mul_aux u u v (Nat.le_refl _) hu hv

end OmegaBig

/-! ## Complete Unconditional Exclusion of $\Omega(n) = 4$ -/

section OmegaFourExclusions

/-- **Family `(3, 1)`: `p^3 * q` exclusion**:
    For distinct primes `p ≠ q`, `p ^ 3 * q` is never a fixed point of OEIS A245211. -/
theorem not_isFixedPoint_prime_cube_mul_prime {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hne : p ≠ q) :
    ¬ IsFixedPoint (p ^ 3 * q) := by
  have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq hne
  have hcop : Nat.Coprime (p ^ 3) q := hcop_pq.pow_left 3
  have hp_pos : 0 < p := by have := hp.1; omega
  have hq_pos : 0 < q := by have := hq.1; omega
  have htau : tau (p ^ 3 * q) = 8 := by
    rw [tau_mul_of_coprime hcop (Nat.pow_pos hp_pos) hq_pos, tau_prime_pow hp 3, tau_of_isPrime hq]
  have htau_even : tau (p ^ 3 * q) % 2 = 0 := by rw [htau]
  have hdvd : p ^ 3 ∣ p ^ 3 * q := Nat.dvd_mul_right (p ^ 3) q
  have hndvd : ¬ (p ^ (3 + 1) ∣ p ^ 3 * q) := by
    intro h
    rw [Nat.pow_succ] at h
    have hq_dvd : p ∣ q := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp_pos) h
    rcases hq.2 p hq_dvd with h1 | heq
    · have := hp.1; omega
    · exact hne heq
  exact not_isFixedPoint_of_exact_exponent_mod_four_ge_two htau_even hp hdvd hndvd (Or.inr rfl)

/-- **Family `(2, 1, 1)`: `p^2 * q * r` exclusion**:
    For pairwise distinct primes `p, q, r`, `p ^ 2 * q * r` is never a fixed point. -/
theorem not_isFixedPoint_prime_sq_mul_two_primes {p q r : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ IsFixedPoint (p ^ 2 * q * r) := by
  have hp_pos : 0 < p := by have := hp.1; omega
  have hq_pos : 0 < q := by have := hq.1; omega
  have hr_pos : 0 < r := by have := hr.1; omega
  have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq hpq
  have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
  have hcop_qr : Nat.Coprime q r := coprime_primes_ne hq hr hqr
  have hcop_p2_qr : Nat.Coprime (p ^ 2) (q * r) :=
    (hcop_pq.mul_right hcop_pr).pow_left 2
  have htau : tau (p ^ 2 * q * r) = 12 := by
    rw [Nat.mul_assoc, tau_mul_of_coprime hcop_p2_qr (Nat.pow_pos hp_pos) (Nat.mul_pos hq_pos hr_pos),
      tau_prime_pow hp 2, tau_mul_of_coprime hcop_qr hq_pos hr_pos, tau_of_isPrime hq, tau_of_isPrime hr]
  have htau_even : tau (p ^ 2 * q * r) % 2 = 0 := by rw [htau]
  have hdvd : p ^ 2 ∣ p ^ 2 * q * r := by
    rw [Nat.mul_assoc]
    exact Nat.dvd_mul_right (p ^ 2) (q * r)
  have hndvd : ¬ (p ^ (2 + 1) ∣ p ^ 2 * q * r) := by
    intro h
    rw [Nat.pow_succ, Nat.mul_assoc] at h
    have hp_dvd_qr : p ∣ q * r := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp_pos) h
    have hp_dvd_r : p ∣ r := hcop_pq.dvd_of_dvd_mul_left hp_dvd_qr
    rcases hr.2 p hp_dvd_r with h1 | heq
    · have := hp.1; omega
    · exact hpr heq
  exact not_isFixedPoint_of_exact_exponent_mod_four_ge_two htau_even hp hdvd hndvd (Or.inl rfl)

/-- Modulo-5 obstruction: `3 * x ^ 2 + 2 * x + 1` is never divisible by `5` for any `x : Nat`. -/
theorem three_sq_add_two_mul_add_one_mod_five_ne_zero (x : Nat) :
    (3 * x * x + 2 * x + 1) % 5 ≠ 0 := by
  have hx : x = 5 * (x / 5) + x % 5 := (Nat.div_add_mod x 5).symm
  have hm : x % 5 < 5 := Nat.mod_lt x (by decide)
  have hmod : (3 * x * x + 2 * x + 1) % 5 =
      (3 * (x % 5) * (x % 5) + 2 * (x % 5) + 1) % 5 := by
    have h1 : (3 * x * x + 2 * x + 1) % 5 =
        ((3 * (x % 5) * (x % 5) + 2 * (x % 5) + 1) +
          5 * (15 * (x / 5) * (x / 5) + 6 * (x / 5) * (x % 5) + 2 * (x / 5))) % 5 := by
      have heq : 3 * x * x + 2 * x + 1 =
          (3 * (x % 5) * (x % 5) + 2 * (x % 5) + 1) +
            5 * (15 * (x / 5) * (x / 5) + 6 * (x / 5) * (x % 5) + 2 * (x / 5)) := by
        calc 3 * x * x + 2 * x + 1
            = 3 * (5 * (x / 5) + x % 5) * (5 * (x / 5) + x % 5) +
                2 * (5 * (x / 5) + x % 5) + 1 := by rw [← hx]
          _ = _ := by grind
      rw [heq]
    rw [h1, Nat.add_mul_mod_self_left]
  rw [hmod]
  have hcases : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
  rcases hcases with h | h | h | h | h <;> rw [h] <;> decide

/-- **Family `(2, 2)`: `p^2 * q^2` Diophantine exclusion**:
    For all integers `p, q`, `(3*p^2 + 2*p + 1) * (3*q^2 + 2*q + 1) ≠ 10 * p^2 * q^2`.
    This follows unconditionally modulo `5` (and for `p ≥ 13, q ≥ 17`, the left-hand side is
    strictly smaller than `10 * p^2 * q^2`). -/
theorem p2q2_diophantine_ne (p q : Nat) :
    (3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1) ≠ 10 * p * p * q * q := by
  intro heq
  have hdvd5 : 5 ∣ (3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1) := by
    rw [heq]
    exact ⟨2 * p * p * q * q, by grind⟩
  rcases coprime_or_dvd_of_isPrime (d := 3 * p * p + 2 * p + 1) isPrime_5 with hcop | hdvd_p
  · have hdvd_q : 5 ∣ 3 * q * q + 2 * q + 1 := hcop.symm.dvd_of_dvd_mul_left hdvd5
    exact three_sq_add_two_mul_add_one_mod_five_ne_zero q (Nat.mod_eq_zero_of_dvd hdvd_q)
  · exact three_sq_add_two_mul_add_one_mod_five_ne_zero p (Nat.mod_eq_zero_of_dvd hdvd_p)

/-- Exact evaluation of `fullMoment (p ^ 2)` for prime `p`: `3 * p^2 + 2 * p + 1`. -/
theorem fullMoment_prime_sq {p : Nat} (hp : IsPrime p) :
    fullMoment (p ^ 2) = 3 * p * p + 2 * p + 1 := by
  rw [fullMoment_prime_pow_succ hp 1, fullMoment_prime_pow_succ hp 0, fullMoment_prime_pow_zero]
  grind

/-- Unconditional exclusion of `p ^ 2 * q ^ 2` for distinct primes `p ≠ q`. -/
theorem not_isFixedPoint_prime_sq_mul_prime_sq {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hne : p ≠ q) :
    ¬ IsFixedPoint (p ^ 2 * q ^ 2) := by
  intro hfp
  have hp_pos : 0 < p := by have := hp.1; omega
  have hq_pos : 0 < q := by have := hq.1; omega
  have hcop : Nat.Coprime (p ^ 2) (q ^ 2) := (coprime_primes_ne hp hq hne).pow 2 2
  have hS_eq : fullMoment (p ^ 2 * q ^ 2) = (p ^ 2 * q ^ 2) * (tau (p ^ 2 * q ^ 2) + 1) :=
    ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop, fullMoment_prime_sq hp, fullMoment_prime_sq hq,
    tau_mul_of_coprime hcop (Nat.pow_pos hp_pos) (Nat.pow_pos hq_pos),
    tau_prime_pow hp 2, tau_prime_pow hq 2] at hS_eq
  have h10 : (p ^ 2 * q ^ 2) * (3 * 3 + 1) = 10 * p * p * q * q := by grind
  rw [h10] at hS_eq
  exact p2q2_diophantine_ne p q hS_eq

/-- Monotonicity cutoff for `p^2 * q^2` when `13 ≤ p` and `17 ≤ q`. -/
theorem p2q2_growth_bound (p q : Nat) (hp : 13 ≤ p) (hq : 17 ≤ q) :
    (3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1) < 10 * p * p * q * q := by
  have h1 : 169 * (3 * p * p + 2 * p + 1) ≤ 534 * (p * p) := by
    have hp_sq : 13 * p ≤ p * p := Nat.mul_le_mul_right p hp
    have hp_sq2 : 169 ≤ p * p := Nat.le_trans (by decide : 169 ≤ 13 * 13) (Nat.mul_le_mul hp hp)
    have hstep : 169 * (3 * p * p + 2 * p + 1) = 507 * (p * p) + 338 * p + 169 := by grind
    have hstep2 : 338 * p ≤ 26 * (p * p) := by
      have : 26 * (13 * p) = 338 * p := by grind
      have := Nat.mul_le_mul_left 26 hp_sq
      omega
    omega
  have h2 : 289 * (3 * q * q + 2 * q + 1) ≤ 902 * (q * q) := by
    have hq_sq : 17 * q ≤ q * q := Nat.mul_le_mul_right q hq
    have hq_sq2 : 289 ≤ q * q := Nat.le_trans (by decide : 289 ≤ 17 * 17) (Nat.mul_le_mul hq hq)
    have hstep : 289 * (3 * q * q + 2 * q + 1) = 867 * (q * q) + 578 * q + 289 := by grind
    have hstep2 : 578 * q ≤ 34 * (q * q) := by
      have : 34 * (17 * q) = 578 * q := by grind
      have := Nat.mul_le_mul_left 34 hq_sq
      omega
    omega
  have hmul : (169 * (3 * p * p + 2 * p + 1)) * (289 * (3 * q * q + 2 * q + 1)) ≤
      (534 * (p * p)) * (902 * (q * q)) := Nat.mul_le_mul h1 h2
  have hp2_pos : 0 < p * p := by omega
  have hq2_pos : 0 < q * q := by omega
  have hpq_pos : 0 < p * p * (q * q) := Nat.mul_pos hp2_pos hq2_pos
  have hlhs : 48841 * ((3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1)) ≤
      481668 * (p * p * (q * q)) := by
    have hA : 48841 * ((3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1)) =
        (169 * (3 * p * p + 2 * p + 1)) * (289 * (3 * q * q + 2 * q + 1)) := by grind
    have hB : 481668 * (p * p * (q * q)) = (534 * (p * p)) * (902 * (q * q)) := by grind
    rw [hA, hB]
    exact hmul
  have hrhs : 481668 * (p * p * (q * q)) < 48841 * (10 * p * p * q * q) := by
    have hC : 48841 * (10 * p * p * q * q) = 488410 * (p * p * (q * q)) := by grind
    rw [hC]
    exact Nat.mul_lt_mul_of_pos_right (by decide) hpq_pos
  have hlt : 48841 * ((3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1)) <
      48841 * (10 * p * p * q * q) := Nat.lt_of_le_of_lt hlhs hrhs
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- **Growth bound for four distinct primes `29 ≤ p < q < r < s`**:
    `(2*p + 1)(2*q + 1)(2*r + 1)(2*s + 1) < 17 * p * q * r * s`. -/
theorem four_prime_growth_bound (p q r s : Nat)
    (hp : 29 ≤ p) (hq : 31 ≤ q) (hr : 37 ≤ r) (hs : 41 ≤ s) :
    (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) < 17 * p * q * r * s := by
  have h1 : 29 * (2 * p + 1) ≤ 59 * p := by omega
  have h2 : 31 * (2 * q + 1) ≤ 63 * q := by omega
  have h3 : 37 * (2 * r + 1) ≤ 75 * r := by omega
  have h4 : 41 * (2 * s + 1) ≤ 83 * s := by omega
  have h12 : (29 * (2 * p + 1)) * (31 * (2 * q + 1)) ≤ (59 * p) * (63 * q) :=
    Nat.mul_le_mul h1 h2
  have h34 : (37 * (2 * r + 1)) * (41 * (2 * s + 1)) ≤ (75 * r) * (83 * s) :=
    Nat.mul_le_mul h3 h4
  have h1234 := Nat.mul_le_mul h12 h34
  have hA : 1363783 * ((2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1)) =
      ((29 * (2 * p + 1)) * (31 * (2 * q + 1))) * ((37 * (2 * r + 1)) * (41 * (2 * s + 1))) := by
    grind
  have hB : 23138325 * (p * q * r * s) = ((59 * p) * (63 * q)) * ((75 * r) * (83 * s)) := by
    grind
  rw [← hA, ← hB] at h1234
  have hpqrs_pos : 0 < p * q * r * s := by
    have : 0 < p := by omega
    have : 0 < q := by omega
    have : 0 < r := by omega
    have : 0 < s := by omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  have hrhs : 23138325 * (p * q * r * s) < 1363783 * (17 * p * q * r * s) := by
    have hC : 1363783 * (17 * p * q * r * s) = 23184311 * (p * q * r * s) := by grind
    rw [hC]
    exact Nat.mul_lt_mul_of_pos_right (by decide) hpqrs_pos
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1234 hrhs)

/-- Helper: if a prime `f` divides `17 * p * q * r * s` (with `5 ≤ p < q < r < s` primes)
    and `f < p` and `f ≠ 17`, contradiction. -/
private theorem prime_dvd_17pqrs_impossible {f p q r s : Nat}
    (hf : IsPrime f) (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s)
    (hfp : f < p) (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (hf17 : f ≠ 17) (hdvd : f ∣ 17 * p * q * r * s) : False := by
  have h17 : Nat.Coprime f 17 := coprime_primes_ne hf (by decide : IsPrime 17) hf17
  have hcp : Nat.Coprime f p := coprime_primes_ne hf hp (by omega)
  have hcq : Nat.Coprime f q := coprime_primes_ne hf hq (by omega)
  have hcr : Nat.Coprime f r := coprime_primes_ne hf hr (by omega)
  have hcs : Nat.Coprime f s := coprime_primes_ne hf hs (by omega)
  have hcop_all : Nat.Coprime f (17 * p * q * r * s) :=
    (((h17.mul_right hcp).mul_right hcq).mul_right hcr).mul_right hcs
  have hgcd_dvd : f ∣ Nat.gcd f (17 * p * q * r * s) := Nat.dvd_gcd (Nat.dvd_refl f) hdvd
  rw [hcop_all] at hgcd_dvd
  have heq1 : f = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
  have := hf.1
  omega

/-- Helper: if a prime `f > p` and `f ≠ 17` divides `17 * p * q * r * s`
    (with `p < q < r < s` primes), then `f = q ∨ f = r ∨ f = s`. -/
private theorem prime_dvd_17pqrs_mem {f p q r s : Nat}
    (hf : IsPrime f) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s)
    (hp_pos : 0 < p) (hfp : p < f) (hf17 : f ≠ 17) (hdvd : f ∣ 17 * p * q * r * s) :
    f = q ∨ f = r ∨ f = s := by
  have h17 : Nat.Coprime f 17 := coprime_primes_ne hf (by decide : IsPrime 17) hf17
  have hdvd1 : f ∣ p * (q * r * s) := by
    have hassoc : 17 * p * q * r * s = 17 * (p * (q * r * s)) := by grind
    rw [hassoc] at hdvd
    exact h17.dvd_of_dvd_mul_left hdvd
  have hcp : Nat.Coprime f p := by
    rcases coprime_or_dvd_of_isPrime (d := p) hf with hcop | hdvd_p
    · exact hcop.symm
    · exfalso
      have hle : f ≤ p := Nat.le_of_dvd hp_pos hdvd_p
      omega
  have hdvd2 : f ∣ q * (r * s) := by
    have hdvd' := hcp.dvd_of_dvd_mul_left hdvd1
    simpa [Nat.mul_assoc] using hdvd'
  by_cases hfq : f = q
  · exact Or.inl hfq
  · have hcq : Nat.Coprime f q := coprime_primes_ne hf hq hfq
    have hdvd3 : f ∣ r * s := hcq.dvd_of_dvd_mul_left hdvd2
    by_cases hfr : f = r
    · exact Or.inr (Or.inl hfr)
    · have hcr : Nat.Coprime f r := coprime_primes_ne hf hr hfr
      have hfs : f ∣ s := hcr.dvd_of_dvd_mul_left hdvd3
      rcases hs.2 f hfs with h1 | rfl
      · have := hf.1; omega
      · exact Or.inr (Or.inr rfl)

/-- Helper: if `5 ≤ p < q < r < s` are primes and `29 ≤ p`, then `31 ≤ q`, `37 ≤ r`, `41 ≤ s`. -/
private theorem next_primes_from_29 {p q r s : Nat}
    (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s)
    (hp : 29 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    31 ≤ q ∧ 37 ≤ r ∧ 41 ≤ s := by
  have hq31 : 31 ≤ q := by
    by_cases h30 : q = 30
    · exfalso; exact (by decide : ¬ IsPrime 30) (h30 ▸ hq)
    · omega
  have hr37 : 37 ≤ r := by
    by_cases h32 : r = 32; · exfalso; exact (by decide : ¬ IsPrime 32) (h32 ▸ hr)
    by_cases h33 : r = 33; · exfalso; exact (by decide : ¬ IsPrime 33) (h33 ▸ hr)
    by_cases h34 : r = 34; · exfalso; exact (by decide : ¬ IsPrime 34) (h34 ▸ hr)
    by_cases h35 : r = 35; · exfalso; exact (by decide : ¬ IsPrime 35) (h35 ▸ hr)
    by_cases h36 : r = 36; · exfalso; exact (by decide : ¬ IsPrime 36) (h36 ▸ hr)
    omega
  have hs41 : 41 ≤ s := by
    by_cases h38 : s = 38; · exfalso; exact (by decide : ¬ IsPrime 38) (h38 ▸ hs)
    by_cases h39 : s = 39; · exfalso; exact (by decide : ¬ IsPrime 39) (h39 ▸ hs)
    by_cases h40 : s = 40; · exfalso; exact (by decide : ¬ IsPrime 40) (h40 ▸ hs)
    omega
  exact ⟨hq31, hr37, hs41⟩

/-- Helper: primes in `(5, 11)` are only `7`. -/
private theorem prime_between_5_and_11 {x : Nat} (hx : IsPrime x) (h5 : 5 < x) (h11 : x < 11) :
    x = 7 := by
  by_cases h6 : x = 6; · exfalso; exact (by decide : ¬ IsPrime 6) (h6 ▸ hx)
  by_cases h8 : x = 8; · exfalso; exact (by decide : ¬ IsPrime 8) (h8 ▸ hx)
  by_cases h9 : x = 9; · exfalso; exact (by decide : ¬ IsPrime 9) (h9 ▸ hx)
  by_cases h10 : x = 10; · exfalso; exact (by decide : ¬ IsPrime 10) (h10 ▸ hx)
  omega

/-- Helper: primes in `(11, 23)` are in `{13, 17, 19}`. -/
private theorem prime_between_11_and_23 {x : Nat} (hx : IsPrime x) (h11 : 11 < x) (h23 : x < 23) :
    x = 13 ∨ x = 17 ∨ x = 19 := by
  by_cases h12 : x = 12; · exfalso; exact (by decide : ¬ IsPrime 12) (h12 ▸ hx)
  by_cases h14 : x = 14; · exfalso; exact (by decide : ¬ IsPrime 14) (h14 ▸ hx)
  by_cases h15 : x = 15; · exfalso; exact (by decide : ¬ IsPrime 15) (h15 ▸ hx)
  by_cases h16 : x = 16; · exfalso; exact (by decide : ¬ IsPrime 16) (h16 ▸ hx)
  by_cases h18 : x = 18; · exfalso; exact (by decide : ¬ IsPrime 18) (h18 ▸ hx)
  by_cases h20 : x = 20; · exfalso; exact (by decide : ¬ IsPrime 20) (h20 ▸ hx)
  by_cases h21 : x = 21; · exfalso; exact (by decide : ¬ IsPrime 21) (h21 ▸ hx)
  by_cases h22 : x = 22; · exfalso; exact (by decide : ¬ IsPrime 22) (h22 ▸ hx)
  omega

/-- Helper: primes in `(23, 47)` are in `{29, 31, 37, 41, 43}`. -/
private theorem prime_between_23_and_47 {x : Nat} (hx : IsPrime x) (h23 : 23 < x) (h47 : x < 47) :
    x = 29 ∨ x = 31 ∨ x = 37 ∨ x = 41 ∨ x = 43 := by
  by_cases h24 : x = 24; · exfalso; exact (by decide : ¬ IsPrime 24) (h24 ▸ hx)
  by_cases h25 : x = 25; · exfalso; exact (by decide : ¬ IsPrime 25) (h25 ▸ hx)
  by_cases h26 : x = 26; · exfalso; exact (by decide : ¬ IsPrime 26) (h26 ▸ hx)
  by_cases h27 : x = 27; · exfalso; exact (by decide : ¬ IsPrime 27) (h27 ▸ hx)
  by_cases h28 : x = 28; · exfalso; exact (by decide : ¬ IsPrime 28) (h28 ▸ hx)
  by_cases h30 : x = 30; · exfalso; exact (by decide : ¬ IsPrime 30) (h30 ▸ hx)
  by_cases h32 : x = 32; · exfalso; exact (by decide : ¬ IsPrime 32) (h32 ▸ hx)
  by_cases h33 : x = 33; · exfalso; exact (by decide : ¬ IsPrime 33) (h33 ▸ hx)
  by_cases h34 : x = 34; · exfalso; exact (by decide : ¬ IsPrime 34) (h34 ▸ hx)
  by_cases h35 : x = 35; · exfalso; exact (by decide : ¬ IsPrime 35) (h35 ▸ hx)
  by_cases h36 : x = 36; · exfalso; exact (by decide : ¬ IsPrime 36) (h36 ▸ hx)
  by_cases h38 : x = 38; · exfalso; exact (by decide : ¬ IsPrime 38) (h38 ▸ hx)
  by_cases h39 : x = 39; · exfalso; exact (by decide : ¬ IsPrime 39) (h39 ▸ hx)
  by_cases h40 : x = 40; · exfalso; exact (by decide : ¬ IsPrime 40) (h40 ▸ hx)
  by_cases h42 : x = 42; · exfalso; exact (by decide : ¬ IsPrime 42) (h42 ▸ hx)
  by_cases h44 : x = 44; · exfalso; exact (by decide : ¬ IsPrime 44) (h44 ▸ hx)
  by_cases h45 : x = 45; · exfalso; exact (by decide : ¬ IsPrime 45) (h45 ▸ hx)
  by_cases h46 : x = 46; · exfalso; exact (by decide : ¬ IsPrime 46) (h46 ▸ hx)
  omega

/-- **Squarefree Four-Prime Exclusion**: For all primes `5 ≤ p < q < r < s`,
    `(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) ≠ 17 * p * q * r * s`. -/
theorem four_prime_moment_ne {p q r s : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s)
    (hp5 : 5 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) ≠ 17 * p * q * r * s := by
  intro heq
  by_cases hp29 : 29 ≤ p
  · obtain ⟨hq31, hr37, hs41⟩ := next_primes_from_29 hq hr hs hp29 hpq hqr hrs
    have hlt := four_prime_growth_bound p q r s hp29 hq31 hr37 hs41
    omega
  · -- `5 ≤ p < 29`, so `p ∈ {5, 7, 11, 13, 17, 19, 23}`
    have hp_cases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
      by_cases h6 : p = 6; · exfalso; exact (by decide : ¬ IsPrime 6) (h6 ▸ hp)
      by_cases h8 : p = 8; · exfalso; exact (by decide : ¬ IsPrime 8) (h8 ▸ hp)
      by_cases h9 : p = 9; · exfalso; exact (by decide : ¬ IsPrime 9) (h9 ▸ hp)
      by_cases h10 : p = 10; · exfalso; exact (by decide : ¬ IsPrime 10) (h10 ▸ hp)
      by_cases h12 : p = 12; · exfalso; exact (by decide : ¬ IsPrime 12) (h12 ▸ hp)
      by_cases h14 : p = 14; · exfalso; exact (by decide : ¬ IsPrime 14) (h14 ▸ hp)
      by_cases h15 : p = 15; · exfalso; exact (by decide : ¬ IsPrime 15) (h15 ▸ hp)
      by_cases h16 : p = 16; · exfalso; exact (by decide : ¬ IsPrime 16) (h16 ▸ hp)
      by_cases h18 : p = 18; · exfalso; exact (by decide : ¬ IsPrime 18) (h18 ▸ hp)
      by_cases h20 : p = 20; · exfalso; exact (by decide : ¬ IsPrime 20) (h20 ▸ hp)
      by_cases h21 : p = 21; · exfalso; exact (by decide : ¬ IsPrime 21) (h21 ▸ hp)
      by_cases h22 : p = 22; · exfalso; exact (by decide : ¬ IsPrime 22) (h22 ▸ hp)
      by_cases h24 : p = 24; · exfalso; exact (by decide : ¬ IsPrime 24) (h24 ▸ hp)
      by_cases h25 : p = 25; · exfalso; exact (by decide : ¬ IsPrime 25) (h25 ▸ hp)
      by_cases h26 : p = 26; · exfalso; exact (by decide : ¬ IsPrime 26) (h26 ▸ hp)
      by_cases h27 : p = 27; · exfalso; exact (by decide : ¬ IsPrime 27) (h27 ▸ hp)
      by_cases h28 : p = 28; · exfalso; exact (by decide : ¬ IsPrime 28) (h28 ▸ hp)
      omega
    rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- `p = 5`: `11 ∣ 17 * 5 * q * r * s`, so `11 ∈ {q, r, s}`, forcing `q ≤ 11`.
      have h11_dvd : 11 ∣ 17 * 5 * q * r * s :=
        ⟨(2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩
      rcases prime_dvd_17pqrs_mem (by decide : IsPrime 11) hq hr hs (by decide) (by omega) (by decide) h11_dvd with
        rfl | rfl | rfl
      · -- `q = 11`: `23 ∣ 17 * 5 * 11 * r * s`, so `r = 23 ∨ s = 23`
        have h23_dvd : 23 ∣ 17 * 5 * 11 * r * s :=
          ⟨11 * (2 * r + 1) * (2 * s + 1), by grind⟩
        have h23_mem := prime_dvd_17pqrs_mem (by decide : IsPrime 23) hq hr hs (by decide) (by omega) (by decide) h23_dvd
        rcases h23_mem with h23_11 | rfl | rfl
        · omega
        · -- `r = 23`: `47 ∣ 17 * 5 * 11 * 23 * s`, so `s = 47`
          have h47_dvd : 47 ∣ 17 * 5 * 11 * 23 * s :=
            ⟨11 * 23 * (2 * s + 1), by grind⟩
          have h47_mem := prime_dvd_17pqrs_mem (by decide : IsPrime 47) hq hr hs (by decide) (by omega) (by decide) h47_dvd
          rcases h47_mem with h47_11 | h47_23 | rfl
          · omega
          · omega
          · revert heq; decide
        · -- `s = 23`: `11 < r < 23`, so `r ∈ {13, 17, 19}`
          rcases prime_between_11_and_23 hr hqr hrs with rfl | rfl | rfl
          · -- `r = 13`: `27` divisible by `3`
            exact prime_dvd_17pqrs_impossible isPrime_3 isPrime_5 isPrime_11 hr hs
              (by omega) hpq hqr hrs (by decide)
              ⟨11 * 23 * 9 * 47, by grind⟩
          · -- `r = 17`: `35` divisible by `7`
            exact prime_dvd_17pqrs_impossible isPrime_7 isPrime_5 isPrime_11 hr hs
              (by omega) hpq hqr hrs (by decide)
              ⟨11 * 23 * 5 * 47, by grind⟩
          · -- `r = 19`: `39` divisible by `3`
            exact prime_dvd_17pqrs_impossible isPrime_3 isPrime_5 isPrime_11 hr hs
              (by omega) hpq hqr hrs (by decide)
              ⟨11 * 23 * 13 * 47, by grind⟩
      · -- `q < r = 11`: `q = 7`, so `2 * 7 + 1 = 15` divisible by `3`
        have hq7 : q = 7 := prime_between_5_and_11 hq hpq hqr
        subst hq7
        exact prime_dvd_17pqrs_impossible isPrime_3 isPrime_5 hq hr hs
          (by omega) hpq hqr hrs (by decide)
          ⟨11 * 5 * 23 * (2 * s + 1), by grind⟩
      · -- `q < r < s = 11`: `5 < q < 11` and `q < r < 11` both equal `7`, impossible
        have hq7 : q = 7 := prime_between_5_and_11 hq hpq (by omega)
        have hr7 : r = 7 := prime_between_5_and_11 hr (by omega) hrs
        omega
    · -- `p = 7`: `2 * 7 + 1 = 15`, so `3 ∣ 17 * 7 * q * r * s`
      exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs
        (by omega) hpq hqr hrs (by decide)
        ⟨5 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩
    · -- `p = 11`: `23 ∣ 17 * 11 * q * r * s`, so `23 ∈ {q, r, s}`
      have h23_dvd : 23 ∣ 17 * 11 * q * r * s :=
        ⟨(2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩
      rcases prime_dvd_17pqrs_mem (by decide : IsPrime 23) hq hr hs (by decide) (by omega) (by decide) h23_dvd with
        rfl | rfl | rfl
      · -- `q = 23`: `47 ∣ 17 * 11 * 23 * r * s`, so `r = 47 ∨ s = 47`
        have h47_dvd : 47 ∣ 17 * 11 * 23 * r * s :=
          ⟨23 * (2 * r + 1) * (2 * s + 1), by grind⟩
        have h47_mem := prime_dvd_17pqrs_mem (by decide : IsPrime 47) hq hr hs (by decide) (by omega) (by decide) h47_dvd
        rcases h47_mem with h47_23 | rfl | rfl
        · omega
        · -- `r = 47`: `2 * 47 + 1 = 95`, divisible by `5`
          exact prime_dvd_17pqrs_impossible isPrime_5 hp hq hr hs
            (by omega) hpq hqr hrs (by decide)
            ⟨23 * 47 * 19 * (2 * s + 1), by grind⟩
        · -- `s = 47`: `23 < r < 47`, so `r ∈ {29, 31, 37, 41, 43}`
          rcases prime_between_23_and_47 hr hqr hrs with rfl | rfl | rfl | rfl | rfl
          · revert heq; decide
          · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
              ⟨23 * 47 * 21 * 95, by grind⟩
          · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
              ⟨23 * 47 * 25 * 95, by grind⟩
          · revert heq; decide
          · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
              ⟨23 * 47 * 29 * 95, by grind⟩
      · -- `11 < q < r = 23`: `q ∈ {13, 17, 19}`
        rcases prime_between_11_and_23 hq hpq hqr with rfl | rfl | rfl
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨23 * 9 * 47 * (2 * s + 1), by grind⟩
        · exact prime_dvd_17pqrs_impossible isPrime_5 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨23 * 7 * 47 * (2 * s + 1), by grind⟩
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨23 * 13 * 47 * (2 * s + 1), by grind⟩
      · -- `11 < q < r < s = 23`: `q ∈ {13, 17, 19}`
        rcases prime_between_11_and_23 hq hpq (by omega) with rfl | rfl | rfl
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨23 * 9 * (2 * r + 1) * 47, by grind⟩
        · exact prime_dvd_17pqrs_impossible isPrime_5 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨23 * 7 * (2 * r + 1) * 47, by grind⟩
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨23 * 13 * (2 * r + 1) * 47, by grind⟩
    · -- `p = 13`: `2 * 13 + 1 = 27`, divisible by `3`
      exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs
        (by omega) hpq hqr hrs (by decide)
        ⟨9 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩
    · -- `p = 17`: `2 * 17 + 1 = 35`, divisible by `5`
      exact prime_dvd_17pqrs_impossible isPrime_5 hp hq hr hs
        (by omega) hpq hqr hrs (by decide)
        ⟨7 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩
    · -- `p = 19`: `2 * 19 + 1 = 39`, divisible by `3`
      exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs
        (by omega) hpq hqr hrs (by decide)
        ⟨13 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩
    · -- `p = 23`: `2 * 23 + 1 = 47 ∣ 17 * 23 * q * r * s`, so `47 ∈ {q, r, s}`
      have h47_dvd : 47 ∣ 17 * 23 * q * r * s :=
        ⟨(2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩
      rcases prime_dvd_17pqrs_mem (by decide : IsPrime 47) hq hr hs (by decide) (by omega) (by decide) h47_dvd with
        rfl | rfl | rfl
      · -- `q = 47`: `2 * 47 + 1 = 95`, divisible by `5`
        exact prime_dvd_17pqrs_impossible isPrime_5 hp hq hr hs
          (by omega) hpq hqr hrs (by decide)
          ⟨47 * 19 * (2 * r + 1) * (2 * s + 1), by grind⟩
      · -- `23 < q < r = 47`: `q ∈ {29, 31, 37, 41, 43}`
        rcases prime_between_23_and_47 hq hpq hqr with rfl | rfl | rfl | rfl | rfl
        · -- `q = 29`: `2 * 29 + 1 = 59 ∣ 17 * 23 * 29 * 47 * s`, so `s = 59`
          have h59_dvd : 59 ∣ 17 * 23 * 29 * 47 * s :=
            ⟨47 * 95 * (2 * s + 1), by grind⟩
          have h59_mem := prime_dvd_17pqrs_mem (by decide : IsPrime 59) hq hr hs (by decide) (by omega) (by decide) h59_dvd
          rcases h59_mem with h59_29 | h59_47 | rfl
          · omega
          · omega
          · revert heq; decide
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨47 * 21 * 95 * (2 * s + 1), by grind⟩
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨47 * 25 * 95 * (2 * s + 1), by grind⟩
        · -- `q = 41`: `2 * 41 + 1 = 83 ∣ 17 * 23 * 41 * 47 * s`, so `s = 83`
          have h83_dvd : 83 ∣ 17 * 23 * 41 * 47 * s :=
            ⟨47 * 95 * (2 * s + 1), by grind⟩
          have h83_mem := prime_dvd_17pqrs_mem (by decide : IsPrime 83) hq hr hs (by decide) (by omega) (by decide) h83_dvd
          rcases h83_mem with h83_41 | h83_47 | rfl
          · omega
          · omega
          · revert heq; decide
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨47 * 29 * 95 * (2 * s + 1), by grind⟩
      · -- `23 < q < r < s = 47`: `q ∈ {29, 31, 37, 41, 43}`
        rcases prime_between_23_and_47 hq hpq (by omega) with rfl | rfl | rfl | rfl | rfl
        · -- `q = 29`: `59 ∣ 17 * 23 * 29 * r * 47`, so `r = 59 > 47`, impossible!
          have h59_dvd : 59 ∣ 17 * 23 * 29 * r * 47 :=
            ⟨47 * (2 * r + 1) * 95, by grind⟩
          have h59_mem := prime_dvd_17pqrs_mem (by decide : IsPrime 59) hq hr hs (by decide) (by omega) (by decide) h59_dvd
          rcases h59_mem with h59_29 | rfl | h59_47 <;> omega
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨47 * 21 * (2 * r + 1) * 95, by grind⟩
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨47 * 25 * (2 * r + 1) * 95, by grind⟩
        · -- `q = 41`: `83 ∣ 17 * 23 * 41 * r * 47`, so `r = 83 > 47`, impossible!
          have h83_dvd : 83 ∣ 17 * 23 * 41 * r * 47 :=
            ⟨47 * (2 * r + 1) * 95, by grind⟩
          have h83_mem := prime_dvd_17pqrs_mem (by decide : IsPrime 83) hq hr hs (by decide) (by omega) (by decide) h83_dvd
          rcases h83_mem with h83_41 | rfl | h83_47 <;> omega
        · exact prime_dvd_17pqrs_impossible isPrime_3 hp hq hr hs (by omega) hpq hqr hrs (by decide)
            ⟨47 * 29 * (2 * r + 1) * 95, by grind⟩

/-- Exact evaluation of `fullMoment p` for prime `p`: `2 * p + 1`. -/
theorem fullMoment_prime {p : Nat} (hp : IsPrime p) :
    fullMoment p = 2 * p + 1 := by
  have h := fullMoment_prime_pow_succ hp 0
  have h0 : fullMoment (p ^ 0) = 1 := fullMoment_prime_pow_zero p
  rw [h0, Nat.pow_one] at h
  omega

/-- Unconditional exclusion of `p * q * r * s` for all primes `5 ≤ p < q < r < s`. -/
theorem not_isFixedPoint_four_distinct_primes {p q r s : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s)
    (hp5 : 5 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    ¬ IsFixedPoint (p * q * r * s) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hr_pos : 0 < r := by omega
  have hs_pos : 0 < s := by omega
  have hpq_c : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
  have hpr_c : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
  have hps_c : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
  have hqr_c : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
  have hqs_c : Nat.Coprime q s := coprime_primes_ne hq hs (by omega)
  have hrs_c : Nat.Coprime r s := coprime_primes_ne hr hs (by omega)
  have hcop_pq_r : Nat.Coprime (p * q) r := hpr_c.mul_left hqr_c
  have hcop_pqr_s : Nat.Coprime (p * q * r) s := (hps_c.mul_left hqs_c).mul_left hrs_c
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop_pqr_s, fullMoment_mul_of_coprime hcop_pq_r,
    fullMoment_mul_of_coprime hpq_c, fullMoment_prime hp, fullMoment_prime hq,
    fullMoment_prime hr, fullMoment_prime hs] at hS_eq
  rw [tau_mul_of_coprime hcop_pqr_s (Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos) hs_pos,
    tau_mul_of_coprime hcop_pq_r (Nat.mul_pos hp_pos hq_pos) hr_pos,
    tau_mul_of_coprime hpq_c hp_pos hq_pos,
    tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime hr, tau_of_isPrime hs] at hS_eq
  have h17 : (p * q * r * s) * (2 * 2 * 2 * 2 + 1) = 17 * p * q * r * s := by grind
  rw [h17] at hS_eq
  exact four_prime_moment_ne hp hq hr hs hp5 hpq hqr hrs hS_eq

/-- Exclusion of `p * q * r` for all distinct primes `p < q < r`. -/
private theorem three_prime_prod_ne_self {p q r : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hpq : p < q) (hqr : q < r) :
    ¬ IsFixedPoint (p * q * r) := by
  intro hfp
  have hp_pos : 0 < p := by have := hp.1; omega
  have hq_pos : 0 < q := by have := hq.1; omega
  have hr_pos : 0 < r := by have := hr.1; omega
  have hpq_c : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
  have hpr_c : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
  have hqr_c : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
  have hcop_pq_r : Nat.Coprime (p * q) r := hpr_c.mul_left hqr_c
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop_pq_r, fullMoment_mul_of_coprime hpq_c,
    fullMoment_prime hp, fullMoment_prime hq, fullMoment_prime hr] at hS_eq
  rw [tau_mul_of_coprime hcop_pq_r (Nat.mul_pos hp_pos hq_pos) hr_pos,
    tau_mul_of_coprime hpq_c hp_pos hq_pos,
    tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime hr] at hS_eq
  have h9 : (p * q * r) * (2 * 2 * 2 + 1) = 9 * p * q * r := by grind
  rw [h9] at hS_eq
  exact three_prime_moment_ne hp hq hr hpq hqr hS_eq

private theorem p2q_ne_self_general {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hne : p ≠ q) :
    ¬ IsFixedPoint (p ^ 2 * q) := by
  intro hfp
  have hp_pos : 0 < p := by have := hp.1; omega
  have hq_pos : 0 < q := by have := hq.1; omega
  have hcop : Nat.Coprime (p ^ 2) q := (coprime_primes_ne hp hq hne).pow_left 2
  have htau : tau (p ^ 2 * q) = 6 := by
    rw [tau_mul_of_coprime hcop (Nat.pow_pos hp_pos) hq_pos, tau_prime_pow hp 2, tau_of_isPrime hq]
  have htau_even : tau (p ^ 2 * q) % 2 = 0 := by rw [htau]
  have hdvd : p ^ 2 ∣ p ^ 2 * q := Nat.dvd_mul_right (p ^ 2) q
  have hndvd : ¬ (p ^ (2 + 1) ∣ p ^ 2 * q) := by
    intro h
    rw [Nat.pow_succ] at h
    have hq_dvd : p ∣ q := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp_pos) h
    rcases hq.2 p hq_dvd with h1 | heq
    · have := hp.1; omega
    · exact hne heq
  exact not_isFixedPoint_of_exact_exponent_mod_four_ge_two htau_even hp hdvd hndvd (Or.inl rfl) hfp

/-- Every `n ≥ 2` with `omegaBig n = 1` is prime. -/
theorem isPrime_of_omegaBig_eq_one {n : Nat} (hn : 2 ≤ n) (ho : omegaBig n = 1) :
    IsPrime n := by
  rw [omegaBig_eq_succ_div_minFac hn] at ho
  have ho_div : omegaBig (n / minFac n) = 0 := by omega
  have hp : IsPrime (minFac n) := minFac_isPrime hn
  obtain ⟨m, hm_eq⟩ := minFac_dvd n
  have hp_pos : 0 < minFac n := by have := hp.1; omega
  have hm_pos : 0 < m := by
    by_cases hm0 : m = 0
    · subst hm0; omega
    · omega
  have hdiv_eq : n / minFac n = m := by
    calc n / minFac n = (minFac n * m) / minFac n := by rw [← hm_eq]
      _ = m := Nat.mul_div_right m hp_pos
  rw [hdiv_eq] at ho_div
  by_cases hm1 : m = 1
  · subst hm1; rw [Nat.mul_one] at hm_eq; rw [hm_eq]; exact hp
  · have hm2 : 2 ≤ m := by omega
    rw [omegaBig_eq_succ_div_minFac hm2] at ho_div
    omega

/-- Decomposition of any `n ≥ 1` with `omegaBig n = k` into a sorted list of `k` primes. -/
theorem exists_primes_of_omegaBig :
    ∀ k n : Nat, 1 ≤ n → omegaBig n = k →
      ∃ ps : List Nat, ps.length = k ∧ (∀ p ∈ ps, IsPrime p) ∧
        (List.Pairwise (· ≤ ·) ps) ∧ n = ps.foldl (· * ·) 1
  | 0, n, hn, ho => by
    by_cases hn1 : n = 1
    · subst hn1; exact ⟨[], rfl, by simp, List.Pairwise.nil, rfl⟩
    · have hn2 : 2 ≤ n := by omega
      rw [omegaBig_eq_succ_div_minFac hn2] at ho
      omega
  | k + 1, n, hn, ho => by
    have hn2 : 2 ≤ n := by
      by_cases hn1 : n = 1
      · subst hn1; simp at ho
      · omega
    have hp : IsPrime (minFac n) := minFac_isPrime hn2
    obtain ⟨m, hm_eq⟩ := minFac_dvd n
    have hp_pos : 0 < minFac n := by have := hp.1; omega
    have hm_pos : 0 < m := by
      by_cases hm0 : m = 0
      · subst hm0; omega
      · omega
    have hdiv_eq : n / minFac n = m := by
      calc n / minFac n = (minFac n * m) / minFac n := by rw [← hm_eq]
        _ = m := Nat.mul_div_right m hp_pos
    rw [omegaBig_eq_succ_div_minFac hn2, hdiv_eq] at ho
    have hok : omegaBig m = k := by omega
    obtain ⟨ps, hlen, hps_prime, hps_sorted, hm_fold⟩ :=
      exists_primes_of_omegaBig k m hm_pos hok
    have hp_le_all : ∀ q ∈ ps, minFac n ≤ q := by
      intro q hq_mem
      have hq_dvd_m : q ∣ m := by
        clear hok hlen hps_prime hps_sorted hm_eq hdiv_eq ho
        have hfold : ∀ (init : Nat) (l : List Nat), q ∈ l → q ∣ l.foldl (· * ·) init := by
          intro init l
          induction l generalizing init with
          | nil => simp
          | cons x xs ih =>
            simp only [List.mem_cons, List.foldl_cons]
            rintro (rfl | hx)
            · have : ∀ (a : Nat) (ys : List Nat), a ∣ ys.foldl (· * ·) a := by
                intro a ys
                induction ys generalizing a with
                | nil => exact Nat.dvd_refl a
                | cons y ys ihy =>
                  simp only [List.foldl_cons]
                  exact Nat.dvd_trans (Nat.dvd_mul_right a y) (ihy (a * y))
              exact Nat.dvd_trans (Nat.dvd_mul_left q init) (this (init * q) xs)
            · exact ih (init * x) hx
        rw [hm_fold]
        exact hfold 1 ps hq_mem
      have hq_dvd_n : q ∣ n := by
        rw [hm_eq]
        exact Nat.dvd_mul_left_of_dvd hq_dvd_m (minFac n)
      have hq2 : 2 ≤ q := (hps_prime q hq_mem).1
      exact minFac_le_of_dvd hq2 hq_dvd_n hn2
    refine ⟨minFac n :: ps, by simp [hlen], ?_, List.pairwise_cons.mpr ⟨hp_le_all, hps_sorted⟩, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hp
      · exact hps_prime x hx'
    · have hfold_mul : ∀ (a : Nat) (l : List Nat), l.foldl (· * ·) a = a * l.foldl (· * ·) 1 := by
        intro a l
        induction l generalizing a with
        | nil => simp
        | cons x xs ih =>
          simp only [List.foldl_cons, Nat.one_mul]
          rw [ih (a * x), ih x, Nat.mul_assoc]
      simp only [List.foldl_cons, Nat.one_mul]
      rw [hfold_mul (minFac n) ps, ← hm_fold]
      exact hm_eq

/-- Helper: every fixed point `n ≠ 21` has `Nat.gcd n 6 = 1` (`¬ (2 ∣ n)` and `¬ (3 ∣ n)`). -/
theorem gcd_six_eq_one_of_isFixedPoint_ne_21 {n : Nat}
    (hfp : IsFixedPoint n) (hne : n ≠ 21) :
    Nat.gcd n 6 = 1 := by
  have hnot2 : ¬ (2 ∣ n) := fun h2 => not_isFixedPoint_of_even h2 hfp
  have hnot3 : ¬ (3 ∣ n) := fun h3 => hne ((three_dvd_fixedPoint_iff_eq_21 n h3).mp hfp)
  have hc2 : Nat.Coprime n 2 := by
    rcases coprime_or_dvd_of_isPrime (d := n) isPrime_2 with hcop | hdvd
    · exact hcop
    · exact absurd hdvd hnot2
  have hc3 : Nat.Coprime n 3 := by
    rcases coprime_or_dvd_of_isPrime (d := n) isPrime_3 with hcop | hdvd
    · exact hcop
    · exact absurd hdvd hnot3
  exact hc2.mul_right hc3

/-- Helper: if `Nat.gcd n 6 = 1` and `p ∣ n` with `IsPrime p`, then `5 ≤ p`. -/
theorem five_le_prime_of_dvd_coprime_six {n p : Nat}
    (hgcd : Nat.gcd n 6 = 1) (hp : IsPrime p) (hdvd : p ∣ n) : 5 ≤ p := by
  have hp2 : 2 ≤ p := hp.1
  by_cases h2 : p = 2
  · subst h2
    have h6 : 2 ∣ Nat.gcd n 6 := Nat.dvd_gcd hdvd (by decide)
    rw [hgcd] at h6
    omega
  · by_cases h3 : p = 3
    · subst h3
      have h6 : 3 ∣ Nat.gcd n 6 := Nat.dvd_gcd hdvd (by decide)
      rw [hgcd] at h6
      omega
    · by_cases h4 : p = 4
      · exfalso; exact (by decide : ¬ IsPrime 4) (h4 ▸ hp)
      · omega

/-- **Complete $\Omega(n) \le 4$ Fixed-Point Uniqueness**:
    For every `n : Nat`, if `IsFixedPoint n` and `omegaBig n ≤ 4`, then `n = 21`. -/
theorem fixedPoint_eq_21_of_omegaBig_le_four {n : Nat}
    (hfp : IsFixedPoint n) (ho : omegaBig n ≤ 4) :
    n = 21 := by
  by_cases h21 : n = 21
  · exact h21
  · exfalso
    have hn_pos : 1 ≤ n := hfp.1
    have hgcd : Nat.gcd n 6 = 1 := gcd_six_eq_one_of_isFixedPoint_ne_21 hfp h21
    have ho_cases : omegaBig n = 0 ∨ omegaBig n = 1 ∨ omegaBig n = 2 ∨
        omegaBig n = 3 ∨ omegaBig n = 4 := by omega
    rcases ho_cases with ho0 | ho1 | ho2 | ho3 | ho4
    · obtain ⟨ps, hlen, _, _, hn_eq⟩ := exists_primes_of_omegaBig 0 n hn_pos ho0
      cases ps with
      | nil =>
        simp at hn_eq
        subst hn_eq
        exact not_isFixedPoint_1 hfp
      | cons _ _ => simp at hlen
    · obtain ⟨ps, hlen, hprime, _, hn_eq⟩ := exists_primes_of_omegaBig 1 n hn_pos ho1
      rcases ps with _ | ⟨p, _ | _⟩
      · simp at hlen
      · simp at hn_eq
        subst hn_eq
        exact not_isFixedPoint_of_isPrime (hprime _ List.mem_cons_self) hfp
      · simp at hlen
    · obtain ⟨ps, hlen, hprime, hsorted, hn_eq⟩ := exists_primes_of_omegaBig 2 n hn_pos ho2
      rcases ps with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp at hlen
      · simp at hlen
      · simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul] at hn_eq
        subst hn_eq
        have hp := hprime p (by simp)
        have hq := hprime q (by simp)
        have hpq : p ≤ q := (List.pairwise_cons.mp hsorted).1 q (by simp)
        rcases (semiprime_fixedPoint_iff hp hq hpq).mp hfp with ⟨rfl, rfl⟩
        exact h21 rfl
      · simp at hlen
    · obtain ⟨ps, hlen, hprime, hsorted, hn_eq⟩ := exists_primes_of_omegaBig 3 n hn_pos ho3
      rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | _⟩⟩⟩ <;> try (simp at hlen)
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul] at hn_eq
      subst hn_eq
      have hp := hprime p (by simp)
      have hq := hprime q (by simp)
      have hr := hprime r (by simp)
      have hpq : p ≤ q := (List.pairwise_cons.mp hsorted).1 q (by simp)
      have hpr : p ≤ r := (List.pairwise_cons.mp hsorted).1 r (by simp)
      have hqr : q ≤ r := (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 r (by simp)
      by_cases heq_pq : p = q
      · subst heq_pq
        by_cases heq_pr : p = r
        · subst heq_pr
          have hpow : p * p * p = p ^ 3 := by grind
          rw [hpow] at hfp
          exact not_isFixedPoint_prime_pow hp (by decide) hfp
        · have hpow : p * p * r = p ^ 2 * r := by grind
          rw [hpow] at hfp
          exact p2q_ne_self_general hp hr heq_pr hfp
      · by_cases heq_qr : q = r
        · subst heq_qr
          have hpow : p * q * q = q ^ 2 * p := by grind
          rw [hpow] at hfp
          exact p2q_ne_self_general hq hp (Ne.symm heq_pq) hfp
        · exact three_prime_prod_ne_self hp hq hr (by omega) (by omega) hfp
    · obtain ⟨ps, hlen, hprime, hsorted, hn_eq⟩ := exists_primes_of_omegaBig 4 n hn_pos ho4
      rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, _ | _⟩⟩⟩⟩ <;> try (simp at hlen)
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul] at hn_eq
      have hp := hprime p (by simp)
      have hq := hprime q (by simp)
      have hr := hprime r (by simp)
      have hs := hprime s (by simp)
      have hpq : p ≤ q := (List.pairwise_cons.mp hsorted).1 q (by simp)
      have hqr : q ≤ r := (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 r (by simp)
      have hrs : r ≤ s :=
        (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).2).1 s (by simp)
      have hp5 : 5 ≤ p :=
        five_le_prime_of_dvd_coprime_six hgcd hp (by rw [hn_eq]; exact ⟨q * r * s, by grind⟩)
      subst hn_eq
      by_cases heq_pq : p = q
      · subst heq_pq
        by_cases heq_qr : p = r
        · subst heq_qr
          by_cases heq_rs : p = s
          · subst heq_rs
            have hpow : p * p * p * p = p ^ 4 := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_pow hp (by decide) hfp
          · have hpow : p * p * p * s = p ^ 3 * s := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_cube_mul_prime hp hs heq_rs hfp
        · by_cases heq_rs : r = s
          · subst heq_rs
            have hpow : p * p * r * r = p ^ 2 * r ^ 2 := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_sq_mul_prime_sq hp hr heq_qr hfp
          · have hpow : p * p * r * s = p ^ 2 * r * s := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_sq_mul_two_primes hp hr hs heq_qr (by omega) heq_rs hfp
      · by_cases heq_qr : q = r
        · subst heq_qr
          by_cases heq_rs : q = s
          · subst heq_rs
            have hpow : p * q * q * q = q ^ 3 * p := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_cube_mul_prime hq hp (Ne.symm heq_pq) hfp
          · have hpow : p * q * q * s = q ^ 2 * p * s := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_sq_mul_two_primes hq hp hs (Ne.symm heq_pq) heq_rs (by omega) hfp
        · by_cases heq_rs : r = s
          · subst heq_rs
            have hpow : p * q * r * r = r ^ 2 * p * q := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_sq_mul_two_primes hr hp hq (by omega) (by omega) heq_pq hfp
          · exact not_isFixedPoint_four_distinct_primes hp hq hr hs hp5 (by omega) (by omega) (by omega) hfp

/-- **Structural Reduction Theorem**: Every fixed point `n ≠ 21` of OEIS A245211 satisfies
    `Nat.gcd n 6 = 1` and `5 ≤ omegaBig n`. -/
theorem omegaBig_ge_five_of_isFixedPoint_ne_21 {n : Nat}
    (hfp : IsFixedPoint n) (hne : n ≠ 21) :
    Nat.gcd n 6 = 1 ∧ 5 ≤ omegaBig n := by
  refine ⟨gcd_six_eq_one_of_isFixedPoint_ne_21 hfp hne, ?_⟩
  by_cases hle : omegaBig n ≤ 4
  · exact absurd (fixedPoint_eq_21_of_omegaBig_le_four hfp hle) hne
  · omega

end OmegaFourExclusions

/-! ## Partial $\Omega(n) = 5$ Exclusions and Lower Bound on Smallest Prime Factor -/

section OmegaFiveExclusions

/-- Exact evaluation of `fullMoment (p ^ 4)` for prime `p`: `5p^4 + 4p^3 + 3p^2 + 2p + 1`. -/
theorem fullMoment_prime_pow_four {p : Nat} (hp : IsPrime p) :
    fullMoment (p ^ 4) = 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 := by
  rw [fullMoment_prime_pow_succ hp 3, fullMoment_prime_pow_succ hp 2,
    fullMoment_prime_pow_succ hp 1, fullMoment_prime_pow_succ hp 0, fullMoment_prime_pow_zero]
  grind

/-- Growth cutoff for `p ^ 4 * q`: for `31 ≤ p` and `7 ≤ q`,
    `(5p^4 + 4p^3 + 3p^2 + 2p + 1) * (2q + 1) < 11 * p^4 * q`. -/
theorem p4q_growth_bound (p q : Nat) (hp : 31 ≤ p) (hq : 7 ≤ q) :
    (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * q + 1) < 11 * p ^ 4 * q := by
  -- Equivalent to `S < q * (p^4 - 8p^3 - 6p^2 - 4p - 2)`.
  -- Since `7 ≤ q`, it suffices to check `S < 7 * (p^4 - 8p^3 - 6p^2 - 4p - 2)`,
  -- i.e. `2 * p^4 > 60 * p^3 + 45 * p^2 + 30 * p + 15`.
  have hp_pos : 0 < p := by omega
  have h1 : 31 * p ^ 3 ≤ p ^ 4 := by
    have hp4 : p ^ 4 = p * p ^ 3 := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp4]
    exact Nat.mul_le_mul_right (p ^ 3) hp
  have h2 : 31 * p ^ 2 ≤ p ^ 3 := by
    have hp3 : p ^ 3 = p * p ^ 2 := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp3]
    exact Nat.mul_le_mul_right (p ^ 2) hp
  have h3 : 31 * p ≤ p ^ 2 := by
    have hp2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
    rw [hp2]
    exact Nat.mul_le_mul_right p hp
  have hbound : 60 * p ^ 3 + 45 * p ^ 2 + 30 * p + 15 < 2 * p ^ 4 := by
    have ha : 2 * p ^ 4 ≥ 62 * p ^ 3 := by omega
    have hb : 2 * p ^ 3 ≥ 62 * p ^ 2 := by omega
    have hc : 17 * p ^ 2 ≥ 17 * 31 * p := by
      have : 31 * p ≤ p ^ 2 := h3
      omega
    omega
  have hden_pos : 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2 < p ^ 4 := by omega
  have h7 : 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 <
      7 * (p ^ 4 - (8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) := by
    omega
  have hq_mul : 7 * (p ^ 4 - (8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) ≤
      q * (p ^ 4 - (8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) :=
    Nat.mul_le_mul_right _ hq
  have hlt : 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 <
      q * (p ^ 4 - (8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) := Nat.lt_of_lt_of_le h7 hq_mul
  have hexp : q * (p ^ 4 - (8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) +
      2 * q * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) =
      11 * p ^ 4 * q := by
    rcases Nat.exists_eq_add_of_le (Nat.le_of_lt hden_pos) with ⟨d, hd⟩
    have hsub : p ^ 4 - (8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2) = d := by omega
    rw [hsub]
    have hp4 : p ^ 4 = (8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2) + d := hd
    grind
  grind

/-- **Family `(4, 1)`: `p^4 * q` exclusion**:
    For primes `p ≠ q` with `5 ≤ p` and `5 ≤ q`, `¬ IsFixedPoint (p ^ 4 * q)`. -/
theorem not_isFixedPoint_prime_four_mul_prime {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) :
    ¬ IsFixedPoint (p ^ 4 * q) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hcop : Nat.Coprime (p ^ 4) q := (coprime_primes_ne hp hq hne).pow_left 4
  have hdom_p : 4 * tau q < p :=
    sharpened_dominance_bound hp (by decide) (by omega) rfl hcop hfp
  rw [tau_of_isPrime hq] at hdom_p
  have hp11 : 11 ≤ p := by
    by_cases h9 : p = 9; · exfalso; exact (by decide : ¬ IsPrime 9) (h9 ▸ hp)
    by_cases h10 : p = 10; · exfalso; exact (by decide : ¬ IsPrime 10) (h10 ▸ hp)
    omega
  have hcop_qp : Nat.Coprime (q ^ 1) (p ^ 4) := by
    rw [Nat.pow_one]
    exact hcop.symm
  have hp4_gt1 : 1 < p ^ 4 := by
    have : 11 ≤ p ^ 4 := Nat.le_trans hp11 (Nat.le_self_pow (by decide) p)
    omega
  have hdom_q : 1 * tau (p ^ 4) < q :=
    sharpened_dominance_bound hq (by decide) hp4_gt1 (by rw [Nat.pow_one, Nat.mul_comm]) hcop_qp hfp
  rw [tau_prime_pow hp 4] at hdom_q
  have hq7 : 7 ≤ q := by
    by_cases h6 : q = 6; · exfalso; exact (by decide : ¬ IsPrime 6) (h6 ▸ hq)
    omega
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop, fullMoment_prime_pow_four hp, fullMoment_prime hq,
    tau_mul_of_coprime hcop (Nat.pow_pos hp_pos) hq_pos, tau_prime_pow hp 4, tau_of_isPrime hq] at hS_eq
  have h11 : (p ^ 4 * q) * (5 * 2 + 1) = 11 * p ^ 4 * q := by grind
  rw [h11] at hS_eq
  by_cases hp31 : 31 ≤ p
  · have hlt := p4q_growth_bound p q hp31 hq7
    omega
  · have hp_cases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 := by
      by_cases h12 : p = 12; · exfalso; exact (by decide : ¬ IsPrime 12) (h12 ▸ hp)
      by_cases h14 : p = 14; · exfalso; exact (by decide : ¬ IsPrime 14) (h14 ▸ hp)
      by_cases h15 : p = 15; · exfalso; exact (by decide : ¬ IsPrime 15) (h15 ▸ hp)
      by_cases h16 : p = 16; · exfalso; exact (by decide : ¬ IsPrime 16) (h16 ▸ hp)
      by_cases h18 : p = 18; · exfalso; exact (by decide : ¬ IsPrime 18) (h18 ▸ hp)
      by_cases h20 : p = 20; · exfalso; exact (by decide : ¬ IsPrime 20) (h20 ▸ hp)
      by_cases h21 : p = 21; · exfalso; exact (by decide : ¬ IsPrime 21) (h21 ▸ hp)
      by_cases h22 : p = 22; · exfalso; exact (by decide : ¬ IsPrime 22) (h22 ▸ hp)
      by_cases h24 : p = 24; · exfalso; exact (by decide : ¬ IsPrime 24) (h24 ▸ hp)
      by_cases h25 : p = 25; · exfalso; exact (by decide : ¬ IsPrime 25) (h25 ▸ hp)
      by_cases h26 : p = 26; · exfalso; exact (by decide : ¬ IsPrime 26) (h26 ▸ hp)
      by_cases h27 : p = 27; · exfalso; exact (by decide : ¬ IsPrime 27) (h27 ▸ hp)
      by_cases h28 : p = 28; · exfalso; exact (by decide : ¬ IsPrime 28) (h28 ▸ hp)
      by_cases h30 : p = 30; · exfalso; exact (by decide : ¬ IsPrime 30) (h30 ▸ hp)
      omega
    rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · have hq_mod : (3221 * q) % 3221 = 78915 % 3221 := by
        have : 3221 * q = 78915 := by grind
        rw [this]
      rw [Nat.mul_mod_right] at hq_mod
      have hne0 : 78915 % 3221 ≠ 0 := by decide
      exact hne0 hq_mod.symm
    · have hq_mod : (9917 * q) % 9917 = 152127 % 9917 := by
        have : 9917 * q = 152127 := by grind
        rw [this]
      rw [Nat.mul_mod_right] at hq_mod
      have hne0 : 152127 % 9917 ≠ 0 := by decide
      exact hne0 hq_mod.symm
    · have hq_mod : (42413 * q) % 42413 = 438159 % 42413 := by
        have : 42413 * q = 438159 := by grind
        rw [this]
      rw [Nat.mul_mod_right] at hq_mod
      have hne0 : 438159 % 42413 ≠ 0 := by decide
      exact hne0 hq_mod.symm
    · have hq_mod : (73205 * q) % 73205 = 680163 % 73205 := by
        have : 73205 * q = 680163 := by grind
        rw [this]
      rw [Nat.mul_mod_right] at hq_mod
      have hne0 : 680163 % 73205 ≠ 0 := by decide
      exact hne0 hq_mod.symm
    · have hq_mod : (179237 * q) % 179237 = 1449507 % 179237 := by
        have : 179237 * q = 1449507 := by grind
        rw [this]
      rw [Nat.mul_mod_right] at hq_mod
      have hne0 : 1449507 % 179237 ≠ 0 := by decide
      exact hne0 hq_mod.symm
    · have hq_mod : (507005 * q) % 507005 = 3636543 % 507005 := by
        have : 507005 * q = 3636543 := by grind
        rw [this]
      rw [Nat.mul_mod_right] at hq_mod
      have hne0 : 3636543 % 507005 ≠ 0 := by decide
      exact hne0 hq_mod.symm

/-- **Exclusion of all non-squarefree $\Omega(n) = 5$ families**:
    By the General Parity Obstruction Theorem, `p^3 q^2`, `p^3 q r`, `p^2 q^2 r`, and
    `p^2 q r s` are all excluded (`tau n` is even and some prime divides `n` to exponent `2` or `3`),
    `p^5` is excluded by prime-power exclusion, and `p^4 q` is excluded by
    `not_isFixedPoint_prime_four_mul_prime`. Hence every fixed point with `omegaBig n = 5`
    must be squarefree of the form `p * q * r * s * t` with `17 ≤ p < q < r < s < t`. -/
theorem omegaFive_must_be_squarefree_ge_17 {n : Nat}
    (hfp : IsFixedPoint n) (ho5 : omegaBig n = 5) :
    ∃ p q r s t : Nat, IsPrime p ∧ IsPrime q ∧ IsPrime r ∧ IsPrime s ∧ IsPrime t ∧
      17 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧ s < t ∧ n = p * q * r * s * t := by
  have h21 : n ≠ 21 := by
    rintro rfl
    have h21_omega : omegaBig 21 = 2 := by
      have hmul21 : (21 : Nat) = 3 * 7 := rfl
      rw [hmul21, omegaBig_prime_mul isPrime_3 (by decide), omegaBig_of_isPrime isPrime_7]
    omega
  have hgcd : Nat.gcd n 6 = 1 := gcd_six_eq_one_of_isFixedPoint_ne_21 hfp h21
  obtain ⟨ps, hlen, hprime, hsorted, hn_eq⟩ := exists_primes_of_omegaBig 5 n hfp.1 ho5
  rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, _ | ⟨t, _ | _⟩⟩⟩⟩⟩ <;> try (simp at hlen)
  simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul] at hn_eq
  have hp := hprime p (by simp)
  have hq := hprime q (by simp)
  have hr := hprime r (by simp)
  have hs := hprime s (by simp)
  have ht := hprime t (by simp)
  have hpq : p ≤ q := (List.pairwise_cons.mp hsorted).1 q (by simp)
  have hqr : q ≤ r := (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 r (by simp)
  have hrs : r ≤ s :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).2).1 s (by simp)
  have hst : s ≤ t :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp
      (List.pairwise_cons.mp hsorted).2).2).2).1 t (by simp)
  have hp5 : 5 ≤ p := five_le_prime_of_dvd_coprime_six hgcd hp (by rw [hn_eq]; exact ⟨q * r * s * t, by grind⟩)
  have hq5 : 5 ≤ q := by omega
  have hr5 : 5 ≤ r := by omega
  have hs5 : 5 ≤ s := by omega
  have ht5 : 5 ≤ t := by omega
  -- Helper lemmas for parity exclusion of exponent 2 or 3 when tau is even:
  have ex_parity2 : ∀ a m : Nat, IsPrime a → 0 < m → Nat.Coprime (a ^ 2) m →
      tau m % 2 = 0 → ¬ IsFixedPoint (a ^ 2 * m) := by
    intro a m ha hm hcop htm hfp'
    have htau : tau (a ^ 2 * m) % 2 = 0 := by
      have ha_pos : 0 < a := by have := ha.1; omega
      rw [tau_mul_of_coprime hcop (Nat.pow_pos ha_pos) hm, Nat.mul_mod, htm, Nat.mul_zero]
    have hdvd : a ^ 2 ∣ a ^ 2 * m := Nat.dvd_mul_right (a ^ 2) m
    have hndvd : ¬ (a ^ (2 + 1) ∣ a ^ 2 * m) := by
      intro h
      rw [Nat.pow_succ] at h
      have ha_pos : 0 < a := by have := ha.1; omega
      have ha_m : a ∣ m := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos ha_pos) h
      have hcop_am : Nat.Coprime a m := by
        have hdvd_a : a ∣ a ^ 2 := ⟨a, by rw [Nat.pow_two]⟩
        exact Nat.Coprime.coprime_dvd_left hdvd_a hcop
      have hgcd_dvd : a ∣ Nat.gcd a m := Nat.dvd_gcd (Nat.dvd_refl a) ha_m
      rw [hcop_am] at hgcd_dvd
      have ha1 : a = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
      have := ha.1
      omega
    exact not_isFixedPoint_of_exact_exponent_mod_four_ge_two htau ha hdvd hndvd (Or.inl rfl) hfp'
  have ex_parity3 : ∀ a m : Nat, IsPrime a → 0 < m → Nat.Coprime (a ^ 3) m →
      ¬ IsFixedPoint (a ^ 3 * m) := by
    intro a m ha hm hcop hfp'
    have ha_pos : 0 < a := by have := ha.1; omega
    have htau : tau (a ^ 3 * m) % 2 = 0 := by
      rw [tau_mul_of_coprime hcop (Nat.pow_pos ha_pos) hm, tau_prime_pow ha 3]
      have hmod : (4 * tau m) % 2 = 0 := by
        have : 4 * tau m = 2 * (2 * tau m) := by grind
        rw [this]; exact Nat.mul_mod_right 2 _
      exact hmod
    have hdvd : a ^ 3 ∣ a ^ 3 * m := Nat.dvd_mul_right (a ^ 3) m
    have hndvd : ¬ (a ^ (3 + 1) ∣ a ^ 3 * m) := by
      intro h
      rw [Nat.pow_succ] at h
      have ha_m : a ∣ m := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos ha_pos) h
      have hcop_am : Nat.Coprime a m := by
        have hdvd_a : a ∣ a ^ 3 := ⟨a ^ 2, by grind⟩
        exact Nat.Coprime.coprime_dvd_left hdvd_a hcop
      have hgcd_dvd : a ∣ Nat.gcd a m := Nat.dvd_gcd (Nat.dvd_refl a) ha_m
      rw [hcop_am] at hgcd_dvd
      have ha1 : a = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
      have := ha.1
      omega
    exact not_isFixedPoint_of_exact_exponent_mod_four_ge_two htau ha hdvd hndvd (Or.inr rfl) hfp'
  -- Eliminate all equalities among `p ≤ q ≤ r ≤ s ≤ t`
  have hpq_lt : p < q := by
    by_cases hlt : p < q
    · exact hlt
    · exfalso
      have heq : p = q := by omega
      subst heq
      by_cases hpr : p = r
      · subst hpr
        by_cases hps : p = s
        · subst hps
          by_cases hpt : p = t
          · subst hpt
            rw [hn_eq] at hfp
            have hpow : p * p * p * p * p = p ^ 5 := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_pow hp (by decide) hfp
          · rw [hn_eq] at hfp
            have hpow : p * p * p * p * t = p ^ 4 * t := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_four_mul_prime hp ht hp5 ht5 hpt hfp
        · rw [hn_eq] at hfp
          have hpow : p * p * p * s * t = p ^ 3 * (s * t) := by grind
          rw [hpow] at hfp
          have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs hps
          have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
          have hs_pos : 0 < s := by omega
          have ht_pos : 0 < t := by omega
          exact ex_parity3 p (s * t) hp (Nat.mul_pos hs_pos ht_pos) ((hcop_ps.mul_right hcop_pt).pow_left 3) hfp
      · by_cases hrs' : r = s
        · subst hrs'
          by_cases hrt : r = t
          · subst hrt
            rw [hn_eq] at hfp
            have hpow : p * p * r * r * r = r ^ 3 * (p * p) := by grind
            rw [hpow] at hfp
            have hcop_rp : Nat.Coprime r p := coprime_primes_ne hr hp (Ne.symm hpr)
            exact ex_parity3 r (p * p) hr (Nat.mul_pos (by omega) (by omega))
              ((hcop_rp.mul_right hcop_rp).pow_left 3) hfp
          · rw [hn_eq] at hfp
            have hpow : p * p * r * r * t = p ^ 2 * (r ^ 2 * t) := by grind
            rw [hpow] at hfp
            have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
            have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
            have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht hrt
            have htm : tau (r ^ 2 * t) % 2 = 0 := by
              rw [tau_mul_of_coprime (hcop_rt.pow_left 2) (Nat.pow_pos (by omega)) (by omega),
                tau_prime_pow hr 2, tau_of_isPrime ht]
            exact ex_parity2 p (r ^ 2 * t) hp (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega))
              (((hcop_pr.pow_right 2).mul_right hcop_pt).pow_left 2) htm hfp
        · by_cases hst' : s = t
          · subst hst'
            rw [hn_eq] at hfp
            have hpow : p * p * r * s * s = p ^ 2 * (r * s ^ 2) := by grind
            rw [hpow] at hfp
            have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
            have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
            have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs hrs'
            have htm : tau (r * s ^ 2) % 2 = 0 := by
              rw [tau_mul_of_coprime (hcop_rs.pow_right 2) (by omega) (Nat.pow_pos (by omega)),
                tau_of_isPrime hr, tau_prime_pow hs 2]
            exact ex_parity2 p (r * s ^ 2) hp (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
              ((hcop_pr.mul_right (hcop_ps.pow_right 2)).pow_left 2) htm hfp
          · rw [hn_eq] at hfp
            have hpow : p * p * r * s * t = p ^ 2 * (r * s * t) := by grind
            rw [hpow] at hfp
            have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
            have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
            have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
            have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs hrs'
            have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht (by omega)
            have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht hst'
            have htm : tau (r * s * t) % 2 = 0 := by
              rw [tau_mul_of_coprime (hcop_rt.mul_left hcop_st) (Nat.mul_pos (by omega) (by omega)) (by omega),
                tau_mul_of_coprime hcop_rs (by omega) (by omega), tau_of_isPrime hr, tau_of_isPrime hs, tau_of_isPrime ht]
            exact ex_parity2 p (r * s * t) hp (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
              (((hcop_pr.mul_right hcop_ps).mul_right hcop_pt).pow_left 2) htm hfp
  have hqr_lt : q < r := by
    by_cases hlt : q < r
    · exact hlt
    · exfalso
      have heq : q = r := by omega
      subst heq
      by_cases hqs : q = s
      · subst hqs
        by_cases hqt : q = t
        · subst hqt
          rw [hn_eq] at hfp
          have hpow : p * q * q * q * q = q ^ 4 * p := by grind
          rw [hpow] at hfp
          exact not_isFixedPoint_prime_four_mul_prime hq hp hq5 hp5 (Ne.symm (by omega)) hfp
        · rw [hn_eq] at hfp
          have hpow : p * q * q * q * t = q ^ 3 * (p * t) := by grind
          rw [hpow] at hfp
          have hcop_qp : Nat.Coprime q p := coprime_primes_ne hq hp (by omega)
          have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht hqt
          exact ex_parity3 q (p * t) hq (Nat.mul_pos (by omega) (by omega))
            ((hcop_qp.mul_right hcop_qt).pow_left 3) hfp
      · by_cases hst' : s = t
        · subst hst'
          rw [hn_eq] at hfp
          have hpow : p * q * q * s * s = q ^ 2 * (p * s ^ 2) := by grind
          rw [hpow] at hfp
          have hcop_qp : Nat.Coprime q p := coprime_primes_ne hq hp (by omega)
          have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs hqs
          have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
          have htm : tau (p * s ^ 2) % 2 = 0 := by
            rw [tau_mul_of_coprime (hcop_ps.pow_right 2) (by omega) (Nat.pow_pos (by omega)),
              tau_of_isPrime hp, tau_prime_pow hs 2]
          exact ex_parity2 q (p * s ^ 2) hq (Nat.mul_pos (by omega) (Nat.pow_pos (by omega)))
            ((hcop_qp.mul_right (hcop_qs.pow_right 2)).pow_left 2) htm hfp
        · rw [hn_eq] at hfp
          have hpow : p * q * q * s * t = q ^ 2 * (p * s * t) := by grind
          rw [hpow] at hfp
          have hcop_qp : Nat.Coprime q p := coprime_primes_ne hq hp (by omega)
          have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs hqs
          have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
          have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
          have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
          have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht hst'
          have htm : tau (p * s * t) % 2 = 0 := by
            rw [tau_mul_of_coprime (hcop_pt.mul_left hcop_st) (Nat.mul_pos (by omega) (by omega)) (by omega),
              tau_mul_of_coprime hcop_ps (by omega) (by omega), tau_of_isPrime hp, tau_of_isPrime hs, tau_of_isPrime ht]
          exact ex_parity2 q (p * s * t) hq (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
            (((hcop_qp.mul_right hcop_qs).mul_right hcop_qt).pow_left 2) htm hfp
  have hrs_lt : r < s := by
    by_cases hlt : r < s
    · exact hlt
    · exfalso
      have heq : r = s := by omega
      subst heq
      by_cases hrt : r = t
      · subst hrt
        rw [hn_eq] at hfp
        have hpow : p * q * r * r * r = r ^ 3 * (p * q) := by grind
        rw [hpow] at hfp
        have hcop_rp : Nat.Coprime r p := coprime_primes_ne hr hp (by omega)
        have hcop_rq : Nat.Coprime r q := coprime_primes_ne hr hq (by omega)
        exact ex_parity3 r (p * q) hr (Nat.mul_pos (by omega) (by omega))
          ((hcop_rp.mul_right hcop_rq).pow_left 3) hfp
      · rw [hn_eq] at hfp
        have hpow : p * q * r * r * t = r ^ 2 * (p * q * t) := by grind
        rw [hpow] at hfp
        have hcop_rp : Nat.Coprime r p := coprime_primes_ne hr hp (by omega)
        have hcop_rq : Nat.Coprime r q := coprime_primes_ne hr hq (by omega)
        have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht hrt
        have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
        have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
        have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
        have htm : tau (p * q * t) % 2 = 0 := by
          rw [tau_mul_of_coprime (hcop_pt.mul_left hcop_qt) (Nat.mul_pos (by omega) (by omega)) (by omega),
            tau_mul_of_coprime hcop_pq (by omega) (by omega), tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime ht]
        exact ex_parity2 r (p * q * t) hr (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
          (((hcop_rp.mul_right hcop_rq).mul_right hcop_rt).pow_left 2) htm hfp
  have hst_lt : s < t := by
    by_cases hlt : s < t
    · exact hlt
    · exfalso
      have heq : s = t := by omega
      subst heq
      rw [hn_eq] at hfp
      have hpow : p * q * r * s * s = s ^ 2 * (p * q * r) := by grind
      rw [hpow] at hfp
      have hcop_sp : Nat.Coprime s p := coprime_primes_ne hs hp (by omega)
      have hcop_sq : Nat.Coprime s q := coprime_primes_ne hs hq (by omega)
      have hcop_sr : Nat.Coprime s r := coprime_primes_ne hs hr (by omega)
      have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
      have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
      have hcop_qr : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
      have htm : tau (p * q * r) % 2 = 0 := by
        rw [tau_mul_of_coprime (hcop_pr.mul_left hcop_qr) (Nat.mul_pos (by omega) (by omega)) (by omega),
          tau_mul_of_coprime hcop_pq (by omega) (by omega), tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime hr]
      exact ex_parity2 s (p * q * r) hs (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
        (((hcop_sp.mul_right hcop_sq).mul_right hcop_sr).pow_left 2) htm hfp
  -- Now `p < q < r < s < t`, so `tau(q * r * s * t) = 16`, giving `17 ≤ p` via `sharpened_dominance_bound`!
  have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
  have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
  have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
  have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
  have hcop_qr : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
  have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs (by omega)
  have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
  have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs (by omega)
  have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht (by omega)
  have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht (by omega)
  have hcop_p_qrst : Nat.Coprime (p ^ 1) (q * r * s * t) := by
    rw [Nat.pow_one]
    exact ((hcop_pq.mul_right hcop_pr).mul_right hcop_ps).mul_right hcop_pt
  have hqrst_gt1 : 1 < q * r * s * t := by
    have hq_pos : 0 < q := by omega
    have hr_pos : 0 < r := by omega
    have hs_pos : 0 < s := by omega
    have ht_pos : 0 < t := by omega
    have hqr_ge : 5 * 5 ≤ q * r := Nat.mul_le_mul hq5 hr5
    have hqrs_ge : 25 * 5 ≤ q * r * s := Nat.mul_le_mul hqr_ge hs5
    have hqrst_ge : 125 * 5 ≤ q * r * s * t := Nat.mul_le_mul hqrs_ge ht5
    omega
  have hdom := sharpened_dominance_bound hp (by decide) hqrst_gt1 (by rw [Nat.pow_one, hn_eq]; grind) hcop_p_qrst hfp
  have htau_qrst : tau (q * r * s * t) = 16 := by
    have hcop_qrs_t : Nat.Coprime (q * r * s) t := (hcop_qt.mul_left hcop_rt).mul_left hcop_st
    have hcop_qr_s : Nat.Coprime (q * r) s := hcop_qs.mul_left hcop_rs
    have hqr_pos : 0 < q * r := Nat.mul_pos (by omega) (by omega)
    have hqrs_pos : 0 < q * r * s := Nat.mul_pos hqr_pos (by omega)
    rw [tau_mul_of_coprime hcop_qrs_t hqrs_pos (by omega),
      tau_mul_of_coprime hcop_qr_s hqr_pos (by omega),
      tau_mul_of_coprime hcop_qr (by omega) (by omega),
      tau_of_isPrime hq, tau_of_isPrime hr, tau_of_isPrime hs, tau_of_isPrime ht]
  rw [htau_qrst, Nat.one_mul] at hdom
  exact ⟨p, q, r, s, t, hp, hq, hr, hs, ht, by omega, hpq_lt, hqr_lt, hrs_lt, hst_lt, hn_eq⟩

end OmegaFiveExclusions

end OeisA245211
