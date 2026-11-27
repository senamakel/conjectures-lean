/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/
import OeisA245211.OmegaFive

/-!
# OEIS A245211: Complete Classification of $\Omega(n) \le 6$ Fixed Points

This module proves the unconditional exclusion of every positive integer `n` with
`omegaBig n = 6`:
1. All non-squarefree $\Omega(n) = 6$ families:
   - `(6)` (`p^6`), excluded by `not_isFixedPoint_prime_pow`;
   - `(5, 1)` (`p^5 * q`), excluded by `p5q_growth_bound` (`79 ≤ p`) and 17 modular checks;
   - `(4, 2)` (`p^4 * q^2`), excluded modulo `4`;
   - `(2, 2, 2)` (`p^2 * q^2 * r^2`), excluded modulo `8`;
   - `(4, 1, 1)` (`p^4 * q * r`), excluded via `p4qr_growth_bound` (`53 ≤ p`, `29 ≤ q`) and small-factor checks;
   - `(3, 3)`, `(3, 2, 1)`, `(3, 1, 1, 1)`, `(2, 2, 1, 1)`, `(2, 1, 1, 1, 1)`, excluded by the
     General Parity Obstruction Theorem (`not_isFixedPoint_of_exact_exponent_mod_four_ge_two`).
2. The non-squarefree reduction `omegaSix_must_be_squarefree_ge_37`: every fixed point with
   `omegaBig n = 6` must be squarefree `p * q * r * s * t * u` with `37 ≤ p < q < r < s < t < u`.
3. Squarefree six-prime exclusion (`six_prime_growth_bound` at `181 ≤ p` and Cunningham forced
   closure on the 30 primes `37 ≤ p < 181`).
4. Top-level classification: every fixed point `n` with `omegaBig n ≤ 6` equals `21`, and every
   fixed point `n ≠ 21` satisfies `7 ≤ omegaBig n`.
-/

namespace OeisA245211

section OmegaSixNonSquarefree

/-! ## Section 1: Family `(5, 1)` (`p ^ 5 * q`) Exclusion -/

/-- Exact evaluation of `fullMoment (p ^ 5)` for prime `p`:
    `6 * p ^ 5 + 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1`. -/
theorem fullMoment_prime_pow_five {p : Nat} (hp : IsPrime p) :
    fullMoment (p ^ 5) = 6 * p ^ 5 + 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 := by
  rw [fullMoment_prime_pow_succ hp 4, fullMoment_prime_pow_succ hp 3,
    fullMoment_prime_pow_succ hp 2, fullMoment_prime_pow_succ hp 1,
    fullMoment_prime_pow_succ hp 0, fullMoment_prime_pow_zero]
  grind

/-- Growth cutoff for `p ^ 5 * q`: for `79 ≤ p` and `7 ≤ q`,
    `(6 * p ^ 5 + 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * q + 1) < 13 * p ^ 5 * q`. -/
theorem p5q_growth_bound (p q : Nat) (hp : 79 ≤ p) (hq : 7 ≤ q) :
    (6 * p ^ 5 + 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * q + 1) < 13 * p ^ 5 * q := by
  have h1 : 79 * p ^ 4 ≤ p ^ 5 := by
    have hp5 : p ^ 5 = p * p ^ 4 := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp5]
    exact Nat.mul_le_mul_right (p ^ 4) hp
  have h2 : 79 * p ^ 3 ≤ p ^ 4 := by
    have hp4 : p ^ 4 = p * p ^ 3 := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp4]
    exact Nat.mul_le_mul_right (p ^ 3) hp
  have h3 : 79 * p ^ 2 ≤ p ^ 3 := by
    have hp3 : p ^ 3 = p * p ^ 2 := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp3]
    exact Nat.mul_le_mul_right (p ^ 2) hp
  have h4 : 79 * p ≤ p ^ 2 := by
    have hp2 : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
    rw [hp2]
    exact Nat.mul_le_mul_right p hp
  have hbound : 76 * p ^ 4 + 61 * p ^ 3 + 46 * p ^ 2 + 31 * p + 16 < 7 * p ^ 5 := by
    have ha : 7 * p ^ 5 ≥ 7 * 79 * p ^ 4 := by omega
    have hb : 477 * p ^ 4 ≥ 477 * 79 * p ^ 3 := by omega
    have hc : 37622 * p ^ 3 ≥ 37622 * 79 * p ^ 2 := by omega
    have hd : 2972092 * p ^ 2 ≥ 2972092 * 79 * p := by omega
    omega
  have hden_pos : 10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2 < p ^ 5 := by omega
  have h7 : 6 * p ^ 5 + 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 <
      7 * (p ^ 5 - (10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) := by
    omega
  have hq_mul : 7 * (p ^ 5 - (10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) ≤
      q * (p ^ 5 - (10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) :=
    Nat.mul_le_mul_right _ hq
  have hlt : 6 * p ^ 5 + 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 <
      q * (p ^ 5 - (10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) :=
    Nat.lt_of_lt_of_le h7 hq_mul
  have hexp : q * (p ^ 5 - (10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2)) +
      2 * q * (6 * p ^ 5 + 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) =
      13 * p ^ 5 * q := by
    rcases Nat.exists_eq_add_of_le (Nat.le_of_lt hden_pos) with ⟨d, hd⟩
    have hsub : p ^ 5 - (10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2) = d := by omega
    rw [hsub]
    have hp5 : p ^ 5 = (10 * p ^ 4 + 8 * p ^ 3 + 6 * p ^ 2 + 4 * p + 2) + d := hd
    grind
  grind

private theorem prime_11_to_73 {p : Nat} (hp : IsPrime p) (hlo : 11 ≤ p) (hhi : p < 79) :
    p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨
      p = 41 ∨ p = 43 ∨ p = 47 ∨ p = 53 ∨ p = 59 ∨ p = 61 ∨ p = 67 ∨ p = 71 ∨ p = 73 := by
  have hdec : ∀ x : Fin 79, 11 ≤ x.1 → IsPrime x.1 →
      x.1 = 11 ∨ x.1 = 13 ∨ x.1 = 17 ∨ x.1 = 19 ∨ x.1 = 23 ∨ x.1 = 29 ∨ x.1 = 31 ∨ x.1 = 37 ∨
        x.1 = 41 ∨ x.1 = 43 ∨ x.1 = 47 ∨ x.1 = 53 ∨ x.1 = 59 ∨ x.1 = 61 ∨ x.1 = 67 ∨ x.1 = 71 ∨ x.1 = 73 := by
    decide
  have hx := hdec ⟨p, hhi⟩ hlo hp
  simpa using hx

/-- **Family `(5, 1)`: `p ^ 5 * q` exclusion**:
    For primes `p ≠ q` with `5 ≤ p` and `5 ≤ q`, `¬ IsFixedPoint (p ^ 5 * q)`. -/
theorem not_isFixedPoint_prime_five_mul_prime {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) :
    ¬ IsFixedPoint (p ^ 5 * q) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hcop : Nat.Coprime (p ^ 5) q := (coprime_primes_ne hp hq hne).pow_left 5
  have hdom_p : 5 * tau q < p :=
    sharpened_dominance_bound hp (by decide) (by omega) rfl hcop hfp
  rw [tau_of_isPrime hq] at hdom_p
  have hp11 : 11 ≤ p := by omega
  have hcop_qp : Nat.Coprime (q ^ 1) (p ^ 5) := by
    rw [Nat.pow_one]
    exact hcop.symm
  have hp5_gt1 : 1 < p ^ 5 := by
    have : 11 ≤ p ^ 5 := Nat.le_trans hp11 (Nat.le_self_pow (by decide) p)
    omega
  have hdom_q : 1 * tau (p ^ 5) < q :=
    sharpened_dominance_bound hq (by decide) hp5_gt1 (by rw [Nat.pow_one, Nat.mul_comm]) hcop_qp hfp
  rw [tau_prime_pow hp 5] at hdom_q
  have hq7 : 7 ≤ q := by omega
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop, fullMoment_prime_pow_five hp, fullMoment_prime hq,
    tau_mul_of_coprime hcop (Nat.pow_pos hp_pos) hq_pos, tau_prime_pow hp 5, tau_of_isPrime hq] at hS_eq
  have h13 : (p ^ 5 * q) * (6 * 2 + 1) = 13 * p ^ 5 * q := by grind
  rw [h13] at hS_eq
  by_cases hp79 : 79 ≤ p
  · have hlt := p5q_growth_bound p q hp79 hq7
    omega
  · have hp_cases := prime_11_to_73 hp hp11 (by omega)
    rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hmod : (57891 * q) % 57891 = 1068183 % 57891 := by
        have : 57891 * q = 1068183 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 1068183 % 57891 ≠ 0) hmod.symm
    · have hmod : (152159 * q) % 152159 = 2441747 % 152159 := by
        have : 152159 * q = 2441747 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 2441747 % 152159 ≠ 0) hmod.symm
    · have hmod : (647903 * q) % 647903 = 8991939 % 647903 := by
        have : 647903 * q = 8991939 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 8991939 % 647903 ≠ 0) hmod.symm
    · have hmod : (1159007 * q) % 1159007 = 15545939 % 1159007 := by
        have : 1159007 * q = 15545939 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 15545939 % 1159007 ≠ 0) hmod.symm
    · have hmod : (3009359 * q) % 3009359 = 39923891 % 3009359 := by
        have : 3009359 * q = 39923891 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 39923891 % 3009359 ≠ 0) hmod.symm
    · have hmod : (10035743 * q) % 10035743 = 126619619 % 10035743 := by
        have : 10035743 * q = 126619619 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 126619619 % 10035743 ≠ 0) hmod.symm
    · have hmod : (14176319 * q) % 14176319 = 176524211 % 14176319 := by
        have : 14176319 * q = 176524211 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 176524211 % 14176319 ≠ 0) hmod.symm
    · have hmod : (35287919 * q) % 35287919 = 425420339 % 35287919 := by
        have : 35287919 * q = 425420339 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 425420339 % 35287919 ≠ 0) hmod.symm
    · have hmod : (59777903 * q) % 59777903 = 708384779 % 59777903 := by
        have : 59777903 * q = 708384779 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 708384779 % 59777903 ≠ 0) hmod.symm
    · have hmod : (76359935 * q) % 76359935 = 899194403 % 76359935 := by
        have : 76359935 * q = 899194403 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 899194403 % 76359935 ≠ 0) hmod.symm
    · have hmod : (120560687 * q) % 120560687 = 1402191299 % 120560687 := by
        have : 120560687 * q = 1402191299 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 1402191299 % 120560687 ≠ 0) hmod.symm
    · have hmod : (220780799 * q) % 220780799 = 2549654819 % 220780799 := by
        have : 220780799 * q = 2549654819 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 2549654819 % 220780799 ≠ 0) hmod.symm
    · have hmod : (379476959 * q) % 379476959 = 4348436939 % 379476959 := by
        have : 379476959 * q = 4348436939 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 4348436939 % 379476959 ≠ 0) hmod.symm
    · have hmod : (449830127 * q) % 449830127 = 5143462523 % 449830127 := by
        have : 449830127 * q = 5143462523 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 5143462523 % 449830127 ≠ 0) hmod.symm
    · have hmod : (722977199 * q) % 722977199 = 8228718939 % 722977199 := by
        have : 722977199 * q = 8228718939 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 8228718939 % 722977199 ≠ 0) hmod.symm
    · have hmod : (970745087 * q) % 970745087 = 11018634299 % 970745087 := by
        have : 970745087 * q = 11018634299 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 11018634299 % 970745087 ≠ 0) hmod.symm
    · have hmod : (1117025375 * q) % 1117025375 = 12661964531 % 1117025375 := by
        have : 1117025375 * q = 12661964531 := by omega
        rw [this]
      rw [Nat.mul_mod_right] at hmod
      exact (by decide : 12661964531 % 1117025375 ≠ 0) hmod.symm

/-! ## Section 2: Families `(4, 2)` and `(2, 2, 2)` via Modulo-4 and Modulo-8 Obstructions -/

private theorem odd_of_prime_ge_five {p : Nat} (hp : IsPrime p) (hp5 : 5 ≤ p) : p % 2 = 1 := by
  have hnot2 : p ≠ 2 := by omega
  have hcop : Nat.Coprime p 2 := coprime_primes_ne hp isPrime_2 hnot2
  have hd : ¬ (2 ∣ p) := by
    intro h2
    have h1 : 2 ∣ Nat.gcd p 2 := Nat.dvd_gcd h2 (Nat.dvd_refl 2)
    rw [hcop] at h1
    omega
  omega

private theorem three_sq_add_two_add_one_mod_four_eq_two {q : Nat} (hq : q % 2 = 1) :
    (3 * q * q + 2 * q + 1) % 4 = 2 := by
  have hq4 : q % 4 < 4 := Nat.mod_lt q (by decide)
  have hdiv : q = 4 * (q / 4) + q % 4 := (Nat.div_add_mod q 4).symm
  have hmod2 : (q % 4) % 2 = 1 := by omega
  have h13 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases h13 with h | h
  · have heq : 3 * q * q + 2 * q + 1 =
        6 + 4 * (12 * (q / 4) * (q / 4) + 8 * (q / 4)) := by
      rw [hdiv, h]; grind
    rw [heq, Nat.add_mul_mod_self_left]
  · have heq : 3 * q * q + 2 * q + 1 =
        34 + 4 * (12 * (q / 4) * (q / 4) + 20 * (q / 4)) := by
      rw [hdiv, h]; grind
    rw [heq, Nat.add_mul_mod_self_left]

/-- **Family `(4, 2)`: `p ^ 4 * q ^ 2` exclusion via mod 4**:
    For distinct primes `p ≠ q` with `5 ≤ p` and `5 ≤ q`, `¬ IsFixedPoint (p ^ 4 * q ^ 2)`. -/
theorem not_isFixedPoint_prime_four_mul_prime_sq {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hne : p ≠ q) :
    ¬ IsFixedPoint (p ^ 4 * q ^ 2) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hp_odd : p % 2 = 1 := odd_of_prime_ge_five hp hp5
  have hq_odd : q % 2 = 1 := odd_of_prime_ge_five hq hq5
  have hcop : Nat.Coprime (p ^ 4) (q ^ 2) := (coprime_primes_ne hp hq hne).pow 4 2
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop, fullMoment_prime_pow_four hp, fullMoment_prime_sq hq,
    tau_mul_of_coprime hcop (Nat.pow_pos hp_pos) (Nat.pow_pos hq_pos),
    tau_prime_pow hp 4, tau_prime_pow hq 2] at hS_eq
  have h16 : (p ^ 4 * q ^ 2) * (5 * 3 + 1) = 4 * (4 * p ^ 4 * q ^ 2) := by grind
  rw [h16] at hS_eq
  have hSp_odd : (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) % 2 = 1 := by
    have hpow : ∀ k : Nat, p ^ k % 2 = 1 := by
      intro k
      induction k with
      | zero => rfl
      | succ m ih => rw [Nat.pow_succ, Nat.mul_mod, ih, hp_odd]
    have h1 := hpow 4
    have h2 := hpow 3
    have h3 := hpow 2
    omega
  have hSq_mod4 : (3 * q * q + 2 * q + 1) % 4 = 2 :=
    three_sq_add_two_add_one_mod_four_eq_two hq_odd
  have hlhs_mod4 : ((5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (3 * q * q + 2 * q + 1)) % 4 = 2 := by
    obtain ⟨k, hk⟩ : ∃ k, 3 * q * q + 2 * q + 1 = 4 * k + 2 :=
      ⟨(3 * q * q + 2 * q + 1) / 4, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, 5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1 = 2 * m + 1 :=
      ⟨(5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) / 2, by omega⟩
    have heq : (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (3 * q * q + 2 * q + 1) =
        2 + 4 * (2 * m * k + m + k) := by rw [hm, hk]; grind
    rw [heq, Nat.add_mul_mod_self_left]
  rw [hS_eq, Nat.mul_mod_right] at hlhs_mod4
  omega

/-- **Family `(2, 2, 2)`: `p ^ 2 * q ^ 2 * r ^ 2` exclusion via mod 8**:
    For pairwise distinct primes `5 ≤ p`, `5 ≤ q`, `5 ≤ r`,
    `¬ IsFixedPoint (p ^ 2 * q ^ 2 * r ^ 2)`. -/
theorem not_isFixedPoint_three_prime_sq {p q r : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hr5 : 5 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ IsFixedPoint (p ^ 2 * q ^ 2 * r ^ 2) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hr_pos : 0 < r := by omega
  have hp_odd : p % 2 = 1 := odd_of_prime_ge_five hp hp5
  have hq_odd : q % 2 = 1 := odd_of_prime_ge_five hq hq5
  have hr_odd : r % 2 = 1 := odd_of_prime_ge_five hr hr5
  have hcop_pq : Nat.Coprime (p ^ 2) (q ^ 2) := (coprime_primes_ne hp hq hpq).pow 2 2
  have hcop_pr : Nat.Coprime (p ^ 2) (r ^ 2) := (coprime_primes_ne hp hr hpr).pow 2 2
  have hcop_qr : Nat.Coprime (q ^ 2) (r ^ 2) := (coprime_primes_ne hq hr hqr).pow 2 2
  have hcop_pqr : Nat.Coprime (p ^ 2 * q ^ 2) (r ^ 2) := hcop_pr.mul_left hcop_qr
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop_pqr, fullMoment_mul_of_coprime hcop_pq,
    fullMoment_prime_sq hp, fullMoment_prime_sq hq, fullMoment_prime_sq hr,
    tau_mul_of_coprime hcop_pqr (Nat.mul_pos (Nat.pow_pos hp_pos) (Nat.pow_pos hq_pos)) (Nat.pow_pos hr_pos),
    tau_mul_of_coprime hcop_pq (Nat.pow_pos hp_pos) (Nat.pow_pos hq_pos),
    tau_prime_pow hp 2, tau_prime_pow hq 2, tau_prime_pow hr 2] at hS_eq
  have hSp_mod4 := three_sq_add_two_add_one_mod_four_eq_two hp_odd
  have hSq_mod4 := three_sq_add_two_add_one_mod_four_eq_two hq_odd
  have hSr_mod4 := three_sq_add_two_add_one_mod_four_eq_two hr_odd
  have hSp_mod : (3 * p * p + 2 * p + 1) % 2 = 0 := by omega
  have hSq_mod : (3 * q * q + 2 * q + 1) % 2 = 0 := by omega
  have hSr_mod : (3 * r * r + 2 * r + 1) % 2 = 0 := by omega
  obtain ⟨a, ha⟩ : ∃ a, 3 * p * p + 2 * p + 1 = 2 * a := ⟨(3 * p * p + 2 * p + 1) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 3 * q * q + 2 * q + 1 = 2 * b := ⟨(3 * q * q + 2 * q + 1) / 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, 3 * r * r + 2 * r + 1 = 2 * c := ⟨(3 * r * r + 2 * r + 1) / 2, by omega⟩
  have hlhs_mod8 : ((3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1) * (3 * r * r + 2 * r + 1)) % 8 = 0 := by
    have heq : (3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1) * (3 * r * r + 2 * r + 1) =
        8 * (a * b * c) := by rw [ha, hb, hc]; grind
    rw [heq, Nat.mul_mod_right]
  have hp2_odd : p ^ 2 % 2 = 1 := by rw [Nat.pow_two, Nat.mul_mod, hp_odd]
  have hq2_odd : q ^ 2 % 2 = 1 := by rw [Nat.pow_two, Nat.mul_mod, hq_odd]
  have hr2_odd : r ^ 2 % 2 = 1 := by rw [Nat.pow_two, Nat.mul_mod, hr_odd]
  have hprod_odd : (p ^ 2 * q ^ 2 * r ^ 2) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.mul_mod (p ^ 2), hp2_odd, hq2_odd, hr2_odd]
  obtain ⟨m, hm⟩ : ∃ m, p ^ 2 * q ^ 2 * r ^ 2 = 2 * m + 1 :=
    ⟨(p ^ 2 * q ^ 2 * r ^ 2) / 2, by omega⟩
  have hrhs_mod8 : ((p ^ 2 * q ^ 2 * r ^ 2) * (3 * 3 * 3 + 1)) % 8 = 4 := by
    have heq : (p ^ 2 * q ^ 2 * r ^ 2) * (3 * 3 * 3 + 1) = 4 + 8 * (7 * m + 3) := by
      rw [hm]; grind
    rw [heq, Nat.add_mul_mod_self_left]
  rw [hS_eq, hrhs_mod8] at hlhs_mod8
  omega

/-! ## Section 3: Family `(4, 1, 1)` (`p ^ 4 * q * r`) Exclusion -/

/-- Growth cutoff for `p ^ 4 * q * r`: for `53 ≤ p`, `29 ≤ q`, `31 ≤ r`,
    `(5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * q + 1) * (2 * r + 1) < 21 * p ^ 4 * q * r`. -/
theorem p4qr_growth_bound (p q r : Nat) (hp : 53 ≤ p) (hq : 29 ≤ q) (hr : 31 ≤ r) :
    (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * q + 1) * (2 * r + 1) <
      21 * p ^ 4 * q * r := by
  have hp4_pos : 0 < p ^ 4 := Nat.pow_pos (by omega)
  have hq_pos : 0 < q := by omega
  have hr_pos : 0 < r := by omega
  have hp53_4 : 53 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp 4
  have hp1 : 53 * p ^ 3 ≤ p ^ 4 := by
    have hp4 : p ^ 4 = p * p ^ 3 := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp4]; exact Nat.mul_le_mul_right (p ^ 3) hp
  have hp2 : 53 ^ 2 * p ^ 2 ≤ p ^ 4 := by
    have : 53 ^ 2 * p ^ 2 = (53 * p) ^ 2 := by grind
    have hle : 53 * 53 ≤ 53 * p := Nat.mul_le_mul_left 53 hp
    have hpow : 53 * 53 * p ^ 2 ≤ 53 * (p * p ^ 2) := by
      have : 53 * p ^ 2 ≤ p * p ^ 2 := Nat.mul_le_mul_right (p ^ 2) hp
      omega
    have : 53 * (p * p ^ 2) = 53 * p ^ 3 := by
      have hp3 : p ^ 3 = p * p ^ 2 := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp3]
    omega
  have hp3 : 53 ^ 3 * p ≤ p ^ 4 := by
    have h1 : 53 ^ 3 * p ≤ 53 ^ 2 * p ^ 2 := by
      have h53p : 53 * p ≤ p * p := Nat.mul_le_mul_right p hp
      have hp2_eq : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
      have h' : 53 ^ 2 * (53 * p) ≤ 53 ^ 2 * (p * p) := Nat.mul_le_mul_left (53 ^ 2) h53p
      have h'' : 53 ^ 3 * p = 53 ^ 2 * (53 * p) := by grind
      have h''' : 53 ^ 2 * (p * p) = 53 ^ 2 * p ^ 2 := by rw [← hp2_eq]
      omega
    exact Nat.le_trans h1 hp2
  have hS_bound : 7890481 * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) ≤ 40056447 * p ^ 4 := by
    have ha : 53 ^ 4 = 7890481 := by decide
    have hb : 53 ^ 3 = 148877 := by decide
    have hc : 53 ^ 2 = 2809 := by decide
    rw [ha] at hp53_4
    rw [hb] at hp3
    rw [hc] at hp2
    omega
  have hq_bound : 29 * (2 * q + 1) ≤ 59 * q := by omega
  have hr_bound : 31 * (2 * r + 1) ≤ 63 * r := by omega
  have h12 : (7890481 * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1)) * (29 * (2 * q + 1)) ≤
      (40056447 * p ^ 4) * (59 * q) := Nat.mul_le_mul hS_bound hq_bound
  have h123 := Nat.mul_le_mul h12 hr_bound
  have hA : 7093542419 * ((5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * q + 1) * (2 * r + 1)) =
      ((7890481 * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1)) * (29 * (2 * q + 1))) * (31 * (2 * r + 1)) := by
    grind
  have hB : 148889813499 * (p ^ 4 * q * r) = ((40056447 * p ^ 4) * (59 * q)) * (63 * r) := by
    grind
  rw [← hA, ← hB] at h123
  have hpqr_pos : 0 < p ^ 4 * q * r := Nat.mul_pos (Nat.mul_pos hp4_pos hq_pos) hr_pos
  have hrhs : 148889813499 * (p ^ 4 * q * r) < 7093542419 * (21 * p ^ 4 * q * r) := by
    have hC : 7093542419 * (21 * p ^ 4 * q * r) = 148964390799 * (p ^ 4 * q * r) := by grind
    rw [hC]
    exact Nat.mul_lt_mul_of_pos_right (by decide) hpqr_pos
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h123 hrhs)

private theorem prime_dvd_21p4qr_impossible {f p q r : Nat}
    (hf : IsPrime f) (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hf3 : f ≠ 3) (hf7 : f ≠ 7) (hfp : f ≠ p) (hfq : f ≠ q) (hfr : f ≠ r)
    (hdvd : f ∣ 21 * p ^ 4 * q * r) : False := by
  have h3 : Nat.Coprime f 3 := coprime_primes_ne hf isPrime_3 hf3
  have h7 : Nat.Coprime f 7 := coprime_primes_ne hf isPrime_7 hf7
  have h21 : Nat.Coprime f 21 := by
    have : (21 : Nat) = 3 * 7 := rfl
    rw [this]; exact h3.mul_right h7
  have hcp : Nat.Coprime f (p ^ 4) := (coprime_primes_ne hf hp hfp).pow_right 4
  have hcq : Nat.Coprime f q := coprime_primes_ne hf hq hfq
  have hcr : Nat.Coprime f r := coprime_primes_ne hf hr hfr
  have hcop_all : Nat.Coprime f (21 * p ^ 4 * q * r) :=
    ((h21.mul_right hcp).mul_right hcq).mul_right hcr
  have hgcd_dvd : f ∣ Nat.gcd f (21 * p ^ 4 * q * r) := Nat.dvd_gcd (Nat.dvd_refl f) hdvd
  rw [hcop_all] at hgcd_dvd
  have heq1 : f = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
  have := hf.1
  omega

private theorem prime_dvd_21p4qr_mem_qr {f p q r : Nat}
    (hf : IsPrime f) (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hf3 : f ≠ 3) (hf7 : f ≠ 7) (hfp : f ≠ p)
    (hdvd : f ∣ 21 * p ^ 4 * q * r) : f = q ∨ f = r := by
  have h3 : Nat.Coprime f 3 := coprime_primes_ne hf isPrime_3 hf3
  have h7 : Nat.Coprime f 7 := coprime_primes_ne hf isPrime_7 hf7
  have h21 : Nat.Coprime f 21 := by
    have : (21 : Nat) = 3 * 7 := rfl
    rw [this]; exact h3.mul_right h7
  have hcp : Nat.Coprime f (p ^ 4) := (coprime_primes_ne hf hp hfp).pow_right 4
  have hdvd1 : f ∣ q * r := by
    have hassoc : 21 * p ^ 4 * q * r = (21 * p ^ 4) * (q * r) := by grind
    rw [hassoc] at hdvd
    exact (h21.mul_right hcp).dvd_of_dvd_mul_left hdvd
  by_cases hfq : f = q
  · exact Or.inl hfq
  · have hcq : Nat.Coprime f q := coprime_primes_ne hf hq hfq
    have hfr : f ∣ r := hcq.dvd_of_dvd_mul_left hdvd1
    rcases hr.2 f hfr with h1 | rfl
    · have := hf.1; omega
    · exact Or.inr rfl

private theorem prime_17_to_47 {p : Nat} (hp : IsPrime p) (hlo : 17 ≤ p) (hhi : p < 53) :
    p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 41 ∨ p = 43 ∨ p = 47 := by
  have hdec : ∀ x : Fin 53, 17 ≤ x.1 → IsPrime x.1 →
      x.1 = 17 ∨ x.1 = 19 ∨ x.1 = 23 ∨ x.1 = 29 ∨ x.1 = 31 ∨ x.1 = 37 ∨ x.1 = 41 ∨ x.1 = 43 ∨ x.1 = 47 := by
    decide
  have hx := hdec ⟨p, hhi⟩ hlo hp
  simpa using hx

private theorem prime_11_to_23 {q : Nat} (hq : IsPrime q) (hlo : 11 ≤ q) (hhi : q < 29) :
    q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 := by
  have hdec : ∀ x : Fin 29, 11 ≤ x.1 → IsPrime x.1 →
      x.1 = 11 ∨ x.1 = 13 ∨ x.1 = 17 ∨ x.1 = 19 ∨ x.1 = 23 := by
    decide
  have hx := hdec ⟨q, hhi⟩ hlo hq
  simpa using hx

private theorem prime_11_to_29 {q : Nat} (hq : IsPrime q) (hlo : 11 ≤ q) (hhi : q < 31) :
    q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 ∨ q = 29 := by
  have hdec : ∀ x : Fin 31, 11 ≤ x.1 → IsPrime x.1 →
      x.1 = 11 ∨ x.1 = 13 ∨ x.1 = 17 ∨ x.1 = 19 ∨ x.1 = 23 ∨ x.1 = 29 := by
    decide
  have hx := hdec ⟨q, hhi⟩ hlo hq
  simpa using hx

private theorem not_nine_dvd_21p4qr {p q r : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hr5 : 5 ≤ r)
    (hdvd : 9 ∣ 21 * p ^ 4 * q * r) : False := by
  obtain ⟨k, hk⟩ := hdvd
  have h3dvd : 3 ∣ p ^ 4 * q * r := ⟨7 * k, by grind⟩
  have h3p : Nat.Coprime 3 p := coprime_primes_ne isPrime_3 hp (by omega)
  have h3q : Nat.Coprime 3 q := coprime_primes_ne isPrime_3 hq (by omega)
  have h3r : Nat.Coprime 3 r := coprime_primes_ne isPrime_3 hr (by omega)
  have hcop : Nat.Coprime 3 (p ^ 4 * q * r) :=
    ((h3p.pow_right 4).mul_right h3q).mul_right h3r
  have hgcd : 3 ∣ Nat.gcd 3 (p ^ 4 * q * r) := Nat.dvd_gcd (Nat.dvd_refl 3) h3dvd
  rw [hcop] at hgcd
  omega

/-- **Family `(4, 1, 1)`: `p ^ 4 * q * r` exclusion**:
    For primes `5 ≤ p, q, r` with `p ≠ q`, `p ≠ r`, `q < r`, `¬ IsFixedPoint (p ^ 4 * q * r)`. -/
theorem not_isFixedPoint_prime_four_mul_two_primes {p q r : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hr5 : 5 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q < r) :
    ¬ IsFixedPoint (p ^ 4 * q * r) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hr_pos : 0 < r := by omega
  have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq hpq
  have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
  have hcop_qr : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
  have hcop_p4_qr : Nat.Coprime (p ^ 4) (q * r) := (hcop_pq.mul_right hcop_pr).pow_left 4
  have hdom_p : 4 * tau (q * r) < p :=
    sharpened_dominance_bound hp (by decide) (by
      have := Nat.mul_le_mul hq5 hr5; omega) (by rw [Nat.mul_assoc]) hcop_p4_qr hfp
  rw [tau_mul_of_coprime hcop_qr hq_pos hr_pos, tau_of_isPrime hq, tau_of_isPrime hr] at hdom_p
  have hp17 : 17 ≤ p := by omega
  have hcop_q_p4r : Nat.Coprime (q ^ 1) (p ^ 4 * r) := by
    rw [Nat.pow_one]
    exact (hcop_pq.symm.pow_right 4).mul_right hcop_qr
  have hp4r_gt1 : 1 < p ^ 4 * r := by
    have : 17 ≤ p ^ 4 := Nat.le_trans hp17 (Nat.le_self_pow (by decide) p)
    have := Nat.mul_le_mul this hr5
    omega
  have hdom_q : 1 * tau (p ^ 4 * r) < q :=
    sharpened_dominance_bound hq (by decide) hp4r_gt1 (by rw [Nat.pow_one]; grind) hcop_q_p4r hfp
  rw [tau_mul_of_coprime (hcop_pr.pow_left 4) (Nat.pow_pos hp_pos) hr_pos,
    tau_prime_pow hp 4, tau_of_isPrime hr] at hdom_q
  have hq11 : 11 ≤ q := by omega
  have hr13 : 13 ≤ r := by
    by_cases h12 : r = 12
    · exfalso; exact (by decide : ¬ IsPrime 12) (h12 ▸ hr)
    · omega
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  have hmul_assoc : p ^ 4 * q * r = p ^ 4 * (q * r) := by grind
  rw [hmul_assoc, fullMoment_mul_of_coprime hcop_p4_qr, fullMoment_mul_of_coprime hcop_qr,
    fullMoment_prime_pow_four hp, fullMoment_prime hq, fullMoment_prime hr,
    tau_mul_of_coprime hcop_p4_qr (Nat.pow_pos hp_pos) (Nat.mul_pos hq_pos hr_pos),
    tau_mul_of_coprime hcop_qr hq_pos hr_pos,
    tau_prime_pow hp 4, tau_of_isPrime hq, tau_of_isPrime hr] at hS_eq
  have h21 : p ^ 4 * (q * r) * (5 * (2 * 2) + 1) = 21 * p ^ 4 * q * r := by grind
  rw [h21, ← Nat.mul_assoc] at hS_eq
  -- Helper to refute small `q` when `r > q` and `p ≥ 53` or `p = 43`
  have small_q_kill : ∀ (hqr_5 : 5 ≤ p) (hp_gt_47 : 47 < p),
      q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 → False := by
    intro hp5' hp47 hq_cases
    rcases hq_cases with rfl | rfl | rfl | rfl | rfl
    · have h23_dvd : 23 ∣ 21 * p ^ 4 * 11 * r :=
        ⟨(5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * r + 1), by grind⟩
      have h23_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 23) hp hq hr
        (by decide) (by decide) (by omega) h23_dvd
      rcases h23_mem with h11 | rfl
      · omega
      · have h47_dvd : 47 ∣ 21 * p ^ 4 * 11 * 23 :=
          ⟨(5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * 11 + 1), by grind⟩
        exact prime_dvd_21p4qr_impossible (by decide : IsPrime 47) hp hq hr
          (by decide) (by decide) (by omega) (by decide) (by decide) h47_dvd
    · have h9_dvd : 9 ∣ 21 * p ^ 4 * 13 * r :=
        ⟨3 * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * r + 1), by grind⟩
      exact not_nine_dvd_21p4qr hp hq hr hp5' hq5 hr5 h9_dvd
    · have h5_dvd : 5 ∣ 21 * p ^ 4 * 17 * r :=
        ⟨7 * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * r + 1), by grind⟩
      exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
        (by decide) (by decide) (by omega) (by decide) (by omega) h5_dvd
    · have h13_dvd : 13 ∣ 21 * p ^ 4 * 19 * r :=
        ⟨3 * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * r + 1), by grind⟩
      exact prime_dvd_21p4qr_impossible (by decide : IsPrime 13) hp hq hr
        (by decide) (by decide) (by omega) (by decide) (by omega) h13_dvd
    · have h47_dvd : 47 ∣ 21 * p ^ 4 * 23 * r :=
        ⟨(5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * r + 1), by grind⟩
      have h47_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 47) hp hq hr
        (by decide) (by decide) (by omega) h47_dvd
      rcases h47_mem with h23 | rfl
      · omega
      · have h5_dvd : 5 ∣ 21 * p ^ 4 * 23 * 47 :=
          ⟨19 * (5 * p ^ 4 + 4 * p ^ 3 + 3 * p ^ 2 + 2 * p + 1) * (2 * 23 + 1), by grind⟩
        exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
          (by decide) (by decide) (by omega) (by decide) (by decide) h5_dvd
  by_cases hp53 : 53 ≤ p
  · by_cases hq29 : 29 ≤ q
    · have hr31 : 31 ≤ r := by
        by_cases h30 : r = 30
        · exfalso; exact (by decide : ¬ IsPrime 30) (h30 ▸ hr)
        · omega
      have hlt := p4qr_growth_bound p q r hp53 hq29 hr31
      omega
    · exact small_q_kill hp5 (by omega) (prime_11_to_23 hq hq11 (by omega))
  · have hp_cases := prime_17_to_47 hp hp17 (by omega)
    rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- `p = 17`: `S(17^4) = 438159 = 3 * 19 * 7687`, `19 ∣ S(17^4)`
      have h19_dvd : 19 ∣ 21 * 17 ^ 4 * q * r :=
        ⟨23061 * (2 * q + 1) * (2 * r + 1), by grind⟩
      have h19_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 19) hp hq hr
        (by decide) (by decide) (by decide) h19_dvd
      rcases h19_mem with rfl | rfl
      · -- `q = 19`: `2 * 19 + 1 = 39 = 3 * 13` => `13 = r < 19`, contradiction
        have h13_dvd : 13 ∣ 21 * 17 ^ 4 * 19 * r :=
          ⟨3 * 438159 * (2 * r + 1), by grind⟩
        exact prime_dvd_21p4qr_impossible (by decide : IsPrime 13) hp hq hr
          (by decide) (by decide) (by decide) (by decide) (by omega) h13_dvd
      · -- `r = 19`: `11 ≤ q < 19`, so `q ∈ {11, 13, 17}` (and `q ≠ 17`)
        have hq_cases : q = 11 ∨ q = 13 := by
          have hq_lt19 : q < 19 := hqr
          have := prime_11_to_23 hq hq11 (by omega)
          rcases this with rfl | rfl | rfl | rfl | rfl <;> omega
        rcases hq_cases with rfl | rfl
        · revert hS_eq; decide
        · revert hS_eq; decide
    · -- `p = 19`: `S(19^4) = 680163 = 3 * 11 * 20611`, `11 ∣ S(19^4)`, since `11 ≤ q < r`, `q = 11`!
      have h11_dvd : 11 ∣ 21 * 19 ^ 4 * q * r :=
        ⟨61833 * (2 * q + 1) * (2 * r + 1), by grind⟩
      have h11_mem := prime_dvd_21p4qr_mem_qr isPrime_11 hp hq hr
        (by decide) (by decide) (by decide) h11_dvd
      rcases h11_mem with rfl | rfl
      · -- `q = 11`: `2 * 11 + 1 = 23` => `r = 23`
        have h23_dvd : 23 ∣ 21 * 19 ^ 4 * 11 * r :=
          ⟨680163 * (2 * r + 1), by grind⟩
        have h23_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 23) hp hq hr
          (by decide) (by decide) (by decide) h23_dvd
        rcases h23_mem with h11 | rfl
        · omega
        · revert hS_eq; decide
      · omega
    · -- `p = 23`: `S(23^4) = 1449507 = 3 * 29 * 16661`, `29 ∣ S(23^4)`
      have h29_dvd : 29 ∣ 21 * 23 ^ 4 * q * r :=
        ⟨49983 * (2 * q + 1) * (2 * r + 1), by grind⟩
      have h29_mem := prime_dvd_21p4qr_mem_qr isPrime_29 hp hq hr
        (by decide) (by decide) (by decide) h29_dvd
      rcases h29_mem with rfl | rfl
      · -- `q = 29`: `2 * 29 + 1 = 59` => `r = 59`
        have h59_dvd : 59 ∣ 21 * 23 ^ 4 * 29 * r :=
          ⟨1449507 * (2 * r + 1), by grind⟩
        have h59_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 59) hp hq hr
          (by decide) (by decide) (by decide) h59_dvd
        rcases h59_mem with h29 | rfl
        · omega
        · revert hS_eq; decide
      · -- `r = 29`: `11 ≤ q < 29` and `q ≠ 23`, so `q ∈ {11, 13, 17, 19}`
        have hq_cases := prime_11_to_23 hq hq11 hqr
        rcases hq_cases with rfl | rfl | rfl | rfl | rfl
        · revert hS_eq; decide
        · revert hS_eq; decide
        · revert hS_eq; decide
        · revert hS_eq; decide
        · exact absurd rfl hpq
    · -- `p = 29`: `S(29^4) = 3636543 = 3 * 19 * 63799`, `19 ∣ S(29^4)`
      have h19_dvd : 19 ∣ 21 * 29 ^ 4 * q * r :=
        ⟨191397 * (2 * q + 1) * (2 * r + 1), by grind⟩
      have h19_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 19) hp hq hr
        (by decide) (by decide) (by decide) h19_dvd
      rcases h19_mem with rfl | rfl
      · -- `q = 19`: `2 * 19 + 1 = 39` => `13 ∣ RHS`, `13 ∉ {3, 7, 29, 19}` and `13 < 19 < r`
        have h13_dvd : 13 ∣ 21 * 29 ^ 4 * 19 * r :=
          ⟨3 * 3636543 * (2 * r + 1), by grind⟩
        exact prime_dvd_21p4qr_impossible (by decide : IsPrime 13) hp hq hr
          (by decide) (by decide) (by decide) (by decide) (by omega) h13_dvd
      · -- `r = 19`: `11 ≤ q < 19`, so `q ∈ {11, 13, 17}`
        have hq_cases : q = 11 ∨ q = 13 ∨ q = 17 := by
          have := prime_11_to_23 hq hq11 (by omega)
          rcases this with rfl | rfl | rfl | rfl | rfl <;> omega
        rcases hq_cases with rfl | rfl | rfl
        · revert hS_eq; decide
        · revert hS_eq; decide
        · revert hS_eq; decide
    · -- `p = 31`: `S(31^4) = 4739715`, `5 ∣ S(31^4)`
      have h5_dvd : 5 ∣ 21 * 31 ^ 4 * q * r :=
        ⟨947943 * (2 * q + 1) * (2 * r + 1), by grind⟩
      exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
        (by decide) (by decide) (by decide) (by omega) (by omega) h5_dvd
    · -- `p = 37`: `S(37^4) = 9577599 = 3 * 367 * 8699`, `367 ∣ S(37^4)` and `8699 ∣ S(37^4)`
      have h367_dvd : 367 ∣ 21 * 37 ^ 4 * q * r :=
        ⟨26097 * (2 * q + 1) * (2 * r + 1), by grind⟩
      have h367_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 367) hp hq hr
        (by decide) (by decide) (by decide) h367_dvd
      rcases h367_mem with rfl | rfl
      · -- `q = 367`: `2 * 367 + 1 = 735 = 3 * 5 * 7^2`, so `5 ∣ LHS`!
        have h5_dvd : 5 ∣ 21 * 37 ^ 4 * 367 * r :=
          ⟨147 * 9577599 * (2 * r + 1), by grind⟩
        exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
          (by decide) (by decide) (by decide) (by decide) (by omega) h5_dvd
      · -- `r = 367`: `2 * 367 + 1 = 735 = 3 * 5 * 7^2`, so `5 ∣ LHS`!
        have h5_dvd : 5 ∣ 21 * 37 ^ 4 * q * 367 :=
          ⟨147 * 9577599 * (2 * q + 1), by grind⟩
        exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
          (by decide) (by decide) (by decide) (by omega) (by decide) h5_dvd
    · -- `p = 41`: `S(41^4) = 14409615`, `5 ∣ S(41^4)`
      have h5_dvd : 5 ∣ 21 * 41 ^ 4 * q * r :=
        ⟨2881923 * (2 * q + 1) * (2 * r + 1), by grind⟩
      exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
        (by decide) (by decide) (by decide) (by omega) (by omega) h5_dvd
    · -- `p = 43`: `S(43^4) = 17417667`
      by_cases hq31 : 31 ≤ q
      · have hr37 : 37 ≤ r := by
          by_cases h32 : r = 32; · exfalso; exact (by decide : ¬ IsPrime 32) (h32 ▸ hr)
          by_cases h33 : r = 33; · exfalso; exact (by decide : ¬ IsPrime 33) (h33 ▸ hr)
          by_cases h34 : r = 34; · exfalso; exact (by decide : ¬ IsPrime 34) (h34 ▸ hr)
          by_cases h35 : r = 35; · exfalso; exact (by decide : ¬ IsPrime 35) (h35 ▸ hr)
          by_cases h36 : r = 36; · exfalso; exact (by decide : ¬ IsPrime 36) (h36 ▸ hr)
          omega
        have h1 : 31 * (2 * q + 1) ≤ 63 * q := by omega
        have h2 : 37 * (2 * r + 1) ≤ 75 * r := by omega
        have h12 := Nat.mul_le_mul h1 h2
        have hA : 1147 * (17417667 * (2 * q + 1) * (2 * r + 1)) =
            17417667 * ((31 * (2 * q + 1)) * (37 * (2 * r + 1))) := by grind
        have hB : 17417667 * 4725 * (q * r) = 17417667 * ((63 * q) * (75 * r)) := by grind
        have hmul := Nat.mul_le_mul_left 17417667 h12
        rw [← hA, ← hB] at hmul
        have hrhs : 17417667 * 4725 * (q * r) < 1147 * (21 * 43 ^ 4 * q * r) := by
          have hC : 1147 * (21 * 43 ^ 4 * q * r) = 82301500767 * (q * r) := by grind
          have hD : 17417667 * 4725 * (q * r) = 82298476575 * (q * r) := by grind
          rw [hC, hD]
          exact Nat.mul_lt_mul_of_pos_right (by decide) (Nat.mul_pos hq_pos hr_pos)
        have hlt := Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hmul hrhs)
        have hS43 : 5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1 = 17417667 := by decide
        rw [hS43] at hS_eq
        omega
      · have hq_cases := prime_11_to_29 hq hq11 (by omega)
        rcases hq_cases with rfl | rfl | rfl | rfl | rfl | rfl
        · -- `q = 11`: `23 ∣ 23`, and `23 ∉ {3, 7, 43}`, so `r = 23`
          have h23_dvd : 23 ∣ 21 * 43 ^ 4 * 11 * r :=
            ⟨(5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1) * (2 * r + 1), by grind⟩
          have h23_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 23) hp hq hr
            (by decide) (by decide) (by decide) h23_dvd
          rcases h23_mem with h11 | rfl
          · omega
          · revert hS_eq; decide
        · -- `q = 13`: `9 ∣ 27`
          have h9_dvd : 9 ∣ 21 * 43 ^ 4 * 13 * r :=
            ⟨3 * (5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1) * (2 * r + 1), by grind⟩
          exact not_nine_dvd_21p4qr hp hq hr hp5 hq5 hr5 h9_dvd
        · -- `q = 17`: `5 ∣ 35`
          have h5_dvd : 5 ∣ 21 * 43 ^ 4 * 17 * r :=
            ⟨7 * (5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1) * (2 * r + 1), by grind⟩
          exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
            (by decide) (by decide) (by decide) (by decide) (by omega) h5_dvd
        · -- `q = 19`: `13 ∣ 39`
          have h13_dvd : 13 ∣ 21 * 43 ^ 4 * 19 * r :=
            ⟨3 * (5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1) * (2 * r + 1), by grind⟩
          exact prime_dvd_21p4qr_impossible (by decide : IsPrime 13) hp hq hr
            (by decide) (by decide) (by decide) (by decide) (by omega) h13_dvd
        · -- `q = 23`: `47 ∣ 47`, `47 ≠ 43`, so `r = 47`, then `5 ∣ 95`
          have h47_dvd : 47 ∣ 21 * 43 ^ 4 * 23 * r :=
            ⟨(5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1) * (2 * r + 1), by grind⟩
          have h47_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 47) hp hq hr
            (by decide) (by decide) (by decide) h47_dvd
          rcases h47_mem with h23 | rfl
          · omega
          · have h5_dvd : 5 ∣ 21 * 43 ^ 4 * 23 * 47 :=
              ⟨19 * (5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1) * (2 * 23 + 1), by grind⟩
            exact prime_dvd_21p4qr_impossible isPrime_5 hp hq hr
              (by decide) (by decide) (by decide) (by decide) (by decide) h5_dvd
        · -- `q = 29`: `59 ∣ 59`, `59 ≠ 43`, so `r = 59`
          have h59_dvd : 59 ∣ 21 * 43 ^ 4 * 29 * r :=
            ⟨(5 * 43 ^ 4 + 4 * 43 ^ 3 + 3 * 43 ^ 2 + 2 * 43 + 1) * (2 * r + 1), by grind⟩
          have h59_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 59) hp hq hr
            (by decide) (by decide) (by decide) h59_dvd
          rcases h59_mem with h29 | rfl
          · omega
          · revert hS_eq; decide
    · -- `p = 47`: `S(47^4) = 24820419 = 3 * 13 * 636421`, `13 ∣ S(47^4)` and `13 < 47`, since `11 ≤ q < r`:
      -- either `q = 13` (`9 ∣ LHS`, impossible) or `q = 11` and `r = 13` (`decide`)
      have h13_dvd : 13 ∣ 21 * 47 ^ 4 * q * r :=
        ⟨1909263 * (2 * q + 1) * (2 * r + 1), by grind⟩
      have h13_mem := prime_dvd_21p4qr_mem_qr (by decide : IsPrime 13) hp hq hr
        (by decide) (by decide) (by decide) h13_dvd
      rcases h13_mem with rfl | rfl
      · have h9_dvd : 9 ∣ 21 * 47 ^ 4 * 13 * r :=
          ⟨3 * (5 * 47 ^ 4 + 4 * 47 ^ 3 + 3 * 47 ^ 2 + 2 * 47 + 1) * (2 * r + 1), by grind⟩
        exact not_nine_dvd_21p4qr hp hq hr hp5 hq5 hr5 h9_dvd
      · have hq11' : q = 11 := by
          have := prime_11_to_23 hq hq11 (by omega)
          rcases this with rfl | rfl | rfl | rfl | rfl <;> omega
        subst hq11'
        revert hS_eq; decide

end OmegaSixNonSquarefree

/-! ## Section 4: Non-Squarefree $\Omega(n) = 6$ Reduction -/

section OmegaSixReduction

/-- **Exclusion of all non-squarefree $\Omega(n) = 6$ families**:
    Every fixed point with `omegaBig n = 6` must be squarefree of the form
    `p * q * r * s * t * u` with `37 ≤ p < q < r < s < t < u`. -/
theorem omegaSix_must_be_squarefree_ge_37 {n : Nat}
    (hfp : IsFixedPoint n) (ho6 : omegaBig n = 6) :
    ∃ p q r s t u : Nat,
      IsPrime p ∧ IsPrime q ∧ IsPrime r ∧ IsPrime s ∧ IsPrime t ∧ IsPrime u ∧
        37 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧ s < t ∧ t < u ∧ n = p * q * r * s * t * u := by
  have h21 : n ≠ 21 := by
    rintro rfl
    have h21_omega : omegaBig 21 = 2 := by
      have hmul21 : (21 : Nat) = 3 * 7 := rfl
      rw [hmul21, omegaBig_prime_mul isPrime_3 (by decide), omegaBig_of_isPrime isPrime_7]
    omega
  have hgcd : Nat.gcd n 6 = 1 := gcd_six_eq_one_of_isFixedPoint_ne_21 hfp h21
  obtain ⟨ps, hlen, hprime, hsorted, hn_eq⟩ := exists_primes_of_omegaBig 6 n hfp.1 ho6
  rcases ps with _ | ⟨p, _ | ⟨q, _ | ⟨r, _ | ⟨s, _ | ⟨t, _ | ⟨u, _ | _⟩⟩⟩⟩⟩⟩ <;> try (simp at hlen)
  simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul] at hn_eq
  have hp := hprime p (by simp)
  have hq := hprime q (by simp)
  have hr := hprime r (by simp)
  have hs := hprime s (by simp)
  have ht := hprime t (by simp)
  have hu := hprime u (by simp)
  have hpq : p ≤ q := (List.pairwise_cons.mp hsorted).1 q (by simp)
  have hqr : q ≤ r := (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 r (by simp)
  have hrs : r ≤ s :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).2).1 s (by simp)
  have hst : s ≤ t :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp
      (List.pairwise_cons.mp hsorted).2).2).2).1 t (by simp)
  have htu : t ≤ u :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp
      (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).2).2).2).1 u (by simp)
  have hp5 : 5 ≤ p :=
    five_le_prime_of_dvd_coprime_six hgcd hp (by rw [hn_eq]; exact ⟨q * r * s * t * u, by grind⟩)
  have hq5 : 5 ≤ q := by omega
  have hr5 : 5 ≤ r := by omega
  have hs5 : 5 ≤ s := by omega
  have ht5 : 5 ≤ t := by omega
  have hu5 : 5 ≤ u := by omega
  -- Helper lemmas for parity exclusion of exponent 2 or 3 when tau(m) is even (or arbitrary m for e=3):
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
      have hcop_am : Nat.Coprime a m :=
        Nat.Coprime.coprime_dvd_left ⟨a, by rw [Nat.pow_two]⟩ hcop
      have hgcd_dvd : a ∣ Nat.gcd a m := Nat.dvd_gcd (Nat.dvd_refl a) ha_m
      rw [hcop_am] at hgcd_dvd
      have ha1 : a = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
      have := ha.1; omega
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
      have hcop_am : Nat.Coprime a m :=
        Nat.Coprime.coprime_dvd_left ⟨a ^ 2, by grind⟩ hcop
      have hgcd_dvd : a ∣ Nat.gcd a m := Nat.dvd_gcd (Nat.dvd_refl a) ha_m
      rw [hcop_am] at hgcd_dvd
      have ha1 : a = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
      have := ha.1; omega
    exact not_isFixedPoint_of_exact_exponent_mod_four_ge_two htau ha hdvd hndvd (Or.inr rfl) hfp'
  -- Eliminate all equalities among `p ≤ q ≤ r ≤ s ≤ t ≤ u`:
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
            by_cases hpu : p = u
            · subst hpu
              rw [hn_eq] at hfp
              have hpow : p * p * p * p * p * p = p ^ 6 := by grind
              rw [hpow] at hfp
              exact not_isFixedPoint_prime_pow hp (by decide) hfp
            · rw [hn_eq] at hfp
              have hpow : p * p * p * p * p * u = p ^ 5 * u := by grind
              rw [hpow] at hfp
              exact not_isFixedPoint_prime_five_mul_prime hp hu hp5 hu5 hpu hfp
          · by_cases htu' : t = u
            · subst htu'
              rw [hn_eq] at hfp
              have hpow : p * p * p * p * t * t = p ^ 4 * t ^ 2 := by grind
              rw [hpow] at hfp
              exact not_isFixedPoint_prime_four_mul_prime_sq hp ht hp5 ht5 hpt hfp
            · rw [hn_eq] at hfp
              have hpow : p * p * p * p * t * u = p ^ 4 * t * u := by grind
              rw [hpow] at hfp
              exact not_isFixedPoint_prime_four_mul_two_primes hp ht hu hp5 ht5 hu5 hpt (by omega) htu' hfp
        · rw [hn_eq] at hfp
          have hpow : p * p * p * s * t * u = p ^ 3 * (s * t * u) := by grind
          rw [hpow] at hfp
          have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs hps
          have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
          have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
          exact ex_parity3 p (s * t * u) hp (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
            (((hcop_ps.mul_right hcop_pt).mul_right hcop_pu).pow_left 3) hfp
      · by_cases hrs' : r = s
        · subst hrs'
          by_cases hrt : r = t
          · subst hrt
            rw [hn_eq] at hfp
            have hpow : p * p * r * r * r * u = r ^ 3 * (p * p * u) := by grind
            rw [hpow] at hfp
            have hcop_rp : Nat.Coprime r p := coprime_primes_ne hr hp (Ne.symm hpr)
            have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
            exact ex_parity3 r (p * p * u) hr (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
              (((hcop_rp.mul_right hcop_rp).mul_right hcop_ru).pow_left 3) hfp
          · by_cases htu' : t = u
            · subst htu'
              rw [hn_eq] at hfp
              have hpow : p * p * r * r * t * t = p ^ 2 * r ^ 2 * t ^ 2 := by grind
              rw [hpow] at hfp
              exact not_isFixedPoint_three_prime_sq hp hr ht hp5 hr5 ht5 hpr (by omega) hrt hfp
            · rw [hn_eq] at hfp
              have hpow : p * p * r * r * t * u = p ^ 2 * (r ^ 2 * t * u) := by grind
              rw [hpow] at hfp
              have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
              have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
              have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
              have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht hrt
              have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
              have hcop_tu : Nat.Coprime t u := coprime_primes_ne ht hu htu'
              have htm : tau (r ^ 2 * t * u) % 2 = 0 := by
                have hr2t_cop : Nat.Coprime (r ^ 2 * t) u := (hcop_ru.pow_left 2).mul_left hcop_tu
                have hr2_cop : Nat.Coprime (r ^ 2) t := hcop_rt.pow_left 2
                rw [tau_mul_of_coprime hr2t_cop (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) (by omega),
                  tau_mul_of_coprime hr2_cop (Nat.pow_pos (by omega)) (by omega),
                  tau_prime_pow hr 2, tau_of_isPrime ht, tau_of_isPrime hu]
              exact ex_parity2 p (r ^ 2 * t * u) hp
                (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)) (by omega))
                ((((hcop_pr.pow_right 2).mul_right hcop_pt).mul_right hcop_pu).pow_left 2) htm hfp
        · by_cases hst' : s = t
          · subst hst'
            by_cases hsu : s = u
            · subst hsu
              rw [hn_eq] at hfp
              have hpow : p * p * r * s * s * s = s ^ 3 * (p * p * r) := by grind
              rw [hpow] at hfp
              have hcop_sp : Nat.Coprime s p := coprime_primes_ne hs hp (by omega)
              have hcop_sr : Nat.Coprime s r := coprime_primes_ne hs hr (Ne.symm hrs')
              exact ex_parity3 s (p * p * r) hs (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
                (((hcop_sp.mul_right hcop_sp).mul_right hcop_sr).pow_left 3) hfp
            · rw [hn_eq] at hfp
              have hpow : p * p * r * s * s * u = p ^ 2 * (r * s ^ 2 * u) := by grind
              rw [hpow] at hfp
              have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
              have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
              have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
              have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs hrs'
              have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
              have hcop_su : Nat.Coprime s u := coprime_primes_ne hs hu hsu
              have htm : tau (r * s ^ 2 * u) % 2 = 0 := by
                have hrs2_cop : Nat.Coprime (r * s ^ 2) u := hcop_ru.mul_left (hcop_su.pow_left 2)
                rw [tau_mul_of_coprime hrs2_cop (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) (by omega),
                  tau_mul_of_coprime (hcop_rs.pow_right 2) (by omega) (Nat.pow_pos (by omega)),
                  tau_of_isPrime hr, tau_prime_pow hs 2, tau_of_isPrime hu]
              exact ex_parity2 p (r * s ^ 2 * u) hp
                (Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) (by omega))
                (((hcop_pr.mul_right (hcop_ps.pow_right 2)).mul_right hcop_pu).pow_left 2) htm hfp
          · by_cases htu' : t = u
            · subst htu'
              rw [hn_eq] at hfp
              have hpow : p * p * r * s * t * t = p ^ 2 * (r * s * t ^ 2) := by grind
              rw [hpow] at hfp
              have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
              have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
              have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
              have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs hrs'
              have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht (by omega)
              have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht hst'
              have htm : tau (r * s * t ^ 2) % 2 = 0 := by
                have hrs_t2 : Nat.Coprime (r * s) (t ^ 2) := (hcop_rt.mul_left hcop_st).pow_right 2
                rw [tau_mul_of_coprime hrs_t2 (Nat.mul_pos (by omega) (by omega)) (Nat.pow_pos (by omega)),
                  tau_mul_of_coprime hcop_rs (by omega) (by omega),
                  tau_of_isPrime hr, tau_of_isPrime hs, tau_prime_pow ht 2]
              exact ex_parity2 p (r * s * t ^ 2) hp
                (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.pow_pos (by omega)))
                (((hcop_pr.mul_right hcop_ps).mul_right (hcop_pt.pow_right 2)).pow_left 2) htm hfp
            · rw [hn_eq] at hfp
              have hpow : p * p * r * s * t * u = p ^ 2 * (r * s * t * u) := by grind
              rw [hpow] at hfp
              have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr hpr
              have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
              have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
              have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
              have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs hrs'
              have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht (by omega)
              have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
              have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht hst'
              have hcop_su : Nat.Coprime s u := coprime_primes_ne hs hu (by omega)
              have hcop_tu : Nat.Coprime t u := coprime_primes_ne ht hu htu'
              have htm : tau (r * s * t * u) % 2 = 0 := by
                have hrst_u : Nat.Coprime (r * s * t) u := (hcop_ru.mul_left hcop_su).mul_left hcop_tu
                have hrs_t : Nat.Coprime (r * s) t := hcop_rt.mul_left hcop_st
                rw [tau_mul_of_coprime hrst_u (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega),
                  tau_mul_of_coprime hrs_t (Nat.mul_pos (by omega) (by omega)) (by omega),
                  tau_mul_of_coprime hcop_rs (by omega) (by omega),
                  tau_of_isPrime hr, tau_of_isPrime hs, tau_of_isPrime ht, tau_of_isPrime hu]
              exact ex_parity2 p (r * s * t * u) hp
                (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
                ((((hcop_pr.mul_right hcop_ps).mul_right hcop_pt).mul_right hcop_pu).pow_left 2) htm hfp
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
          by_cases hqu : q = u
          · subst hqu
            rw [hn_eq] at hfp
            have hpow : p * q * q * q * q * q = q ^ 5 * p := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_five_mul_prime hq hp hq5 hp5 (Ne.symm (by omega)) hfp
          · rw [hn_eq] at hfp
            have hpow : p * q * q * q * q * u = q ^ 4 * p * u := by grind
            rw [hpow] at hfp
            exact not_isFixedPoint_prime_four_mul_two_primes hq hp hu hq5 hp5 hu5 (Ne.symm (by omega)) hqu (by omega) hfp
        · rw [hn_eq] at hfp
          have hpow : p * q * q * q * t * u = q ^ 3 * (p * t * u) := by grind
          rw [hpow] at hfp
          have hcop_qp : Nat.Coprime q p := coprime_primes_ne hq hp (by omega)
          have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht hqt
          have hcop_qu : Nat.Coprime q u := coprime_primes_ne hq hu (by omega)
          exact ex_parity3 q (p * t * u) hq (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
            (((hcop_qp.mul_right hcop_qt).mul_right hcop_qu).pow_left 3) hfp
      · by_cases hst' : s = t
        · subst hst'
          by_cases hsu : s = u
          · subst hsu
            rw [hn_eq] at hfp
            have hpow : p * q * q * s * s * s = s ^ 3 * (p * q * q) := by grind
            rw [hpow] at hfp
            have hcop_sp : Nat.Coprime s p := coprime_primes_ne hs hp (by omega)
            have hcop_sq : Nat.Coprime s q := coprime_primes_ne hs hq (Ne.symm hqs)
            exact ex_parity3 s (p * q * q) hs (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
              (((hcop_sp.mul_right hcop_sq).mul_right hcop_sq).pow_left 3) hfp
          · rw [hn_eq] at hfp
            have hpow : p * q * q * s * s * u = q ^ 2 * (p * s ^ 2 * u) := by grind
            rw [hpow] at hfp
            have hcop_qp : Nat.Coprime q p := coprime_primes_ne hq hp (by omega)
            have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs hqs
            have hcop_qu : Nat.Coprime q u := coprime_primes_ne hq hu (by omega)
            have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
            have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
            have hcop_su : Nat.Coprime s u := coprime_primes_ne hs hu hsu
            have htm : tau (p * s ^ 2 * u) % 2 = 0 := by
              have hps2_u : Nat.Coprime (p * s ^ 2) u := hcop_pu.mul_left (hcop_su.pow_left 2)
              rw [tau_mul_of_coprime hps2_u (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) (by omega),
                tau_mul_of_coprime (hcop_ps.pow_right 2) (by omega) (Nat.pow_pos (by omega)),
                tau_of_isPrime hp, tau_prime_pow hs 2, tau_of_isPrime hu]
            exact ex_parity2 q (p * s ^ 2 * u) hq
              (Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) (by omega))
              (((hcop_qp.mul_right (hcop_qs.pow_right 2)).mul_right hcop_qu).pow_left 2) htm hfp
        · by_cases htu' : t = u
          · subst htu'
            rw [hn_eq] at hfp
            have hpow : p * q * q * s * t * t = q ^ 2 * (p * s * t ^ 2) := by grind
            rw [hpow] at hfp
            have hcop_qp : Nat.Coprime q p := coprime_primes_ne hq hp (by omega)
            have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs hqs
            have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
            have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
            have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
            have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht hst'
            have htm : tau (p * s * t ^ 2) % 2 = 0 := by
              have hps_t2 : Nat.Coprime (p * s) (t ^ 2) := (hcop_pt.mul_left hcop_st).pow_right 2
              rw [tau_mul_of_coprime hps_t2 (Nat.mul_pos (by omega) (by omega)) (Nat.pow_pos (by omega)),
                tau_mul_of_coprime hcop_ps (by omega) (by omega),
                tau_of_isPrime hp, tau_of_isPrime hs, tau_prime_pow ht 2]
            exact ex_parity2 q (p * s * t ^ 2) hq
              (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.pow_pos (by omega)))
              (((hcop_qp.mul_right hcop_qs).mul_right (hcop_qt.pow_right 2)).pow_left 2) htm hfp
          · rw [hn_eq] at hfp
            have hpow : p * q * q * s * t * u = q ^ 2 * (p * s * t * u) := by grind
            rw [hpow] at hfp
            have hcop_qp : Nat.Coprime q p := coprime_primes_ne hq hp (by omega)
            have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs hqs
            have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
            have hcop_qu : Nat.Coprime q u := coprime_primes_ne hq hu (by omega)
            have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
            have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
            have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
            have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht hst'
            have hcop_su : Nat.Coprime s u := coprime_primes_ne hs hu (by omega)
            have hcop_tu : Nat.Coprime t u := coprime_primes_ne ht hu htu'
            have htm : tau (p * s * t * u) % 2 = 0 := by
              have hpst_u : Nat.Coprime (p * s * t) u := (hcop_pu.mul_left hcop_su).mul_left hcop_tu
              have hps_t : Nat.Coprime (p * s) t := hcop_pt.mul_left hcop_st
              rw [tau_mul_of_coprime hpst_u (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega),
                tau_mul_of_coprime hps_t (Nat.mul_pos (by omega) (by omega)) (by omega),
                tau_mul_of_coprime hcop_ps (by omega) (by omega),
                tau_of_isPrime hp, tau_of_isPrime hs, tau_of_isPrime ht, tau_of_isPrime hu]
            exact ex_parity2 q (p * s * t * u) hq
              (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
              ((((hcop_qp.mul_right hcop_qs).mul_right hcop_qt).mul_right hcop_qu).pow_left 2) htm hfp
  have hrs_lt : r < s := by
    by_cases hlt : r < s
    · exact hlt
    · exfalso
      have heq : r = s := by omega
      subst heq
      by_cases hrt : r = t
      · subst hrt
        by_cases hru : r = u
        · subst hru
          rw [hn_eq] at hfp
          have hpow : p * q * r * r * r * r = r ^ 4 * p * q := by grind
          rw [hpow] at hfp
          exact not_isFixedPoint_prime_four_mul_two_primes hr hp hq hr5 hp5 hq5 (by omega) (by omega) hpq_lt hfp
        · rw [hn_eq] at hfp
          have hpow : p * q * r * r * r * u = r ^ 3 * (p * q * u) := by grind
          rw [hpow] at hfp
          have hcop_rp : Nat.Coprime r p := coprime_primes_ne hr hp (by omega)
          have hcop_rq : Nat.Coprime r q := coprime_primes_ne hr hq (by omega)
          have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu hru
          exact ex_parity3 r (p * q * u) hr (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
            (((hcop_rp.mul_right hcop_rq).mul_right hcop_ru).pow_left 3) hfp
      · by_cases htu' : t = u
        · subst htu'
          rw [hn_eq] at hfp
          have hpow : p * q * r * r * t * t = r ^ 2 * (p * q * t ^ 2) := by grind
          rw [hpow] at hfp
          have hcop_rp : Nat.Coprime r p := coprime_primes_ne hr hp (by omega)
          have hcop_rq : Nat.Coprime r q := coprime_primes_ne hr hq (by omega)
          have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht hrt
          have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
          have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
          have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
          have htm : tau (p * q * t ^ 2) % 2 = 0 := by
            have hpq_t2 : Nat.Coprime (p * q) (t ^ 2) := (hcop_pt.mul_left hcop_qt).pow_right 2
            rw [tau_mul_of_coprime hpq_t2 (Nat.mul_pos (by omega) (by omega)) (Nat.pow_pos (by omega)),
              tau_mul_of_coprime hcop_pq (by omega) (by omega),
              tau_of_isPrime hp, tau_of_isPrime hq, tau_prime_pow ht 2]
          exact ex_parity2 r (p * q * t ^ 2) hr
            (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.pow_pos (by omega)))
            (((hcop_rp.mul_right hcop_rq).mul_right (hcop_rt.pow_right 2)).pow_left 2) htm hfp
        · rw [hn_eq] at hfp
          have hpow : p * q * r * r * t * u = r ^ 2 * (p * q * t * u) := by grind
          rw [hpow] at hfp
          have hcop_rp : Nat.Coprime r p := coprime_primes_ne hr hp (by omega)
          have hcop_rq : Nat.Coprime r q := coprime_primes_ne hr hq (by omega)
          have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht hrt
          have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
          have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
          have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
          have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
          have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
          have hcop_qu : Nat.Coprime q u := coprime_primes_ne hq hu (by omega)
          have hcop_tu : Nat.Coprime t u := coprime_primes_ne ht hu htu'
          have htm : tau (p * q * t * u) % 2 = 0 := by
            have hpqt_u : Nat.Coprime (p * q * t) u := (hcop_pu.mul_left hcop_qu).mul_left hcop_tu
            have hpq_t : Nat.Coprime (p * q) t := hcop_pt.mul_left hcop_qt
            rw [tau_mul_of_coprime hpqt_u (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega),
              tau_mul_of_coprime hpq_t (Nat.mul_pos (by omega) (by omega)) (by omega),
              tau_mul_of_coprime hcop_pq (by omega) (by omega),
              tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime ht, tau_of_isPrime hu]
          exact ex_parity2 r (p * q * t * u) hr
            (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
            ((((hcop_rp.mul_right hcop_rq).mul_right hcop_rt).mul_right hcop_ru).pow_left 2) htm hfp
  have hst_lt : s < t := by
    by_cases hlt : s < t
    · exact hlt
    · exfalso
      have heq : s = t := by omega
      subst heq
      by_cases hsu : s = u
      · subst hsu
        rw [hn_eq] at hfp
        have hpow : p * q * r * s * s * s = s ^ 3 * (p * q * r) := by grind
        rw [hpow] at hfp
        have hcop_sp : Nat.Coprime s p := coprime_primes_ne hs hp (by omega)
        have hcop_sq : Nat.Coprime s q := coprime_primes_ne hs hq (by omega)
        have hcop_sr : Nat.Coprime s r := coprime_primes_ne hs hr (by omega)
        exact ex_parity3 s (p * q * r) hs (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
          (((hcop_sp.mul_right hcop_sq).mul_right hcop_sr).pow_left 3) hfp
      · rw [hn_eq] at hfp
        have hpow : p * q * r * s * s * u = s ^ 2 * (p * q * r * u) := by grind
        rw [hpow] at hfp
        have hcop_sp : Nat.Coprime s p := coprime_primes_ne hs hp (by omega)
        have hcop_sq : Nat.Coprime s q := coprime_primes_ne hs hq (by omega)
        have hcop_sr : Nat.Coprime s r := coprime_primes_ne hs hr (by omega)
        have hcop_su : Nat.Coprime s u := coprime_primes_ne hs hu hsu
        have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
        have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
        have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
        have hcop_qr : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
        have hcop_qu : Nat.Coprime q u := coprime_primes_ne hq hu (by omega)
        have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
        have htm : tau (p * q * r * u) % 2 = 0 := by
          have hpqr_u : Nat.Coprime (p * q * r) u := (hcop_pu.mul_left hcop_qu).mul_left hcop_ru
          have hpq_r : Nat.Coprime (p * q) r := hcop_pr.mul_left hcop_qr
          rw [tau_mul_of_coprime hpqr_u (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega),
            tau_mul_of_coprime hpq_r (Nat.mul_pos (by omega) (by omega)) (by omega),
            tau_mul_of_coprime hcop_pq (by omega) (by omega),
            tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime hr, tau_of_isPrime hu]
        exact ex_parity2 s (p * q * r * u) hs
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
          ((((hcop_sp.mul_right hcop_sq).mul_right hcop_sr).mul_right hcop_su).pow_left 2) htm hfp
  have htu_lt : t < u := by
    by_cases hlt : t < u
    · exact hlt
    · exfalso
      have heq : t = u := by omega
      subst heq
      rw [hn_eq] at hfp
      have hpow : p * q * r * s * t * t = t ^ 2 * (p * q * r * s) := by grind
      rw [hpow] at hfp
      have hcop_tp : Nat.Coprime t p := coprime_primes_ne ht hp (by omega)
      have hcop_tq : Nat.Coprime t q := coprime_primes_ne ht hq (by omega)
      have hcop_tr : Nat.Coprime t r := coprime_primes_ne ht hr (by omega)
      have hcop_ts : Nat.Coprime t s := coprime_primes_ne ht hs (by omega)
      have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
      have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
      have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
      have hcop_qr : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
      have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs (by omega)
      have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs (by omega)
      have htm : tau (p * q * r * s) % 2 = 0 := by
        have hpqr_s : Nat.Coprime (p * q * r) s := (hcop_ps.mul_left hcop_qs).mul_left hcop_rs
        have hpq_r : Nat.Coprime (p * q) r := hcop_pr.mul_left hcop_qr
        rw [tau_mul_of_coprime hpqr_s (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega),
          tau_mul_of_coprime hpq_r (Nat.mul_pos (by omega) (by omega)) (by omega),
          tau_mul_of_coprime hcop_pq (by omega) (by omega),
          tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime hr, tau_of_isPrime hs]
      exact ex_parity2 t (p * q * r * s) ht
        (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
        ((((hcop_tp.mul_right hcop_tq).mul_right hcop_tr).mul_right hcop_ts).pow_left 2) htm hfp
  -- Now `p < q < r < s < t < u`, so `tau(q * r * s * t * u) = 32`, giving `37 ≤ p`!
  have hcop_pq : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
  have hcop_pr : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
  have hcop_ps : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
  have hcop_pt : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
  have hcop_pu : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
  have hcop_qr : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
  have hcop_qs : Nat.Coprime q s := coprime_primes_ne hq hs (by omega)
  have hcop_qt : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
  have hcop_qu : Nat.Coprime q u := coprime_primes_ne hq hu (by omega)
  have hcop_rs : Nat.Coprime r s := coprime_primes_ne hr hs (by omega)
  have hcop_rt : Nat.Coprime r t := coprime_primes_ne hr ht (by omega)
  have hcop_ru : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
  have hcop_st : Nat.Coprime s t := coprime_primes_ne hs ht (by omega)
  have hcop_su : Nat.Coprime s u := coprime_primes_ne hs hu (by omega)
  have hcop_tu : Nat.Coprime t u := coprime_primes_ne ht hu (by omega)
  have hcop_p_qrstu : Nat.Coprime (p ^ 1) (q * r * s * t * u) := by
    rw [Nat.pow_one]
    exact (((hcop_pq.mul_right hcop_pr).mul_right hcop_ps).mul_right hcop_pt).mul_right hcop_pu
  have hqrstu_gt1 : 1 < q * r * s * t * u := by
    have hqr_ge : 5 * 5 ≤ q * r := Nat.mul_le_mul hq5 hr5
    have hqrs_ge : 25 * 5 ≤ q * r * s := Nat.mul_le_mul hqr_ge hs5
    have hqrst_ge : 125 * 5 ≤ q * r * s * t := Nat.mul_le_mul hqrs_ge ht5
    have hqrstu_ge : 625 * 5 ≤ q * r * s * t * u := Nat.mul_le_mul hqrst_ge hu5
    omega
  have hdom := sharpened_dominance_bound hp (by decide) hqrstu_gt1
    (by rw [Nat.pow_one, hn_eq]; grind) hcop_p_qrstu hfp
  have htau_qrstu : tau (q * r * s * t * u) = 32 := by
    have hcop_qrst_u : Nat.Coprime (q * r * s * t) u :=
      ((hcop_qu.mul_left hcop_ru).mul_left hcop_su).mul_left hcop_tu
    have hcop_qrs_t : Nat.Coprime (q * r * s) t := (hcop_qt.mul_left hcop_rt).mul_left hcop_st
    have hcop_qr_s : Nat.Coprime (q * r) s := hcop_qs.mul_left hcop_rs
    have hqr_pos : 0 < q * r := Nat.mul_pos (by omega) (by omega)
    have hqrs_pos : 0 < q * r * s := Nat.mul_pos hqr_pos (by omega)
    have hqrst_pos : 0 < q * r * s * t := Nat.mul_pos hqrs_pos (by omega)
    rw [tau_mul_of_coprime hcop_qrst_u hqrst_pos (by omega),
      tau_mul_of_coprime hcop_qrs_t hqrs_pos (by omega),
      tau_mul_of_coprime hcop_qr_s hqr_pos (by omega),
      tau_mul_of_coprime hcop_qr (by omega) (by omega),
      tau_of_isPrime hq, tau_of_isPrime hr, tau_of_isPrime hs, tau_of_isPrime ht, tau_of_isPrime hu]
  rw [htau_qrstu, Nat.one_mul] at hdom
  have hp37 : 37 ≤ p := by
    by_cases h33 : p = 33; · exfalso; exact (by decide : ¬ IsPrime 33) (h33 ▸ hp)
    by_cases h34 : p = 34; · exfalso; exact (by decide : ¬ IsPrime 34) (h34 ▸ hp)
    by_cases h35 : p = 35; · exfalso; exact (by decide : ¬ IsPrime 35) (h35 ▸ hp)
    by_cases h36 : p = 36; · exfalso; exact (by decide : ¬ IsPrime 36) (h36 ▸ hp)
    omega
  exact ⟨p, q, r, s, t, u, hp, hq, hr, hs, ht, hu, hp37, hpq_lt, hqr_lt, hrs_lt, hst_lt, htu_lt, hn_eq⟩

end OmegaSixReduction

/-! ## Section 5: Squarefree Six-Prime Exclusion and $\Omega(n) \le 6$ Classification -/

section OmegaSixClosure

/-- **Growth bound for six distinct primes `181 ≤ p < q < r < s < t < u`**:
    `(2*p+1)*(2*q+1)*(2*r+1)*(2*s+1)*(2*t+1)*(2*u+1) < 65 * p * q * r * s * t * u`. -/
theorem six_prime_growth_bound (p q r s t u : Nat)
    (hp : 181 ≤ p) (hq : 191 ≤ q) (hr : 193 ≤ r) (hs : 197 ≤ s) (ht : 199 ≤ t) (hu : 211 ≤ u) :
    (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1) <
      65 * p * q * r * s * t * u := by
  have h1 : 181 * (2 * p + 1) ≤ 363 * p := by omega
  have h2 : 191 * (2 * q + 1) ≤ 383 * q := by omega
  have h3 : 193 * (2 * r + 1) ≤ 387 * r := by omega
  have h4 : 197 * (2 * s + 1) ≤ 395 * s := by omega
  have h5 : 199 * (2 * t + 1) ≤ 399 * t := by omega
  have h6 : 211 * (2 * u + 1) ≤ 423 * u := by omega
  have h12 := Nat.mul_le_mul h1 h2
  have h34 := Nat.mul_le_mul h3 h4
  have h56 := Nat.mul_le_mul h5 h6
  have h1234 := Nat.mul_le_mul h12 h34
  have h123456 := Nat.mul_le_mul h1234 h56
  have hA : 55191348958099 * ((2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1)) =
      (((181 * (2 * p + 1)) * (191 * (2 * q + 1))) * ((193 * (2 * r + 1)) * (197 * (2 * s + 1)))) *
        ((199 * (2 * t + 1)) * (211 * (2 * u + 1))) := by
    grind
  have hB : 3586961561382045 * (p * q * r * s * t * u) =
      (((363 * p) * (383 * q)) * ((387 * r) * (395 * s))) * ((399 * t) * (423 * u)) := by
    grind
  rw [← hA, ← hB] at h123456
  have hpqrstu_pos : 0 < p * q * r * s * t * u := by
    have : 0 < p := by omega
    have : 0 < q := by omega
    have : 0 < r := by omega
    have : 0 < s := by omega
    have : 0 < t := by omega
    have : 0 < u := by omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)) (by omega)) (by omega)
  have hrhs : 3586961561382045 * (p * q * r * s * t * u) <
      55191348958099 * (65 * p * q * r * s * t * u) := by
    have hC : 55191348958099 * (65 * p * q * r * s * t * u) =
        3587437682276435 * (p * q * r * s * t * u) := by grind
    rw [hC]
    exact Nat.mul_lt_mul_of_pos_right (by decide) hpqrstu_pos
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h123456 hrhs)

/-- Helper: if a prime `f` divides `65 * p * q * r * s * t * u` with `p < q < r < s < t < u` primes,
    `f < p`, `f ≠ 5`, and `f ≠ 13`, contradiction. -/
theorem prime_dvd_65pqrstu_impossible {f p q r s t u : Nat}
    (hf : IsPrime f) (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hs : IsPrime s) (ht : IsPrime t) (hu : IsPrime u)
    (hfp : f < p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (hf5 : f ≠ 5) (hf13 : f ≠ 13) (hdvd : f ∣ 65 * p * q * r * s * t * u) : False := by
  have h5 : Nat.Coprime f 5 := coprime_primes_ne hf isPrime_5 hf5
  have h13 : Nat.Coprime f 13 := coprime_primes_ne hf (by decide : IsPrime 13) hf13
  have h65 : Nat.Coprime f 65 := by
    have : (65 : Nat) = 5 * 13 := rfl
    rw [this]; exact h5.mul_right h13
  have hcp : Nat.Coprime f p := coprime_primes_ne hf hp (by omega)
  have hcq : Nat.Coprime f q := coprime_primes_ne hf hq (by omega)
  have hcr : Nat.Coprime f r := coprime_primes_ne hf hr (by omega)
  have hcs : Nat.Coprime f s := coprime_primes_ne hf hs (by omega)
  have hct : Nat.Coprime f t := coprime_primes_ne hf ht (by omega)
  have hcu : Nat.Coprime f u := coprime_primes_ne hf hu (by omega)
  have hcop_all : Nat.Coprime f (65 * p * q * r * s * t * u) :=
    (((((h65.mul_right hcp).mul_right hcq).mul_right hcr).mul_right hcs).mul_right hct).mul_right hcu
  have hgcd_dvd : f ∣ Nat.gcd f (65 * p * q * r * s * t * u) := Nat.dvd_gcd (Nat.dvd_refl f) hdvd
  rw [hcop_all] at hgcd_dvd
  have heq1 : f = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
  have := hf.1; omega

/-- Helper: if a prime `f > p` with `f ≠ 5` and `f ≠ 13` divides `65 * p * q * r * s * t * u`
    (`p < q < r < s < t < u` primes, `0 < p`), then `f = q ∨ f = r ∨ f = s ∨ f = t ∨ f = u`. -/
theorem prime_dvd_65pqrstu_mem {f p q r s t u : Nat}
    (hf : IsPrime f) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t) (hu : IsPrime u)
    (hp_pos : 0 < p) (hfp : p < f) (hf5 : f ≠ 5) (hf13 : f ≠ 13)
    (hdvd : f ∣ 65 * p * q * r * s * t * u) :
    f = q ∨ f = r ∨ f = s ∨ f = t ∨ f = u := by
  have h5 : Nat.Coprime f 5 := coprime_primes_ne hf isPrime_5 hf5
  have h13 : Nat.Coprime f 13 := coprime_primes_ne hf (by decide : IsPrime 13) hf13
  have h65 : Nat.Coprime f 65 := by
    have : (65 : Nat) = 5 * 13 := rfl
    rw [this]; exact h5.mul_right h13
  have hdvd1 : f ∣ p * (q * r * s * t * u) := by
    have hassoc : 65 * p * q * r * s * t * u = 65 * (p * (q * r * s * t * u)) := by grind
    rw [hassoc] at hdvd
    exact h65.dvd_of_dvd_mul_left hdvd
  have hcp : Nat.Coprime f p := by
    rcases coprime_or_dvd_of_isPrime (d := p) hf with hcop | hdvd_p
    · exact hcop.symm
    · exfalso
      have hle : f ≤ p := Nat.le_of_dvd hp_pos hdvd_p
      omega
  have hdvd2 : f ∣ q * (r * s * t * u) := by
    have hdvd' := hcp.dvd_of_dvd_mul_left hdvd1
    simpa [Nat.mul_assoc] using hdvd'
  by_cases hfq : f = q
  · exact Or.inl hfq
  · have hcq : Nat.Coprime f q := coprime_primes_ne hf hq hfq
    have hdvd3 : f ∣ r * (s * t * u) := by
      have hdvd' := hcq.dvd_of_dvd_mul_left hdvd2
      simpa [Nat.mul_assoc] using hdvd'
    by_cases hfr : f = r
    · exact Or.inr (Or.inl hfr)
    · have hcr : Nat.Coprime f r := coprime_primes_ne hf hr hfr
      have hdvd4 : f ∣ s * (t * u) := by
        have hdvd' := hcr.dvd_of_dvd_mul_left hdvd3
        simpa [Nat.mul_assoc] using hdvd'
      by_cases hfs : f = s
      · exact Or.inr (Or.inr (Or.inl hfs))
      · have hcs : Nat.Coprime f s := coprime_primes_ne hf hs hfs
        have hdvd5 : f ∣ t * u := hcs.dvd_of_dvd_mul_left hdvd4
        by_cases hft : f = t
        · exact Or.inr (Or.inr (Or.inr (Or.inl hft)))
        · have hct : Nat.Coprime f t := coprime_primes_ne hf ht hft
          have hfu : f ∣ u := hct.dvd_of_dvd_mul_left hdvd5
          rcases hu.2 f hfu with h1 | rfl
          · have := hf.1; omega
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem next_primes_from_181 {p q r s t u : Nat}
    (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t) (hu : IsPrime u)
    (hp : 181 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) (htu : t < u) :
    191 ≤ q ∧ 193 ≤ r ∧ 197 ≤ s ∧ 199 ≤ t ∧ 211 ≤ u := by
  have hdec : ∀ x : Fin 211, 182 ≤ x.1 → IsPrime x.1 →
      x.1 = 191 ∨ x.1 = 193 ∨ x.1 = 197 ∨ x.1 = 199 := by decide
  have hq191 : 191 ≤ q := by
    by_cases hle : 191 ≤ q
    · exact hle
    · exfalso
      have hx := hdec ⟨q, by omega⟩ (by simp; omega) hq
      simp at hx; omega
  have hr193 : 193 ≤ r := by
    by_cases hle : 193 ≤ r
    · exact hle
    · exfalso
      have hx := hdec ⟨r, by omega⟩ (by simp; omega) hr
      simp at hx; omega
  have hs197 : 197 ≤ s := by
    by_cases hle : 197 ≤ s
    · exact hle
    · exfalso
      have hx := hdec ⟨s, by omega⟩ (by simp; omega) hs
      simp at hx; omega
  have ht199 : 199 ≤ t := by
    by_cases hle : 199 ≤ t
    · exact hle
    · exfalso
      have hx := hdec ⟨t, by omega⟩ (by simp; omega) ht
      simp at hx; omega
  have hu211 : 211 ≤ u := by
    by_cases hle : 211 ≤ u
    · exact hle
    · exfalso
      have hx := hdec ⟨u, by omega⟩ (by simp; omega) hu
      simp at hx; omega
  exact ⟨hq191, hr193, hs197, ht199, hu211⟩

private theorem prime_37_to_179 {p : Nat} (hp : IsPrime p) (hlo : 37 ≤ p) (hhi : p < 181) :
    p = 37 ∨ p = 41 ∨ p = 43 ∨ p = 47 ∨ p = 53 ∨ p = 59 ∨ p = 61 ∨ p = 67 ∨
      p = 71 ∨ p = 73 ∨ p = 79 ∨ p = 83 ∨ p = 89 ∨ p = 97 ∨ p = 101 ∨ p = 103 ∨
      p = 107 ∨ p = 109 ∨ p = 113 ∨ p = 127 ∨ p = 131 ∨ p = 137 ∨ p = 139 ∨ p = 149 ∨
      p = 151 ∨ p = 157 ∨ p = 163 ∨ p = 167 ∨ p = 173 ∨ p = 179 := by
  have hdec : ∀ x : Fin 181, 37 ≤ x.1 → IsPrime x.1 →
      x.1 = 37 ∨ x.1 = 41 ∨ x.1 = 43 ∨ x.1 = 47 ∨ x.1 = 53 ∨ x.1 = 59 ∨ x.1 = 61 ∨ x.1 = 67 ∨
        x.1 = 71 ∨ x.1 = 73 ∨ x.1 = 79 ∨ x.1 = 83 ∨ x.1 = 89 ∨ x.1 = 97 ∨ x.1 = 101 ∨ x.1 = 103 ∨
        x.1 = 107 ∨ x.1 = 109 ∨ x.1 = 113 ∨ x.1 = 127 ∨ x.1 = 131 ∨ x.1 = 137 ∨ x.1 = 139 ∨ x.1 = 149 ∨
        x.1 = 151 ∨ x.1 = 157 ∨ x.1 = 163 ∨ x.1 = 167 ∨ x.1 = 173 ∨ x.1 = 179 := by
    decide
  have hx := hdec ⟨p, hhi⟩ hlo hp
  simpa using hx

private theorem two_mul_add_one_dvd_prod6 {x p q r s t u : Nat}
    (hx : x = q ∨ x = r ∨ x = s ∨ x = t ∨ x = u) :
    2 * x + 1 ∣ (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1) := by
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(2 * p + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1), by grind⟩
  · exact ⟨(2 * p + 1) * (2 * q + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1), by grind⟩
  · exact ⟨(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * t + 1) * (2 * u + 1), by grind⟩
  · exact ⟨(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * u + 1), by grind⟩
  · exact ⟨(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩

/-- Shared Cunningham forced-closure chain starting from `179`:
    if `179 ∈ {q, r, s, t, u}` (or `p = 179`) with `p ≤ 179`, then following
    `179 -> 359 -> 719 -> 1439 -> 2879 -> 443 -> 887` forces `71 ∣ 65 * p * q * r * s * t * u`. -/
private theorem cunningham_179_forces_71 {p q r s t u : Nat}
    (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t) (hu : IsPrime u)
    (hp_pos : 0 < p) (hp_lt : p < 359)
    (heq : (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1) =
      65 * p * q * r * s * t * u)
    (h359_dvd : 359 ∣ 65 * p * q * r * s * t * u) :
    71 ∣ 65 * p * q * r * s * t * u := by
  have h359_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 359) hq hr hs ht hu
    hp_pos (by omega) (by decide) (by decide) h359_dvd
  have h719_dvd : 719 ∣ 65 * p * q * r * s * t * u := by
    rw [← heq]; exact two_mul_add_one_dvd_prod6 h359_mem
  have h719_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 719) hq hr hs ht hu
    hp_pos (by omega) (by decide) (by decide) h719_dvd
  have h1439_dvd : 1439 ∣ 65 * p * q * r * s * t * u := by
    rw [← heq]; exact two_mul_add_one_dvd_prod6 h719_mem
  have h1439_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 1439) hq hr hs ht hu
    hp_pos (by omega) (by decide) (by decide) h1439_dvd
  have h2879_dvd : 2879 ∣ 65 * p * q * r * s * t * u := by
    rw [← heq]; exact two_mul_add_one_dvd_prod6 h1439_mem
  have h2879_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 2879) hq hr hs ht hu
    hp_pos (by omega) (by decide) (by decide) h2879_dvd
  have h5759_dvd : 5759 ∣ 65 * p * q * r * s * t * u := by
    rw [← heq]; exact two_mul_add_one_dvd_prod6 h2879_mem
  have h443_dvd : 443 ∣ 65 * p * q * r * s * t * u := Nat.dvd_trans ⟨13, by decide⟩ h5759_dvd
  have h443_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 443) hq hr hs ht hu
    hp_pos (by omega) (by decide) (by decide) h443_dvd
  have h887_dvd : 887 ∣ 65 * p * q * r * s * t * u := by
    rw [← heq]; exact two_mul_add_one_dvd_prod6 h443_mem
  have h887_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 887) hq hr hs ht hu
    hp_pos (by omega) (by decide) (by decide) h887_dvd
  have h1775_dvd : 1775 ∣ 65 * p * q * r * s * t * u := by
    rw [← heq]; exact two_mul_add_one_dvd_prod6 h887_mem
  exact Nat.dvd_trans ⟨25, by decide⟩ h1775_dvd

private theorem factor_dvd_rhs6 {f c p q r s t u : Nat}
    (hf : 2 * p + 1 = f * c)
    (heq : (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1) =
      65 * p * q * r * s * t * u) :
    f ∣ 65 * p * q * r * s * t * u := by
  rw [← heq, hf]
  exact ⟨c * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1), by ac_rfl⟩

/-- **Squarefree Six-Prime Exclusion**: For all primes `37 ≤ p < q < r < s < t < u`,
    `(2*p+1)*(2*q+1)*(2*r+1)*(2*s+1)*(2*t+1)*(2*u+1) ≠ 65 * p * q * r * s * t * u`. -/
theorem six_prime_moment_ne {p q r s t u : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hs : IsPrime s) (ht : IsPrime t) (hu : IsPrime u)
    (hp37 : 37 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) (htu : t < u) :
    (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) * (2 * u + 1) ≠
      65 * p * q * r * s * t * u := by
  intro heq
  by_cases hp181 : 181 ≤ p
  · obtain ⟨hq191, hr193, hs197, ht199, hu211⟩ :=
      next_primes_from_181 hq hr hs ht hu hp181 hpq hqr hrs hst htu
    have hlt := six_prime_growth_bound p q r s t u hp181 hq191 hr193 hs197 ht199 hu211
    omega
  · have hp_cases := prime_37_to_179 hp hp37 (by omega)
    rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
    · -- `p = 37`: `2 * 37 + 1 = 75 = 3 * 25`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 41`: `41 -> 83 -> 167 -> 67 -> 3 < 41`
      have h83_dvd : 83 ∣ 65 * 41 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h83_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 83) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h83_dvd
      have h167_dvd : 167 ∣ 65 * 41 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h83_mem
      have h167_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 167) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h167_dvd
      have h335_dvd : 335 ∣ 65 * 41 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h167_mem
      have h67_dvd : 67 ∣ 65 * 41 * q * r * s * t * u := Nat.dvd_trans ⟨5, by decide⟩ h335_dvd
      have h67_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 67) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h67_dvd
      have h135_dvd : 135 ∣ 65 * 41 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h67_mem
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (Nat.dvd_trans ⟨45, by decide⟩ h135_dvd)
    · -- `p = 43`: `2 * 43 + 1 = 87 = 3 * 29`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 47`: `2 * 47 + 1 = 95 = 19 * 5`
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 19) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 53`: `53 -> 107 -> 43 < 53`
      have h107_dvd : 107 ∣ 65 * 53 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h107_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 107) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h107_dvd
      have h215_dvd : 215 ∣ 65 * 53 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h107_mem
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 43) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (Nat.dvd_trans ⟨5, by decide⟩ h215_dvd)
    · -- `p = 59`: `2 * 59 + 1 = 119 = 17 * 7`
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 17) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 61`: `2 * 61 + 1 = 123 = 41 * 3`
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 41) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 67`: `2 * 67 + 1 = 135 = 3 * 45`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 71`: `2 * 71 + 1 = 143 = 11 * 13`
      exact prime_dvd_65pqrstu_impossible isPrime_11 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 73`: `2 * 73 + 1 = 147 = 3 * 49`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 79`: `2 * 79 + 1 = 159 = 3 * 53`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 83`: `83 -> 167 -> 67 < 83`
      have h167_dvd : 167 ∣ 65 * 83 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h167_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 167) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h167_dvd
      have h335_dvd : 335 ∣ 65 * 83 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h167_mem
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 67) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (Nat.dvd_trans ⟨5, by decide⟩ h335_dvd)
    · -- `p = 89`: `89 -> 179 -> 359 -> 719 -> 1439 -> 2879 -> 443 -> 887 -> 71 < 89`
      have h179_dvd : 179 ∣ 65 * 89 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h179_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 179) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h179_dvd
      have h359_dvd : 359 ∣ 65 * 89 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h179_mem
      have h71_dvd := cunningham_179_forces_71 hq hr hs ht hu (by decide) (by omega) heq h359_dvd
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 71) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) h71_dvd
    · -- `p = 97`: `2 * 97 + 1 = 195 = 3 * 65`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 101`: `2 * 101 + 1 = 203 = 29 * 7`
      exact prime_dvd_65pqrstu_impossible isPrime_29 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 103`: `2 * 103 + 1 = 207 = 3 * 69`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 107`: `2 * 107 + 1 = 215 = 43 * 5`
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 43) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 109`: `2 * 109 + 1 = 219 = 3 * 73`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 113`: `113 -> 227 -> 7 < 113`
      have h227_dvd : 227 ∣ 65 * 113 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h227_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 227) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h227_dvd
      have h455_dvd : 455 ∣ 65 * 113 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h227_mem
      exact prime_dvd_65pqrstu_impossible isPrime_7 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (Nat.dvd_trans ⟨65, by decide⟩ h455_dvd)
    · -- `p = 127`: `2 * 127 + 1 = 255 = 3 * 85`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 131`: `131 -> 263 -> 17 < 131`
      have h263_dvd : 263 ∣ 65 * 131 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h263_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 263) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h263_dvd
      have h527_dvd : 527 ∣ 65 * 131 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h263_mem
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 17) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (Nat.dvd_trans ⟨31, by decide⟩ h527_dvd)
    · -- `p = 137`: `2 * 137 + 1 = 275 = 11 * 25`
      exact prime_dvd_65pqrstu_impossible isPrime_11 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 139`: `2 * 139 + 1 = 279 = 3 * 93`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 149`: `2 * 149 + 1 = 299 = 23 * 13`
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 23) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 151`: `2 * 151 + 1 = 303 = 3 * 101`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 157`: `2 * 157 + 1 = 315 = 3 * 105`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 163`: `2 * 163 + 1 = 327 = 3 * 109`
      exact prime_dvd_65pqrstu_impossible isPrime_3 hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 167`: `2 * 167 + 1 = 335 = 67 * 5`
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 67) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (factor_dvd_rhs6 rfl heq)
    · -- `p = 173`: `173 -> 347 -> 139 < 173`
      have h347_dvd : 347 ∣ 65 * 173 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h347_mem := prime_dvd_65pqrstu_mem (by decide : IsPrime 347) hq hr hs ht hu
        (by decide) (by omega) (by decide) (by decide) h347_dvd
      have h695_dvd : 695 ∣ 65 * 173 * q * r * s * t * u := by
        rw [← heq]; exact two_mul_add_one_dvd_prod6 h347_mem
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 139) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) (Nat.dvd_trans ⟨5, by decide⟩ h695_dvd)
    · -- `p = 179`: `179 -> 359 -> 719 -> 1439 -> 2879 -> 443 -> 887 -> 71 < 179`
      have h359_dvd : 359 ∣ 65 * 179 * q * r * s * t * u := factor_dvd_rhs6 (c := 1) rfl heq
      have h71_dvd := cunningham_179_forces_71 hq hr hs ht hu (by decide) (by omega) heq h359_dvd
      exact prime_dvd_65pqrstu_impossible (by decide : IsPrime 71) hp hq hr hs ht hu (by omega) hpq hqr hrs hst htu
        (by decide) (by decide) h71_dvd

/-- Unconditional exclusion of `p * q * r * s * t * u` for all primes `37 ≤ p < q < r < s < t < u`. -/
theorem not_isFixedPoint_six_distinct_primes {p q r s t u : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r)
    (hs : IsPrime s) (ht : IsPrime t) (hu : IsPrime u)
    (hp37 : 37 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) (htu : t < u) :
    ¬ IsFixedPoint (p * q * r * s * t * u) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hr_pos : 0 < r := by omega
  have hs_pos : 0 < s := by omega
  have ht_pos : 0 < t := by omega
  have hu_pos : 0 < u := by omega
  have hpq_c : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
  have hpr_c : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
  have hps_c : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
  have hpt_c : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
  have hpu_c : Nat.Coprime p u := coprime_primes_ne hp hu (by omega)
  have hqr_c : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
  have hqs_c : Nat.Coprime q s := coprime_primes_ne hq hs (by omega)
  have hqt_c : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
  have hqu_c : Nat.Coprime q u := coprime_primes_ne hq hu (by omega)
  have hrs_c : Nat.Coprime r s := coprime_primes_ne hr hs (by omega)
  have hrt_c : Nat.Coprime r t := coprime_primes_ne hr ht (by omega)
  have hru_c : Nat.Coprime r u := coprime_primes_ne hr hu (by omega)
  have hst_c : Nat.Coprime s t := coprime_primes_ne hs ht (by omega)
  have hsu_c : Nat.Coprime s u := coprime_primes_ne hs hu (by omega)
  have htu_c : Nat.Coprime t u := coprime_primes_ne ht hu (by omega)
  have hcop_pq_r : Nat.Coprime (p * q) r := hpr_c.mul_left hqr_c
  have hcop_pqr_s : Nat.Coprime (p * q * r) s := (hps_c.mul_left hqs_c).mul_left hrs_c
  have hcop_pqrs_t : Nat.Coprime (p * q * r * s) t :=
    ((hpt_c.mul_left hqt_c).mul_left hrt_c).mul_left hst_c
  have hcop_pqrst_u : Nat.Coprime (p * q * r * s * t) u :=
    (((hpu_c.mul_left hqu_c).mul_left hru_c).mul_left hsu_c).mul_left htu_c
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop_pqrst_u, fullMoment_mul_of_coprime hcop_pqrs_t,
    fullMoment_mul_of_coprime hcop_pqr_s, fullMoment_mul_of_coprime hcop_pq_r,
    fullMoment_mul_of_coprime hpq_c,
    fullMoment_prime hp, fullMoment_prime hq, fullMoment_prime hr,
    fullMoment_prime hs, fullMoment_prime ht, fullMoment_prime hu] at hS_eq
  rw [tau_mul_of_coprime hcop_pqrst_u
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos) hs_pos) ht_pos) hu_pos,
    tau_mul_of_coprime hcop_pqrs_t
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos) hs_pos) ht_pos,
    tau_mul_of_coprime hcop_pqr_s (Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos) hs_pos,
    tau_mul_of_coprime hcop_pq_r (Nat.mul_pos hp_pos hq_pos) hr_pos,
    tau_mul_of_coprime hpq_c hp_pos hq_pos,
    tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime hr,
    tau_of_isPrime hs, tau_of_isPrime ht, tau_of_isPrime hu] at hS_eq
  have h65 : (p * q * r * s * t * u) * (2 * 2 * 2 * 2 * 2 * 2 + 1) = 65 * p * q * r * s * t * u := by grind
  rw [h65] at hS_eq
  exact six_prime_moment_ne hp hq hr hs ht hu hp37 hpq hqr hrs hst htu hS_eq

/-- Unconditional exclusion of every positive integer `n` with `omegaBig n = 6`. -/
theorem not_isFixedPoint_of_omegaBig_eq_six {n : Nat} (ho6 : omegaBig n = 6) :
    ¬ IsFixedPoint n := by
  intro hfp
  obtain ⟨p, q, r, s, t, u, hp, hq, hr, hs, ht, hu, hp37, hpq, hqr, hrs, hst, htu, hn_eq⟩ :=
    omegaSix_must_be_squarefree_ge_37 hfp ho6
  rw [hn_eq] at hfp
  exact not_isFixedPoint_six_distinct_primes hp hq hr hs ht hu hp37 hpq hqr hrs hst htu hfp

/-- **Complete $\Omega(n) \le 6$ Fixed-Point Uniqueness**:
    For every `n : Nat`, if `IsFixedPoint n` and `omegaBig n ≤ 6`, then `n = 21`. -/
theorem fixedPoint_eq_21_of_omegaBig_le_six {n : Nat}
    (hfp : IsFixedPoint n) (ho : omegaBig n ≤ 6) :
    n = 21 := by
  by_cases ho6 : omegaBig n = 6
  · exact absurd hfp (not_isFixedPoint_of_omegaBig_eq_six ho6)
  · exact fixedPoint_eq_21_of_omegaBig_le_five hfp (by omega)

/-- **Structural Reduction Theorem ($\Omega(n) \ge 7$)**:
    Every fixed point `n ≠ 21` of OEIS A245211 satisfies `7 ≤ omegaBig n`. -/
theorem omegaBig_ge_seven_of_isFixedPoint_ne_21 {n : Nat}
    (hfp : IsFixedPoint n) (hne : n ≠ 21) :
    7 ≤ omegaBig n := by
  by_cases hle : omegaBig n ≤ 6
  · exact absurd (fixedPoint_eq_21_of_omegaBig_le_six hfp hle) hne
  · omega

end OmegaSixClosure

end OeisA245211
