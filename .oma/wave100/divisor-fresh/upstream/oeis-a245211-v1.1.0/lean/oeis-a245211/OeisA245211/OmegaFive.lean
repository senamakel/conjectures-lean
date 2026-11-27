/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/
import OeisA245211.OmegaFour

/-!
# OEIS A245211: Complete Classification of $\Omega(n) \le 5$ Fixed Points

This module closes the squarefree five-prime case (`p * q * r * s * t` with `17 ≤ p < q < r < s < t`)
via the growth bound at `73 ≤ p` and Cunningham prime-factor forced closure on the fourteen primes
`17 ≤ p < 73`. Combined with `omegaFive_must_be_squarefree_ge_17` and
`fixedPoint_eq_21_of_omegaBig_le_four` from `OmegaFour.lean`, this proves that every fixed point
`n` with `omegaBig n ≤ 5` equals `21`, and hence any fixed point `n ≠ 21` satisfies
`Nat.gcd n 6 = 1` and `6 ≤ omegaBig n`.
-/

namespace OeisA245211

section OmegaFiveClosure

/-- **Growth bound for five distinct primes `73 ≤ p < q < r < s < t`**:
    `(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) < 33 * p * q * r * s * t`. -/
theorem five_prime_growth_bound (p q r s t : Nat)
    (hp : 73 ≤ p) (hq : 79 ≤ q) (hr : 83 ≤ r) (hs : 89 ≤ s) (ht : 97 ≤ t) :
    (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) <
      33 * p * q * r * s * t := by
  have h1 : 73 * (2 * p + 1) ≤ 147 * p := by omega
  have h2 : 79 * (2 * q + 1) ≤ 159 * q := by omega
  have h3 : 83 * (2 * r + 1) ≤ 167 * r := by omega
  have h4 : 89 * (2 * s + 1) ≤ 179 * s := by omega
  have h5 : 97 * (2 * t + 1) ≤ 195 * t := by omega
  have h12 : (73 * (2 * p + 1)) * (79 * (2 * q + 1)) ≤ (147 * p) * (159 * q) :=
    Nat.mul_le_mul h1 h2
  have h34 : (83 * (2 * r + 1)) * (89 * (2 * s + 1)) ≤ (167 * r) * (179 * s) :=
    Nat.mul_le_mul h3 h4
  have h1234 :
      ((73 * (2 * p + 1)) * (79 * (2 * q + 1))) * ((83 * (2 * r + 1)) * (89 * (2 * s + 1))) ≤
        ((147 * p) * (159 * q)) * ((167 * r) * (179 * s)) :=
    Nat.mul_le_mul h12 h34
  have h12345 := Nat.mul_le_mul h1234 h5
  have hA :
      4132280413 * ((2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1)) =
        (((73 * (2 * p + 1)) * (79 * (2 * q + 1))) *
          ((83 * (2 * r + 1)) * (89 * (2 * s + 1)))) * (97 * (2 * t + 1)) := by
    grind
  have hB :
      136244372355 * (p * q * r * s * t) =
        (((147 * p) * (159 * q)) * ((167 * r) * (179 * s))) * (195 * t) := by
    grind
  rw [← hA, ← hB] at h12345
  have hpqrst_pos : 0 < p * q * r * s * t := by
    have : 0 < p := by omega
    have : 0 < q := by omega
    have : 0 < r := by omega
    have : 0 < s := by omega
    have : 0 < t := by omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)) (by omega)
  have hrhs : 136244372355 * (p * q * r * s * t) < 4132280413 * (33 * p * q * r * s * t) := by
    have hC : 4132280413 * (33 * p * q * r * s * t) = 136365253629 * (p * q * r * s * t) := by grind
    rw [hC]
    exact Nat.mul_lt_mul_of_pos_right (by decide) hpqrst_pos
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h12345 hrhs)

/-- Helper: if a prime `f` divides `33 * p * q * r * s * t` with `p < q < r < s < t` primes,
    `f < p`, `f ≠ 3`, and `f ≠ 11`, contradiction. -/
theorem prime_dvd_33pqrst_impossible {f p q r s t : Nat}
    (hf : IsPrime f) (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t)
    (hfp : f < p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t)
    (hf3 : f ≠ 3) (hf11 : f ≠ 11) (hdvd : f ∣ 33 * p * q * r * s * t) : False := by
  have h3 : Nat.Coprime f 3 := coprime_primes_ne hf isPrime_3 hf3
  have h11 : Nat.Coprime f 11 := coprime_primes_ne hf isPrime_11 hf11
  have h33 : Nat.Coprime f 33 := by
    have : (33 : Nat) = 3 * 11 := rfl
    rw [this]
    exact h3.mul_right h11
  have hcp : Nat.Coprime f p := coprime_primes_ne hf hp (by omega)
  have hcq : Nat.Coprime f q := coprime_primes_ne hf hq (by omega)
  have hcr : Nat.Coprime f r := coprime_primes_ne hf hr (by omega)
  have hcs : Nat.Coprime f s := coprime_primes_ne hf hs (by omega)
  have hct : Nat.Coprime f t := coprime_primes_ne hf ht (by omega)
  have hcop_all : Nat.Coprime f (33 * p * q * r * s * t) :=
    ((((h33.mul_right hcp).mul_right hcq).mul_right hcr).mul_right hcs).mul_right hct
  have hgcd_dvd : f ∣ Nat.gcd f (33 * p * q * r * s * t) := Nat.dvd_gcd (Nat.dvd_refl f) hdvd
  rw [hcop_all] at hgcd_dvd
  have heq1 : f = 1 := Nat.eq_one_of_dvd_one hgcd_dvd
  have := hf.1
  omega

/-- Helper: if a prime `f > p` with `f ≠ 3` and `f ≠ 11` divides `33 * p * q * r * s * t`
    (`p < q < r < s < t` primes, `0 < p`), then `f = q ∨ f = r ∨ f = s ∨ f = t`. -/
theorem prime_dvd_33pqrst_mem {f p q r s t : Nat}
    (hf : IsPrime f) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t)
    (hp_pos : 0 < p) (hfp : p < f) (hf3 : f ≠ 3) (hf11 : f ≠ 11)
    (hdvd : f ∣ 33 * p * q * r * s * t) :
    f = q ∨ f = r ∨ f = s ∨ f = t := by
  have h3 : Nat.Coprime f 3 := coprime_primes_ne hf isPrime_3 hf3
  have h11 : Nat.Coprime f 11 := coprime_primes_ne hf isPrime_11 hf11
  have h33 : Nat.Coprime f 33 := by
    have : (33 : Nat) = 3 * 11 := rfl
    rw [this]
    exact h3.mul_right h11
  have hdvd1 : f ∣ p * (q * r * s * t) := by
    have hassoc : 33 * p * q * r * s * t = 33 * (p * (q * r * s * t)) := by grind
    rw [hassoc] at hdvd
    exact h33.dvd_of_dvd_mul_left hdvd
  have hcp : Nat.Coprime f p := by
    rcases coprime_or_dvd_of_isPrime (d := p) hf with hcop | hdvd_p
    · exact hcop.symm
    · exfalso
      have hle : f ≤ p := Nat.le_of_dvd hp_pos hdvd_p
      omega
  have hdvd2 : f ∣ q * (r * s * t) := by
    have hdvd' := hcp.dvd_of_dvd_mul_left hdvd1
    simpa [Nat.mul_assoc] using hdvd'
  by_cases hfq : f = q
  · exact Or.inl hfq
  · have hcq : Nat.Coprime f q := coprime_primes_ne hf hq hfq
    have hdvd3 : f ∣ r * (s * t) := by
      have hdvd' := hcq.dvd_of_dvd_mul_left hdvd2
      simpa [Nat.mul_assoc] using hdvd'
    by_cases hfr : f = r
    · exact Or.inr (Or.inl hfr)
    · have hcr : Nat.Coprime f r := coprime_primes_ne hf hr hfr
      have hdvd4 : f ∣ s * t := hcr.dvd_of_dvd_mul_left hdvd3
      by_cases hfs : f = s
      · exact Or.inr (Or.inr (Or.inl hfs))
      · have hcs : Nat.Coprime f s := coprime_primes_ne hf hs hfs
        have hft : f ∣ t := hcs.dvd_of_dvd_mul_left hdvd4
        rcases ht.2 f hft with h1 | rfl
        · have := hf.1; omega
        · exact Or.inr (Or.inr (Or.inr rfl))

private theorem next_primes_from_73 {p q r s t : Nat}
    (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t)
    (hp : 73 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) :
    79 ≤ q ∧ 83 ≤ r ∧ 89 ≤ s ∧ 97 ≤ t := by
  have hdec : ∀ x : Fin 97, 74 ≤ x.1 → IsPrime x.1 →
      x.1 = 79 ∨ x.1 = 83 ∨ x.1 = 89 := by decide
  have hq79 : 79 ≤ q := by
    by_cases hle : 79 ≤ q
    · exact hle
    · exfalso
      have hx := hdec ⟨q, by omega⟩ (by simp; omega) hq
      simp at hx
      omega
  have hr83 : 83 ≤ r := by
    by_cases hle : 83 ≤ r
    · exact hle
    · exfalso
      have hx := hdec ⟨r, by omega⟩ (by simp; omega) hr
      simp at hx
      omega
  have hs89 : 89 ≤ s := by
    by_cases hle : 89 ≤ s
    · exact hle
    · exfalso
      have hx := hdec ⟨s, by omega⟩ (by simp; omega) hs
      simp at hx
      omega
  have ht97 : 97 ≤ t := by
    by_cases hle : 97 ≤ t
    · exact hle
    · exfalso
      have hx := hdec ⟨t, by omega⟩ (by simp; omega) ht
      simp at hx
      omega
  exact ⟨hq79, hr83, hs89, ht97⟩

private theorem prime_17_to_71 {p : Nat} (hp : IsPrime p) (hlo : 17 ≤ p) (hhi : p < 73) :
    p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 41 ∨
      p = 43 ∨ p = 47 ∨ p = 53 ∨ p = 59 ∨ p = 61 ∨ p = 67 ∨ p = 71 := by
  have hdec : ∀ x : Fin 73, 17 ≤ x.1 → IsPrime x.1 →
      x.1 = 17 ∨ x.1 = 19 ∨ x.1 = 23 ∨ x.1 = 29 ∨ x.1 = 31 ∨ x.1 = 37 ∨ x.1 = 41 ∨
        x.1 = 43 ∨ x.1 = 47 ∨ x.1 = 53 ∨ x.1 = 59 ∨ x.1 = 61 ∨ x.1 = 67 ∨ x.1 = 71 := by
    decide
  have hx := hdec ⟨p, hhi⟩ hlo hp
  simpa using hx

private theorem two_mul_add_one_dvd_prod {x p q r s t : Nat}
    (hx : x = q ∨ x = r ∨ x = s ∨ x = t) :
    2 * x + 1 ∣ (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨(2 * p + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
  · exact ⟨(2 * p + 1) * (2 * q + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
  · exact ⟨(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * t + 1), by grind⟩
  · exact ⟨(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1), by grind⟩

/-- **Squarefree Five-Prime Exclusion**: For all primes `17 ≤ p < q < r < s < t`,
    `(2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) ≠ 33 * p * q * r * s * t`. -/
theorem five_prime_moment_ne {p q r s t : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t)
    (hp17 : 17 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) :
    (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1) ≠
      33 * p * q * r * s * t := by
  intro heq
  by_cases hp73 : 73 ≤ p
  · obtain ⟨hq79, hr83, hs89, ht97⟩ := next_primes_from_73 hq hr hs ht hp73 hpq hqr hrs hst
    have hlt := five_prime_growth_bound p q r s t hp73 hq79 hr83 hs89 ht97
    omega
  · have hp_cases := prime_17_to_71 hp hp17 (by omega)
    rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- `p = 17`: `2 * 17 + 1 = 35 = 5 * 7`, `5 < 17`
      exact prime_dvd_33pqrst_impossible isPrime_5 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨7 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 19`: `2 * 19 + 1 = 39 = 13 * 3`, `13 < 19`
      exact prime_dvd_33pqrst_impossible (by decide : IsPrime 13) hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨3 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 23`: `2 * 23 + 1 = 47`, forcing `47 ∈ {q, r, s, t}`, hence `2 * 47 + 1 = 95 = 5 * 19` divides RHS
      have h47_dvd : 47 ∣ 33 * 23 * q * r * s * t :=
        ⟨(2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
      have h47_mem := prime_dvd_33pqrst_mem (by decide : IsPrime 47) hq hr hs ht
        (by decide) (by omega) (by decide) (by decide) h47_dvd
      have h95_dvd : 95 ∣ 33 * 23 * q * r * s * t := by
        rw [← heq]
        exact two_mul_add_one_dvd_prod h47_mem
      have h5_dvd : 5 ∣ 33 * 23 * q * r * s * t := Nat.dvd_trans ⟨19, by decide⟩ h95_dvd
      exact prime_dvd_33pqrst_impossible isPrime_5 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) h5_dvd
    · -- `p = 29`: `2 * 29 + 1 = 59`, forcing `59 ∈ {q, r, s, t}`, hence `2 * 59 + 1 = 119 = 7 * 17` divides RHS
      have h59_dvd : 59 ∣ 33 * 29 * q * r * s * t :=
        ⟨(2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
      have h59_mem := prime_dvd_33pqrst_mem (by decide : IsPrime 59) hq hr hs ht
        (by decide) (by omega) (by decide) (by decide) h59_dvd
      have h119_dvd : 119 ∣ 33 * 29 * q * r * s * t := by
        rw [← heq]
        exact two_mul_add_one_dvd_prod h59_mem
      have h7_dvd : 7 ∣ 33 * 29 * q * r * s * t := Nat.dvd_trans ⟨17, by decide⟩ h119_dvd
      exact prime_dvd_33pqrst_impossible isPrime_7 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) h7_dvd
    · -- `p = 31`: `2 * 31 + 1 = 63 = 7 * 9`, `7 < 31`
      exact prime_dvd_33pqrst_impossible isPrime_7 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨9 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 37`: `2 * 37 + 1 = 75 = 5 * 15`, `5 < 37`
      exact prime_dvd_33pqrst_impossible isPrime_5 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨15 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 41`: `2 * 41 + 1 = 83`, forcing `83 ∈ {q, r, s, t}`, hence `167 ∈ {q, r, s, t}`, hence `335 = 5 * 67` divides RHS
      have h83_dvd : 83 ∣ 33 * 41 * q * r * s * t :=
        ⟨(2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
      have h83_mem := prime_dvd_33pqrst_mem (by decide : IsPrime 83) hq hr hs ht
        (by decide) (by omega) (by decide) (by decide) h83_dvd
      have h167_dvd : 167 ∣ 33 * 41 * q * r * s * t := by
        rw [← heq]
        exact two_mul_add_one_dvd_prod h83_mem
      have h167_mem := prime_dvd_33pqrst_mem (by decide : IsPrime 167) hq hr hs ht
        (by decide) (by omega) (by decide) (by decide) h167_dvd
      have h335_dvd : 335 ∣ 33 * 41 * q * r * s * t := by
        rw [← heq]
        exact two_mul_add_one_dvd_prod h167_mem
      have h5_dvd : 5 ∣ 33 * 41 * q * r * s * t := Nat.dvd_trans ⟨67, by decide⟩ h335_dvd
      exact prime_dvd_33pqrst_impossible isPrime_5 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) h5_dvd
    · -- `p = 43`: `2 * 43 + 1 = 87 = 29 * 3`, `29 < 43`
      exact prime_dvd_33pqrst_impossible isPrime_29 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨3 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 47`: `2 * 47 + 1 = 95 = 5 * 19`, `5 < 47`
      exact prime_dvd_33pqrst_impossible isPrime_5 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨19 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 53`: `2 * 53 + 1 = 107`, forcing `107 ∈ {q, r, s, t}`, hence `2 * 107 + 1 = 215 = 5 * 43` divides RHS
      have h107_dvd : 107 ∣ 33 * 53 * q * r * s * t :=
        ⟨(2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
      have h107_mem := prime_dvd_33pqrst_mem (by decide : IsPrime 107) hq hr hs ht
        (by decide) (by omega) (by decide) (by decide) h107_dvd
      have h215_dvd : 215 ∣ 33 * 53 * q * r * s * t := by
        rw [← heq]
        exact two_mul_add_one_dvd_prod h107_mem
      have h5_dvd : 5 ∣ 33 * 53 * q * r * s * t := Nat.dvd_trans ⟨43, by decide⟩ h215_dvd
      exact prime_dvd_33pqrst_impossible isPrime_5 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) h5_dvd
    · -- `p = 59`: `2 * 59 + 1 = 119 = 7 * 17`, `7 < 59`
      exact prime_dvd_33pqrst_impossible isPrime_7 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨17 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 61`: `2 * 61 + 1 = 123 = 41 * 3`, `41 < 61`
      exact prime_dvd_33pqrst_impossible (by decide : IsPrime 41) hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨3 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 67`: `2 * 67 + 1 = 135 = 5 * 27`, `5 < 67`
      exact prime_dvd_33pqrst_impossible isPrime_5 hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨27 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩
    · -- `p = 71`: `2 * 71 + 1 = 143 = 13 * 11`, `13 < 71`
      exact prime_dvd_33pqrst_impossible (by decide : IsPrime 13) hp hq hr hs ht (by omega) hpq hqr hrs hst
        (by decide) (by decide) ⟨11 * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) * (2 * t + 1), by grind⟩

/-- Unconditional exclusion of `p * q * r * s * t` for all primes `17 ≤ p < q < r < s < t`. -/
theorem not_isFixedPoint_five_distinct_primes {p q r s t : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hr : IsPrime r) (hs : IsPrime s) (ht : IsPrime t)
    (hp17 : 17 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) :
    ¬ IsFixedPoint (p * q * r * s * t) := by
  intro hfp
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hr_pos : 0 < r := by omega
  have hs_pos : 0 < s := by omega
  have ht_pos : 0 < t := by omega
  have hpq_c : Nat.Coprime p q := coprime_primes_ne hp hq (by omega)
  have hpr_c : Nat.Coprime p r := coprime_primes_ne hp hr (by omega)
  have hps_c : Nat.Coprime p s := coprime_primes_ne hp hs (by omega)
  have hpt_c : Nat.Coprime p t := coprime_primes_ne hp ht (by omega)
  have hqr_c : Nat.Coprime q r := coprime_primes_ne hq hr (by omega)
  have hqs_c : Nat.Coprime q s := coprime_primes_ne hq hs (by omega)
  have hqt_c : Nat.Coprime q t := coprime_primes_ne hq ht (by omega)
  have hrs_c : Nat.Coprime r s := coprime_primes_ne hr hs (by omega)
  have hrt_c : Nat.Coprime r t := coprime_primes_ne hr ht (by omega)
  have hst_c : Nat.Coprime s t := coprime_primes_ne hs ht (by omega)
  have hcop_pq_r : Nat.Coprime (p * q) r := hpr_c.mul_left hqr_c
  have hcop_pqr_s : Nat.Coprime (p * q * r) s := (hps_c.mul_left hqs_c).mul_left hrs_c
  have hcop_pqrs_t : Nat.Coprime (p * q * r * s) t :=
    ((hpt_c.mul_left hqt_c).mul_left hrt_c).mul_left hst_c
  have hS_eq := ((isFixedPoint_iff_fullMoment _).mp hfp).2
  rw [fullMoment_mul_of_coprime hcop_pqrs_t, fullMoment_mul_of_coprime hcop_pqr_s,
    fullMoment_mul_of_coprime hcop_pq_r, fullMoment_mul_of_coprime hpq_c,
    fullMoment_prime hp, fullMoment_prime hq, fullMoment_prime hr,
    fullMoment_prime hs, fullMoment_prime ht] at hS_eq
  rw [tau_mul_of_coprime hcop_pqrs_t
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos) hs_pos) ht_pos,
    tau_mul_of_coprime hcop_pqr_s (Nat.mul_pos (Nat.mul_pos hp_pos hq_pos) hr_pos) hs_pos,
    tau_mul_of_coprime hcop_pq_r (Nat.mul_pos hp_pos hq_pos) hr_pos,
    tau_mul_of_coprime hpq_c hp_pos hq_pos,
    tau_of_isPrime hp, tau_of_isPrime hq, tau_of_isPrime hr,
    tau_of_isPrime hs, tau_of_isPrime ht] at hS_eq
  have h33 : (p * q * r * s * t) * (2 * 2 * 2 * 2 * 2 + 1) = 33 * p * q * r * s * t := by grind
  rw [h33] at hS_eq
  exact five_prime_moment_ne hp hq hr hs ht hp17 hpq hqr hrs hst hS_eq

/-- Unconditional exclusion of every positive integer `n` with `omegaBig n = 5`. -/
theorem not_isFixedPoint_of_omegaBig_eq_five {n : Nat} (ho5 : omegaBig n = 5) :
    ¬ IsFixedPoint n := by
  intro hfp
  obtain ⟨p, q, r, s, t, hp, hq, hr, hs, ht, hp17, hpq, hqr, hrs, hst, hn_eq⟩ :=
    omegaFive_must_be_squarefree_ge_17 hfp ho5
  rw [hn_eq] at hfp
  exact not_isFixedPoint_five_distinct_primes hp hq hr hs ht hp17 hpq hqr hrs hst hfp

/-- **Complete $\Omega(n) \le 5$ Fixed-Point Uniqueness**:
    For every `n : Nat`, if `IsFixedPoint n` and `omegaBig n ≤ 5`, then `n = 21`. -/
theorem fixedPoint_eq_21_of_omegaBig_le_five {n : Nat}
    (hfp : IsFixedPoint n) (ho : omegaBig n ≤ 5) :
    n = 21 := by
  by_cases ho5 : omegaBig n = 5
  · exact absurd hfp (not_isFixedPoint_of_omegaBig_eq_five ho5)
  · exact fixedPoint_eq_21_of_omegaBig_le_four hfp (by omega)

/-- **Structural Reduction Theorem ($\Omega(n) \ge 6$)**:
    Every fixed point `n ≠ 21` of OEIS A245211 satisfies
    `Nat.gcd n 6 = 1` and `6 ≤ omegaBig n`. -/
theorem omegaBig_ge_six_of_isFixedPoint_ne_21 {n : Nat}
    (hfp : IsFixedPoint n) (hne : n ≠ 21) :
    Nat.gcd n 6 = 1 ∧ 6 ≤ omegaBig n := by
  refine ⟨gcd_six_eq_one_of_isFixedPoint_ne_21 hfp hne, ?_⟩
  by_cases hle : omegaBig n ≤ 5
  · exact absurd (fixedPoint_eq_21_of_omegaBig_le_five hfp hle) hne
  · omega

end OmegaFiveClosure

end OeisA245211
