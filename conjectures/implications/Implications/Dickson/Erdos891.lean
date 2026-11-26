import Implications.Dickson.Linear

/-!
# Erdős Problem 891, Weisenberg's variant, from Dickson's conjecture

Source: `FormalConjectures/ErdosProblems/891.lean`, `Erdos891.erdos_891.variants.weisenberg`,
formal-conjectures `9097e2f` (labelled research solved, proof `sorry` there). The statement below
is verbatim, with `type_of% Dickson.dickson_conjecture` written as `DicksonConjecture`
(`Implications.Dickson.Statement`), which is the same proposition.

The argument is the one in the formal-conjectures docstring (attributed there to Weisenberg,
erdosproblems.com/891). Write `P = p₁ ⋯ p_k` and `L = P!`. The forms `(L/i) X + 1` for
`1 ≤ i ≤ P` have constant term 1, so they meet the Schinzel condition at `X = 0`; Dickson gives
infinitely many `t` with every `(L/i) t + 1` prime. For `n = L t + 1`, each `m ∈ [n, n + P - 1)`
is `L t + i = i ((L/i) t + 1)` with `1 ≤ i < P`, so `ω m ≤ ω i + 1`. An `i` with `ω i ≥ k` is at
least the product of the first `k` primes, which is `P`, so `ω i ≤ k - 1` and `ω m ≤ k`.
(The docstring uses `L = lcm(1, …, P)`; any common multiple works, and we use `P!`.)
-/

open Polynomial

namespace Implications.Dickson

open Finset

open scoped ArithmeticFunction.omega

/-- The product of the elements of a finite set of primes is at least the product of the first
`#s` primes. -/
theorem prod_range_nth_prime_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ i ∈ range s.card, i.nth Nat.Prime ≤ ∏ p ∈ s, p := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [card_insert_of_notMem has, prod_range_succ, prod_insert has]
    have ih' := ih (fun p hp => hs p (mem_insert_of_mem hp))
    have hcount : s.card < Nat.count Nat.Prime (a + 1) := by
      rw [Nat.count_eq_card_filter_range]
      calc s.card < (insert a s).card := by rw [card_insert_of_notMem has]; omega
        _ ≤ _ := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_range]
          rcases mem_insert.mp hx with rfl | hx'
          · exact ⟨by omega, hs _ (mem_insert_self _ _)⟩
          · exact ⟨by have := ha x hx'; omega, hs x (mem_insert_of_mem hx')⟩
    have hnth := Nat.nth_lt_of_lt_count hcount
    calc (∏ i ∈ range s.card, i.nth Nat.Prime) * s.card.nth Nat.Prime
        ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul ih' (by omega)
      _ = a * ∏ p ∈ s, p := mul_comm _ _

/-- A positive integer below `p₁ ⋯ p_k` has fewer than `k` distinct prime factors. -/
theorem omega_lt_of_lt_prod (k i : ℕ) (hi : 0 < i) (h : i < ∏ j ∈ range k, j.nth Nat.Prime) :
    ω i < k := by
  by_contra hk
  push Not at hk
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hk
  have h1 : ∏ j ∈ range k, j.nth Nat.Prime ≤ ∏ j ∈ range i.primeFactors.card, j.nth Nat.Prime :=
    prod_le_prod_of_subset_of_one_le' (range_subset_range.mpr hk)
      (fun j _ _ => (Nat.prime_nth_prime j).one_lt.le)
  have h2 := prod_range_nth_prime_le i.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have h3 : ∏ p ∈ i.primeFactors, p ≤ i := Nat.le_of_dvd hi (Nat.prod_primeFactors_dvd i)
  omega

theorem omega_mul_prime_le (i q : ℕ) (hi : i ≠ 0) (hq : q.Prime) : ω (i * q) ≤ ω i + 1 := by
  simp only [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
  rw [Nat.primeFactors_mul hi hq.ne_zero, hq.primeFactors]
  exact (card_union_le _ _).trans (by simp)

/-- Source: `FormalConjectures/ErdosProblems/891.lean`, `Erdos891.erdos_891.variants.weisenberg`,
formal-conjectures `9097e2f`; binders and conclusion verbatim, with
`hdickson : type_of% Dickson.dickson_conjecture` written as `hdickson : DicksonConjecture`. -/
theorem erdos_891_variants_weisenberg (k : ℕ) (hk : k ≥ 2)
    (hdickson : DicksonConjecture) :
    ∃ᶠ n in Filter.atTop,
      ∀ m ∈ Ico n (n + (∏ i ∈ range k, i.nth Nat.Prime) - 1),
      ω m ≤ k := by
  set P := ∏ i ∈ range k, i.nth Nat.Prime with hP
  have hP0 : 0 < P := prod_pos (fun j _ => (Nat.prime_nth_prime j).pos)
  set L := P.factorial with hL
  have hL0 : 0 < L := Nat.factorial_pos P
  have hdvd : ∀ i, 1 ≤ i → i ≤ P → i ∣ L := fun i h1 h2 => Nat.dvd_factorial h1 h2
  have hLi : ∀ i, 1 ≤ i → i ≤ P → 0 < L / i := fun i h1 h2 =>
    Nat.div_pos (Nat.le_of_dvd hL0 (hdvd i h1 h2)) h1
  let fs : Finset ℤ[X] := (Icc 1 P).image (fun i => C ((L / i : ℕ) : ℤ) * X + C ((1 : ℕ) : ℤ))
  have H := hdickson fs ?_ ?_
  · rw [Set.infinite_coe_iff] at H
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨t, ht, hta⟩ := H.exists_gt a
    refine ⟨L * t + 1, ?_, ?_⟩
    · have : t ≤ L * t := Nat.le_mul_of_pos_left t hL0
      omega
    intro m hm
    rw [mem_Ico] at hm
    obtain ⟨j, rfl⟩ : ∃ j, m = L * t + 1 + j := ⟨m - (L * t + 1), by omega⟩
    have hi1 : 1 ≤ j + 1 := by omega
    have hiP : j + 1 < P := by omega
    have hq := ht (C ((L / (j + 1) : ℕ) : ℤ) * X + C ((1 : ℕ) : ℤ))
      (mem_image_of_mem _ (mem_Icc.mpr ⟨hi1, hiP.le⟩))
    simp only [eval_add, eval_mul, eval_C, eval_X] at hq
    rw [natAbs_linear] at hq
    have hm' : L * t + 1 + j = (j + 1) * (L / (j + 1) * t + 1) := by
      rw [mul_add, ← mul_assoc, Nat.mul_div_cancel' (hdvd _ hi1 hiP.le)]
      ring
    rw [hm']
    have h1 := omega_mul_prime_le (j + 1) _ (by omega) hq
    have h2 := omega_lt_of_lt_prod k (j + 1) (by omega) hiP
    omega
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hf
    rw [mem_Icc] at hi
    exact linear_degree_bunyakovsky (by exact_mod_cast hLi i hi.1 hi.2)
      (by simpa using isRelPrime_one_left)
  · intro p hp
    refine ⟨0, ?_⟩
    intro f hf
    obtain ⟨i, -, rfl⟩ := mem_image.mp hf
    simp only [eval_add, eval_mul, eval_C, eval_X, Nat.cast_zero, mul_zero, zero_add,
      Nat.cast_one]
    intro h
    exact hp.ne_one (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)

end Implications.Dickson
