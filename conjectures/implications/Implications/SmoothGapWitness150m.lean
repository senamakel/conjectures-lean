import Mathlib

/-!
An exact two-hit witness near the upper endpoint of the bounded Erdős 932
census. The theorem uses the same zero-based prime indexing and strict
smoothness condition as the conjecture.
-/

namespace Implications.SmoothGapWitness150m

private theorem left_prime : Nat.Prime 149973611 := by norm_num

private theorem right_prime : Nat.Prime 149973667 := by norm_num

private theorem interior_not_prime (n : ℕ) (hlo : 149973611 < n) (hhi : n < 149973667) :
    ¬ n.Prime := by
  interval_cases n <;> norm_num

private theorem hit_left : Nat.maxPrimeFac 149973616 < 56 := by
  rw [show (149973616 : ℕ) = 2 ^ 4 * 13 * 23 ^ 2 * 29 * 47 by norm_num]
  rw [Nat.maxPrimeFac_mul (by norm_num) (by norm_num),
    Nat.maxPrimeFac_mul (by norm_num) (by norm_num),
    Nat.maxPrimeFac_mul (by norm_num) (by norm_num),
    Nat.maxPrimeFac_mul (by norm_num) (by norm_num)]
  simp only [Nat.maxPrimeFac_pow (by decide : 4 ≠ 0),
    Nat.maxPrimeFac_pow (by decide : 2 ≠ 0), max_lt_iff]
  iterate 4 apply And.intro
  all_goals exact Nat.maxPrimeFac_le.trans_lt (by decide)

private theorem hit_right : Nat.maxPrimeFac 149973660 < 56 := by
  rw [show (149973660 : ℕ) = 2 ^ 2 * 3 ^ 3 * 5 * 17 ^ 2 * 31 ^ 2 by norm_num]
  rw [Nat.maxPrimeFac_mul (by norm_num) (by norm_num),
    Nat.maxPrimeFac_mul (by norm_num) (by norm_num),
    Nat.maxPrimeFac_mul (by norm_num) (by norm_num),
    Nat.maxPrimeFac_mul (by norm_num) (by norm_num)]
  simp only [Nat.maxPrimeFac_pow (by decide : 2 ≠ 0),
    Nat.maxPrimeFac_pow (by decide : 3 ≠ 0), max_lt_iff]
  iterate 4 apply And.intro
  all_goals exact Nat.maxPrimeFac_le.trans_lt (by decide)

/-- The gap between 149,973,611 and 149,973,667 is consecutive in the prime
sequence and contains two integers with largest prime factor below 56. -/
theorem exists_two_hit_prime_index :
    ∃ r : ℕ, (Nat.nth Nat.Prime r = 149973611) ∧
      (Nat.nth Nat.Prime (r + 1) = 149973667) ∧
      2 ≤ ((Finset.Ioo (Nat.nth Nat.Prime r) (Nat.nth Nat.Prime (r + 1))).filter
        (fun m => m.maxPrimeFac < Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r)).card := by
  obtain ⟨r, hr⟩ := Nat.subset_range_nth (p := Nat.Prime) left_prime
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hsuccPrime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (r + 1)
  have hlt : 149973611 < Nat.nth Nat.Prime (r + 1) := hr ▸ hmono r.lt_succ_self
  have hupper : Nat.nth Nat.Prime (r + 1) ≤ 149973667 := by
    by_contra h
    have hcontra := Nat.le_nth_of_lt_nth_succ (p := Nat.Prime) (lt_of_not_ge h) right_prime
    omega
  have hnext : Nat.nth Nat.Prime (r + 1) = 149973667 := by
    by_contra h
    exact interior_not_prime _ hlt (lt_of_le_of_ne hupper h) hsuccPrime
  refine ⟨r, hr, hnext, ?_⟩
  rw [hr, hnext]
  have hsmall :
      ({149973616, 149973660} : Finset ℕ) ⊆
        (Finset.Ioo 149973611 149973667).filter (fun m => m.maxPrimeFac < 56) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by norm_num, hit_left⟩
    · exact Finset.mem_filter.mpr ⟨by norm_num, hit_right⟩
  exact (by simpa using Finset.card_le_card hsmall)

end Implications.SmoothGapWitness150m

#print axioms Implications.SmoothGapWitness150m.exists_two_hit_prime_index
