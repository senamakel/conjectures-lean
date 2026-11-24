import Cramer.Statement
import Cramer.Large
import Cramer.Small

/-!
# Cramér's theorem under RH: the headline theorems

* `primeInShortInterval_of_RH : PrimeInShortInterval 2` — every `(x, x + 2√x log x]`, `x ≥ 2`,
  contains a prime (analytic for `x ≥ 10^6`, `Cramer.Large`; checked chain below, `Cramer.Small`);
* `primeGapExplicit_of_RH : PrimeGapExplicit 2` — `p_{n+1} − p_n ≤ 2 √p_n log p_n` for all `n`;
* `cramer_of_RH : CramerGapBound` — the formal-conjectures `O(√p_n log p_n)` statement.
-/

namespace Cramer

open Filter Asymptotics

/-- **Under RH, every interval `(x, x + 2√x log x]` with `x ≥ 2` contains a prime.** -/
theorem primeInShortInterval_of_RH (hRH : RiemannHypothesis) : PrimeInShortInterval 2 := by
  intro x hx
  rcases lt_or_ge x (10 ^ 6) with h | h
  · exact exists_prime_small hx h
  · exact exists_prime_of_RH_large hRH h

/-- The next prime after `p_n` is at most any prime larger than `p_n`. -/
lemma nth_succ_le_of_prime {n q : ℕ} (hq : q.Prime) (hlt : Nat.nth Nat.Prime n < q) :
    Nat.nth Nat.Prime (n + 1) ≤ q := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hq' : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  rw [← hq'] at hlt ⊢
  have : n < Nat.count Nat.Prime q := hmono.lt_iff_lt.mp hlt
  exact hmono.monotone (by omega)

/-- **Under RH, `p_{n+1} − p_n ≤ 2 √p_n log p_n` for every `n`.** -/
theorem primeGapExplicit_of_RH (hRH : RiemannHypothesis) : PrimeGapExplicit 2 := by
  intro n
  set p := Nat.nth Nat.Prime n
  have hp : p.Prime := Nat.prime_nth_prime n
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨q, hq, hpq, hqle⟩ := primeInShortInterval_of_RH hRH p hp2
  have hnext := nth_succ_le_of_prime hq (by exact_mod_cast hpq)
  have hlt : p < Nat.nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  unfold primeGap
  rw [Nat.cast_sub hlt.le]
  have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ q := by exact_mod_cast hnext
  linarith

/-- **Cramér (1920) under RH**: `p_{n+1} − p_n = O(√p_n log p_n)`, the statement of
formal-conjectures' `cramer_conjecture.variants.conditional_rh`. -/
theorem cramer_of_RH (hRH : RiemannHypothesis) : CramerGapBound := by
  unfold CramerGapBound
  refine IsBigO.of_bound 2 (Eventually.of_forall fun n => ?_)
  have h := primeGapExplicit_of_RH hRH n
  have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime n := by exact_mod_cast (Nat.prime_nth_prime n).two_le
  have hlog : 0 ≤ Real.log (Nat.nth Nat.Prime n) := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  linarith

end Cramer
