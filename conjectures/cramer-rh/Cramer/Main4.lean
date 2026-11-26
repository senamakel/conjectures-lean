import Cramer.Statement4
import Cramer.Main
import Cramer.Sharp.Large
import Cramer.Sharp.Small

/-!
# Cramér's theorem under RH with constant `3/2`: the headline theorems

* `primeInShortInterval_three_halves_of_RH : PrimeInShortInterval (3/2)` — every
  `(x, x + (3/2)√x log x]`, `x ≥ 2`, contains a prime (analytic for `x ≥ 6.4·10^7`,
  `Cramer.Sharp.Large`; a checked chain of 696 primes below, `Cramer.Sharp.Small`);
* `primeGapExplicit_three_halves_of_RH : PrimeGapExplicit (3/2)` —
  `p_{n+1} − p_n ≤ (3/2)√p_n log p_n` for every `n`;
* `primeInClosedInterval_three_halves_of_RH : PrimeInClosedInterval 2 (3/2)` — the closed-interval
  form of `Cramer/Statement4.lean` (Carneiro–Milinovich–Soundararajan's shape) with `3/2` and
  `x ≥ 2`. Their constant `22/25` (`CMSPrimeInterval`) is not proved.
-/

namespace Cramer

/-- **Under RH, every interval `(x, x + (3/2)√x log x]` with `x ≥ 2` contains a prime.** -/
theorem primeInShortInterval_three_halves_of_RH (hRH : RiemannHypothesis) :
    PrimeInShortInterval (3 / 2) := by
  intro x hx
  rcases lt_or_ge x (64 * 10 ^ 6) with h | h
  · exact exists_prime_small_32 hx h
  · exact exists_prime_of_RH_large_32 hRH h

/-- **Under RH, `p_{n+1} − p_n ≤ (3/2) √p_n log p_n` for every `n`.** -/
theorem primeGapExplicit_three_halves_of_RH (hRH : RiemannHypothesis) :
    PrimeGapExplicit (3 / 2) := by
  intro n
  set p := Nat.nth Nat.Prime n
  have hp : p.Prime := Nat.prime_nth_prime n
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨q, hq, hpq, hqle⟩ := primeInShortInterval_three_halves_of_RH hRH p hp2
  have hnext := nth_succ_le_of_prime hq (by exact_mod_cast hpq)
  have hlt : p < Nat.nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  unfold primeGap
  rw [Nat.cast_sub hlt.le]
  have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ q := by exact_mod_cast hnext
  linarith

/-- **Under RH, every closed interval `[x, x + (3/2)√x log x]` with `x ≥ 2` contains a prime.** -/
theorem primeInClosedInterval_three_halves_of_RH (hRH : RiemannHypothesis) :
    PrimeInClosedInterval 2 (3 / 2) := by
  intro x hx
  obtain ⟨p, hp, h1, h2⟩ := primeInShortInterval_three_halves_of_RH hRH x hx
  exact ⟨p, hp, h1.le, h2⟩

end Cramer
