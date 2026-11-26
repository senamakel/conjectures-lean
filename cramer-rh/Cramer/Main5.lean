import Cramer.Statement4
import Cramer.Main
import Cramer.Shift.Large
import Cramer.Shift.Small
import Cramer.Shift.Facts

/-!
# Cramér's theorem under RH with constant `107/100`: the headline theorems

* `primeInShortInterval_107_of_RH : PrimeInShortInterval (107/100)` — every
  `(x, x + (107/100)√x log x]`, `x ≥ 2`, contains a prime (analytic for `x ≥ 10^8`,
  `Cramer.Shift.Large`, with the shifted-Lorentzian majorant `maj107`; a checked chain of 1176
  primes below, `Cramer.Shift.Small`);
* `primeGapExplicit_107_of_RH : PrimeGapExplicit (107/100)` —
  `p_{n+1} − p_n ≤ (107/100)√p_n log p_n` for every `n`;
* `primeInClosedInterval_107_of_RH : PrimeInClosedInterval 2 (107/100)` — the closed-interval
  form of `Cramer/Statement4.lean` with `107/100` and `x ≥ 2`. The constant `22/25` of
  Carneiro–Milinovich–Soundararajan (`CMSPrimeInterval`) is not proved.
-/

namespace Cramer

/-- **Under RH, every interval `(x, x + (107/100)√x log x]` with `x ≥ 2` contains a prime.** -/
theorem primeInShortInterval_107_of_RH (hRH : RiemannHypothesis) :
    PrimeInShortInterval (107 / 100) := by
  intro x hx
  rcases lt_or_ge x (10 ^ 8) with h | h
  · exact Shift.exists_prime_small_107 hx h
  · exact Shift.exists_prime_of_RH_large_shift hRH Shift.good107 Shift.buckets107 Shift.SS107
      Shift.NS107 h

/-- **Under RH, `p_{n+1} − p_n ≤ (107/100) √p_n log p_n` for every `n`.** -/
theorem primeGapExplicit_107_of_RH (hRH : RiemannHypothesis) :
    PrimeGapExplicit (107 / 100) := by
  intro n
  set p := Nat.nth Nat.Prime n
  have hp : p.Prime := Nat.prime_nth_prime n
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨q, hq, hpq, hqle⟩ := primeInShortInterval_107_of_RH hRH p hp2
  have hnext := nth_succ_le_of_prime hq (by exact_mod_cast hpq)
  have hlt : p < Nat.nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  unfold primeGap
  rw [Nat.cast_sub hlt.le]
  have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ q := by exact_mod_cast hnext
  linarith

/-- **Under RH, every closed interval `[x, x + (107/100)√x log x]` with `x ≥ 2` contains a prime.** -/
theorem primeInClosedInterval_107_of_RH (hRH : RiemannHypothesis) :
    PrimeInClosedInterval 2 (107 / 100) := by
  intro x hx
  obtain ⟨p, hp, h1, h2⟩ := primeInShortInterval_107_of_RH hRH x hx
  exact ⟨p, hp, h1.le, h2⟩

end Cramer
