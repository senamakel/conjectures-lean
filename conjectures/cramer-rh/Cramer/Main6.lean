import Cramer.Statement4
import Cramer.Main
import Cramer.CMS.Large
import Cramer.CMS.Small

/-!
# The Carneiro–Milinovich–Soundararajan constant `22/25`: the headline theorems

* `cmsPrimeInterval_of_RH : RiemannHypothesis → CMSPrimeInterval` — every
  `[x, x + (22/25)√x log x]`, `x ≥ 4`, contains a prime (Carneiro–Milinovich–Soundararajan 2019,
  Theorem 5). The prime is even `> x` once `x ≥ 5` (`primeInShortInterval_cms_of_RH`). For
  `x ≥ 10⁸` this is `Cramer.CMS.exists_prime_large_cms` (the CMS weight, Brun–Titchmarsh outside
  the gap, the certified zero sum); below, a checked chain of 1426 primes (`Cramer.CMS.Small`),
  and `5` for `4 ≤ x < 5`.
* `cmsPrimeGap_of_RH : RiemannHypothesis → CMSPrimeGap` —
  `p_{n+1} − p_n ≤ (22/25)√p_n log p_n` for every prime `p_n > 3`.
-/

namespace Cramer

/-- **Under RH, `(x, x + (22/25)√x log x]` contains a prime for every `x ≥ 5`.** -/
theorem primeInShortInterval_cms_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 5 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 22 / 25 * Real.sqrt x * Real.log x := by
  rcases lt_or_ge x (10 ^ 8) with h | h
  · exact CMS.exists_prime_small_cms hx h
  · exact CMS.exists_prime_large_cms hRH (by norm_num at h ⊢; linarith)

/-- **Carneiro–Milinovich–Soundararajan (2019), Theorem 5, under RH**: every
`[x, x + (22/25)√x log x]` with `x ≥ 4` contains a prime. -/
theorem cmsPrimeInterval_of_RH (hRH : RiemannHypothesis) : CMSPrimeInterval := by
  intro x hx
  rcases lt_or_ge x 5 with h | h
  · refine ⟨5, by norm_num, by push_cast; linarith, ?_⟩
    have hs : 2 ≤ Real.sqrt x := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hx
    have hl : 1.38 ≤ Real.log x := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_le_log (by norm_num) hx
      have := Real.log_two_gt_d9
      linarith
    have : 2 * 1.38 ≤ Real.sqrt x * Real.log x := mul_le_mul hs hl (by norm_num) (by linarith)
    push_cast
    nlinarith
  · obtain ⟨p, hp, h1, h2⟩ := primeInShortInterval_cms_of_RH hRH h
    exact ⟨p, hp, h1.le, h2⟩

/-- **Carneiro–Milinovich–Soundararajan (2019), gap form, under RH**:
`p_{n+1} − p_n ≤ (22/25)√p_n log p_n` for every prime `p_n > 3`. -/
theorem cmsPrimeGap_of_RH (hRH : RiemannHypothesis) : CMSPrimeGap := by
  intro n h3
  set p := Nat.nth Nat.Prime n
  have hp : p.Prime := Nat.prime_nth_prime n
  have hp5 : (5 : ℝ) ≤ p := by
    have : 4 ≤ p := h3
    have : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have : 5 ≤ p := by omega
    exact_mod_cast this
  obtain ⟨q, hq, hpq, hqle⟩ := primeInShortInterval_cms_of_RH hRH hp5
  have hnext := nth_succ_le_of_prime hq (by exact_mod_cast hpq)
  have hlt : p < Nat.nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  unfold primeGap
  rw [Nat.cast_sub hlt.le]
  have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ q := by exact_mod_cast hnext
  linarith

end Cramer
