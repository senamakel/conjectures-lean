import Cramer.Statement

/-!
# Explicit prime gaps under RH: the Carneiro–Milinovich–Soundararajan form (target statements,
Round 7 — do not change the definitions)

E. Carneiro, M. B. Milinovich, K. Soundararajan, *Fourier optimization and prime gaps*,
Comment. Math. Helv. **94** (2019), 533–568, arXiv:1708.04122, Theorem 5 (read in the arXiv
source, version R1 of 2018-09-02):

> Assume the Riemann hypothesis. Then, for `x ≥ 4`, there is always a prime number in the
> interval `[x, x + (22/25)√x log x]`.

and, as stated just before it, `p_{n+1} − p_n ≤ (22/25)√p_n log p_n` for all primes `p_n > 3`.

The paper's interval is closed and its range is `x ≥ 4`, while `Cramer.PrimeInShortInterval c`
(`Cramer/Statement.lean`) uses `(x, x + c√x log x]` for `x ≥ 2`. The two do not agree for
`c = 22/25`: `(2, 2 + (22/25)√2 log 2] = (2, 2.86…]` contains no prime, so
`PrimeInShortInterval (22/25)` is false. The paper's form is therefore stated separately, with
the starting point as a parameter.
-/

namespace Cramer

/-- Every closed interval `[x, x + c√x log x]` with `x ≥ x₀` contains a prime. -/
def PrimeInClosedInterval (x₀ c : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + c * Real.sqrt x * Real.log x

/-- **Carneiro–Milinovich–Soundararajan (2019), Theorem 5**: under RH, every
`[x, x + (22/25)√x log x]` with `x ≥ 4` contains a prime. -/
def CMSPrimeInterval : Prop := PrimeInClosedInterval 4 (22 / 25)

/-- **Carneiro–Milinovich–Soundararajan (2019)**, gap form: `p_{n+1} − p_n ≤ (22/25)√p_n log p_n`
for every prime `p_n > 3`. -/
def CMSPrimeGap : Prop :=
  ∀ n : ℕ, 3 < Nat.nth Nat.Prime n → (primeGap n : ℝ) ≤
    22 / 25 * Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)

end Cramer
