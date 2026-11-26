import BachCorollaries.SolovayStrassen
import BachCorollaries.Jacobi
import Miller.Test

/-!
# An executable deterministic Solovay–Strassen test

`solovayStrassenTest n` checks, for every base `1 ≤ a ≤ min (n - 1) (millerBound n)`, that
`gcd(a, n) = 1` and `a^((n-1)/2) ≡ (a/n) (mod n)`, using miller-grh's `powMod` and the binary
Jacobi algorithm `jacobiCalc`. `millerBound n = (⌊log₂ n⌋ + 1)²` is an integer upper bound for
`2 log² n` (miller-grh, `Miller.two_mul_log_sq_le_millerBound`). Under `BachSubgroupBound 2`
the test is correct for every odd `n > 1` (`solovayStrassenTest_iff_prime`).
-/

namespace BachCorollaries

/-- Decides `a.Coprime n ∧ IsEulerProbablePrime n a` for odd `n`. -/
def eulerBool (n a : ℕ) : Bool :=
  Nat.gcd a n == 1 &&
    ((Miller.powMod a ((n - 1) / 2) n : ℕ) - jacobiCalc a n : ℤ) % (n : ℤ) == 0

theorem eulerBool_iff {n : ℕ} (hn : Odd n) (a : ℕ) :
    eulerBool n a = true ↔ a.Coprime n ∧ IsEulerProbablePrime n a := by
  rw [eulerBool, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  refine and_congr Iff.rfl ?_
  rw [jacobiCalc_eq a n hn, ← Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_eq_intCast_iff_dvd_sub,
    Int.cast_natCast, Miller.powMod_cast, IsEulerProbablePrime, eq_comm]

/-- The deterministic Solovay–Strassen test with Bach's constant `2`. -/
def solovayStrassenTest (n : ℕ) : Bool :=
  (List.range' 1 (min (n - 1) (Miller.millerBound n))).all (eulerBool n)

/-- **Correctness of the deterministic Solovay–Strassen test** under Bach's bound with
constant `2`, for every odd `n > 1`. -/
theorem solovayStrassenTest_iff_prime (h : Ankeny.BachSubgroupBound 2) {n : ℕ} (hn : Odd n)
    (h1 : 1 < n) : solovayStrassenTest n = true ↔ n.Prime := by
  have hall : solovayStrassenTest n = true ↔
      ∀ a, 1 ≤ a → a ≤ min (n - 1) (Miller.millerBound n) →
        a.Coprime n ∧ IsEulerProbablePrime n a := by
    rw [solovayStrassenTest, List.all_eq_true]
    simp only [List.mem_range'_1, eulerBool_iff hn]
    exact ⟨fun H a ha1 ha2 => H a ⟨ha1, by omega⟩, fun H a ha => H a ha.1 (by omega)⟩
  rw [hall, prime_iff_euler_of_bach h hn h1]
  constructor
  · intro H a ha0 han hac
    have : (a : ℝ) ≤ Miller.millerBound n :=
      hac.trans (Miller.two_mul_log_sq_le_millerBound n)
    exact H a ha0 (le_min (by omega) (by exact_mod_cast this))
  · intro H a ha1 ha2
    have hp : n.Prime := (prime_iff_euler_of_bach h hn h1).mpr fun b hb0 hbn hbc => H b hb0 hbn hbc
    exact ⟨Nat.Coprime.symm (Nat.coprime_of_lt_prime (by omega) (by omega) hp),
      isEulerProbablePrime_of_prime hp (by rintro rfl; exact absurd hn (by decide)) a⟩

/-! ### Sanity checks (evaluated by the interpreter; they add no axioms) -/

-- `jacobiCalc` agrees with known values.
#guard jacobiCalc 1001 9907 = -1
#guard jacobiCalc 19 45 = 1
#guard jacobiCalc 8 21 = -1
#guard jacobiCalc 5 21 = 1
#guard jacobiCalc 21 3 = 0
-- Carmichael numbers and strong pseudoprimes are rejected.
#guard solovayStrassenTest 561 = false
#guard solovayStrassenTest 1105 = false
#guard solovayStrassenTest 1729 = false        -- Carmichael number
#guard solovayStrassenTest 3215031751 = false  -- strong pseudoprime to bases 2, 3, 5, 7
#guard solovayStrassenTest 9 = false
#guard solovayStrassenTest 15 = false
-- Primes are accepted.
#guard solovayStrassenTest 3 = true
#guard solovayStrassenTest 97 = true
#guard solovayStrassenTest 7919 = true
#guard solovayStrassenTest 2147483647 = true   -- 2^31 - 1
#guard solovayStrassenTest 1000000007 = true
-- Agreement with `Nat.Prime` on all odd numbers below 3000.
#guard (List.range 1500).all fun k =>
  let n := 2 * k + 3
  solovayStrassenTest n == decide n.Prime

end BachCorollaries
