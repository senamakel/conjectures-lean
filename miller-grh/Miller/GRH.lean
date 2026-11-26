import Miller.Test
import Ankeny.Main

/-!
# Miller's test under GRH

`Ankeny.bach_of_GRH` (ankeny-grh) proves `BachSubgroupBound (21 / 5)` from GRH. The two
definitions of `BachSubgroupBound` are the same text, so it plugs straight into
`miller_of_bach`. With GRH supplied by leanprover-community/riemann-hypothesis
(`LFunction_ne_zero_of_half_lt_re`), these become unconditional.

The executable test uses `3 · millerBound n` bases, which is at least `(21/5) log² n`.
-/

namespace Miller

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- Under GRH every odd composite `n` has a strong-pseudoprime witness `a ≤ (21/5) log² n`. -/
theorem miller_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : MillerStatement (21 / 5) :=
  miller_of_bach (Ankeny.bach_of_GRH hGRH)

/-- Under GRH, the strong test on bases `0 < a < n` with `a ≤ (21/5) log² n` decides primality. -/
theorem prime_iff_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (n : ℕ) (hn : Odd n)
    (h1 : 1 < n) :
    n.Prime ↔ ∀ a : ℕ, 0 < a → a < n → (a : ℝ) ≤ 21 / 5 * Real.log n ^ 2 →
      IsStrongProbablePrime n a :=
  prime_iff_of_bach (Ankeny.bach_of_GRH hGRH) n hn h1

/-- An integer upper bound for `(21/5) log² n`. -/
def millerBoundGRH (n : ℕ) : ℕ := 3 * millerBound n

theorem log_sq_le_millerBoundGRH (n : ℕ) : 21 / 5 * Real.log n ^ 2 ≤ millerBoundGRH n := by
  have h := two_mul_log_sq_le_millerBound n
  have h0 : (0 : ℝ) ≤ Real.log n ^ 2 := sq_nonneg _
  simp only [millerBoundGRH, Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- The deterministic Miller test with the GRH constant `21/5`. -/
def millerTestGRH (n : ℕ) : Bool :=
  (List.range' 1 (min (n - 1) (millerBoundGRH n))).all (sppBool n)

/-- Under GRH, `millerTestGRH` is a correct primality test for odd `n > 1`. -/
theorem millerTestGRH_iff_prime (hGRH : DirichletLNonvanishingRightOfHalf) {n : ℕ} (hn : Odd n)
    (h1 : 1 < n) : millerTestGRH n = true ↔ n.Prime := by
  have hall : millerTestGRH n = true ↔
      ∀ a, 1 ≤ a → a ≤ min (n - 1) (millerBoundGRH n) → IsStrongProbablePrime n a := by
    rw [millerTestGRH, List.all_eq_true]
    simp only [List.mem_range'_1, sppBool_iff (by omega : 0 < n)]
    exact ⟨fun H a ha1 ha2 => H a ⟨ha1, by omega⟩, fun H a ha => H a ha.1 (by omega)⟩
  rw [hall]
  constructor
  · intro H
    refine (prime_iff_of_GRH hGRH n hn h1).mpr fun a ha0 han hac => H a ha0 ?_
    have : (a : ℝ) ≤ millerBoundGRH n := hac.trans (log_sq_le_millerBoundGRH n)
    exact le_min (by omega) (by exact_mod_cast this)
  · intro hp a ha1 ha2
    exact isStrongProbablePrime_of_prime hp ha1 (by omega)

#guard millerTestGRH 3215031751 = false
#guard millerTestGRH 2147483647 = true
#guard (List.range 1500).all fun k =>
  let n := 2 * k + 3
  millerTestGRH n == decide n.Prime

end Miller
