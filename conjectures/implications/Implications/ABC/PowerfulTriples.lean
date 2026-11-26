import Implications.ABC.Variants

/-!
# Consecutive powerful triples under the abc conjecture

formal-conjectures `Erdos364.erdos_364` (`FormalConjectures/ErdosProblems/364.lean`, commit
`9097e2f`) states that **no** three consecutive integers are all powerful:

```
theorem erdos_364 :
    ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2)
```

abc cannot give "none", only "finitely many". `Erdos364.FinitelyManyPowerfulTriples` is
**our statement** of that finiteness version (it is not in formal-conjectures), with
formal-conjectures' `Nat.Powerful` (copied verbatim in `Implications.ABC.Statement`).
`erdos_364` implies it trivially; it does not imply `erdos_364`.

Deduction (folklore; erdosproblems.com/364 says abc implies finitely many): apply abc at
`ε = 1/4` to `(1, n(n+2), (n+1)²)`, which is coprime since `(n+1)² = n(n+2) + 1`. If `n, n+1, n+2`
are powerful, `rad(abc) ≤ rad n · rad(n+1) · rad(n+2) =: X` and `X² ≤ n(n+1)(n+2) < (n+1)³`,
so `X⁵ < (n+1)^8 = c⁴`, i.e. `X^(1+1/4) < c`.
-/

namespace Erdos364

open Nat

/-- **Our statement** (not in formal-conjectures): only finitely many `n` have `n`, `n + 1`,
`n + 2` all powerful. The finiteness weakening of `erdos_364`. -/
def FinitelyManyPowerfulTriples : Prop :=
  {n : ℕ | Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2)}.Finite

end Erdos364

namespace Implications.Abc

open _root_.ABC Erdos364 Nat

/-- abc implies that only finitely many triples of consecutive integers are all powerful. -/
theorem finitelyManyPowerfulTriples_of_abc (habc : ABCConjecture) :
    FinitelyManyPowerfulTriples := by
  refine finite_of_abc habc (by norm_num : (0 : ℝ) < 1 / ((4 : ℕ) : ℝ)) _
    (fun n => (1, n * (n + 2), (n + 1) ^ 2)) 1 (fun n hn hP => ?_)
    (fun n => by
      show n ≤ (n + 1) ^ 2
      nlinarith)
  obtain ⟨h0, h1, h2⟩ := hP
  have hn0 : n ≠ 0 := by omega
  have hsq : (n + 1) ^ 2 = n * (n + 2) + 1 := by ring
  have hcop : Nat.Coprime (n * (n + 2)) ((n + 1) ^ 2) := by
    rw [hsq]; exact coprime_self_succ _
  refine mem_abcSet_of_pow_lt (k := 4) (X := radical n * radical (n + 2) * radical (n + 1))
    (by norm_num) Nat.one_pos (by positivity) (Nat.coprime_one_left _) (Nat.coprime_one_left _)
    hcop (by rw [hsq]; ring) ?_ ?_
  · rw [one_mul, radical_mul hcop, radical_pow (by norm_num)]
    exact Nat.mul_le_mul_right _ (radical_mul_le hn0 (by omega))
  · -- `X² ≤ n (n+2) (n+1) < (n+1)³`
    have hX2 : (radical n * radical (n + 2) * radical (n + 1)) ^ 2 ≤ n * (n + 2) * (n + 1) := by
      rw [mul_pow, mul_pow]
      exact Nat.mul_le_mul (Nat.mul_le_mul (radical_sq_le_of_powerful hn0 h0)
        (radical_sq_le_of_powerful (by omega) h2)) (radical_sq_le_of_powerful (by omega) h1)
    have hP3 : n * (n + 2) * (n + 1) < (n + 1) ^ 3 := by
      have : n * (n + 2) < (n + 1) ^ 2 := by nlinarith
      calc n * (n + 2) * (n + 1) < (n + 1) ^ 2 * (n + 1) :=
            Nat.mul_lt_mul_of_pos_right this (by omega)
        _ = (n + 1) ^ 3 := by ring
    set X := radical n * radical (n + 2) * radical (n + 1)
    have h10 : (X ^ 5) ^ 2 < (((n + 1) ^ 2) ^ 4) ^ 2 := by
      calc (X ^ 5) ^ 2 = (X ^ 2) ^ 5 := by ring
        _ ≤ (n * (n + 2) * (n + 1)) ^ 5 := Nat.pow_le_pow_left hX2 5
        _ < ((n + 1) ^ 3) ^ 5 := Nat.pow_lt_pow_left hP3 (by norm_num)
        _ ≤ (((n + 1) ^ 2) ^ 4) ^ 2 := by
          rw [← pow_mul, ← pow_mul, ← pow_mul]
          exact Nat.pow_le_pow_right (by omega) (by norm_num)
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h10

end Implications.Abc
