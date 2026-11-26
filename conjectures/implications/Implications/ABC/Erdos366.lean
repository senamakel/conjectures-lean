import Implications.ABC.Variants

/-!
# Erdős 366 under the abc conjecture: finiteness forms

formal-conjectures (`FormalConjectures/ErdosProblems/366.lean`, commit `9097e2f`) asks two
existence questions, both open there:

```
theorem erdos_366 : ∃ n > 0, (2).Full n ∧ (3).Full (n + 1)
theorem erdos_366.variants.weaker : ∃ n > 0, (3).Full n ∧ (3).Full (n + 1)
```

and records (`erdos_366.variants.three_two`, solved) that `(3).Full n ∧ (2).Full (n + 1)` has
solutions besides `n = 8`. abc says nothing about existence. What it gives is finiteness, so the
three definitions below are **our statements** (not in formal-conjectures), with
formal-conjectures' `Nat.Full` (copied verbatim in `Implications.ABC.Statement`). Each set
contains `n = 0` (since `0` is vacuously `k`-full), which does not affect finiteness.

Deduction (Turturean, erdosproblems.com/366 comments, unverified; folklore): apply abc to
`(n, 1, n + 1)`, where `rad(abc) = rad n · rad (n+1) =: X` and `rad(m)^k ≤ m` for `k`-full `m`.
* `2`-full `n`, `3`-full `n+1`: `X⁶ ≤ n³ (n+1)² < (n+1)⁵`, so abc at `ε = 1/5`.
* `3`-full `n`, `2`-full `n+1`: `X⁶ ≤ n² (n+1)³ < (n+1)⁵`, so abc at `ε = 1/5`.
* `3`-full `n`, `3`-full `n+1`: `X³ ≤ n (n+1) < (n+1)²`, so abc at `ε = 1/2`.
-/

namespace Erdos366

open Nat

/-- **Our statement**: only finitely many `n` are `2`-full with `n + 1` `3`-full (finiteness
companion of `erdos_366`). -/
def TwoThreeFinite : Prop := {n : ℕ | (2).Full n ∧ (3).Full (n + 1)}.Finite

/-- **Our statement**: only finitely many `n` are `3`-full with `n + 1` `2`-full (finiteness
companion of `erdos_366.variants.three_two`). -/
def ThreeTwoFinite : Prop := {n : ℕ | (3).Full n ∧ (2).Full (n + 1)}.Finite

/-- **Our statement**: only finitely many pairs of consecutive `3`-full integers (finiteness
companion of `erdos_366.variants.weaker`). -/
def ThreeThreeFinite : Prop := {n : ℕ | (3).Full n ∧ (3).Full (n + 1)}.Finite

end Erdos366

namespace Implications.Abc

open _root_.ABC Erdos366 Nat

/-- The common step: for `n ≥ 1`, a bound `X^(k+1) < (n+1)^k` with
`X = rad n · rad (n+1)` puts `(n, 1, n+1)` in the exceptional set at `ε = 1/k`. -/
lemma mem_abcSet_consecutive {n k : ℕ} (hk : 0 < k) (hn : 1 ≤ n)
    (h : (radical n * radical (n + 1)) ^ (k + 1) < (n + 1) ^ k) :
    (n, 1, n + 1) ∈ abcSet (1 / (k : ℝ)) := by
  refine mem_abcSet_of_pow_lt hk hn Nat.one_pos (Nat.coprime_one_right _) (coprime_self_succ _)
    (Nat.coprime_one_left _) rfl (le_of_eq ?_) h
  rw [mul_one, radical_mul (coprime_self_succ _)]

/-- abc implies only finitely many `2`-full `n` with `n + 1` `3`-full. -/
theorem twoThreeFinite_of_abc (habc : ABCConjecture) : TwoThreeFinite := by
  refine finite_of_abc habc (by norm_num : (0 : ℝ) < 1 / ((5 : ℕ) : ℝ)) _
    (fun n => (n, 1, n + 1)) 1 (fun n hn hP => mem_abcSet_consecutive (by norm_num) hn ?_)
    (fun n => Nat.le_succ n)
  obtain ⟨h2, h3⟩ := hP
  have hA := radical_pow_le_of_full (by omega) h2
  have hB := radical_pow_le_of_full (by omega) h3
  calc (radical n * radical (n + 1)) ^ (5 + 1)
      = (radical n ^ 2) ^ 3 * (radical (n + 1) ^ 3) ^ 2 := by ring
    _ ≤ n ^ 3 * (n + 1) ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left hA 3)
        (Nat.pow_le_pow_left hB 2)
    _ < (n + 1) ^ 3 * (n + 1) ^ 2 :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by omega) (by norm_num)) (by positivity)
    _ = (n + 1) ^ 5 := by ring

/-- abc implies only finitely many `3`-full `n` with `n + 1` `2`-full. -/
theorem threeTwoFinite_of_abc (habc : ABCConjecture) : ThreeTwoFinite := by
  refine finite_of_abc habc (by norm_num : (0 : ℝ) < 1 / ((5 : ℕ) : ℝ)) _
    (fun n => (n, 1, n + 1)) 1 (fun n hn hP => mem_abcSet_consecutive (by norm_num) hn ?_)
    (fun n => Nat.le_succ n)
  obtain ⟨h3, h2⟩ := hP
  have hA := radical_pow_le_of_full (by omega) h3
  have hB := radical_pow_le_of_full (by omega) h2
  calc (radical n * radical (n + 1)) ^ (5 + 1)
      = (radical n ^ 3) ^ 2 * (radical (n + 1) ^ 2) ^ 3 := by ring
    _ ≤ n ^ 2 * (n + 1) ^ 3 := Nat.mul_le_mul (Nat.pow_le_pow_left hA 2)
        (Nat.pow_le_pow_left hB 3)
    _ < (n + 1) ^ 2 * (n + 1) ^ 3 :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by omega) (by norm_num)) (by positivity)
    _ = (n + 1) ^ 5 := by ring

/-- abc implies only finitely many pairs of consecutive `3`-full integers. -/
theorem threeThreeFinite_of_abc (habc : ABCConjecture) : ThreeThreeFinite := by
  refine finite_of_abc habc (by norm_num : (0 : ℝ) < 1 / ((2 : ℕ) : ℝ)) _
    (fun n => (n, 1, n + 1)) 1 (fun n hn hP => mem_abcSet_consecutive (by norm_num) hn ?_)
    (fun n => Nat.le_succ n)
  obtain ⟨hA3, hB3⟩ := hP
  have hA := radical_pow_le_of_full (by omega) hA3
  have hB := radical_pow_le_of_full (by omega) hB3
  calc (radical n * radical (n + 1)) ^ (2 + 1)
      = radical n ^ 3 * radical (n + 1) ^ 3 := by ring
    _ ≤ n * (n + 1) := Nat.mul_le_mul hA hB
    _ < (n + 1) * (n + 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    _ = (n + 1) ^ 2 := by ring

end Implications.Abc
