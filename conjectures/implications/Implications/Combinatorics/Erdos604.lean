import Mathlib

/-!
# Erdős 604: the average form ⇒ the `n / √(log n)` form

The statements are copied word for word from formal-conjectures (commit `9097e2f`),
`FormalConjectures/ErdosProblems/604.lean`, with `Erdos604.pinnedDistinctDistances` from the same
file, `distinctDistancesFrom` from `FormalConjecturesForMathlib/Geometry/Metric.lean` and the
notation `ℝ²` from `FormalConjecturesForMathlib/Geometry/2d.lean` (Apache-2.0, © 2025 The Formal
Conjectures Authors):

* `Erdos604.erdos_604.variants.average` (research open; Erdős 1975), stated here as
  `Erdos604Average`: `∑_{x ∈ A} d(x) ≥ C n² / √(log n)` for every `n`-point set `A ⊂ ℝ²`;
* `Erdos604.erdos_604.variants.sqrt_log` (research open), stated here as `Erdos604SqrtLog`:
  `n / √(log n) = O(f(n))` for the pinned distance function `f`.

The deduction is the one in the docstring of `average`: the sum is at most `n` times the largest
`d(x)`. The infimum defining `f(n)` is attained (some `n`-point set exists), so a set `A` with
`max d(x) = f(n)` gives `C n² / √(log n) ≤ n f(n)`.
-/

open Filter
open scoped Finset

namespace Implications.Combinatorics.Erdos604

/-- The notation of formal-conjectures `9097e2f`, `FormalConjecturesForMathlib/Geometry/2d.lean`. -/
scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Classical in
/-- Verbatim from formal-conjectures `9097e2f`, `FormalConjecturesForMathlib/Geometry/Metric.lean`,
`distinctDistancesFrom`: the number of distinct distances between a given point and all other
points of a finite set. -/
noncomputable def distinctDistancesFrom {X : Type*} [MetricSpace X] (points : Finset X)
    (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

/-- Verbatim from formal-conjectures `9097e2f`, `Erdos604.pinnedDistinctDistances`: the pinned
distance function `f(n)`. -/
noncomputable def pinnedDistinctDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℝ², #A = n ∧ A.sup (distinctDistancesFrom A) = m}

/-- Verbatim from formal-conjectures `9097e2f`, `Erdos604.erdos_604.variants.sqrt_log`. -/
def Erdos604SqrtLog : Prop :=
    (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) =O[atTop]
      (fun n => (pinnedDistinctDistances n : ℝ))

/-- Verbatim from formal-conjectures `9097e2f`, `Erdos604.erdos_604.variants.average`. -/
def Erdos604Average : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n →
      C * (n : ℝ) ^ 2 / (n : ℝ).log.sqrt ≤ ((∑ x ∈ A, distinctDistancesFrom A x : ℕ) : ℝ)

/-- The infimum defining `pinnedDistinctDistances n` is attained. -/
theorem exists_sup_eq_pinnedDistinctDistances (n : ℕ) :
    ∃ A : Finset ℝ², #A = n ∧ A.sup (distinctDistancesFrom A) = pinnedDistinctDistances n := by
  have : Infinite ℝ² :=
    Infinite.of_injective (fun t : ℝ => EuclideanSpace.single (0 : Fin 2) t)
      (fun s t hst => by simpa using congrArg (fun v : ℝ² => v 0) hst)
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ² n
  exact Nat.sInf_mem (s := {m : ℕ | ∃ A : Finset ℝ², #A = n ∧
    A.sup (distinctDistancesFrom A) = m}) ⟨_, A, hA, rfl⟩

/-- **Erdős 604, average form ⇒ `n / √(log n)` form.** -/
theorem erdos604SqrtLog_of_average (h : Erdos604Average) : Erdos604SqrtLog := by
  obtain ⟨C, hC, hev⟩ := h
  refine Asymptotics.IsBigO.of_bound C⁻¹ ?_
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨A, hA, hsup⟩ := exists_sup_eq_pinnedDistinctDistances n
  have hsum : (∑ x ∈ A, distinctDistancesFrom A x : ℕ) ≤ n * pinnedDistinctDistances n := by
    rw [← hsup, ← hA]
    exact Finset.sum_le_card_nsmul _ _ _ fun x hx => Finset.le_sup (f := distinctDistancesFrom A) hx
  have hsumR : ((∑ x ∈ A, distinctDistancesFrom A x : ℕ) : ℝ) ≤
      (n : ℝ) * (pinnedDistinctDistances n : ℝ) := by exact_mod_cast hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set s := (n : ℝ).log.sqrt
  have key : (n : ℝ) * (C * ((n : ℝ) / s)) ≤ (n : ℝ) * (pinnedDistinctDistances n : ℝ) := by
    have := (hn A hA).trans hsumR
    calc (n : ℝ) * (C * ((n : ℝ) / s)) = C * (n : ℝ) ^ 2 / s := by ring
      _ ≤ _ := this
  have key' : C * ((n : ℝ) / s) ≤ (pinnedDistinctDistances n : ℝ) :=
    le_of_mul_le_mul_left key hnpos
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hq : 0 ≤ (n : ℝ) / s := div_nonneg hnpos.le hs
  rw [Real.norm_of_nonneg hq, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [le_inv_mul_iff₀ hC]
  exact key'

end Implications.Combinatorics.Erdos604
