/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/
import OeisA245211.Basic

/-!
# OEIS A245211: The Fundamental Dominance Inequality and Parity Exclusions

Establishes general point-sampling lower bounds for `sumUpTo` and `sumDivUpTo`, derives
divisor-count bounds $\tau(m) \ge 2$ (for $m > 1$) and $\tau(m) \ge 3$ (when $m$ possesses a proper
divisor $1 < d < m$), and proves the Fundamental Dominance Theorem (`gt_self_of_dvd_le_tau`):
whenever $n = k \cdot m$ with $1 < k$, $1 < m$, and $k \le \tau(m)$, the proper divisors $1$ and $m$
alone force $a(n) \ge 1 + m \cdot \tau(m) \ge n + 1 > n$.

As immediate unconditional consequences:
- Every even integer $n > 2$ satisfies $a(n) \ge n + 1 > n$ (`a_gt_self_of_even_gt_two`).
- No even integer $n \ge 1$ satisfies $a(n) = n$ (`ne_self_of_even`, `not_isFixedPoint_of_even`).
- Every fixed point of OEIS A245211 is odd (`odd_of_isFixedPoint`).
- Every multiple of $3$ of the form $n = 3m$ where $m$ is composite satisfies $a(3m) \ge 3m + 1 > 3m$
  (`a_three_mul_ge_of_proper_divisor`).
-/

namespace OeisA245211

section SumLowerBounds

theorem sumUpTo_mono (f : Nat → Nat) {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) :
    sumUpTo f k₁ ≤ sumUpTo f k₂ := by
  induction k₂ with
  | zero =>
    have : k₁ = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ m ih =>
    by_cases hlt : k₁ ≤ m
    · have hih := ih hlt
      have hstep : sumUpTo f (m + 1) = sumUpTo f m + f (m + 1) := sumUpTo_succ f m
      omega
    · have heq : k₁ = m + 1 := by omega
      subst heq
      exact Nat.le_refl _

theorem le_sumUpTo_self (f : Nat → Nat) {i : Nat} (hi : 1 ≤ i) :
    f i ≤ sumUpTo f i := by
  cases i with
  | zero => omega
  | succ m =>
    rw [sumUpTo_succ]
    omega

/-- Single-term lower bound: for `1 ≤ i ≤ k`, `f i ≤ sumUpTo f k`. -/
theorem le_sumUpTo (f : Nat → Nat) {i k : Nat} (hi : 1 ≤ i) (hik : i ≤ k) :
    f i ≤ sumUpTo f k :=
  Nat.le_trans (le_sumUpTo_self f hi) (sumUpTo_mono f hik)

/-- Two-term lower bound: for `1 ≤ i < j ≤ k`, `f i + f j ≤ sumUpTo f k`. -/
theorem add_le_sumUpTo (f : Nat → Nat) {i j k : Nat}
    (hi : 1 ≤ i) (hij : i < j) (hjk : j ≤ k) :
    f i + f j ≤ sumUpTo f k := by
  cases j with
  | zero => omega
  | succ m =>
    have him : i ≤ m := by omega
    have h1 : f i ≤ sumUpTo f m := le_sumUpTo f hi him
    have h2 : sumUpTo f (m + 1) = sumUpTo f m + f (m + 1) := sumUpTo_succ f m
    have h3 : sumUpTo f (m + 1) ≤ sumUpTo f k := sumUpTo_mono f hjk
    omega

/-- Three-term lower bound: for `1 ≤ i < j < l ≤ k`, `f i + f j + f l ≤ sumUpTo f k`. -/
theorem add_three_le_sumUpTo (f : Nat → Nat) {i j l k : Nat}
    (hi : 1 ≤ i) (hij : i < j) (hjl : j < l) (hlk : l ≤ k) :
    f i + f j + f l ≤ sumUpTo f k := by
  cases l with
  | zero => omega
  | succ m =>
    have hjm : j ≤ m := by omega
    have h1 : f i + f j ≤ sumUpTo f m := add_le_sumUpTo f hi hij hjm
    have h2 : sumUpTo f (m + 1) = sumUpTo f m + f (m + 1) := sumUpTo_succ f m
    have h3 : sumUpTo f (m + 1) ≤ sumUpTo f k := sumUpTo_mono f hlk
    omega

end SumLowerBounds

section TauAndProperMomentBounds

/-- For `0 < n`, `1 ≤ tau n` since `1 ∣ n`. -/
theorem tau_pos {n : Nat} (hn : 0 < n) : 1 ≤ tau n := by
  unfold tau sumDiv sumDivUpTo
  have h1 := le_sumUpTo (fun d => if dividesB d n then 1 else 0) (Nat.le_refl 1) hn
  rw [dividesB_one] at h1
  exact h1

/-- For `1 < m`, `2 ≤ tau m` since `1` and `m` are distinct positive divisors of `m`. -/
theorem tau_ge_two {m : Nat} (hm : 1 < m) : 2 ≤ tau m := by
  unfold tau sumDiv sumDivUpTo
  have h12 := add_le_sumUpTo (fun d => if dividesB d m then 1 else 0)
    (Nat.le_refl 1) hm (Nat.le_refl m)
  rw [dividesB_one, dividesB_self (by omega)] at h12
  exact h12

/-- If `m` has a proper divisor `1 < d < m`, then `3 ≤ tau m` since `1 < d < m` all divide `m`. -/
theorem tau_ge_three_of_proper_divisor {d m : Nat}
    (hd1 : 1 < d) (hdm : d < m) (hdvd : d ∣ m) : 3 ≤ tau m := by
  unfold tau sumDiv sumDivUpTo
  have h123 := add_three_le_sumUpTo (fun x => if dividesB x m then 1 else 0)
    (Nat.le_refl 1) hd1 hdm (Nat.le_refl m)
  have hdivd : dividesB d m = true := (dividesB_eq_true d m).mpr ⟨by omega, hdvd⟩
  rw [dividesB_one, hdivd, dividesB_self (by omega)] at h123
  exact h123

/-- Single proper-divisor lower bound on `a n`: if `1 ≤ d < n` and `d ∣ n`, then `d * tau d ≤ a n`. -/
theorem a_ge_single_properDiv {d n : Nat}
    (hd1 : 1 ≤ d) (hdn : d < n) (hdvd : d ∣ n) :
    d * tau d ≤ a n := by
  unfold a sumProperDiv sumDivUpTo
  have hle : d ≤ n - 1 := by omega
  have h := le_sumUpTo (fun x => if dividesB x n then x * tau x else 0) hd1 hle
  have hdiv : dividesB d n = true := (dividesB_eq_true d n).mpr ⟨by omega, hdvd⟩
  rw [hdiv] at h
  exact h

/-- Two proper-divisor lower bound on `a n` using `1` and `d`:
if `1 < d < n` and `d ∣ n`, then `1 + d * tau d ≤ a n`. -/
theorem a_ge_one_add_properDiv {d n : Nat}
    (hd1 : 1 < d) (hdn : d < n) (hdvd : d ∣ n) :
    1 + d * tau d ≤ a n := by
  unfold a sumProperDiv sumDivUpTo
  have hle : d ≤ n - 1 := by omega
  have h := add_le_sumUpTo (fun x => if dividesB x n then x * tau x else 0)
    (Nat.le_refl 1) hd1 hle
  have hdiv : dividesB d n = true := (dividesB_eq_true d n).mpr ⟨by omega, hdvd⟩
  rw [dividesB_one, tau_1, hdiv] at h
  simpa using h

/-- **Fundamental Dominance Theorem**:
If `n = k * m` with `1 < k`, `1 < m`, and `k ≤ tau m`, then `n + 1 ≤ a n`. -/
theorem gt_self_of_dvd_le_tau {k m n : Nat}
    (hkm : n = k * m) (hk : 1 < k) (hm : 1 < m) (htau : k ≤ tau m) :
    n + 1 ≤ a n := by
  have hmn : m < n := by
    subst hkm
    have : 1 * m < k * m := Nat.mul_lt_mul_of_pos_right hk (by omega)
    omega
  have hdvd : m ∣ n := ⟨k, by rw [Nat.mul_comm]; exact hkm⟩
  have hlow := a_ge_one_add_properDiv hm hmn hdvd
  have hmul : n ≤ m * tau m := by
    rw [hkm, Nat.mul_comm]
    exact Nat.mul_le_mul_left m htau
  omega

/-- Corollary of the Fundamental Dominance Theorem: under the same hypotheses, `¬ IsFixedPoint n`. -/
theorem not_isFixedPoint_of_dvd_le_tau {k m n : Nat}
    (hkm : n = k * m) (hk : 1 < k) (hm : 1 < m) (htau : k ≤ tau m) :
    ¬ IsFixedPoint n := by
  have hgt := gt_self_of_dvd_le_tau hkm hk hm htau
  rintro ⟨_, ha⟩
  omega

end TauAndProperMomentBounds

section EvenAndThreeMulExclusions

/-- For every `m ≥ 2`, `2 * m + 1 ≤ a (2 * m)`. -/
theorem a_two_mul_ge {m : Nat} (hm : 2 ≤ m) :
    2 * m + 1 ≤ a (2 * m) :=
  gt_self_of_dvd_le_tau rfl (by decide) hm (tau_ge_two hm)

/-- Every even integer `n > 2` satisfies `n + 1 ≤ a n`. -/
theorem a_gt_self_of_even_gt_two {n : Nat} (hn : 2 < n) (heven : 2 ∣ n) :
    n + 1 ≤ a n := by
  rcases heven with ⟨m, rfl⟩
  have hm : 2 ≤ m := by omega
  exact a_two_mul_ge hm

/-- **Unconditional Even Exclusion Theorem**:
No positive even integer `n` satisfies `a n = n`. -/
theorem ne_self_of_even {n : Nat} (hn : 0 < n) (heven : 2 ∣ n) :
    a n ≠ n := by
  by_cases h2 : n = 2
  · subst h2
    decide
  · have hgt : 2 < n := by
      rcases heven with ⟨m, rfl⟩
      omega
    have := a_gt_self_of_even_gt_two hgt heven
    omega

/-- No even integer `n` is a fixed point of OEIS A245211. -/
theorem not_isFixedPoint_of_even {n : Nat} (heven : 2 ∣ n) :
    ¬ IsFixedPoint n := by
  rintro ⟨hn, ha⟩
  exact ne_self_of_even hn heven ha

/-- **Oddness of Fixed Points**:
Every fixed point `n` of OEIS A245211 is odd (`n % 2 = 1`). -/
theorem odd_of_isFixedPoint {n : Nat} (h : IsFixedPoint n) :
    n % 2 = 1 := by
  by_cases hmod : n % 2 = 0
  · have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hmod
    exact False.elim (not_isFixedPoint_of_even hdvd h)
  · omega

/-- Every multiple of `3` of the form `3 * m` where `m` has a proper divisor `1 < d < m`
satisfies `3 * m + 1 ≤ a (3 * m)`. -/
theorem a_three_mul_ge_of_proper_divisor {d m : Nat}
    (hd1 : 1 < d) (hdm : d < m) (hdvd : d ∣ m) :
    3 * m + 1 ≤ a (3 * m) :=
  gt_self_of_dvd_le_tau rfl (by decide) (by omega) (tau_ge_three_of_proper_divisor hd1 hdm hdvd)

/-- No integer `3 * m` with a composite cofactor `m` (`1 < d < m`, `d ∣ m`) is a fixed point. -/
theorem not_isFixedPoint_three_mul_of_proper_divisor {d m : Nat}
    (hd1 : 1 < d) (hdm : d < m) (hdvd : d ∣ m) :
    ¬ IsFixedPoint (3 * m) := by
  have hgt := a_three_mul_ge_of_proper_divisor hd1 hdm hdvd
  rintro ⟨_, ha⟩
  omega

end EvenAndThreeMulExclusions

end OeisA245211
