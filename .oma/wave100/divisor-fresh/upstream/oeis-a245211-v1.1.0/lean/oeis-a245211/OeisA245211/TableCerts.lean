/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/
import OeisA245211.Basic
import OeisA245211.Dominance
import OeisA245211.Families

/-!
# OEIS A245211 — Certified OEIS Table Values and Bounded Uniqueness

This module proves:
1. All 66 initial terms $a(1), \dots, a(66)$ listed in the `%S`, `%T`, and `%U`
   lines of `OEIS A245211` (subsuming all five `decide` theorems `a 1` through
   `a 5` in `google-deepmind/formal-conjectures:FormalConjectures/OEIS/245211.lean`).
2. Certified minimum-entry milestones for the companion sequences:
   - `OEIS A245213`: $n = 72$ ($a(72) = 802$, $72 \cdot \tau(72) = 864$,
     $\text{cantileverDiff}(72) = 62 < 72$) is the minimum positive integer
     satisfying $n \cdot \tau(n) - a(n) < n$.
   - `OEIS A245214`: $n = 144$ ($a(144) = 2226$, $144 \cdot \tau(144) = 2160$,
     $\text{cantileverDiff}(144) = -66 < 0$) is the minimum positive integer
     satisfying $n \cdot \tau(n) < a(n)$, certifying Krizek's 2014 OEIS remark.
3. Certified bounded uniqueness of the fixed point $n = 21$ across $1 \le n \le 150$:
   `fixedPoint_iff_eq_21_upto_150 : 1 ≤ n → n ≤ 150 → (IsFixedPoint n ↔ n = 21)`.
-/

namespace OeisA245211

/-! ## Complete `%S`, `%T`, `%U` Table of OEIS A245211 ($1 \le n \le 66$) -/

/-- The 66 initial values of OEIS A245211 ($n = 1, \dots, 66$). -/
def oeisA245211Table66 : List Nat :=
  [0, 1, 1, 5, 1, 11, 1, 17, 7, 15, 1, 47, 1, 19, 17, 49, 1, 62, 1, 67,
   21, 27, 1, 151, 11, 31, 34, 87, 1, 145, 1, 129, 29, 39, 25, 254, 1, 43, 33, 219,
   1, 189, 1, 127, 104, 51, 1, 423, 15, 130, 41, 147, 1, 278, 33, 287, 45, 63, 1, 589,
   1, 67, 132, 321, 37, 277]

/-- Verification that `(List.range 66).map (fun k => a (k + 1))` matches the
    66-term OEIS A245211 table (`%S`, `%T`, `%U`). -/
theorem map_a_range_66 :
    (List.range 66).map (fun k => a (k + 1)) = oeisA245211Table66 := by decide

/-- Individual OEIS A245211 table certificates ($n = 1, \dots, 25$). -/
theorem a_1_eq : a 1 = 0 := by decide
theorem a_2_eq : a 2 = 1 := by decide
theorem a_3_eq : a 3 = 1 := by decide
theorem a_4_eq : a 4 = 5 := by decide
theorem a_5_eq : a 5 = 1 := by decide
theorem a_6_eq : a 6 = 11 := by decide
theorem a_7_eq : a 7 = 1 := by decide
theorem a_8_eq : a 8 = 17 := by decide
theorem a_9_eq : a 9 = 7 := by decide
theorem a_10_eq : a 10 = 15 := by decide
theorem a_11_eq : a 11 = 1 := by decide
theorem a_12_eq : a 12 = 47 := by decide
theorem a_13_eq : a 13 = 1 := by decide
theorem a_14_eq : a 14 = 19 := by decide
theorem a_15_eq : a 15 = 17 := by decide
theorem a_16_eq : a 16 = 49 := by decide
theorem a_17_eq : a 17 = 1 := by decide
theorem a_18_eq : a 18 = 62 := by decide
theorem a_19_eq : a 19 = 1 := by decide
theorem a_20_eq : a 20 = 67 := by decide
theorem a_21_eq : a 21 = 21 := by decide
theorem a_22_eq : a 22 = 27 := by decide
theorem a_23_eq : a 23 = 1 := by decide
theorem a_24_eq : a 24 = 151 := by decide
theorem a_25_eq : a 25 = 11 := by decide
theorem a_66_eq : a 66 = 277 := by decide

/-! ## Companion Sequence Milestones: OEIS A245213 ($n = 72$) and A245214 ($n = 144$) -/

/-- Exact values at $n = 72$: $a(72) = 802$, $\tau(72) = 12$, $72 \cdot \tau(72) = 864$,
    and $\text{cantileverDiff}(72) = 62$. -/
theorem a_72_eq : a 72 = 802 := by decide
theorem tau_72_eq : tau 72 = 12 := by decide
theorem nTau_72_eq : nTau 72 = 864 := by decide
theorem cantileverDiff_72_eq : cantileverDiff 72 = 62 := by decide

/-- No positive integer $n < 72$ belongs to `OEIS A245213`, so $72$ is the minimum element. -/
theorem not_isInA245213_below_72 (n : Nat) (hn1 : 1 ≤ n) (hn72 : n < 72) :
    ¬ IsInA245213 n := by
  revert hn1
  revert n
  decide

/-- Exact values at $n = 144$: $a(144) = 2226$, $\tau(144) = 15$, $144 \cdot \tau(144) = 2160$,
    and $\text{cantileverDiff}(144) = -66$. -/
theorem a_144_eq : a 144 = 2226 := by decide
theorem tau_144_eq : tau 144 = 15 := by decide
theorem nTau_144_eq : nTau 144 = 2160 := by decide
theorem cantileverDiff_144_eq : cantileverDiff 144 = -66 := by decide

/-- $n = 144$ belongs to `OEIS A245214` ($144 \cdot \tau(144) < a(144)$). -/
theorem isInA245214_144 : IsInA245214 144 := by decide

/-- Refutation at $n = 143$: $143 \notin \text{A245214}$. -/
theorem not_isInA245214_143 : ¬ IsInA245214 143 := by decide

/-- **Krizek's Cantilever Sign-Change Theorem (2014)**:
    For every $1 \le n < 144$, $a(n) \le n \cdot \tau(n)$ (`¬ IsInA245214 n`),
    so $n = 144$ is the smallest positive integer where $n \cdot \tau(n) < a(n)$. -/
theorem not_isInA245214_below_144 (n : Nat) (hn1 : 1 ≤ n) (hn144 : n < 144) :
    ¬ IsInA245214 n := by
  revert hn1
  revert n
  decide

/-! ## Bounded Uniqueness of $n = 21$ Across $1 \le n \le 150$ -/

/-- No positive integer $n \le 150$ other than $n = 21$ is a fixed point of $a(n)$. -/
theorem not_isFixedPoint_upto_150_of_ne_21 (n : Nat)
    (hn1 : 1 ≤ n) (hn150 : n ≤ 150) (hne : n ≠ 21) :
    ¬ IsFixedPoint n := by
  have hlt : n < 151 := by omega
  revert hn1 hne
  revert n
  decide

/-- **Bounded Fixed-Point Uniqueness ($1 \le n \le 150$)**:
    For $1 \le n \le 150$, $a(n) = n$ if and only if $n = 21$. -/
theorem fixedPoint_iff_eq_21_upto_150 (n : Nat) (hn1 : 1 ≤ n) (hn150 : n ≤ 150) :
    IsFixedPoint n ↔ n = 21 := by
  constructor
  · intro hfp
    by_cases h21 : n = 21
    · exact h21
    · exfalso
      exact not_isFixedPoint_upto_150_of_ne_21 n hn1 hn150 h21 hfp
  · rintro rfl
    exact isFixedPoint_21

/-- Certified evaluation of the closest odd composite near-miss $n = 725 = 5^2 \cdot 29$:
    $a(725) = 724 = 725 - 1$. -/
theorem a_725_eq : a 725 = 724 := by decide

/-- Refutation at the near-miss $n = 725$: $725$ is not a fixed point. -/
theorem not_isFixedPoint_725 : ¬ IsFixedPoint 725 := by decide

end OeisA245211
