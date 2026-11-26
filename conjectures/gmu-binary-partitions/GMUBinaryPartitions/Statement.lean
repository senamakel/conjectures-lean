import Mathlib

/-!
# Conjecture 5.6 of Gawron–Miska–Ulas: the statement

M. Gawron, P. Miska, M. Ulas, *Arithmetic properties of coefficients of power series expansion
of `∏_{n≥0}(1−x^{2^n})^t`* (with an appendix by A. Schinzel), arXiv:1703.01955 v1 (source file
`GMU_MOFM_Revision_II.tex`); Monatsh. Math. 185 (2018) 307–360.

The paper (Section 4) puts `F(x) = ∏_{n≥0} (1 − x^{2^n})` and, for `m ∈ ℕ₊`,

  `H_m(x) := F(x)^{−m} = ∑_{n≥0} b_m(n) x^n`,

so `b_m(n)` is the number of representations of `n` as a sum of powers of `2` in which each
summand has one of `m` colours. Conjecture 5.6 (label `cong:powerof2-1`) reads:

> Let `m` be a fixed positive integer. Then for each `n ∈ ℕ` and `k ≥ m+2` the following
> congruence holds:
> `b_{2^m−1}(2^{k+1}n) ≡ b_{2^m−1}(2^{k−1}n) (mod 2^{4⌊(k+1)/2⌋−2})`.

In the paper `ℕ` contains `0` (the sequences `(b_m(n))_{n∈ℕ}` start at `b_m(0) = 1`, and
positive integers are written `ℕ₊`), so `n` ranges over Lean's `ℕ`.

## The power series

`(1 − X^{2^i})` has the inverse `geomPow2 i = ∑_{j≥0} X^{2^i j}` in `ℤ⟦X⟧`
(`GMU.one_sub_mul_geomPow2` in `GMUBinaryPartitions/Series.lean`). The coefficient of `x^n` in
the infinite product only sees the factors with `2^i ≤ n`, so we take the finite product over
`i < N` and read off the coefficient of `X^n` at `N = n + 1`. `GMU.coeff_truncatedSeries` proves
that every `N` with `n < 2^N` gives the same coefficient, and `GMU.b_eq_coeff_of_mul_eq_one`
that `b m n` is the `n`-th coefficient of the inverse of `∏_{i<N} (1 − X^{2^i})^m` for any such
`N`.
-/

namespace GMU

open PowerSeries

/-- `∑_{j ≥ 0} X^{2^i j}`, the inverse of `1 − X^{2^i}` in `ℤ⟦X⟧`. -/
noncomputable def geomPow2 (i : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if 2 ^ i ∣ n then 1 else 0

/-- `∏_{i<N} (1 − X^{2^i})^{−m}`, written as `∏_{i<N} (∑_j X^{2^i j})^m`. -/
noncomputable def truncatedSeries (m N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, geomPow2 i ^ m

/-- `b_m(n)`: the coefficient of `x^n` in `∏_{i≥0} (1 − x^{2^i})^{−m}`, read off the product over
`i < n + 1` (the factors with `2^i > n` do not change it). -/
noncomputable def b (m n : ℕ) : ℤ :=
  PowerSeries.coeff n (truncatedSeries m (n + 1))

/-- Conjecture 5.6 of Gawron–Miska–Ulas (arXiv:1703.01955 v1, label `cong:powerof2-1`).
Here `k ≥ m + 2 ≥ 3`, so `k − 1` and `4⌊(k+1)/2⌋ − 2` involve no truncated subtraction, and
`⌊(k+1)/2⌋` is `(k + 1) / 2` in `ℕ`. -/
def GMUConjecture56 : Prop :=
  ∀ m : ℕ, 0 < m → ∀ n k : ℕ, m + 2 ≤ k →
    b (2 ^ m - 1) (2 ^ (k + 1) * n) ≡ b (2 ^ m - 1) (2 ^ (k - 1) * n)
      [ZMOD 2 ^ (4 * ((k + 1) / 2) - 2)]

end GMU
