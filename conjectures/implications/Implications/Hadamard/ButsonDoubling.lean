import Mathlib

/-!
# Quaternary complex Hadamard conjecture ⇒ Hadamard conjecture (Turyn's doubling)

Both statements are copied word for word from formal-conjectures (commit `9097e2f`):

* `FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean`,
  `ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture` (open), with the definition
  `ButsonHadamardMatrix.IsButsonHadamard`; stated here as the `Prop`
  `ButsonHadamardFourthRootsConjecture`;
* `FormalConjectures/Wikipedia/Hadamard.lean`, `Hadamard.HadamardConjecture` (open), with the
  definition `Hadamard.IsHadamard` (entries `±1` and `|det M| = n ^ (n / 2)`); stated here as the
  `Prop` `HadamardConjectureStatement`.

The deduction is Turyn's doubling (Turyn 1970, cited in the formal-conjectures docstring;
the paper was not opened). An `H(4, n)` matrix `M` has entries in `{±1, ±i}`; write
`M = A + iB` with `A = Re M`, `B = Im M`. Then `M M* = n I` says `A Aᵀ + B Bᵀ = n I` and
`B Aᵀ = A Bᵀ`. With `P = A + B` and `Q = A - B` (entries `±1`), the block matrix
`H = [[P, Q], [-Q, P]]` satisfies `H Hᵀ = 2n I`, so `|det H| = (2n)^(2n/2)`. For the order
`4k` with `k ≥ 1` take `m = k`, `n = 2k`; the order `0` is the empty matrix.
-/

open Matrix

namespace Implications.Hadamard

/-- Verbatim from formal-conjectures `9097e2f`,
`FormalConjectures/Wikipedia/ButsonHadamardMatrix.lean`,
`ButsonHadamardMatrix.IsButsonHadamard`: `M` is a **Butson-type Hadamard matrix** $H(k, n)$ if
$k > 0$, every entry satisfies $z^k = 1$, and $M M^* = n I_n$. -/
def IsButsonHadamard {n : ℕ} (k : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < k ∧ (∀ i j, M i j ^ k = 1) ∧ M * M.conjTranspose = (n : ℂ) • 1

/-- Verbatim from formal-conjectures `9097e2f`, `FormalConjectures/Wikipedia/Hadamard.lean`,
`Hadamard.IsHadamard`: a square matrix $M$ with $±1$-entries that satisfies the equality
$|M| = n^\frac{n}{2}$. -/
def IsHadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = n ^ ((n : ℝ) / 2)

-- The binder name `hm` is kept from the source although unused.
set_option linter.unusedVariables false in
/-- **Complex Hadamard conjecture for fourth roots of unity**, verbatim from formal-conjectures
`9097e2f`, `ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture`: for every integer
$m \ge 1$ there exists a $2m \times 2m$ Butson-type Hadamard matrix $H(4, 2m)$. -/
def ButsonHadamardFourthRootsConjecture : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), ∃ M, IsButsonHadamard (n := 2 * m) 4 M

/-- **Hadamard's conjecture**, verbatim from formal-conjectures `9097e2f`,
`Hadamard.HadamardConjecture`: there exists a Hadamard matrix for all $n = 4k$. -/
def HadamardConjectureStatement : Prop :=
  ∀ (k : ℕ), ∃ M, IsHadamard (n := 4 * k) M

/-- A fourth root of unity in `ℂ` is `1`, `-1`, `i` or `-i`. -/
lemma fourth_root_cases {z : ℂ} (hz : z ^ 4 = 1) :
    (z.re = 1 ∧ z.im = 0) ∨ (z.re = -1 ∧ z.im = 0) ∨ (z.re = 0 ∧ z.im = 1) ∨
      (z.re = 0 ∧ z.im = -1) := by
  have h : (z - 1) * (z + 1) * (z - Complex.I) * (z + Complex.I) = 0 := by
    have : (z - 1) * (z + 1) * (z - Complex.I) * (z + Complex.I) = z ^ 4 - 1 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this, hz, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; rw [sub_eq_zero.mp h]; simp
      · right; left; rw [eq_neg_of_add_eq_zero_left h]; simp
    · right; right; left; rw [sub_eq_zero.mp h]; simp
  · right; right; right; rw [eq_neg_of_add_eq_zero_left h]; simp

/-- If `H Hᵀ = N I` for a real square matrix of size `N`, then `|det H| = N ^ (N / 2)`. -/
lemma abs_det_of_mul_transpose {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (hH : H * H.transpose = (N : ℝ) • 1) : |H.det| = (N : ℝ) ^ ((N : ℝ) / 2) := by
  have hdet : H.det ^ 2 = (N : ℝ) ^ N := by
    have := congrArg Matrix.det hH
    rw [det_mul, det_transpose, det_smul, det_one, mul_one, Fintype.card_fin] at this
    rw [sq]; exact this
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ ((N : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [← pow_left_inj₀ (abs_nonneg _) hpos two_ne_zero, sq_abs, hdet,
    ← Real.rpow_natCast ((N : ℝ) ^ ((N : ℝ) / 2)) 2, ← Real.rpow_mul (Nat.cast_nonneg N),
    ← Real.rpow_natCast]
  congr 1
  push_cast; ring

/-- The real block construction: from `A`, `B` with `(A, B)` entrywise one of `(±1, 0)`,
`(0, ±1)`, `A Aᵀ + B Bᵀ = n I` and `B Aᵀ = A Bᵀ`, the matrix
`[[A + B, A - B], [-(A - B), A + B]]` has entries `±1` and orthogonal rows of norm `2n`. -/
lemma doubling_of_parts {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hentry : ∀ i j, (A i j = 1 ∧ B i j = 0) ∨ (A i j = -1 ∧ B i j = 0) ∨
      (A i j = 0 ∧ B i j = 1) ∨ (A i j = 0 ∧ B i j = -1))
    (hre : A * A.transpose + B * B.transpose = (n : ℝ) • 1)
    (him : B * A.transpose = A * B.transpose) :
    ∃ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H * H.transpose = ((2 * n : ℕ) : ℝ) • 1 := by
  have hPP : (A + B) * (A + B).transpose + (A - B) * (A - B).transpose =
      ((2 * n : ℕ) : ℝ) • 1 := by
    simp only [transpose_add, transpose_sub, add_mul, mul_add, sub_mul, mul_sub]
    have : A * A.transpose + A * B.transpose + (B * A.transpose + B * B.transpose) +
        (A * A.transpose - A * B.transpose - (B * A.transpose - B * B.transpose)) =
        (2 : ℝ) • (A * A.transpose + B * B.transpose) := by
      rw [two_smul]; abel
    rw [this, hre, smul_smul]
    push_cast; ring_nf
  have hPQ : (A - B) * (A + B).transpose = (A + B) * (A - B).transpose := by
    simp only [transpose_add, transpose_sub, add_mul, mul_add, sub_mul, mul_sub]
    rw [him]; abel
  refine ⟨fromBlocks (A + B) (A - B) (-(A - B)) (A + B), ?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, neg_apply, add_apply, sub_apply] <;>
      rcases hentry i j with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rw [ha, hb] <;> norm_num
  · rw [fromBlocks_transpose, fromBlocks_multiply, transpose_neg]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [hPP, add_comm ((A - B) * (A - B).transpose), hPP, hPQ, neg_add_cancel,
      add_neg_cancel, ← fromBlocks_one, fromBlocks_smul, smul_zero]

/-- **Turyn's doubling.** An `H(4, n)` matrix gives a real `2n × 2n` matrix with entries `±1`
whose rows are orthogonal of norm `2n`. -/
lemma turyn_doubling {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsButsonHadamard 4 M) :
    ∃ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H * H.transpose = ((2 * n : ℕ) : ℝ) • 1 := by
  obtain ⟨-, hroot, hmul⟩ := hM
  refine doubling_of_parts (M.map Complex.re) (M.map Complex.im)
    (fun i j => fourth_root_cases (hroot i j)) ?_ ?_
  · -- real part of `M M* = n I`
    ext i j
    have := congrArg Complex.re (congrFun (congrFun hmul i) j)
    rw [add_apply, mul_apply, mul_apply, smul_apply, one_apply]
    rw [mul_apply, smul_apply, one_apply, Complex.re_sum] at this
    simp only [conjTranspose_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, smul_eq_mul] at this
    simp only [transpose_apply, map_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    rw [show (∑ x, ((M i x).re * (M j x).re + (M i x).im * (M j x).im)) =
      ∑ x, ((M i x).re * (M j x).re - (M i x).im * -(M j x).im) from
        Finset.sum_congr rfl (fun _ _ => by ring), this]
    split_ifs <;> simp
  · -- imaginary part of `M M* = n I`
    ext i j
    have := congrArg Complex.im (congrFun (congrFun hmul i) j)
    rw [mul_apply, mul_apply]
    rw [mul_apply, smul_apply, one_apply, Complex.im_sum] at this
    simp only [conjTranspose_apply, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, smul_eq_mul] at this
    simp only [transpose_apply, map_apply]
    have h0 : ((n : ℂ) * (if i = j then 1 else 0)).im = 0 := by split_ifs <;> simp
    rw [h0] at this
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← this]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- **Quaternary complex Hadamard conjecture ⇒ Hadamard conjecture** (Turyn 1970): the
formal-conjectures statement `Hadamard.HadamardConjecture`, from
`ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture`. -/
theorem hadamardConjecture_of_butsonHadamardFourthRoots
    (h : ButsonHadamardFourthRootsConjecture) : HadamardConjectureStatement := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, by simp [IsHadamard]⟩
  obtain ⟨M, hM⟩ := h k hk
  obtain ⟨H, hpm, hHH⟩ := turyn_doubling hM
  let e : Fin (2 * k) ⊕ Fin (2 * k) ≃ Fin (4 * k) :=
    finSumFinEquiv.trans (finCongr (by ring))
  refine ⟨reindex e e H, fun i j => ?_, ?_⟩
  · rcases hpm (e.symm i) (e.symm j) with h1 | h1 <;> simp [reindex_apply, h1]
  · apply abs_det_of_mul_transpose
    rw [transpose_reindex, ← reindex_mul, hHH, reindex_apply, submatrix_smul,
      submatrix_one_equiv]
    congr 2
    push_cast; ring

end Implications.Hadamard
