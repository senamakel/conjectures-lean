import Mathlib

/-!
# Step 3: a ratio bound for `Γ` on vertical lines

`|Γ(b + iy)| ≤ C |y|^{b-a} |Γ(a + iy)|` for `0 ≤ a ≤ b ≤ 1`, `|y| ≥ 1`, with `C` absolute.
See `docs/BLUEPRINT.md`, Step 3 (Gauss product `Complex.GammaSeq_tendsto_Gamma`).

## Proof

Write `d = b - a`, `D_j = (b+j)² + y²` and `t_j = (a+b+2j)/D_j`. Then
`|a+j+iy|² = D_j (1 - d t_j) ≤ D_j e^{-d t_j}`, so
`∏_{j≤n} |a+j+iy| ≤ e^{-(d/2) S_n} ∏_{j≤n} |b+j+iy|` with `S_n = Σ_{j≤n} t_j`.
Comparing `t_j` with the telescoping increments of `log D_j + 8/(j+1)` gives
`S_n ≥ 2 log n - 2 log |y| - 9`, hence `|GammaSeq (b+iy) n| ≤ e⁵ |y|^d |GammaSeq (a+iy) n|`
for all `n ≥ 1`, and the bound passes to the limit.
-/

namespace Lindelof

open Complex Filter Topology

private lemma sq_norm_add_nat (x y : ℝ) (j : ℕ) :
    ‖(x : ℂ) + y * I + j‖ ^ 2 = (x + j) ^ 2 + y ^ 2 := by
  have : (x : ℂ) + y * I + j = ((x + j : ℝ) : ℂ) + y * I := by push_cast; ring
  rw [this, Complex.sq_norm, Complex.normSq_add_mul_I]

/-- One factor of the Gauss product. -/
private lemma norm_factor_le (a b y : ℝ) (j : ℕ) (hy : 1 ≤ |y|) :
    ‖(a : ℂ) + y * I + j‖ ≤ ‖(b : ℂ) + y * I + j‖ *
      Real.exp (-((b - a) / 2) * ((a + b + 2 * j) / ((b + j) ^ 2 + y ^ 2))) := by
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hD : 0 < (b + j) ^ 2 + y ^ 2 := by positivity
  set t := (a + b + 2 * j) / ((b + j) ^ 2 + y ^ 2) with ht
  have key : (a + j) ^ 2 + y ^ 2 ≤ ((b + j) ^ 2 + y ^ 2) * Real.exp (-((b - a) * t)) := by
    have h1 := Real.add_one_le_exp (-((b - a) * t))
    have h2 : ((b + j) ^ 2 + y ^ 2) * (-((b - a) * t) + 1) = (a + j) ^ 2 + y ^ 2 := by
      rw [ht]; field_simp; ring
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 hD.le
  have hsq : ‖(a : ℂ) + y * I + j‖ ^ 2 ≤
      (‖(b : ℂ) + y * I + j‖ * Real.exp (-((b - a) / 2) * t)) ^ 2 := by
    rw [mul_pow, sq_norm_add_nat, sq_norm_add_nat, ← Real.exp_nat_mul]
    convert key using 3
    push_cast; ring
  have h0 : 0 ≤ ‖(b : ℂ) + y * I + j‖ * Real.exp (-((b - a) / 2) * t) := by positivity
  nlinarith [norm_nonneg ((a : ℂ) + y * I + j)]

/-- The sum `S_n = Σ_{j≤n} t_j` grows like `2 log n`. -/
private lemma sum_ge (a b y : ℝ) (n : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hy : 1 ≤ |y|) (hn : 1 ≤ n) :
    2 * Real.log n - 2 * Real.log |y| - 9 ≤
      ∑ j ∈ Finset.range (n + 1), (a + b + 2 * j) / ((b + j) ^ 2 + y ^ 2) := by
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  set f : ℕ → ℝ := fun j => Real.log ((b + j) ^ 2 + y ^ 2) + 8 / (j + 1) with hf
  have step : ∀ j : ℕ, f (j + 1) - f j ≤ (a + b + 2 * j) / ((b + j) ^ 2 + y ^ 2) := by
    intro j
    have hj : (0 : ℝ) ≤ j := j.cast_nonneg
    have hD : 0 < (b + j) ^ 2 + y ^ 2 := by positivity
    have hD' : 0 < (b + (j + 1 : ℕ)) ^ 2 + y ^ 2 := by positivity
    have hlog : Real.log ((b + (j + 1 : ℕ)) ^ 2 + y ^ 2) - Real.log ((b + j) ^ 2 + y ^ 2) ≤
        ((b + (j + 1 : ℕ)) ^ 2 + y ^ 2) / ((b + j) ^ 2 + y ^ 2) - 1 := by
      rw [← Real.log_div hD'.ne' hD.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hD' hD)
    simp only [hf]
    have h1 : ((b + (j + 1 : ℕ)) ^ 2 + y ^ 2) / ((b + j) ^ 2 + y ^ 2) - 1 -
        (a + b + 2 * j) / ((b + j) ^ 2 + y ^ 2) = (1 + b - a) / ((b + j) ^ 2 + y ^ 2) := by
      field_simp; push_cast; ring
    have h2 : (8 : ℝ) / ((j + 1 : ℕ) + 1) - 8 / (j + 1) = -(8 / ((j + 1) * (j + 2))) := by
      push_cast; field_simp; ring
    have h3 : (1 + b - a) / ((b + j) ^ 2 + y ^ 2) ≤ 8 / ((j + 1) * (j + 2)) := by
      rw [div_le_div_iff₀ hD (by positivity)]
      have hb0 : 0 ≤ b := by linarith
      nlinarith [mul_nonneg hb0 hj, mul_nonneg hj hj, sq_nonneg ((j : ℝ) - 1)]
    linarith
  have htel := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (n + 1)) => step j)
  rw [Finset.sum_range_sub] at htel
  simp only [hf] at htel
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 2 * Real.log n ≤ Real.log ((b + (n + 1 : ℕ)) ^ 2 + y ^ 2) := by
    have hp := Real.log_pow (n : ℝ) 2
    push_cast at hp
    rw [← hp]
    apply Real.log_le_log (by positivity)
    push_cast
    have hle : (n : ℝ) ≤ b + (n + 1) := by linarith
    nlinarith [mul_le_mul hle hle (by positivity) (by linarith)]
  have hL0 : Real.log ((b + (0 : ℕ)) ^ 2 + y ^ 2) ≤ 1 + 2 * Real.log |y| := by
    have h2 : Real.log ((b + (0 : ℕ)) ^ 2 + y ^ 2) ≤ Real.log (2 * |y| ^ 2) := by
      apply Real.log_le_log (by positivity)
      push_cast
      rw [sq_abs]
      have hb0 : 0 ≤ b := by linarith
      nlinarith [mul_le_mul hb hb hb0 zero_le_one]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    push_cast at h2 ⊢
    linarith
  have h8 : 0 ≤ 8 / ((n + 1 : ℕ) + 1 : ℝ) := by positivity
  push_cast at htel hL1 hL0 h8
  linarith

theorem norm_Gamma_le_rpow_mul :
    ∃ C : ℝ, ∀ a b y : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ |y| →
      ‖Gamma (b + y * I)‖ ≤ C * |y| ^ (b - a) * ‖Gamma (a + y * I)‖ := by
  refine ⟨Real.exp 5, fun a b y ha hab hb hy => ?_⟩
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := abs_pos.1 hy0
  set K := Real.exp 5 * |y| ^ (b - a) with hK
  have hseq : ∀ n : ℕ, 1 ≤ n →
      ‖GammaSeq (b + y * I) n‖ ≤ K * ‖GammaSeq (a + y * I) n‖ := by
    intro n hn
    have hn0 : 0 < n := hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have hne : ∀ (x : ℝ) (j : ℕ), (x : ℂ) + y * I + j ≠ 0 := by
      intro x j h
      have := congrArg Complex.im h
      simp at this
      exact hyne this
    set S := ∑ j ∈ Finset.range (n + 1), (a + b + 2 * j) / ((b + j) ^ 2 + y ^ 2) with hS
    set P := ∏ j ∈ Finset.range (n + 1), ‖(a : ℂ) + y * I + j‖ with hP
    set P' := ∏ j ∈ Finset.range (n + 1), ‖(b : ℂ) + y * I + j‖ with hP'
    have hPpos : 0 < P := Finset.prod_pos fun j _ => norm_pos_iff.2 (hne a j)
    have hP'pos : 0 < P' := Finset.prod_pos fun j _ => norm_pos_iff.2 (hne b j)
    have hPP : P ≤ P' * Real.exp (-((b - a) / 2) * S) := by
      calc P ≤ ∏ j ∈ Finset.range (n + 1), (‖(b : ℂ) + y * I + j‖ *
            Real.exp (-((b - a) / 2) * ((a + b + 2 * j) / ((b + j) ^ 2 + y ^ 2)))) :=
            Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
              (fun j _ => norm_factor_le a b y j hy)
        _ = P' * Real.exp (-((b - a) / 2) * S) := by
            rw [Finset.prod_mul_distrib, ← Real.exp_sum, hS, Finset.mul_sum]
    have hSge := sum_ge a b y n ha hab hb hy hn
    have hpow : (n : ℝ) ^ b * Real.exp (-((b - a) / 2) * S) ≤ K * (n : ℝ) ^ a := by
      have hsplit : (n : ℝ) ^ b = (n : ℝ) ^ (b - a) * (n : ℝ) ^ a := by
        rw [← Real.rpow_add hnr]; ring_nf
      rw [hsplit, hK, Real.rpow_def_of_pos hnr, Real.rpow_def_of_pos hy0]
      have : Real.exp (Real.log n * (b - a)) * Real.exp (-((b - a) / 2) * S) ≤
          Real.exp 5 * Real.exp (Real.log |y| * (b - a)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith
      have hna : 0 ≤ (n : ℝ) ^ a := by positivity
      calc Real.exp (Real.log n * (b - a)) * (n : ℝ) ^ a * Real.exp (-((b - a) / 2) * S)
          = Real.exp (Real.log n * (b - a)) * Real.exp (-((b - a) / 2) * S) * (n : ℝ) ^ a := by
            ring
        _ ≤ Real.exp 5 * Real.exp (Real.log |y| * (b - a)) * (n : ℝ) ^ a :=
            mul_le_mul_of_nonneg_right this hna
    have hnormb : ‖GammaSeq (b + y * I) n‖ = (n : ℝ) ^ b * (Nat.factorial n : ℝ) / P' := by
      rw [GammaSeq, norm_div, norm_mul, norm_natCast_cpow_of_pos hn0, norm_prod]
      simp only [Complex.norm_natCast, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
      rfl
    have hnorma : ‖GammaSeq (a + y * I) n‖ = (n : ℝ) ^ a * (Nat.factorial n : ℝ) / P := by
      rw [GammaSeq, norm_div, norm_mul, norm_natCast_cpow_of_pos hn0, norm_prod]
      simp only [Complex.norm_natCast, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
      rfl
    rw [hnormb, hnorma, mul_div_assoc', div_le_div_iff₀ hP'pos hPpos]
    have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hb0 : 0 ≤ (n : ℝ) ^ b := by positivity
    calc (n : ℝ) ^ b * (Nat.factorial n : ℝ) * P ≤ (n : ℝ) ^ b * (Nat.factorial n : ℝ) * (P' * Real.exp (-((b - a) / 2) * S)) :=
          mul_le_mul_of_nonneg_left hPP (by positivity)
      _ = (Nat.factorial n : ℝ) * P' * ((n : ℝ) ^ b * Real.exp (-((b - a) / 2) * S)) := by ring
      _ ≤ (Nat.factorial n : ℝ) * P' * (K * (n : ℝ) ^ a) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = K * ((n : ℝ) ^ a * (Nat.factorial n : ℝ)) * P' := by ring
  have hb := (GammaSeq_tendsto_Gamma (b + y * I)).norm
  have ha' := ((GammaSeq_tendsto_Gamma (a + y * I)).norm).const_mul K
  exact le_of_tendsto_of_tendsto hb ha' (eventually_atTop.2 ⟨1, hseq⟩)

end Lindelof
