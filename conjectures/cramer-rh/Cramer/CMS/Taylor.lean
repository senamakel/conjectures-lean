import Cramer.Sharp.Taylor

/-!
# Taylor bounds for `cos` of every even order

`cosP n x = Σ_{i<n} (−1)^i x^{2i}/(2i)!` and `sinP n x = Σ_{i<n} (−1)^i x^{2i+1}/(2i+1)!`.
For `n ≥ 1` and every real `x`, `(−1)^n (cos x − cosP n x) ≥ 0` (`cos_sub_cosP_sign`): `cos`
lies above `cosP n` for even `n` and below it for odd `n`. The proof is the usual induction:
both remainders vanish at `0` and each is the derivative of the next.
-/

namespace Cramer.CMS

open Real Finset

/-- The cosine Taylor polynomial with `n` terms. -/
noncomputable def cosP (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range n, (-1) ^ i * x ^ (2 * i) / ((2 * i).factorial : ℝ)

/-- The sine Taylor polynomial with `n` terms. -/
noncomputable def sinP (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range n, (-1) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)

lemma hasDerivAt_sinP (n : ℕ) (x : ℝ) : HasDerivAt (sinP n) (cosP n x) x := by
  induction n with
  | zero => simp only [sinP, cosP, range_zero, sum_empty]; exact hasDerivAt_const x 0
  | succ n ih =>
    have h := (hasDerivAt_pow (2 * n + 1) x).const_mul ((-1 : ℝ) ^ n)
      |>.div_const ((2 * n + 1).factorial : ℝ)
    have e : sinP (n + 1) = fun y => sinP n y +
        (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
      ext y; simp [sinP, sum_range_succ]
    rw [e]
    convert ih.add h using 1
    simp only [cosP, sum_range_succ]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    have : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    field_simp

lemma hasDerivAt_cosP (n : ℕ) (x : ℝ) : HasDerivAt (cosP (n + 1)) (-sinP n x) x := by
  induction n with
  | zero =>
    have : cosP 1 = fun _ => 1 := by ext y; simp [cosP]
    rw [this]; simp only [sinP, range_zero, sum_empty, neg_zero]; exact hasDerivAt_const x 1
  | succ n ih =>
    have h := (hasDerivAt_pow (2 * (n + 1)) x).const_mul ((-1 : ℝ) ^ (n + 1))
      |>.div_const ((2 * (n + 1)).factorial : ℝ)
    have e : cosP (n + 1 + 1) = fun y => cosP (n + 1) y +
        (-1) ^ (n + 1) * y ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ) := by
      ext y; simp [cosP, sum_range_succ (n := n + 1)]
    rw [e]
    convert ih.add h using 1
    simp only [sinP, sum_range_succ, neg_add]
    congr 1
    have hf1 : ((2 * (n + 1)).factorial : ℝ) = (2 * n + 2) * (2 * n + 1) * ((2 * n).factorial : ℝ) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hf2 : ((2 * n + 1).factorial : ℝ) = (2 * n + 1) * ((2 * n).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hf1, hf2, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
    have : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- `(−1)^n (sin x − sinP n x) ≥ 0` and `(−1)^n (cos x − cosP n x) ≥ 0` for `x ≥ 0`, `n ≥ 1`. -/
lemma sign_remainders (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (-1) ^ n * (sin x - sinP n x) ∧ 0 ≤ (-1) ^ n * (cos x - cosP n x) := by
  induction n, hn using Nat.le_induction generalizing x with
  | base =>
    constructor
    · simp only [sinP, range_one, sum_singleton, pow_zero, one_mul, mul_zero, zero_add, pow_one,
        Nat.factorial_one, Nat.cast_one, div_one]
      nlinarith [Real.sin_le hx]
    · simp only [cosP, range_one, sum_singleton, pow_zero, one_mul, mul_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, pow_one]
      nlinarith [Real.cos_le_one x]
  | succ n hn ih =>
    -- cosine first: `C = cos − cosP (n+1)` has `C' = −(sin − sinP n)`
    have hC : 0 ≤ (-1) ^ (n + 1) * (cos x - cosP (n + 1) x) := by
      set C : ℝ → ℝ := fun u => (-1) ^ (n + 1) * (cos u - cosP (n + 1) u)
      have hCd : ∀ u, HasDerivAt C ((-1) ^ n * (sin u - sinP n u)) u := by
        intro u
        have h := ((hasDerivAt_cos u).sub (hasDerivAt_cosP n u)).const_mul ((-1 : ℝ) ^ (n + 1))
        convert h using 1
        ring
      have := nonneg_of_deriv_nonneg (f := C) (fun u => (hCd u).differentiableAt)
        (by simp [C, cosP, sum_range_succ', Finset.sum_eq_zero]) (fun u hu => by
          rw [(hCd u).deriv]; exact (ih hu).1) hx
      exact this
    refine ⟨?_, hC⟩
    set S : ℝ → ℝ := fun u => (-1) ^ (n + 1) * (sin u - sinP (n + 1) u)
    have hSd : ∀ u, HasDerivAt S ((-1) ^ (n + 1) * (cos u - cosP (n + 1) u)) u := by
      intro u
      exact ((hasDerivAt_sin u).sub (hasDerivAt_sinP (n + 1) u)).const_mul _
    have hS0 : S 0 = 0 := by simp [S, sinP]
    have := nonneg_of_deriv_nonneg (f := S) (fun u => (hSd u).differentiableAt)
      hS0 (fun u hu => by
        rw [(hSd u).deriv]
        have : 0 ≤ (-1) ^ (n + 1) * (cos u - cosP (n + 1) u) := by
          -- recompute `hC` at `u`
          set C : ℝ → ℝ := fun v => (-1) ^ (n + 1) * (cos v - cosP (n + 1) v)
          have hCd : ∀ v, HasDerivAt C ((-1) ^ n * (sin v - sinP n v)) v := by
            intro v
            have h := ((hasDerivAt_cos v).sub (hasDerivAt_cosP n v)).const_mul ((-1 : ℝ) ^ (n + 1))
            convert h using 1
            ring
          exact nonneg_of_deriv_nonneg (f := C) (fun v => (hCd v).differentiableAt)
            (by simp [C, cosP, sum_range_succ', Finset.sum_eq_zero]) (fun v hv => by
              rw [(hCd v).deriv]; exact (ih hv).1) hu
        exact this) hx
    exact this

lemma cosP_neg (n : ℕ) (x : ℝ) : cosP n (-x) = cosP n x := by
  unfold cosP; refine sum_congr rfl fun i _ => ?_; rw [pow_mul, pow_mul, neg_sq]

/-- **Taylor bounds for `cos`**: for every real `x` and `n ≥ 1`,
`0 ≤ (−1)^n (cos x − cosP n x)`. -/
theorem cos_sub_cosP_sign (n : ℕ) (hn : 1 ≤ n) (x : ℝ) : 0 ≤ (-1) ^ n * (cos x - cosP n x) := by
  rcases le_total 0 x with hx | hx
  · exact (sign_remainders n hn hx).2
  · have := (sign_remainders n hn (neg_nonneg.2 hx)).2
    rwa [cos_neg, cosP_neg] at this

lemma cosP_le_cos_of_even {n : ℕ} (hn : 1 ≤ n) (he : Even n) (x : ℝ) : cosP n x ≤ cos x := by
  have := cos_sub_cosP_sign n hn x
  rw [he.neg_one_pow, one_mul] at this; linarith

lemma cos_le_cosP_of_odd {n : ℕ} (ho : Odd n) (x : ℝ) : cos x ≤ cosP n x := by
  have := cos_sub_cosP_sign n ho.pos x
  rw [ho.neg_one_pow] at this; linarith

end Cramer.CMS
