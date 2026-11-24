import LLS.Sharp.Defs

/-!
# The gamma part of the shifted Cesàro formula, per parity

`ELpar 𝔞 x ≤ Re(Γₛ(x) + (1 − 1/x) G(3)) ≤ EUpar 𝔞 x` and `Re G(1) = Gpar 𝔞`.

For the even upper bound, each tail term `tau x m` (`m = 2k + 3`) is at most
`(1/(m+2) − 1/m) + (1/x)(1/(m−1) − 1/(m+2))`; the first parts telescope to `−1/3` and the second
are at most `(3/2)/((k+1)(k+2))`, which sum to `3/2`.
-/

namespace LLS.Sharp.AssemblyAux

open Complex Erdos985.Analytic Erdos985.Analytic.BoundsAux LLS.ShiftAux

variable {N : ℕ} [NeZero N]

lemma core_odd_sharp (y p K : ℝ) (hp0 : 0 ≤ p) (hy : 0 ≤ y) (hK : 0 ≤ K) :
    (1 - y) / (2 + (2 * (K + 1) + 1)) - (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1))
      + 1 / (2 * (K + 1) + 1) - y / (2 * (K + 1) + 1 - 1))
      ≤ -(1 / (2 * K + 3) - 1 / (2 * K + 3 + 2)) + y * (3 / 2) * (1 / ((K + 1) * (K + 2))) := by
  have h1 : 2 * K + 3 ≠ 0 := by intro h; linarith
  have h2 : 2 * K + 5 ≠ 0 := by intro h; linarith
  have h4 : K + 1 ≠ 0 := by intro h; linarith
  have h5 : K + 2 ≠ 0 := by intro h; linarith
  rw [← sub_nonneg]
  have e : -(1 / (2 * K + 3) - 1 / (2 * K + 3 + 2)) + y * (3 / 2) * (1 / ((K + 1) * (K + 2)))
      - ((1 - y) / (2 + (2 * (K + 1) + 1)) - (p / ((2 * (K + 1) + 1) * (2 * (K + 1) + 1 - 1))
        + 1 / (2 * (K + 1) + 1) - y / (2 * (K + 1) + 1 - 1)))
      = p / ((2 * K + 3) * (2 * K + 2)) + y * (3 * (K + 3)) / (2 * (K + 1) * (K + 2) * (2 * K + 5)) := by
    field_simp
    ring
  rw [e]
  positivity

lemma tau_le_odd_sharp (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    tau x (2 * (k + 1) + 1) ≤ -(1 / (2 * (k : ℝ) + 3) - 1 / (2 * (k : ℝ) + 3 + 2))
      + 1 / x * (3 / 2) * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hm0 : 2 * (k + 1) + 1 ≠ 0 := by omega
  have hm1 : 2 * (k + 1) + 1 ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  have hy0 : 0 < 1 / x := by positivity
  have := core_odd_sharp (1 / x) ((1 / x) ^ (2 * (k + 1) + 1)) k (by positivity) hy0.le
    (Nat.cast_nonneg k)
  push_cast
  exact this

omit [NeZero N] in
/-- `Re G(1) = Gpar 𝔞`. -/
lemma re_gammaLogDeriv_one_eq (χ : DirichletCharacter ℂ N) :
    (gammaLogDeriv χ 1).re = LLS.Sharp.Gpar (parity χ) := by
  unfold gammaLogDeriv
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (parity_le_one χ) with h | h
  · rw [h]
    have e1 : ((1 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 1 / 2 := by norm_num
    rw [e1, Complex.digamma_one_half]
    have e : (-2 * Complex.log 2 - (Real.eulerMascheroniConstant : ℂ))
        = ((-2 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
      push_cast; rw [Complex.ofReal_log (by norm_num)]; push_cast; ring
    rw [e]
    simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    unfold LLS.Sharp.Gpar
    norm_num
    ring
  · rw [h]
    have e1 : ((1 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 1 := by norm_num
    rw [e1, Complex.digamma_one]
    simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    unfold LLS.Sharp.Gpar
    norm_num
    ring

/-- `ELpar 𝔞 x ≤ Re(Γₛ(x) + (1 − 1/x) G(3)) ≤ EUpar 𝔞 x`. -/
theorem gamma_shift_bounds (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    LLS.Sharp.ELpar (parity χ) x ≤ (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re ∧
      (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re
        ≤ LLS.Sharp.EUpar (parity χ) x := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : 0 < 1 / (x : ℝ) := by positivity
  have hfac : (1 - 1 / (x : ℂ)) = ((1 - 1 / (x : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [gammaPartS_eq χ x hx, hfac, ← Complex.ofReal_tsum, add_re, ofReal_re, re_ofReal_mul,
    re_gammaLogDeriv_three]
  unfold LLS.Sharp.ELpar LLS.Sharp.EUpar LLS.Sharp.G3par
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (parity_le_one χ) with h | h
  · rw [h]
    simp only [↓reduceIte, add_zero]
    have hS := (tsum_tau_bound x hx1 1 le_rfl).1
    have hS' : Summable (fun k : ℕ => tau x (2 * k + 1)) := by simpa using hS
    rw [hS'.tsum_eq_zero_add]
    have hg : Summable (fun k : ℕ => tau x (2 * (k + 1) + 1)) :=
      (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k + 1)) 1).mpr hS'
    have ht := (LLS.hasSum_tele 3 (by norm_num)).neg
    have hge : -(1 / 3 : ℝ) ≤ ∑' k : ℕ, tau x (2 * (k + 1) + 1) := by
      refine hasSum_le (fun k => ?_) ht hg.hasSum
      have := LLS.tau_ge_tele x hx1 (2 * (k + 1) + 1) (by omega)
      push_cast at this ⊢
      have e1 : (2 * ((k : ℝ) + 1) + 1 : ℝ) = 2 * k + 3 := by ring
      rw [e1] at this
      linarith
    have hle : ∑' k : ℕ, tau x (2 * (k + 1) + 1) ≤ -(1 / 3) + 1 / (x : ℝ) * (3 / 2) * 1 :=
      hasSum_le (fun k => tau_le_odd_sharp x hx1 k) hg.hasSum
        (ht.add (hasSum_u.mul_left (1 / (x : ℝ) * (3 / 2))))
    have ht1 : tau x (2 * 0 + 1)
        = (1 - 1 / (x : ℝ)) / 3 - (1 - 1 / (x : ℝ) - 1 / (x : ℝ) * Real.log x) := by
      simp [tau]
    rw [ht1]
    constructor <;> linarith
  · rw [h]
    simp only [one_ne_zero, ↓reduceIte]
    have hS := (tsum_tau_bound x hx1 0 (by norm_num)).1
    have hS' : Summable (fun k : ℕ => tau x (2 * k)) := by simpa using hS
    have hg : Summable (fun k : ℕ => tau x (2 * (k + 1))) :=
      (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k)) 1).mpr hS'
    have he : (fun k : ℕ => tau x (2 * k + 1 + 1)) = fun k : ℕ => tau x (2 * (k + 1)) := by
      funext k; congr 1
    rw [he]
    have ht := (LLS.hasSum_tele 2 (by norm_num)).neg
    have hge : -(1 / 2 : ℝ) ≤ ∑' k : ℕ, tau x (2 * (k + 1)) := by
      refine hasSum_le (fun k => ?_) ht hg.hasSum
      have := LLS.tau_ge_tele x hx1 (2 * (k + 1)) (by omega)
      push_cast at this ⊢
      have e1 : (2 * ((k : ℝ) + 1) : ℝ) = 2 * k + 2 := by ring
      rw [e1] at this
      linarith
    have hle : ∑' k : ℕ, tau x (2 * (k + 1)) ≤ (3 * (1 / (x : ℝ)) - 1) / 2 * 1 :=
      hasSum_le (fun k => tau_le_even x hx1 k) hg.hasSum
        (hasSum_u.mul_left ((3 * (1 / (x : ℝ)) - 1) / 2))
    constructor <;> nlinarith

end LLS.Sharp.AssemblyAux
