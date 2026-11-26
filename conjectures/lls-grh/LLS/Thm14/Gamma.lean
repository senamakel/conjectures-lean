import LLS.Sharp.NumBasic
import LLS.Sharp.AssemblyAux.Gamma

/-!
# Absolute values of the gamma parts

* `LLS.Thm14.norm_logGamma_le`: the gamma part `Γ̃(x) = Γ̃_part(x) + G(2) log x` of the
  log-weighted explicit formula is real, and with `l = log x ≥ 4`, `0 ≤ λ`:
  `|½ λ l + Γ̃(x)| ≤ ½ l max(λ − 3, l + 2) + 5/4`. Here `Γ̃ = −l²/2 − (½ log π + γ/2) l + [0, ½]`
  for even characters and `Γ̃ = −(½ log π + γ/2 + log 2) l + [0, 5/4]` for odd ones.
* `LLS.Thm14.norm_shiftGamma_le`: the gamma part of the shifted Cesàro formula is real, so its
  norm is at most `max |E_L| |E_U|`.
-/

namespace LLS.Thm14

open Complex Erdos985.Analytic Erdos985.Analytic.BoundsAux LLS.ShiftAux

variable {N : ℕ} [NeZero N]

/-- `G(2)` per parity. -/
noncomputable def G2par (a : ℕ) : ℝ :=
  if a = 0 then -(1 / 2) * Real.log Real.pi - Real.eulerMascheroniConstant / 2
  else -(1 / 2) * Real.log Real.pi + 1 - Real.log 2 - Real.eulerMascheroniConstant / 2

omit [NeZero N] in
lemma gammaLogDeriv_two_eq (χ : DirichletCharacter ℂ N) :
    gammaLogDeriv χ 2 = ((G2par (parity χ) : ℝ) : ℂ) := by
  unfold gammaLogDeriv G2par
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (parity_le_one χ) with h | h
  · rw [h]
    have e : ((2 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 1 := by norm_num
    rw [e, Complex.digamma_one]
    simp only [↓reduceIte]
    push_cast; ring
  · rw [h]
    have e : ((2 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 1 / 2 + 1 := by norm_num
    have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    rw [e, digamma_apply_add_one _ hs, digamma_one_half]
    have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    rw [hlog]
    simp only [one_ne_zero, ↓reduceIte]
    push_cast; ring

omit [NeZero N] in
lemma gammaLogDeriv_three_eq (χ : DirichletCharacter ℂ N) :
    gammaLogDeriv χ 3 = ((LLS.Sharp.G3par (parity χ) : ℝ) : ℂ) := by
  unfold gammaLogDeriv LLS.Sharp.G3par
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (parity_le_one χ) with h | h
  · rw [h]
    have e : ((3 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 1 / 2 + 1 := by norm_num
    have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    rw [e, digamma_apply_add_one _ hs, digamma_one_half]
    have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    rw [hlog]
    simp only [↓reduceIte]
    push_cast; ring
  · rw [h]
    have e : ((3 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 1 + 1 := by norm_num
    have hs : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    rw [e, digamma_apply_add_one _ hs, Complex.digamma_one]
    simp only [one_ne_zero, ↓reduceIte]
    push_cast; ring

lemma norm_eq_abs_re {z : ℂ} (hz : z.im = 0) : ‖z‖ = |z.re| := by
  have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
  rw [this, Complex.norm_real, Real.norm_eq_abs]; simp

/-- The shifted gamma part is real. -/
lemma im_shiftGamma (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).im = 0 := by
  rw [gammaPartS_eq χ x hx, gammaLogDeriv_three_eq, ← Complex.ofReal_tsum,
    show (1 - 1 / (x : ℂ)) = ((1 - 1 / (x : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, Complex.ofReal_im]

theorem norm_shiftGamma_le (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    ‖gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3‖
      ≤ max |LLS.Sharp.ELpar (parity χ) x| |LLS.Sharp.EUpar (parity χ) x| := by
  rw [norm_eq_abs_re (im_shiftGamma χ x hx)]
  obtain ⟨h1, h2⟩ := LLS.Sharp.AssemblyAux.gamma_shift_bounds χ x hx
  rw [abs_le']
  constructor
  · exact h2.trans ((le_abs_self _).trans (le_max_right _ _))
  · have := neg_abs_le (LLS.Sharp.ELpar (parity χ) x)
    have := le_max_left |LLS.Sharp.ELpar (parity χ) x| |LLS.Sharp.EUpar (parity χ) x|
    linarith

lemma ltau_bounds (y : ℝ) (hy : 1 ≤ y) (m : ℕ) (hm : m ≠ 0) :
    Real.log y / (2 + m) - Real.log y / m ≤ LogAux.ltau y m ∧
      LogAux.ltau y m ≤ Real.log y / (2 + m) - Real.log y / m + 1 / (m : ℝ) ^ 2 := by
  simp only [LogAux.ltau, hm, ↓reduceIte]
  have h0 : 0 ≤ 1 / y ^ m := by positivity
  have h1 : 1 / y ^ m ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hy
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  constructor
  · have : 0 ≤ (1 - 1 / y ^ m) / (m : ℝ) ^ 2 := div_nonneg (by linarith) hm2.le
    linarith
  · have : (1 - 1 / y ^ m) / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) hm2.le
    linarith

/-- Bounds for `Σ_k ltau(x, 2k + 𝔞)`. -/
lemma tsum_ltau_bounds (x : ℝ) (hx : 1 ≤ x) (a : ℕ) (ha : a ≤ 1)
    (hs : Summable fun k : ℕ => LogAux.ltau x (2 * k + a)) :
    (a = 0 → -(Real.log x) ^ 2 / 2 ≤ ∑' k : ℕ, LogAux.ltau x (2 * k + a) ∧
        ∑' k : ℕ, LogAux.ltau x (2 * k + a) ≤ -(Real.log x) ^ 2 / 2 + 1 / 2) ∧
      (a = 1 → -(Real.log x) ≤ ∑' k : ℕ, LogAux.ltau x (2 * k + a) ∧
        ∑' k : ℕ, LogAux.ltau x (2 * k + a) ≤ -(Real.log x) + 5 / 4) := by
  set l := Real.log x
  have hl : 0 ≤ l := Real.log_nonneg hx
  have hrest := (summable_nat_add_iff (f := fun k : ℕ => LogAux.ltau x (2 * k + a)) 1).mpr hs
  rw [hs.tsum_eq_zero_add]
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · subst h0
    have e0 : LogAux.ltau x (2 * 0 + 0) = l / 2 - l ^ 2 / 2 := by simp [LogAux.ltau, l]
    rw [e0]
    have ht := (LLS.hasSum_tele 2 (by norm_num)).mul_left (-l)
    have hu := (hasSum_u).mul_left (1 / 2 : ℝ)
    have hlo : -l * (1 / 2) ≤ ∑' k : ℕ, LogAux.ltau x (2 * (k + 1) + 0) := by
      refine hasSum_le (fun k => ?_) ht hrest.hasSum
      have hm : 2 * (k + 1) + 0 ≠ 0 := by omega
      have := (ltau_bounds x hx _ hm).1
      have e : (((2 * (k + 1) + 0 : ℕ)) : ℝ) = 2 * (k : ℝ) + 2 := by push_cast; ring
      rw [e] at this
      have e2 : -l * (1 / (2 * (k : ℝ) + 2) - 1 / (2 * (k : ℝ) + 2 + 2))
          = l / (2 + (2 * (k : ℝ) + 2)) - l / (2 * (k : ℝ) + 2) := by ring
      rw [e2]; exact this
    have hhi : ∑' k : ℕ, LogAux.ltau x (2 * (k + 1) + 0) ≤ -l * (1 / 2) + 1 / 2 * 1 := by
      refine hasSum_le (fun k => ?_) hrest.hasSum (ht.add hu)
      have hm : 2 * (k + 1) + 0 ≠ 0 := by omega
      have := (ltau_bounds x hx _ hm).2
      have e : (((2 * (k + 1) + 0 : ℕ)) : ℝ) = 2 * (k : ℝ) + 2 := by push_cast; ring
      rw [e] at this
      have hk : (0 : ℝ) ≤ k := k.cast_nonneg
      have h3 : 1 / (2 * (k : ℝ) + 2) ^ 2 ≤ 1 / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
      have e2 : -l * (1 / (2 * (k : ℝ) + 2) - 1 / (2 * (k : ℝ) + 2 + 2))
          = l / (2 + (2 * (k : ℝ) + 2)) - l / (2 * (k : ℝ) + 2) := by ring
      show _ ≤ _ + _
      rw [e2]; linarith
    constructor <;> nlinarith
  · subst h1
    have e0 : LogAux.ltau x (2 * 0 + 1) = l / 3 - l + (1 - 1 / x) := by
      simp [LogAux.ltau, l]; norm_num
    rw [e0]
    have hx0 : 0 < x := by linarith
    have hx1 : 0 ≤ 1 / x := by positivity
    have hx2 : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
    have ht := (LLS.hasSum_tele 3 (by norm_num)).mul_left (-l)
    have hu := (hasSum_u).mul_left (1 / 4 : ℝ)
    have hlo : -l * (1 / 3) ≤ ∑' k : ℕ, LogAux.ltau x (2 * (k + 1) + 1) := by
      refine hasSum_le (fun k => ?_) ht hrest.hasSum
      have hm : 2 * (k + 1) + 1 ≠ 0 := by omega
      have := (ltau_bounds x hx _ hm).1
      have e : (((2 * (k + 1) + 1 : ℕ)) : ℝ) = 2 * (k : ℝ) + 3 := by push_cast; ring
      rw [e] at this
      have e2 : -l * (1 / (2 * (k : ℝ) + 3) - 1 / (2 * (k : ℝ) + 3 + 2))
          = l / (2 + (2 * (k : ℝ) + 3)) - l / (2 * (k : ℝ) + 3) := by ring
      rw [e2]; exact this
    have hhi : ∑' k : ℕ, LogAux.ltau x (2 * (k + 1) + 1) ≤ -l * (1 / 3) + 1 / 4 * 1 := by
      refine hasSum_le (fun k => ?_) hrest.hasSum (ht.add hu)
      have hm : 2 * (k + 1) + 1 ≠ 0 := by omega
      have := (ltau_bounds x hx _ hm).2
      have e : (((2 * (k + 1) + 1 : ℕ)) : ℝ) = 2 * (k : ℝ) + 3 := by push_cast; ring
      rw [e] at this
      have hk : (0 : ℝ) ≤ k := k.cast_nonneg
      have h3 : 1 / (2 * (k : ℝ) + 3) ^ 2 ≤ 1 / 4 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
      have e2 : -l * (1 / (2 * (k : ℝ) + 3) - 1 / (2 * (k : ℝ) + 3 + 2))
          = l / (2 + (2 * (k : ℝ) + 3)) - l / (2 * (k : ℝ) + 3) := by ring
      show _ ≤ _ + _
      rw [e2]; linarith
    constructor <;> nlinarith

/-- `|½ λ l + Γ̃(x)| ≤ ½ l max(λ − 3, l + 2) + 5/4` for `l = log x ≥ 4`, `λ ≥ 0`. -/
theorem norm_logGamma_le (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) (lf : ℝ)
    (hlf : 0 ≤ lf) (hl4 : 4 ≤ Real.log x) :
    ‖((1 / 2 * lf * Real.log x : ℝ) : ℂ)
        + (LogAux.lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ))‖
      ≤ 1 / 2 * Real.log x * max (lf - 3) (Real.log x + 2) + 5 / 4 := by
  obtain ⟨hs, he⟩ := LogAux.lgammaPart_eq χ x hx
  rw [he, gammaLogDeriv_two_eq, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  obtain ⟨hE, hO⟩ := tsum_ltau_bounds (x : ℝ) hx1 (parity χ) (parity_le_one χ) hs
  set l := Real.log x
  set T := ∑' k : ℕ, LogAux.ltau x (2 * k + parity χ)
  obtain ⟨g1, g2, p1, p2, l1, l2⟩ := LLS.Sharp.consts
  have hm1 := le_max_left (lf - 3) (l + 2)
  have hm2 := le_max_right (lf - 3) (l + 2)
  rw [abs_le]
  unfold G2par
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (parity_le_one χ) with h | h
  · obtain ⟨t1, t2⟩ := hE h
    rw [h]; simp only [↓reduceIte]
    constructor <;> nlinarith
  · obtain ⟨t1, t2⟩ := hO h
    rw [h]; simp only [one_ne_zero, ↓reduceIte]
    constructor <;> nlinarith

end LLS.Thm14
