import Mathlib

/-!
# One Euler–Maclaurin step for `x ↦ x^{-s}`, with a positive kernel

For `n > 0` real and `s ≠ 1`, with `f(x) = x^{-s}`:

`r n s = (f(n) + f(n+1))/2 - (n^{1-s} - (n+1)^{1-s})/(s-1) - (f'(n+1) - f'(n))/12
       = -∫₀¹ K(u) f''''(n+u) du`,  `K(u) = u²(1-u)²/24`,

by one application of the fundamental theorem of calculus to
`G(u) = K f''' - K' f'' + K'' f' - K''' f + F` (`F' = f`, `K'''' = 1`). Hence
`‖r n s‖ ≤ ‖s(s+1)(s+2)(s+3)‖ n^{-σ-4} / 384` for `σ ≥ -4`.
-/

open Complex intervalIntegral

namespace Speiser.Band

/-- The Peano kernel and its derivatives. -/
noncomputable def K0 (u : ℝ) : ℝ := u ^ 2 * (1 - u) ^ 2 / 24
noncomputable def K1 (u : ℝ) : ℝ := u * (1 - u) * (1 - 2 * u) / 12
noncomputable def K2 (u : ℝ) : ℝ := (6 * u ^ 2 - 6 * u + 1) / 12
noncomputable def K3 (u : ℝ) : ℝ := u - 1 / 2

/-- `s(s+1)(s+2)(s+3)`. -/
def P4 (s : ℂ) : ℂ := s * (s + 1) * (s + 2) * (s + 3)

/-- The Euler–Maclaurin remainder on `[n, n+1]`. -/
noncomputable def emR (n : ℝ) (s : ℂ) : ℂ :=
  (((n : ℂ)) ^ (-s) + ((n : ℂ) + 1) ^ (-s)) / 2 -
    (((n : ℂ)) ^ (1 - s) - ((n : ℂ) + 1) ^ (1 - s)) / (s - 1) -
    (-s * ((n : ℂ) + 1) ^ (-s - 1) - (-s * ((n : ℂ)) ^ (-s - 1))) / 12

lemma hasDerivAt_shift_cpow {n : ℝ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) (a b : ℂ)
    (hab : b = a - 1) :
    HasDerivAt (fun y : ℝ => ((n : ℂ) + y) ^ a) (a * ((n : ℂ) + u) ^ b) u := by
  have hmem : (n : ℂ) + (u : ℂ) ∈ slitPlane := by
    rw [show (n : ℂ) + (u : ℂ) = ((n + u : ℝ) : ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (by linarith)
  have h := (((hasDerivAt_id (u : ℂ)).const_add (n : ℂ)).cpow_const (c := a) hmem)
  have h2 := h.comp_ofReal (z := u)
  rw [hab]
  simpa using h2

lemma hasDerivAt_K (u : ℝ) :
    HasDerivAt (fun y : ℝ => ((K0 y : ℝ) : ℂ)) ((K1 u : ℝ) : ℂ) u ∧
    HasDerivAt (fun y : ℝ => ((K1 y : ℝ) : ℂ)) ((K2 u : ℝ) : ℂ) u ∧
    HasDerivAt (fun y : ℝ => ((K2 y : ℝ) : ℂ)) ((K3 u : ℝ) : ℂ) u ∧
    HasDerivAt (fun y : ℝ => ((K3 y : ℝ) : ℂ)) 1 u := by
  have e0 : HasDerivAt K0 (K1 u) u := by
    have := ((hasDerivAt_pow 2 u).mul ((hasDerivAt_id u).const_sub 1 |>.pow 2)).div_const 24
    convert this using 1
    · funext y; simp [K0]
    · simp [K1]; ring
  have e1 : HasDerivAt K1 (K2 u) u := by
    have := (((hasDerivAt_id u).mul ((hasDerivAt_id u).const_sub 1)).mul
      (((hasDerivAt_id u).const_mul 2).const_sub 1)).div_const 12
    convert this using 1
    · funext y; simp [K1]
    · simp [K2]; ring
  have e2 : HasDerivAt K2 (K3 u) u := by
    have := ((((hasDerivAt_pow 2 u).const_mul 6).sub ((hasDerivAt_id u).const_mul 6)).add_const
      1).div_const 12
    convert this using 1
    · funext y; simp [K2]
    · simp [K3]; ring
  have e3 : HasDerivAt K3 1 u := by
    unfold K3; exact (hasDerivAt_id' u).sub_const (1 / 2 : ℝ)
  exact ⟨e0.ofReal_comp, e1.ofReal_comp, e2.ofReal_comp, by simpa using e3.ofReal_comp⟩

/-- The antiderivative `G`. -/
noncomputable def emG (n : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  ((K0 u : ℝ) : ℂ) * (-(s * (s + 1) * (s + 2)) * ((n : ℂ) + u) ^ (-s - 3)) -
    ((K1 u : ℝ) : ℂ) * (s * (s + 1) * ((n : ℂ) + u) ^ (-s - 2)) +
    ((K2 u : ℝ) : ℂ) * (-s * ((n : ℂ) + u) ^ (-s - 1)) -
    ((K3 u : ℝ) : ℂ) * ((n : ℂ) + u) ^ (-s) +
    ((n : ℂ) + u) ^ (1 - s) / (1 - s)

lemma hasDerivAt_emG {n : ℝ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 1) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (emG n s) (((K0 u : ℝ) : ℂ) * (P4 s * ((n : ℂ) + u) ^ (-s - 4))) u := by
  obtain ⟨k0, k1, k2, k3⟩ := hasDerivAt_K u
  have p0 := hasDerivAt_shift_cpow hn hu (-s) (-s - 1) (by ring)
  have p1 := hasDerivAt_shift_cpow hn hu (-s - 1) (-s - 2) (by ring)
  have p2 := hasDerivAt_shift_cpow hn hu (-s - 2) (-s - 3) (by ring)
  have p3 := hasDerivAt_shift_cpow hn hu (-s - 3) (-s - 4) (by ring)
  have pF := hasDerivAt_shift_cpow hn hu (1 - s) (-s) (by ring)
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have h := ((((k0.mul (p3.const_mul (-(s * (s + 1) * (s + 2))))).sub
    (k1.mul (p2.const_mul (s * (s + 1))))).add (k2.mul (p1.const_mul (-s)))).sub
    (k3.mul p0)).add (pF.div_const (1 - s))
  convert h using 1
  · funext y; simp only [emG, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · simp only [P4]
    field_simp
    ring

lemma emG_one_sub_zero {n : ℝ} (s : ℂ) :
    emG n s 1 - emG n s 0 =
      (-s * ((n : ℂ) + 1) ^ (-s - 1) - (-s * ((n : ℂ)) ^ (-s - 1))) / 12 -
        (((n : ℂ)) ^ (-s) + ((n : ℂ) + 1) ^ (-s)) / 2 +
        (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ)) ^ (1 - s)) / (1 - s) := by
  simp only [emG, K0, K1, K2, K3]
  push_cast
  ring_nf

lemma continuousAt_integrand {n : ℝ} (hn : 0 < n) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ContinuousAt (fun y : ℝ => ((K0 y : ℝ) : ℂ) * (P4 s * ((n : ℂ) + y) ^ (-s - 4))) u := by
  have hK : Continuous fun y : ℝ => ((K0 y : ℝ) : ℂ) := by
    unfold K0; fun_prop
  exact hK.continuousAt.mul
    ((hasDerivAt_shift_cpow hn hu (-s - 4) (-s - 5) (by ring)).continuousAt.const_mul _)

/-- **The remainder as an integral against the positive kernel.** -/
theorem emR_eq_integral {n : ℝ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 1) :
    emR n s = -∫ u in (0 : ℝ)..1, ((K0 u : ℝ) : ℂ) * (P4 s * ((n : ℂ) + u) ^ (-s - 4)) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (emG n s)
      (((K0 x : ℝ) : ℂ) * (P4 s * ((n : ℂ) + x) ^ (-s - 4))) x := fun x hx => by
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact hasDerivAt_emG hn hs hx.1
  have hint : IntervalIntegrable
      (fun u : ℝ => ((K0 u : ℝ) : ℂ) * (P4 s * ((n : ℂ) + u) ^ (-s - 4))) MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact (continuousAt_integrand hn s hx.1).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, emG_one_sub_zero, emR]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

lemma K0_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ K0 u ∧ K0 u ≤ 1 / 384 := by
  unfold K0
  have h : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have h' : 0 ≤ u * (1 - u) := mul_nonneg h0 (by linarith)
  constructor
  · positivity
  · have : u ^ 2 * (1 - u) ^ 2 = (u * (1 - u)) ^ 2 := by ring
    rw [this]
    nlinarith

lemma norm_shift_cpow_le {n : ℝ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) {a : ℂ} (ha : a.re ≤ 0) :
    ‖((n : ℂ) + u) ^ a‖ ≤ n ^ a.re := by
  rw [show (n : ℂ) + (u : ℂ) = ((n + u : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact Real.rpow_le_rpow_of_nonpos hn (by linarith) ha

/-- **The remainder bound** `‖r n s‖ ≤ ‖P₄(s)‖ n^{-σ-4} / 384`. -/
theorem norm_emR_le {n : ℝ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 1) (hσ : -4 ≤ s.re) :
    ‖emR n s‖ ≤ ‖P4 s‖ * n ^ (-s.re - 4) / 384 := by
  rw [emR_eq_integral hn hs, norm_neg]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖((K0 u : ℝ) : ℂ) * (P4 s * ((n : ℂ) + u) ^ (-s - 4))‖ ≤ ‖P4 s‖ * n ^ (-s.re - 4) / 384 := by
    intro u hu
    rw [Set.uIoc_of_le zero_le_one] at hu
    obtain ⟨hk0, hk1⟩ := K0_le hu.1.le hu.2
    have hp := norm_shift_cpow_le hn hu.1.le (a := -s - 4) (by simp; linarith)
    have hre : (-s - 4).re = -s.re - 4 := by simp
    rw [hre] at hp
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0]
    have h0 : 0 ≤ ‖P4 s‖ * ‖((n : ℂ) + u) ^ (-s - 4)‖ := by positivity
    calc K0 u * (‖P4 s‖ * ‖((n : ℂ) + u) ^ (-s - 4)‖)
        ≤ 1 / 384 * (‖P4 s‖ * n ^ (-s.re - 4)) := by
          apply mul_le_mul hk1 (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) h0 (by norm_num)
      _ = ‖P4 s‖ * n ^ (-s.re - 4) / 384 := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

end Speiser.Band
