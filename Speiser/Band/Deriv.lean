import Speiser.Band.Zeta

/-!
# `ζ'` on the band: main part, its derivative, and the tail by Cauchy's estimate

With `N = 9`, on the boxes `U± = {-1 < σ < 2, 1 < ±t < 10}`:

* `ζ = mainM 9 + tailT 9` (Euler–Maclaurin), hence `ζ' = M1 + T'`, where `M1` is the explicit
  derivative of the main part (`hasDerivAt_mainM`), and `M1' = M2` (`hasDerivAt_M1`);
* `‖T(z)‖ ≤ P(‖z‖)/147456` for `Re z ≥ -1/2`, with `P(a) = a(a+1)(a+2)(a+3)`
  (`norm_tailT_le`), so `‖T'(s)‖ ≤ P(‖s‖ + ρ)/(147456 ρ)` when `Re s ≥ ρ - 1/2`
  (`norm_deriv_tailT_le`).
-/

open Complex Filter Topology

namespace Speiser.Band

/-- `n^{-s}`. -/
noncomputable def E (n : ℕ) (s : ℂ) : ℂ := (n : ℂ) ^ (-s)

/-- `log n`, as a complex number. -/
noncomputable def ell (n : ℕ) : ℂ := (Real.log n : ℂ)

lemma hasDerivAt_E {n : ℕ} (hn : n ≠ 0) (s : ℂ) : HasDerivAt (E n) (-(ell n * E n s)) s := by
  have h := (hasDerivAt_neg s).const_cpow (c := (n : ℂ)) (Or.inl (by exact_mod_cast hn))
  unfold E ell
  convert h using 1
  rw [show Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]]
  ring

/-- The derivative of the main part, in the shape the checker evaluates. -/
noncomputable def M1 (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.range 7, -(ell (k + 2) * E (k + 2) s)) - ell 9 * E 9 s / 2 -
    9 * (ell 9 * E 9 s * (1 / (s - 1))) - 9 * (E 9 s * ((1 / (s - 1)) * (1 / (s - 1)))) +
    (E 9 s - s * (ell 9 * E 9 s)) / 108

/-- Its derivative. -/
noncomputable def M2 (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.range 7, ell (k + 2) ^ 2 * E (k + 2) s) + ell 9 ^ 2 * E 9 s / 2 +
    9 * E 9 s * (ell 9 ^ 2 * (1 / (s - 1)) + 2 * ell 9 * (1 / (s - 1)) ^ 2 +
      2 * (1 / (s - 1)) ^ 3) +
    E 9 s * (-2 * ell 9 + s * ell 9 ^ 2) / 108

lemma mainM_nine (s : ℂ) :
    mainM 9 s = 1 + (∑ k ∈ Finset.range 7, E (k + 2) s) + E 9 s / 2 +
      9 * E 9 s / (s - 1) + s * E 9 s / 108 := by
  unfold mainM
  have h9 : (9 : ℂ) ≠ 0 := by norm_num
  have e1 : (9 : ℂ) ^ (1 - s) = 9 * (9 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, cpow_add _ _ h9, cpow_one]
  have e2 : (9 : ℂ) ^ (-s - 1) = (9 : ℂ) ^ (-s) / 9 := by
    rw [show -s - 1 = -s + -1 by ring, cpow_add _ _ h9, cpow_neg_one]; field_simp
  have hN : ((9 : ℕ) : ℂ) = 9 := by norm_num
  simp only [hN, e1, e2, show (9 : ℕ) - 1 = 8 by rfl]
  rw [Finset.sum_range_succ' _ 7]
  have hf : ∀ k ∈ Finset.range 7, (((k + 1 : ℕ) : ℂ) + 1) ^ (-s) = E (k + 2) s := fun k _ => by
    simp only [E]; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl hf]
  simp only [Nat.cast_zero, zero_add, one_cpow]
  simp only [E]
  push_cast
  ring

lemma hasDerivAt_mainM {s : ℂ} (hs : s ≠ 1) : HasDerivAt (mainM 9) (M1 s) s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hsum : HasDerivAt (fun z => ∑ k ∈ Finset.range 7, E (k + 2) z)
      (∑ k ∈ Finset.range 7, -(ell (k + 2) * E (k + 2) s)) s :=
    HasDerivAt.fun_sum fun k _ => hasDerivAt_E (by omega) s
  have h9 := hasDerivAt_E (n := 9) (by norm_num) s
  have hinv : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have h := ((((hasDerivAt_const s (1 : ℂ)).add hsum).add (h9.div_const 2)).add
    ((h9.const_mul 9).div hinv hs1)).add (((hasDerivAt_id s).mul h9).div_const 108)
  have heq : mainM 9 = fun z => 1 + (∑ k ∈ Finset.range 7, E (k + 2) z) + E 9 z / 2 +
      9 * E 9 z / (z - 1) + z * E 9 z / 108 := funext mainM_nine
  rw [heq]
  convert h using 1
  · funext z; simp
  · unfold M1
    simp only [id]
    field_simp
    ring

lemma hasDerivAt_M1 {s : ℂ} (hs : s ≠ 1) : HasDerivAt M1 (M2 s) s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hsum : HasDerivAt (fun z => ∑ k ∈ Finset.range 7, -(ell (k + 2) * E (k + 2) z))
      (∑ k ∈ Finset.range 7, ell (k + 2) ^ 2 * E (k + 2) s) s := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    convert ((hasDerivAt_E (n := k + 2) (by omega) s).const_mul (ell (k + 2))).neg using 1
    ring
  have h9 := hasDerivAt_E (n := 9) (by norm_num) s
  have hu : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-(1 / (s - 1)) ^ 2) s := by
    have := ((hasDerivAt_id s).sub_const 1).inv hs1
    convert this using 1
    · funext z; simp
    · simp; field_simp
  have h := (((hsum.sub ((h9.const_mul (ell 9)).div_const 2)).sub
    ((((h9.const_mul (ell 9)).mul hu)).const_mul 9)).sub
    ((h9.mul (hu.mul hu)).const_mul 9)).add
    ((h9.sub ((hasDerivAt_id s).mul (h9.const_mul (ell 9)))).div_const 108)
  convert h using 1
  · funext z; simp only [M1, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id]
  · unfold M2
    simp only [id, Pi.mul_apply]
    field_simp
    ring

/-! ### The boxes `U±` -/

/-- `{-1 < σ < 2, 1 < t < 10}` (`sgn = 1`) and its mirror image (`sgn = -1`). -/
def Ubox (sgn : ℝ) : Set ℂ := {s | -1 < s.re ∧ s.re < 2 ∧ 1 < sgn * s.im ∧ sgn * s.im < 10}

lemma isOpen_Ubox (sgn : ℝ) : IsOpen (Ubox sgn) := by
  have hc : Continuous fun s : ℂ => sgn * s.im := continuous_const.mul continuous_im
  have := ((isOpen_lt (f := fun _ : ℂ => (-1 : ℝ)) continuous_const continuous_re).inter
    (isOpen_lt (g := fun _ : ℂ => (2 : ℝ)) continuous_re continuous_const)).inter
    ((isOpen_lt (f := fun _ : ℂ => (1 : ℝ)) continuous_const hc).inter
    (isOpen_lt (g := fun _ : ℂ => (10 : ℝ)) hc continuous_const))
  convert this using 1
  ext s; simp [Ubox, and_assoc]

lemma convex_Ubox (sgn : ℝ) : Convex ℝ (Ubox sgn) := by
  have h1 : Convex ℝ {s : ℂ | -1 < s.re} := convex_halfSpace_re_gt _
  have h2 : Convex ℝ {s : ℂ | s.re < 2} := convex_halfSpace_re_lt _
  have h3 := (convex_Ioi (1 : ℝ)).linear_preimage (sgn • Complex.imLm)
  have h4 := (convex_Iio (10 : ℝ)).linear_preimage (sgn • Complex.imLm)
  have : Ubox sgn = {s : ℂ | -1 < s.re} ∩ {s | s.re < 2} ∩
      ((sgn • Complex.imLm) ⁻¹' Set.Ioi 1 ∩ (sgn • Complex.imLm) ⁻¹' Set.Iio 10) := by
    ext s; simp [Ubox, and_assoc]
  rw [this]
  exact (h1.inter h2).inter (h3.inter h4)

lemma Ubox_props {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) {s : ℂ} (hs : s ∈ Ubox sgn) :
    s ≠ 1 ∧ -2 < s.re ∧ ‖s‖ ≤ 12 := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have him : |s.im| < 10 ∧ 1 < |s.im| := by
    rcases hsgn with rfl | rfl
    · simp at h3 h4; exact ⟨abs_lt.mpr ⟨by linarith, h4⟩, by rw [abs_of_pos (by linarith)]; exact h3⟩
    · simp at h3 h4
      exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, by rw [abs_of_neg (by linarith)]; linarith⟩
  refine ⟨fun h => by rw [h] at him; simp at him; linarith, by linarith, ?_⟩
  calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ 12 := by have := abs_lt.mpr ⟨(by linarith : -2 < s.re), h2⟩; linarith

lemma eqOn_Ubox {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) :
    Set.EqOn riemannZeta (zetaEM 9) (Ubox sgn) := by
  refine riemannZeta_eqOn_zetaEM 9 (by norm_num) (isOpen_Ubox sgn) (convex_Ubox sgn)
    (fun s hs => Ubox_props hsgn hs) (z₀ := ⟨3 / 2, 5 * sgn⟩) ?_ (by norm_num)
  rcases hsgn with rfl | rfl <;> simp [Ubox] <;> norm_num

/-- **`ζ' = M1 + T'` on `U±`.** -/
theorem deriv_riemannZeta_eq {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) {s : ℂ}
    (hs : s ∈ Ubox sgn) : deriv riemannZeta s = M1 s + deriv (tailT 9) s := by
  have hev : riemannZeta =ᶠ[𝓝 s] zetaEM 9 :=
    Filter.eventuallyEq_of_mem ((isOpen_Ubox sgn).mem_nhds hs) (eqOn_Ubox hsgn)
  rw [hev.deriv_eq]
  have hT := (differentiableOn_tailT 9 (by norm_num) (isOpen_Ubox sgn)
    (fun s hs => Ubox_props hsgn hs) s hs).differentiableAt ((isOpen_Ubox sgn).mem_nhds hs)
  have hM := hasDerivAt_mainM (Ubox_props hsgn hs).1
  exact (hM.add hT.hasDerivAt).deriv

/-! ### The tail -/

lemma sum_inv_cube_le (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / (((9 + k : ℕ) : ℝ) ^ 3) ≤ 1 / 128 - 1 / (2 * ((8 + K : ℕ) : ℝ) ^ 2) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hK : (8 : ℝ) ≤ ((8 + K : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right 8 K
    have e1 : ((9 + K : ℕ) : ℝ) = ((8 + K : ℕ) : ℝ) + 1 := by push_cast; ring
    have e2 : ((8 + (K + 1) : ℕ) : ℝ) = ((8 + K : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    set x := ((8 + K : ℕ) : ℝ)
    have hx : 0 < x := by linarith
    have key : 1 / (x + 1) ^ 3 ≤ 1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [sq_nonneg x, mul_pos hx hx, pow_pos hx 3, pow_pos hx 4]
    linarith

lemma tsum_inv_cube_le : ∑' k : ℕ, 1 / (((9 + k : ℕ) : ℝ) ^ 3) ≤ 1 / 128 := by
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) fun K => ?_
  have := sum_inv_cube_le K
  have : 0 ≤ 1 / (2 * ((8 + K : ℕ) : ℝ) ^ 2) := by positivity
  linarith

lemma rpow_le_inv_cube (k : ℕ) {a : ℝ} (ha : a ≤ -7 / 2) :
    ((9 + k : ℕ) : ℝ) ^ a ≤ 1 / 3 * (1 / (((9 + k : ℕ) : ℝ) ^ 3)) := by
  have hx9 : (9 : ℝ) ≤ ((9 + k : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right 9 k
  set x := ((9 + k : ℕ) : ℝ)
  have hx : 0 < x := by linarith
  have h1 : x ^ a ≤ x ^ (-7 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
  have h2 : x ^ (-7 / 2 : ℝ) = x ^ (-1 / 2 : ℝ) * (x ^ 3)⁻¹ := by
    rw [show (-7 / 2 : ℝ) = -1 / 2 + (-3 : ℤ) by norm_num, Real.rpow_add hx, Real.rpow_intCast,
      zpow_neg, zpow_ofNat]
  have h3 : x ^ (-1 / 2 : ℝ) ≤ 1 / 3 := by
    have h9 : (9 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 3 := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← h9]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hx9 (by norm_num)
  rw [h2] at h1
  calc x ^ a ≤ x ^ (-1 / 2 : ℝ) * (x ^ 3)⁻¹ := h1
    _ ≤ 1 / 3 * (x ^ 3)⁻¹ := by gcongr
    _ = _ := by rw [one_div (x ^ 3)]

/-- `P(a) = a (a+1) (a+2) (a+3)`. -/
def Pa (a : ℝ) : ℝ := a * (a + 1) * (a + 2) * (a + 3)

lemma norm_P4_le_Pa (z : ℂ) : ‖P4 z‖ ≤ Pa ‖z‖ := by
  unfold P4 Pa
  have h1 : ‖z + 1‖ ≤ ‖z‖ + 1 := by have := norm_add_le z 1; simpa using this
  have h2 : ‖z + 2‖ ≤ ‖z‖ + 2 := by have := norm_add_le z 2; norm_num at this ⊢; linarith
  have h3 : ‖z + 3‖ ≤ ‖z‖ + 3 := by have := norm_add_le z 3; norm_num at this ⊢; linarith
  rw [norm_mul, norm_mul, norm_mul]
  gcongr

/-- **The tail bound** for `Re z ≥ -1/2`. -/
theorem norm_tailT_le {z : ℂ} (hz : z ≠ 1) (hre : -1 / 2 ≤ z.re) :
    ‖tailT 9 z‖ ≤ Pa ‖z‖ / 147456 := by
  have hsum := summable_emR 9 (by norm_num) hz (by linarith)
  have hb : ∀ k : ℕ, ‖emR ((9 + k : ℕ) : ℝ) z‖ ≤
      Pa ‖z‖ / 384 * (1 / 3 * (1 / (((9 + k : ℕ) : ℝ) ^ 3))) := fun k => by
    have hpos := natCast_add_pos 9 k (by norm_num)
    have h := norm_emR_le hpos hz (by linarith)
    have h2 := rpow_le_inv_cube k (a := -z.re - 4) (by linarith)
    have h3 := norm_P4_le_Pa z
    calc ‖emR ((9 + k : ℕ) : ℝ) z‖ ≤ ‖P4 z‖ * ((9 + k : ℕ) : ℝ) ^ (-z.re - 4) / 384 := h
      _ ≤ Pa ‖z‖ * (1 / 3 * (1 / (((9 + k : ℕ) : ℝ) ^ 3))) / 384 := by
          gcongr
          · exact (norm_nonneg _).trans h3
      _ = _ := by ring
  have hs3 : Summable fun k : ℕ => 1 / (((9 + k : ℕ) : ℝ) ^ 3) := by
    have := summable_shift_rpow 9 (a := -3) (by norm_num)
    refine this.congr fun k => ?_
    rw [Real.rpow_neg (by positivity), one_div]; norm_cast
  calc ‖tailT 9 z‖ ≤ ∑' k : ℕ, Pa ‖z‖ / 384 * (1 / 3 * (1 / (((9 + k : ℕ) : ℝ) ^ 3))) :=
        tsum_of_norm_bounded ((hs3.mul_left (1 / 3)).mul_left _).hasSum hb
    _ = Pa ‖z‖ / 384 * (1 / 3 * ∑' k : ℕ, 1 / (((9 + k : ℕ) : ℝ) ^ 3)) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ ≤ Pa ‖z‖ / 384 * (1 / 3 * (1 / 128)) := by
        have : 0 ≤ Pa ‖z‖ := by unfold Pa; positivity
        gcongr
        exact tsum_inv_cube_le
    _ = Pa ‖z‖ / 147456 := by ring

lemma Pa_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : Pa a ≤ Pa b := by
  unfold Pa
  have hb : 0 ≤ b := ha.trans hab
  have e1 : a * (a + 1) ≤ b * (b + 1) := mul_le_mul hab (by linarith) (by linarith) hb
  have e2 : a * (a + 1) * (a + 2) ≤ b * (b + 1) * (b + 2) :=
    mul_le_mul e1 (by linarith) (by linarith) (by positivity)
  exact mul_le_mul e2 (by linarith) (by linarith) (by positivity)

/-- **Cauchy's estimate for `T'`.** -/
theorem norm_deriv_tailT_le {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall s ρ ⊆ Ubox sgn) (hre : -1 / 2 ≤ s.re - ρ) :
    ‖deriv (tailT 9) s‖ ≤ Pa (‖s‖ + ρ) / 147456 / ρ := by
  have hdT := differentiableOn_tailT 9 (by norm_num) (isOpen_Ubox sgn)
    (fun s hs => Ubox_props hsgn hs)
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
    (hdT.diffContOnCl_ball hball) fun z hz => ?_
  have hzb : z ∈ Metric.closedBall s ρ := Metric.sphere_subset_closedBall hz
  have hz1 := (Ubox_props hsgn (hball hzb)).1
  have hdist : ‖z - s‖ = ρ := by rw [← dist_eq_norm]; exact hz
  have hrez : -1 / 2 ≤ z.re := by
    have := Complex.abs_re_le_norm (z - s)
    rw [hdist] at this
    have := (abs_le.mp this).1
    simp at this; linarith
  refine (norm_tailT_le hz1 hrez).trans ?_
  have : ‖z‖ ≤ ‖s‖ + ρ := by
    calc ‖z‖ = ‖s + (z - s)‖ := by ring_nf
      _ ≤ ‖s‖ + ‖z - s‖ := norm_add_le _ _
      _ = ‖s‖ + ρ := by rw [hdist]
  gcongr
  exact Pa_mono (norm_nonneg _) this

/-- **Mean value bound for `M1`** on a closed disc inside `U±`. -/
theorem norm_M1_sub_le {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) {c s : ℂ} {r C : ℝ}
    (hball : Metric.closedBall c r ⊆ Ubox sgn) (hs : s ∈ Metric.closedBall c r)
    (hC : ∀ w ∈ Metric.closedBall c r, ‖M2 w‖ ≤ C) : ‖M1 s - M1 c‖ ≤ C * r := by
  have hc : c ∈ Metric.closedBall c r := Metric.mem_closedBall_self (dist_nonneg.trans hs)
  have h := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
    (f := M1) (fun w hw => (hasDerivAt_M1 (Ubox_props hsgn (hball hw)).1).differentiableAt)
    (fun w hw => by rw [(hasDerivAt_M1 (Ubox_props hsgn (hball hw)).1).deriv]; exact hC w hw)
    hc hs
  refine h.trans ?_
  have : ‖s - c‖ ≤ r := by rw [← dist_eq_norm]; exact hs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC c hc)
  exact mul_le_mul_of_nonneg_left this hC0

end Speiser.Band
