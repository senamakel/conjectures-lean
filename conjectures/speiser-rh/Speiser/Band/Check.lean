import Speiser.Band.Sound
import Speiser.Band.Logs
import Speiser.Band.Deriv

/-!
# What `cellOK` and `coverOK` certify

* `mem_npow`: `n^{-c} ∈ npow n x y` (`2 ≤ n ≤ 9`, `c = (x+iy)/δ`).
* `mem_M1`: `M1 c ∈ SpeiserCompute.M1 x y`.
* `norm_M2_le`: `‖M2 w‖ ≤ BM/δ` on the cell's disc.
* `deriv_ne_zero_of_cellOK`, `deriv_ne_zero_of_coverOK`: no zero of `ζ'` in a certified box.
-/

open Complex SpeiserCompute

namespace Speiser.Band

/-! ### Logarithms -/

lemma mem_of_bounds {L : ℝ} {lo hi : ℤ} (h1 : (lo : ℝ) / δ ≤ L) (h2 : L ≤ (hi : ℝ) / δ) :
    Mem (L : ℂ) ⟨(lo + hi) / 2, 0, cdiv (hi - lo) 2 + 1⟩ := by
  have hδ := δ_pos
  have hm1 := ediv_le_real (lo + hi) (by norm_num : (0 : ℤ) < 2)
  have hm2 := lt_ediv_real (lo + hi) (by norm_num : (0 : ℤ) < 2)
  have hc := le_cdiv_real (hi - lo) (by norm_num : (0 : ℤ) < 2)
  unfold Mem
  have e : (L : ℂ) - (⟨(lo + hi) / 2, 0, cdiv (hi - lo) 2 + 1⟩ : Disc).c =
      ((L - (((lo + hi) / 2 : ℤ) : ℝ) / δ : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Disc.c]
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  rw [div_le_iff₀ hδ] at h1
  rw [le_div_iff₀ hδ] at h2
  push_cast at hm1 hm2 hc ⊢
  have key : |L * δ - (((lo + hi) / 2 : ℤ) : ℝ)| ≤ ((cdiv (hi - lo) 2 : ℤ) : ℝ) + 1 := by
    rw [abs_le]; constructor <;> linarith
  have e2 : L - (((lo + hi) / 2 : ℤ) : ℝ) / δ = (L * δ - (((lo + hi) / 2 : ℤ) : ℝ)) / δ := by
    field_simp
  rw [e2, abs_div, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right key hδ.le

lemma logP_bounds {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7) :
    ((logLoP p : ℤ) : ℝ) / δ ≤ Real.log p ∧ Real.log p ≤ ((logHiP p : ℤ) : ℝ) / δ := by
  have hδ := δ_pos
  obtain ⟨h1, h2⟩ := logQ_bounds hp
  have hq : (0 : ℤ) < 1000000000000 := by norm_num
  constructor
  · have e := ediv_le_real (logLoQ p * D) hq
    unfold logLoP
    calc ((logLoQ p * D / 1000000000000 : ℤ) : ℝ) / δ ≤
          ((logLoQ p * D : ℤ) : ℝ) / ((1000000000000 : ℤ) : ℝ) / δ :=
          div_le_div_of_nonneg_right e hδ.le
      _ = ((logLoQ p : ℤ) : ℝ) / 10 ^ 12 := by
          have hD : ((D : ℤ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D_pos)
          unfold δ; push_cast; field_simp; ring
      _ ≤ _ := h1
  · have e := le_cdiv_real (logHiQ p * D) hq
    unfold logHiP
    calc Real.log p ≤ ((logHiQ p : ℤ) : ℝ) / 10 ^ 12 := h2
      _ = ((logHiQ p * D : ℤ) : ℝ) / ((1000000000000 : ℤ) : ℝ) / δ := by
          have hD : ((D : ℤ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D_pos)
          unfold δ; push_cast; field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right e hδ.le

lemma log_bounds_scaled {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) :
    ((logLo n : ℤ) : ℝ) / δ ≤ Real.log n ∧ Real.log n ≤ ((logHi n : ℤ) : ℝ) / δ := by
  have b2 := logP_bounds (p := 2) (by norm_num)
  have b3 := logP_bounds (p := 3) (by norm_num)
  have b5 := logP_bounds (p := 5) (by norm_num)
  have b7 := logP_bounds (p := 7) (by norm_num)
  have l4 : Real.log (4 : ℕ) = 2 * Real.log (2 : ℕ) := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have l6 : Real.log (6 : ℕ) = Real.log (2 : ℕ) + Real.log (3 : ℕ) := by
    rw [show ((6 : ℕ) : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    push_cast; ring
  have l8 : Real.log (8 : ℕ) = 3 * Real.log (2 : ℕ) := by
    rw [show ((8 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have l9 : Real.log (9 : ℕ) = 2 * Real.log (3 : ℕ) := by
    rw [show ((9 : ℕ) : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  interval_cases n
  · simpa [logLo, logHi] using b2
  · simpa [logLo, logHi] using b3
  · simp only [logLo, logHi]; rw [l4]; push_cast
    constructor <;> [rw [mul_div_assoc]; rw [mul_div_assoc]] <;> linarith [b2.1, b2.2]
  · simpa [logLo, logHi] using b5
  · simp only [logLo, logHi]; rw [l6]; push_cast
    rw [add_div, add_div]; constructor <;> linarith [b2.1, b2.2, b3.1, b3.2]
  · simpa [logLo, logHi] using b7
  · simp only [logLo, logHi]; rw [l8]; push_cast
    constructor <;> [rw [mul_div_assoc]; rw [mul_div_assoc]] <;> linarith [b2.1, b2.2]
  · simp only [logLo, logHi]; rw [l9]; push_cast
    constructor <;> [rw [mul_div_assoc]; rw [mul_div_assoc]] <;> linarith [b3.1, b3.2]

lemma mem_logD {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) : Mem (Real.log n : ℂ) (logD n) := by
  obtain ⟨h1, h2⟩ := log_bounds_scaled hn2 hn9
  exact mem_of_bounds h1 h2

lemma ell_eq_log (n : ℕ) : ell n = (Real.log n : ℂ) := rfl

/-! ### Powers -/

lemma c_neg_pt (x y : ℤ) : (Disc.pt (-x) (-y)).c = -(Disc.pt x y).c := by
  apply Complex.ext <;> simp [c_pt] <;> ring

lemma mem_npowArg {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) (x y : ℤ) :
    Mem (-(Disc.pt x y).c * (Real.log n : ℂ)) (npowArg n x y) := by
  rw [← c_neg_pt]
  exact mem_mul (mem_pt _ _) (mem_logD hn2 hn9)

lemma mem_npow {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) {x y : ℤ}
    (hok : expOK (npowArg n x y) = true) : Mem (E n (Disc.pt x y).c) (npow n x y) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have e : E n (Disc.pt x y).c = Complex.exp (-(Disc.pt x y).c * (Real.log n : ℂ)) := by
    unfold E
    rw [cpow_def_of_ne_zero hn0, show Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]]
    ring_nf
  rw [e]
  exact mem_expDisc (mem_npowArg hn2 hn9 x y) hok

/-! ### Folding sums -/

lemma mem_foldl_add (f : ℕ → ℂ) (g : ℕ → Disc) (n : ℕ) (h : ∀ k < n, Mem (f k) (g k))
    {z : ℂ} {init : Disc} (hz : Mem z init) :
    Mem (z + ∑ k ∈ Finset.range n, f k)
      ((List.range n).foldl (fun acc k => acc.add (g k)) init) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← add_assoc]
    exact mem_add (ih fun k hk => h k (by omega)) (h n (by omega))

/-! ### The main part -/

lemma c_pt_sub_D (x y : ℤ) : (Disc.pt (x - D) y).c = (Disc.pt x y).c - 1 := by
  have hD : ((D : ℤ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D_pos)
  apply Complex.ext <;> simp [c_pt, δ] <;> field_simp <;> ring

/-- All the exponentials at the point `(x, y)` are sound. -/
lemma argsOK_point {x y sg : ℤ} (h : argsOK x y sg = true) {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) :
    expOK (npowArg n x y) = true ∧ expOK (npowArg n sg 0) = true := by
  unfold argsOK at h
  rw [List.all_eq_true] at h
  have := h (n - 2) (List.mem_range.mpr (by omega))
  rw [show n - 2 + 2 = n by omega] at this
  simpa [Bool.and_eq_true] using this

theorem mem_M1 {x y sg : ℤ} (hok : argsOK x y sg = true) (hy : y ≠ 0) :
    Mem (M1 (Disc.pt x y).c) (SpeiserCompute.M1 x y) := by
  set c := (Disc.pt x y).c
  have e9 := mem_npow (n := 9) (by norm_num) le_rfl (argsOK_point hok (n := 9) (by norm_num)
    le_rfl).1
  have l9 := mem_logD (n := 9) (by norm_num) le_rfl
  have hiv : Mem (1 / (c - 1)) (Disc.invPt (x - D) y) := by
    have := mem_invPt (x := x - D) (y := y)
      (ne_of_gt (by nlinarith [mul_self_pos.mpr hy, mul_self_nonneg (x - D)]))
    rwa [c_pt_sub_D] at this
  have hs8 := mem_foldl_add (fun k => -(ell (k + 2) * E (k + 2) c))
    (fun k => ((logD (k + 2)).mul (npow (k + 2) x y)).neg) 7
    (fun k hk => mem_neg (mem_mul (mem_logD (by omega) (by omega))
      (mem_npow (by omega) (by omega) (argsOK_point hok (n := k + 2) (by omega) (by omega)).1)))
    (mem_pt 0 0)
  have h0 : (Disc.pt 0 0).c = 0 := by apply Complex.ext <;> simp [c_pt]
  rw [h0, zero_add] at hs8
  have le9 := mem_mul l9 e9
  have t1 := mem_neg (mem_divInt (k := 2) (by norm_num) le9)
  have t2 := mem_neg (mem_smulInt 9 (mem_mul le9 hiv))
  have t3 := mem_neg (mem_smulInt 9 (mem_mul e9 (mem_mul hiv hiv)))
  have t4 := mem_divInt (k := 108) (by norm_num) (mem_sub e9 (mem_mul (mem_pt x y) le9))
  have h := mem_add (mem_add (mem_add (mem_add hs8 t1) t2) t3) t4
  have eq : M1 c = (∑ k ∈ Finset.range 7, -(ell (k + 2) * E (k + 2) c)) +
      -(↑(Real.log (9 : ℕ)) * E 9 c / ((2 : ℤ) : ℂ)) +
      -(((9 : ℤ) : ℂ) * (↑(Real.log (9 : ℕ)) * E 9 c * (1 / (c - 1)))) +
      -(((9 : ℤ) : ℂ) * (E 9 c * (1 / (c - 1) * (1 / (c - 1))))) +
      (E 9 c - c * (↑(Real.log (9 : ℕ)) * E 9 c)) / ((108 : ℤ) : ℂ) := by
    unfold M1; simp only [ell_eq_log]; push_cast; ring
  rw [eq]
  exact h

/-! ### The bound on `M2` -/

lemma foldl_add_eq (f : ℕ → ℤ) (n : ℕ) (init : ℤ) :
    (List.range n).foldl (fun acc k => acc + f k) init = init + ∑ k ∈ Finset.range n, f k := by
  induction n generalizing init with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; simp; ring

/-- `X Y ≤ ⌈a b / D⌉ / δ` from `0 ≤ X ≤ a/δ`, `0 ≤ Y ≤ b/δ`. -/
lemma mul_le_fmulUp {X Y : ℝ} {a b : ℤ} (hX : 0 ≤ X) (ha : X ≤ (a : ℝ) / δ) (hY : 0 ≤ Y)
    (hb : Y ≤ (b : ℝ) / δ) : X * Y ≤ ((fmulUp a b : ℤ) : ℝ) / δ :=
  (mul_le_mul ha hb hY (hX.trans ha)).trans (le_fmulUp a b)

lemma div_le_cdiv {X : ℝ} {a k : ℤ} (hk : 0 < k) (ha : X ≤ (a : ℝ) / δ) :
    X / k ≤ ((cdiv a k : ℤ) : ℝ) / δ := by
  have hδ := δ_pos
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := le_cdiv_real a hk
  calc X / k ≤ (a : ℝ) / δ / k := div_le_div_of_nonneg_right ha hk'.le
    _ = (a : ℝ) / k / δ := by ring
    _ ≤ _ := div_le_div_of_nonneg_right h hδ.le

/-- `X Y ≤ ⌈a b / D⌉ / δ` from `X ≤ a/δ` (`0 ≤ X`) and `0 ≤ Y ≤ b/δ`, in the form used for sums. -/
lemma mul_le_mul_fmulUp' {X Y : ℝ} {a b : ℤ} (ha : X ≤ (a : ℝ) / δ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hb : Y ≤ (b : ℝ) / δ) : X * Y ≤ ((fmulUp a b : ℤ) : ℝ) / δ :=
  mul_le_fmulUp hX ha hY hb

lemma norm_E_le {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) {sg : ℤ} (hok : expOK (npowArg n sg 0) = true)
    {w : ℂ} (hw : (sg : ℝ) / δ ≤ w.re) : ‖E n w‖ ≤ ((npowRe n sg : ℤ) : ℝ) / δ := by
  have hm := mem_npow hn2 hn9 hok
  have h1 := norm_le_of_mem hm
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have e1 : ‖E n w‖ = (n : ℝ) ^ (-w.re) := by
    unfold E
    rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; rfl, norm_cpow_eq_rpow_re_of_pos hn]
    simp
  have e2 : ‖E n (Disc.pt sg 0).c‖ = (n : ℝ) ^ (-((sg : ℝ) / δ)) := by
    unfold E
    rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; rfl, norm_cpow_eq_rpow_re_of_pos hn]
    simp [c_pt]
  rw [e1]
  calc (n : ℝ) ^ (-w.re) ≤ (n : ℝ) ^ (-((sg : ℝ) / δ)) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
    _ = ‖E n (Disc.pt sg 0).c‖ := e2.symm
    _ ≤ _ := h1

lemma norm_ell_le {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) :
    0 ≤ ‖ell n‖ ∧ ‖ell n‖ ≤ ((logHi n : ℤ) : ℝ) / δ := by
  refine ⟨norm_nonneg _, ?_⟩
  have h := (log_bounds_scaled hn2 hn9).2
  have hpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  rw [ell_eq_log, Complex.norm_real, Real.norm_of_nonneg hpos]
  exact h

lemma logHi_nonneg {n : ℕ} (hn2 : 2 ≤ n) (hn9 : n ≤ 9) : (0 : ℝ) ≤ ((logHi n : ℤ) : ℝ) / δ :=
  (norm_ell_le hn2 hn9).1.trans (norm_ell_le hn2 hn9).2

theorem norm_M2_le {sg A d : ℤ} (hok : ∀ n, 2 ≤ n → n ≤ 9 → expOK (npowArg n sg 0) = true)
    (hd : 0 < d) {w : ℂ} (hre : (sg : ℝ) / δ ≤ w.re) (hA : ‖w‖ ≤ (A : ℝ) / δ)
    (hw1 : (d : ℝ) / δ ≤ ‖w - 1‖) : ‖M2 w‖ ≤ ((BM sg A d : ℤ) : ℝ) / δ := by
  have hδ := δ_pos
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  -- elementary bounds
  have hE : ∀ n, 2 ≤ n → n ≤ 9 → ‖E n w‖ ≤ ((npowRe n sg : ℤ) : ℝ) / δ := fun n h2 h9 =>
    norm_E_le h2 h9 (hok n h2 h9) hre
  have hu : ‖1 / (w - 1)‖ ≤ ((cdiv (D * D) d : ℤ) : ℝ) / δ := by
    have hpos : 0 < ‖w - 1‖ := lt_of_lt_of_le (by positivity) hw1
    rw [norm_div, norm_one]
    calc 1 / ‖w - 1‖ ≤ 1 / ((d : ℝ) / δ) := one_div_le_one_div_of_le (by positivity) hw1
      _ = ((D * D : ℤ) : ℝ) / d / δ := by unfold δ; push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (le_cdiv_real _ hd) hδ.le
  set e9 := npowRe 9 sg
  set h9 := logHi 9
  set id := cdiv (D * D) d
  have hE9 := hE 9 (by norm_num) le_rfl
  have hl9 := norm_ell_le (n := 9) (by norm_num) le_rfl
  have hun := norm_nonneg (1 / (w - 1))
  have hEn := norm_nonneg (E 9 w)
  -- pieces
  have hsum : ‖∑ k ∈ Finset.range 7, ell (k + 2) ^ 2 * E (k + 2) w‖ ≤
      ((∑ k ∈ Finset.range 7, fmulUp (fmulUp (logHi (k + 2)) (logHi (k + 2)))
        (npowRe (k + 2) sg) : ℤ) : ℝ) / δ := by
    refine (norm_sum_le _ _).trans ?_
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk7 : k < 7 := Finset.mem_range.mp hk
    obtain ⟨h0, hl⟩ := norm_ell_le (n := k + 2) (by omega) (by omega)
    rw [norm_mul, norm_pow, pow_two]
    exact mul_le_fmulUp (mul_nonneg h0 h0) (mul_le_fmulUp h0 hl h0 hl) (norm_nonneg _)
      (hE (k + 2) (by omega) (by omega))
  set u := 1 / (w - 1)
  set L := ‖ell 9‖
  have hL0 : 0 ≤ L := hl9.1
  have hL2 : L * L ≤ ((fmulUp h9 h9 : ℤ) : ℝ) / δ := mul_le_fmulUp hL0 hl9.2 hL0 hl9.2
  have hu2 : ‖u‖ * ‖u‖ ≤ ((fmulUp id id : ℤ) : ℝ) / δ := mul_le_fmulUp hun hu hun hu
  have hu3 : ‖u‖ * ‖u‖ * ‖u‖ ≤ ((fmulUp (fmulUp id id) id : ℤ) : ℝ) / δ :=
    mul_le_fmulUp (mul_nonneg hun hun) hu2 hun hu
  have ha : ‖ell 9 ^ 2 * E 9 w / 2‖ ≤ ((cdiv (fmulUp (fmulUp h9 h9) e9) 2 : ℤ) : ℝ) / δ := by
    rw [norm_div, norm_mul, norm_pow, pow_two, show ‖(2 : ℂ)‖ = ((2 : ℤ) : ℝ) by simp]
    exact div_le_cdiv (by norm_num) (mul_le_fmulUp (mul_nonneg hL0 hL0) hL2 hEn hE9)
  have hB : ‖ell 9 ^ 2 * u + 2 * ell 9 * u ^ 2 + 2 * u ^ 3‖ ≤
      ((fmulUp (fmulUp h9 h9) id + 2 * fmulUp h9 (fmulUp id id) +
        2 * fmulUp (fmulUp id id) id : ℤ) : ℝ) / δ := by
    have b1 : ‖ell 9 ^ 2 * u‖ ≤ ((fmulUp (fmulUp h9 h9) id : ℤ) : ℝ) / δ := by
      rw [norm_mul, norm_pow, pow_two]
      exact mul_le_fmulUp (mul_nonneg hL0 hL0) hL2 hun hu
    have b2 : ‖2 * ell 9 * u ^ 2‖ ≤ 2 * (((fmulUp h9 (fmulUp id id) : ℤ) : ℝ) / δ) := by
      rw [norm_mul, norm_mul, norm_pow, pow_two, show ‖(2 : ℂ)‖ = 2 by simp, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_fmulUp hL0 hl9.2 (mul_nonneg hun hun) hu2) (by norm_num)
    have b3 : ‖2 * u ^ 3‖ ≤ 2 * (((fmulUp (fmulUp id id) id : ℤ) : ℝ) / δ) := by
      rw [norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by simp,
        show ‖u‖ ^ 3 = ‖u‖ * ‖u‖ * ‖u‖ by ring]
      exact mul_le_mul_of_nonneg_left hu3 (by norm_num)
    calc _ ≤ ‖ell 9 ^ 2 * u‖ + ‖2 * ell 9 * u ^ 2‖ + ‖2 * u ^ 3‖ := norm_add₃_le
      _ ≤ _ := by
        have := add_le_add (add_le_add b1 b2) b3
        refine this.trans (le_of_eq ?_)
        push_cast; ring
  have hBn := norm_nonneg (ell 9 ^ 2 * u + 2 * ell 9 * u ^ 2 + 2 * u ^ 3)
  have hb9 : ‖9 * E 9 w * (ell 9 ^ 2 * u + 2 * ell 9 * u ^ 2 + 2 * u ^ 3)‖ ≤
      9 * (((fmulUp e9 (fmulUp (fmulUp h9 h9) id + 2 * fmulUp h9 (fmulUp id id) +
        2 * fmulUp (fmulUp id id) id) : ℤ) : ℝ) / δ) := by
    rw [norm_mul, norm_mul, show ‖(9 : ℂ)‖ = 9 by simp, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_fmulUp hEn hE9 hBn hB) (by norm_num)
  have hC : ‖-2 * ell 9 + w * ell 9 ^ 2‖ ≤ ((2 * h9 + fmulUp A (fmulUp h9 h9) : ℤ) : ℝ) / δ := by
    have c1 : ‖-2 * ell 9‖ ≤ 2 * ((h9 : ℝ) / δ) := by
      rw [norm_mul, show ‖(-2 : ℂ)‖ = 2 by simp]
      exact mul_le_mul_of_nonneg_left hl9.2 (by norm_num)
    have c2 : ‖w * ell 9 ^ 2‖ ≤ ((fmulUp A (fmulUp h9 h9) : ℤ) : ℝ) / δ := by
      rw [norm_mul, norm_pow, pow_two]
      exact mul_le_fmulUp (norm_nonneg _) hA (mul_nonneg hL0 hL0) hL2
    calc _ ≤ ‖-2 * ell 9‖ + ‖w * ell 9 ^ 2‖ := norm_add_le _ _
      _ ≤ _ := by
        have := add_le_add c1 c2
        refine this.trans (le_of_eq ?_)
        push_cast; ring
  have hCn := norm_nonneg (-2 * ell 9 + w * ell 9 ^ 2)
  have hc9 : ‖E 9 w * (-2 * ell 9 + w * ell 9 ^ 2) / 108‖ ≤
      ((cdiv (fmulUp e9 (2 * h9 + fmulUp A (fmulUp h9 h9))) 108 : ℤ) : ℝ) / δ := by
    rw [norm_div, norm_mul, show ‖(108 : ℂ)‖ = ((108 : ℤ) : ℝ) by simp]
    exact div_le_cdiv (by norm_num) (mul_le_fmulUp hEn hE9 hCn hC)
  have hM2 : M2 w = (∑ k ∈ Finset.range 7, ell (k + 2) ^ 2 * E (k + 2) w) +
      ell 9 ^ 2 * E 9 w / 2 +
      9 * E 9 w * (ell 9 ^ 2 * u + 2 * ell 9 * u ^ 2 + 2 * u ^ 3) +
      E 9 w * (-2 * ell 9 + w * ell 9 ^ 2) / 108 := rfl
  rw [hM2]
  have hBM : BM sg A d = (∑ k ∈ Finset.range 7, fmulUp (fmulUp (logHi (k + 2)) (logHi (k + 2)))
      (npowRe (k + 2) sg)) + cdiv (fmulUp (fmulUp h9 h9) e9) 2 +
      9 * fmulUp e9 (fmulUp (fmulUp h9 h9) id + 2 * fmulUp h9 (fmulUp id id) +
        2 * fmulUp (fmulUp id id) id) +
      cdiv (fmulUp e9 (2 * h9 + fmulUp A (fmulUp h9 h9))) 108 := by
    unfold BM
    rw [foldl_add_eq]
    simp only [zero_add]
    rfl
  rw [hBM]
  calc _ ≤ ‖∑ k ∈ Finset.range 7, ell (k + 2) ^ 2 * E (k + 2) w‖ + ‖ell 9 ^ 2 * E 9 w / 2‖ +
        ‖9 * E 9 w * (ell 9 ^ 2 * u + 2 * ell 9 * u ^ 2 + 2 * u ^ 3)‖ +
        ‖E 9 w * (-2 * ell 9 + w * ell 9 ^ 2) / 108‖ := norm_add₄_le
    _ ≤ _ := by
      have := add_le_add (add_le_add (add_le_add hsum ha) hb9) hc9
      refine this.trans (le_of_eq ?_)
      push_cast; ring

/-! ### The tail bound -/

lemma rho_pos : (0 : ℤ) < rho := by unfold rho D; norm_num

lemma rho_le : ((rho : ℤ) : ℝ) / δ ≤ 2 / 5 := by
  have hδ := δ_pos
  have h := ediv_le_real (2 * D) (by norm_num : (0 : ℤ) < 5)
  unfold rho
  rw [div_le_iff₀ hδ]
  unfold δ
  push_cast at h ⊢
  linarith

theorem Pa_le_Tb {a : ℝ} {A' : ℤ} (ha0 : 0 ≤ a) (ha : a ≤ (A' : ℝ) / δ) :
    Pa a / 147456 / (((rho : ℤ) : ℝ) / δ) ≤ ((Tb A' : ℤ) : ℝ) / δ := by
  have hδ := δ_pos
  have hD0 : ((D : ℤ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast D_pos)
  have hr : (0 : ℝ) < ((rho : ℤ) : ℝ) := by exact_mod_cast rho_pos
  have hr0 : ((rho : ℤ) : ℝ) ≠ 0 := hr.ne'
  have e1 : a + 1 ≤ ((A' + D : ℤ) : ℝ) / δ := by
    have : ((A' + D : ℤ) : ℝ) / δ = (A' : ℝ) / δ + 1 := by unfold δ; push_cast; field_simp
    rw [this]; linarith
  have e2 : a + 2 ≤ ((A' + 2 * D : ℤ) : ℝ) / δ := by
    have : ((A' + 2 * D : ℤ) : ℝ) / δ = (A' : ℝ) / δ + 2 := by unfold δ; push_cast; field_simp
    rw [this]; linarith
  have e3 : a + 3 ≤ ((A' + 3 * D : ℤ) : ℝ) / δ := by
    have : ((A' + 3 * D : ℤ) : ℝ) / δ = (A' : ℝ) / δ + 3 := by unfold δ; push_cast; field_simp
    rw [this]; linarith
  have p1 := mul_le_fmulUp ha0 ha (by linarith) e1
  have p2 := mul_le_fmulUp (by positivity) p1 (by linarith) e2
  have p3 := mul_le_fmulUp (by positivity) p2 (by linarith) e3
  set p := fmulUp (fmulUp (fmulUp A' (A' + D)) (A' + 2 * D)) (A' + 3 * D)
  have hTb : Tb A' = cdiv (p * D) (147456 * rho) := rfl
  have hc := le_cdiv_real (p * D) (b := 147456 * rho) (by have := rho_pos; positivity)
  rw [hTb]
  calc Pa a / 147456 / (((rho : ℤ) : ℝ) / δ) ≤ ((p : ℤ) : ℝ) / δ / 147456 / (((rho : ℤ) : ℝ) / δ) := by
        unfold Pa; gcongr
    _ = ((p * D : ℤ) : ℝ) / ((147456 * rho : ℤ) : ℝ) / δ := by
        unfold δ; push_cast; field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hc hδ.le

/-! ### One cell -/

lemma abs_sub_mid_le {v : ℝ} {s0 s1 : ℤ} (h0 : (s0 : ℝ) / δ ≤ v) (h1 : v ≤ (s1 : ℝ) / δ) :
    |v - (((s0 + s1) / 2 : ℤ) : ℝ) / δ| ≤ (((cdiv (s1 - s0) 2) + 1 : ℤ) : ℝ) / δ := by
  have hδ := δ_pos
  have m1 := ediv_le_real (s0 + s1) (by norm_num : (0 : ℤ) < 2)
  have m2 := lt_ediv_real (s0 + s1) (by norm_num : (0 : ℤ) < 2)
  have hc := le_cdiv_real (s1 - s0) (by norm_num : (0 : ℤ) < 2)
  rw [div_le_iff₀ hδ] at h0
  rw [le_div_iff₀ hδ] at h1
  push_cast at m1 m2 hc ⊢
  rw [show v - (((s0 + s1) / 2 : ℤ) : ℝ) / δ = (v * δ - (((s0 + s1) / 2 : ℤ) : ℝ)) / δ by
    field_simp, abs_div, abs_of_pos hδ]
  refine div_le_div_of_nonneg_right ?_ hδ.le
  rw [abs_le]; constructor <;> linarith

lemma int_div_le {a b : ℤ} (h : a ≤ b) : (a : ℝ) / δ ≤ (b : ℝ) / δ :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) δ_pos.le

lemma int_div_lt {a b : ℤ} (h : a < b) : (a : ℝ) / δ < (b : ℝ) / δ :=
  div_lt_div_of_pos_right (by exact_mod_cast h) δ_pos

lemma D_div : ((D : ℤ) : ℝ) / δ = 1 := div_self δ_pos.ne'

lemma D10_div : -1 / 10 ≤ ((-(D / 10) : ℤ) : ℝ) / δ := by
  have := ediv_le_real D (by norm_num : (0 : ℤ) < 10)
  have hδ := δ_pos
  rw [le_div_iff₀ hδ]
  unfold δ at *; push_cast at this ⊢; linarith

theorem deriv_ne_zero_of_cellOK {s0 s1 t0 t1 : ℤ} (h : cellOK s0 s1 t0 t1 = true) {s : ℂ}
    (hs0 : (s0 : ℝ) / δ ≤ s.re) (hs1 : s.re ≤ (s1 : ℝ) / δ) (ht0 : (t0 : ℝ) / δ ≤ s.im)
    (ht1 : s.im ≤ (t1 : ℝ) / δ) : deriv riemannZeta s ≠ 0 := by
  have hδ := δ_pos
  unfold cellOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hx1, hx2⟩, hd⟩, hside⟩, hargs⟩, he0⟩, hlt⟩ := h
  generalize hx : (s0 + s1) / 2 = x at *
  generalize hy : (t0 + t1) / 2 = y at *
  generalize hr : cdiv (s1 - s0) 2 + cdiv (t1 - t0) 2 + 2 = r at *
  generalize hA : iabs x + iabs y + r = A at *
  generalize hdd : iabs y - r = d at *
  -- real abbreviations
  set c := (Disc.pt x y).c with hc
  have hcre : c.re = (x : ℝ) / δ := rfl
  have hcim : c.im = (y : ℝ) / δ := rfl
  set R := (r : ℝ) / δ with hR
  set P := ((rho : ℤ) : ℝ) / δ with hP
  have hP0 : 0 < P := by
    have : (0 : ℝ) < ((rho : ℤ) : ℝ) := by exact_mod_cast rho_pos
    positivity
  have hP1 : P ≤ 2 / 5 := rho_le
  have hxr1 : -1 / 10 ≤ (x : ℝ) / δ - R := by
    have := D10_div.trans (int_div_le hx1); push_cast at this; rw [sub_div] at this; exact this
  have hxr2 : (x : ℝ) / δ + R ≤ 1 := by
    have := int_div_le hx2; push_cast at this; rw [add_div, D_div] at this; exact this
  -- `s` is in the disc about `c`
  have hre := abs_sub_mid_le hs0 hs1
  have him := abs_sub_mid_le ht0 ht1
  rw [hx] at hre
  rw [hy] at him
  have hsc : ‖s - c‖ ≤ R := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [sub_re, sub_im, hcre, hcim]
    have : R = (((cdiv (s1 - s0) 2) + 1 : ℤ) : ℝ) / δ +
        (((cdiv (t1 - t0) 2) + 1 : ℤ) : ℝ) / δ := by
      rw [hR, ← hr]; push_cast; ring
    rw [this]; exact add_le_add hre him
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hsc
  -- the box `U±`
  obtain ⟨sgn, hsgn, hy1, hy2⟩ : ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧
      1 < sgn * ((y : ℝ) / δ) - R - P ∧ sgn * ((y : ℝ) / δ) + R + P < 10 := by
    rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨1, Or.inl rfl, ?_, ?_⟩
      · have := int_div_lt h1; push_cast at this; rw [D_div, sub_div, sub_div] at this
        linarith
      · have := int_div_lt h2; push_cast at this
        rw [add_div, add_div, mul_div_assoc, D_div] at this; linarith
    · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
      · have := int_div_lt h2; push_cast at this
        rw [add_div, add_div, neg_div, D_div] at this; linarith
      · have := int_div_lt h1; push_cast at this
        rw [sub_div, sub_div, neg_mul, neg_div, mul_div_assoc, D_div] at this; linarith
  have hin : ∀ z : ℂ, ‖z - c‖ ≤ R + P → z ∈ Ubox sgn := by
    intro z hz
    have hzre := abs_le.mp ((Complex.abs_re_le_norm (z - c)).trans hz)
    have hzim := abs_le.mp ((Complex.abs_im_le_norm (z - c)).trans hz)
    simp only [sub_re, sub_im, hcre, hcim] at hzre hzim
    refine ⟨by linarith [hzre.1], by linarith [hzre.2], ?_, ?_⟩
    · rcases hsgn with rfl | rfl
      · simp only [one_mul] at hy1 ⊢; linarith [hzim.1]
      · simp only [neg_mul, one_mul] at hy1 ⊢; linarith [hzim.2]
    · rcases hsgn with rfl | rfl
      · simp only [one_mul] at hy2 ⊢; linarith [hzim.2]
      · simp only [neg_mul, one_mul] at hy2 ⊢; linarith [hzim.1]
  have hballc : Metric.closedBall c R ⊆ Ubox sgn := fun z hz =>
    hin z (by rw [Metric.mem_closedBall, dist_eq_norm] at hz; linarith)
  have hballs : Metric.closedBall s P ⊆ Ubox sgn := fun z hz => by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    apply hin
    calc ‖z - c‖ = ‖(z - s) + (s - c)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - c‖ := norm_add_le _ _
      _ ≤ R + P := by linarith
  have hsU : s ∈ Ubox sgn := hballc (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hsc)
  -- the tail
  have hreS : -1 / 2 ≤ s.re - P := by
    have := (abs_le.mp ((Complex.abs_re_le_norm (s - c)).trans hsc)).1
    simp only [sub_re, hcre] at this
    linarith
  have hT := norm_deriv_tailT_le hsgn hP0 hballs hreS
  have hnormw : ∀ w : ℂ, ‖w - c‖ ≤ R → ‖w‖ ≤ (A : ℝ) / δ := fun w hw => by
    calc ‖w‖ = ‖c + (w - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ((Disc.pt x y).l1 : ℝ) / δ + R := add_le_add (norm_c_le _) hw
      _ = _ := by rw [hR, ← hA]; simp only [Disc.l1, Disc.pt]; push_cast; ring
  have hTb := Pa_le_Tb (a := ‖s‖ + P) (A' := A + rho) (by positivity)
    (by push_cast; rw [add_div]; linarith [hnormw s hsc])
  -- the main part
  have hok : ∀ n, 2 ≤ n → n ≤ 9 → expOK (npowArg n (x - r) 0) = true := fun n h2 h9 =>
    (argsOK_point hargs h2 h9).2
  have hdpos : 0 < d := hd
  have hM2 : ∀ w ∈ Metric.closedBall c R, ‖M2 w‖ ≤ ((BM (x - r) A d : ℤ) : ℝ) / δ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    refine norm_M2_le hok hd ?_ (hnormw w hw) ?_
    · have := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hw)).1
      simp only [sub_re, hcre] at this
      push_cast; rw [sub_div]; linarith
    · have h1 := abs_le.mp ((Complex.abs_im_le_norm (w - c)).trans hw)
      simp only [sub_im, hcim] at h1
      have h2 := Complex.abs_im_le_norm (w - 1)
      simp only [sub_im, one_im, sub_zero] at h2
      have h3 : |(y : ℝ) / δ| - R ≤ |w.im| := by
        have := abs_sub_abs_le_abs_sub ((y : ℝ) / δ) w.im
        have h4 : |(y : ℝ) / δ - w.im| ≤ R := by rw [abs_le]; constructor <;> linarith
        linarith
      have e : ((d : ℤ) : ℝ) / δ = |(y : ℝ) / δ| - R := by
        rw [← hdd, hR]; push_cast; rw [iabs_eq, sub_div, abs_div, abs_of_pos hδ]
      rw [e]; linarith
  have hMV := norm_M1_sub_le hsgn hballc
    (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hsc) hM2
  have hMV' : ((BM (x - r) A d : ℤ) : ℝ) / δ * R ≤ ((fmulUp r (BM (x - r) A d) : ℤ) : ℝ) / δ := by
    rw [mul_comm, hR]; exact le_fmulUp _ _
  have hy0 : y ≠ 0 := by
    intro h0
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by
      have := hR0; rw [hR, le_div_iff₀ hδ, zero_mul] at this; exact this
    have hr0' : 0 ≤ r := by exact_mod_cast hr0
    have : d = -r := by rw [← hdd, h0]; simp [iabs]
    omega
  have hmem := mem_M1 hargs hy0
  -- conclude
  intro hzero
  rw [deriv_riemannZeta_eq hsgn hsU] at hzero
  set m := SpeiserCompute.M1 x y
  set e := m.rad + fmulUp r (BM (x - r) A d) + Tb (A + rho) with he
  have hmc : ‖m.c‖ ≤ ((e : ℤ) : ℝ) / δ := by
    have hMs : M1 s = -deriv (tailT 9) s := by linear_combination hzero
    have e1 : m.c = -(M1 c - m.c) + (M1 c - M1 s) - deriv (tailT 9) s := by
      rw [hMs]; ring
    rw [e1]
    have h1 : ‖M1 c - m.c‖ ≤ (m.rad : ℝ) / δ := hmem
    have h2 : ‖M1 c - M1 s‖ ≤ ((fmulUp r (BM (x - r) A d) : ℤ) : ℝ) / δ := by
      rw [norm_sub_rev]; exact hMV.trans hMV'
    have h3 : ‖deriv (tailT 9) s‖ ≤ ((Tb (A + rho) : ℤ) : ℝ) / δ := hT.trans hTb
    calc ‖-(M1 c - m.c) + (M1 c - M1 s) - deriv (tailT 9) s‖
        ≤ ‖M1 c - m.c‖ + ‖M1 c - M1 s‖ + ‖deriv (tailT 9) s‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
          rw [norm_neg]
      _ ≤ _ := by
          have := add_le_add (add_le_add h1 h2) h3
          refine this.trans (le_of_eq ?_)
          rw [he]; push_cast; ring
  have hsq : ‖m.c‖ ^ 2 = ((m.re * m.re + m.im * m.im : ℤ) : ℝ) / δ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Disc.c]; push_cast; ring
  have hlt' : ((e * e : ℤ) : ℝ) < ((m.re * m.re + m.im * m.im : ℤ) : ℝ) := by exact_mod_cast hlt
  have he0' : (0 : ℝ) ≤ ((e : ℤ) : ℝ) := by exact_mod_cast he0
  have hlt2 : (((e : ℤ) : ℝ) / δ) ^ 2 < ‖m.c‖ ^ 2 := by
    rw [hsq, div_pow]
    refine div_lt_div_of_pos_right ?_ (by positivity)
    have h2 : (((e : ℤ) : ℝ)) ^ 2 = ((e * e : ℤ) : ℝ) := by push_cast; ring
    rw [h2]; exact hlt'
  have : ((e : ℤ) : ℝ) / δ < ‖m.c‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt2
  linarith

end Speiser.Band