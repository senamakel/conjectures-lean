import Robin.Defs

/-!
# The integrated Chebyshev function `Ψ₁` and pointwise bounds for `ψ`

From `|Ψ₁(m) − m²/2| ≤ m^{3/2}/20 + 3m` at natural `m` (which is `BachBound` multiplied by `m`)
we get the bound for real `t`, and pointwise bounds for `ψ` by monotone differencing:
`(Ψ₁(s) − Ψ₁(s−h))/h ≤ ψ(s) ≤ (Ψ₁(s+h) − Ψ₁(s))/h`.
-/

namespace Robin

open ArithmeticFunction Real Chebyshev

/-- The hypothesis in the form "Ψ₁ at integers". (`BachBound` multiplied by `m`.) -/
def Psi1NatBound : Prop :=
  ∀ m : ℕ, 1 ≤ m → |psi1 m - (m : ℝ) ^ 2 / 2| ≤ (m : ℝ) ^ ((3 : ℝ) / 2) / 20 + 3 * m

/-- Extending a sum over `n ≤ ⌊s⌋₊` to `n ≤ N`, when the new terms vanish. -/
lemma sum_range_floor_eq (s : ℝ) {N : ℕ} (hN : ⌊s⌋₊ ≤ N) (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ s → f n = g n)
    (h2 : ∀ n : ℕ, s < n → g n = 0) :
    ∑ n ∈ Finset.range (⌊s⌋₊ + 1), f n = ∑ n ∈ Finset.range (N + 1), g n := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega) :
    Finset.range (⌊s⌋₊ + 1) ⊆ Finset.range (N + 1))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · exact h0
    · simp only [Finset.mem_range] at hn
      exact h1 n hn0 ((Nat.le_floor_iff' hn0).mp (by omega))
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    exact h2 n (Nat.lt_of_floor_lt (by omega))

lemma psi1_eq_sum_max {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    psi1 t = ∑ n ∈ Finset.range (N + 1), (Λ n : ℝ) * max (t - n) 0 :=
  sum_range_floor_eq t hN _ _ (by simp)
    (fun n _ hn => by rw [max_eq_left (by linarith)])
    (fun n hn => by rw [max_eq_right (by linarith), mul_zero])

lemma psi_eq_sum_range (t : ℝ) : ψ t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) := by
  rw [psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

lemma psi_eq_sum_ite {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    ψ t = ∑ n ∈ Finset.range (N + 1), if (n : ℝ) ≤ t then (Λ n : ℝ) else 0 := by
  rw [psi_eq_sum_range]
  exact sum_range_floor_eq t hN _ _ (by simp) (fun n _ hn => by simp [hn])
    (fun n hn => by simp [not_le.mpr hn])

/-- Monotone differencing: `h ψ(s) ≤ Ψ₁(s+h) − Ψ₁(s) ≤ h ψ(s+h)`. -/
lemma psi1_diff (s h : ℝ) (hh : 0 ≤ h) :
    h * ψ s ≤ psi1 (s + h) - psi1 s ∧ psi1 (s + h) - psi1 s ≤ h * ψ (s + h) := by
  have hN : ⌊s⌋₊ ≤ ⌊s + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [psi1_eq_sum_max hN, psi1_eq_sum_max le_rfl, psi_eq_sum_ite hN, psi_eq_sum_ite le_rfl,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      exact le_of_eq (by ring)
    · rw [mul_zero, ← mul_sub]
      exact mul_nonneg hΛ (sub_nonneg.mpr (max_le_max (by linarith) le_rfl))
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [← mul_sub, mul_comm h]
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      have := le_max_left (s - n) 0
      have := le_max_right (s - n) 0
      have : max (s + h - n) 0 ≤ max (s - n) 0 + h := max_le (by linarith) (by linarith)
      linarith
    · push Not at hn
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      simp

theorem psi1_continuous : Continuous psi1 := by
  rw [continuous_iff_continuousAt]
  intro t
  have hF : Continuous fun s : ℝ =>
      ∑ n ∈ Finset.range (⌊t⌋₊ + 1 + 1), (Λ n : ℝ) * max (s - n) 0 := by
    fun_prop
  refine hF.continuousAt.congr ?_
  have ht : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one t
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact (psi1_eq_sum_max (Nat.le_of_lt ((Nat.floor_lt' (by omega)).mpr hs))).symm

/-- `Ψ₁` has right derivative `ψ(t)` everywhere. -/
theorem psi1_hasDerivWithinAt (t : ℝ) : HasDerivWithinAt psi1 (ψ t) (Set.Ioi t) t := by
  set m := ⌊t⌋₊ with hm
  set A := ∑ n ∈ Finset.range (m + 1), (Λ n : ℝ)
  set B := ∑ n ∈ Finset.range (m + 1), (Λ n : ℝ) * n
  have hψ : ψ t = A := psi_eq_sum_range t
  have hG : HasDerivAt (fun s => A * s - B) A t := by
    simpa using ((hasDerivAt_id t).const_mul A).sub_const B
  rw [hψ]
  have htm : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
  have heq : ∀ s, t ≤ s → s < (m : ℝ) + 1 → psi1 s = A * s - B := by
    intro s hts hs
    have hfl : ⌊s⌋₊ = m := le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.floor_lt' (by omega)).mpr (by push_cast; exact hs)))
      (Nat.floor_le_floor hts)
    simp only [psi1, hfl, A, B, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  refine hG.hasDerivWithinAt.congr_of_eventuallyEq ?_ (heq t le_rfl htm)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds htm)] with s hs1 hs2
  exact heq s (le_of_lt hs1) hs2

lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx (by norm_num)]
  norm_num

theorem psi1_bound (hB : Psi1NatBound) {t : ℝ} (ht : 16 ≤ t) :
    |psi1 t - t ^ 2 / 2| ≤ t ^ ((3 : ℝ) / 2) / 20 + 4 * t := by
  have ht0 : 0 ≤ t := by linarith
  set m := ⌊t⌋₊ with hm
  have hmt : (m : ℝ) ≤ t := Nat.floor_le ht0
  have htm : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
  have hm1 : 1 ≤ m := Nat.le_floor (by norm_num; linarith)
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  set l := t - m with hl
  have hl0 : 0 ≤ l := by linarith
  have hl1 : l ≤ 1 := by linarith
  have h1 : psi1 t = ∑ n ∈ Finset.range (m + 1), (Λ n : ℝ) * (t - n) := rfl
  have h2 : psi1 m = ∑ n ∈ Finset.range (m + 1), (Λ n : ℝ) * (m - n) := by
    simp [psi1]
  have h3 : psi1 ((m : ℝ) + 1) = ∑ n ∈ Finset.range (m + 1), (Λ n : ℝ) * ((m : ℝ) + 1 - n) := by
    have e : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, psi1, Nat.floor_natCast, Finset.sum_range_succ, sub_self, mul_zero, add_zero]
  have hinterp : psi1 t = (1 - l) * psi1 m + l * psi1 ((m : ℝ) + 1) := by
    rw [h1, h2, h3, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hl]; ring
  have em := hB m hm1
  have em1 := hB (m + 1) (by omega)
  push_cast at em1
  rw [rpow_three_halves hm0] at em
  rw [rpow_three_halves (by positivity)] at em1
  rw [rpow_three_halves ht0]
  set a := √t with ha
  set b := √(t + 1) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = t := Real.sq_sqrt ht0
  have hb2 : b ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
  have hcm : √(m : ℝ) ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hcm1 : √((m : ℝ) + 1) ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hba : b ≤ a + 1 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have ha4 : 4 ≤ a := by nlinarith
  have hat : a ≤ t := by nlinarith
  set X := (t + 1) * b / 20 + 3 * (t + 1) with hX
  have hX1 : (m : ℝ) * √(m : ℝ) ≤ (t + 1) * b :=
    mul_le_mul (by linarith) hcm (Real.sqrt_nonneg _) (by linarith)
  have hX2 : ((m : ℝ) + 1) * √((m : ℝ) + 1) ≤ (t + 1) * b :=
    mul_le_mul (by linarith) hcm1 (Real.sqrt_nonneg _) (by linarith)
  have hem : |psi1 m - (m : ℝ) ^ 2 / 2| ≤ X := em.trans (by rw [hX]; linarith)
  have hem1 : |psi1 ((m : ℝ) + 1) - ((m : ℝ) + 1) ^ 2 / 2| ≤ X := em1.trans (by rw [hX]; linarith)
  have key : psi1 t - t ^ 2 / 2 = (1 - l) * (psi1 m - (m : ℝ) ^ 2 / 2)
      + l * (psi1 ((m : ℝ) + 1) - ((m : ℝ) + 1) ^ 2 / 2) + l * (1 - l) / 2 := by
    rw [hinterp]; simp only [hl]; ring
  obtain ⟨a1, a2⟩ := abs_le.mp hem
  obtain ⟨b1, b2⟩ := abs_le.mp hem1
  have p1 := mul_le_mul_of_nonneg_left a2 (by linarith : (0 : ℝ) ≤ 1 - l)
  have p2 := mul_le_mul_of_nonneg_left a1 (by linarith : (0 : ℝ) ≤ 1 - l)
  have p3 := mul_le_mul_of_nonneg_left b2 hl0
  have p4 := mul_le_mul_of_nonneg_left b1 hl0
  have hfin : X + 1 / 8 ≤ t * a / 20 + 4 * t := by
    have := mul_le_mul_of_nonneg_left hba (by linarith : (0 : ℝ) ≤ t + 1)
    rw [hX]; linarith
  have hq1 : 0 ≤ l * (1 - l) / 2 := by have := mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ 1 - l); linarith
  have hq2 : l * (1 - l) / 2 ≤ 1 / 8 := by nlinarith [sq_nonneg (l - 1 / 2)]
  rw [key, abs_le]
  generalize psi1 (m : ℝ) = P0 at p1 p2 ⊢
  generalize psi1 ((m : ℝ) + 1) = P1 at p3 p4 ⊢
  clear_value X a l
  constructor
  · linarith only [p1, p2, p3, p4, hfin, hq1, hq2]
  · linarith only [p1, p2, p3, p4, hfin, hq1, hq2]

/-- `psi1_bound` in the form `r √r`. -/
lemma psi1_bound' (hB : Psi1NatBound) {r : ℝ} (hr : 16 ≤ r) :
    |psi1 r - r ^ 2 / 2| ≤ r * √r / 20 + 4 * r := by
  have := psi1_bound hB hr
  rwa [rpow_three_halves (by linarith)] at this

/-- Fourth roots: `s = u⁴`, `s^{3/4} = u³`. -/
lemma exists_fourth_root {s : ℝ} (hs : 0 ≤ s) :
    ∃ u : ℝ, 0 ≤ u ∧ s = u ^ 4 ∧ s ^ ((3 : ℝ) / 4) = u ^ 3 := by
  refine ⟨s ^ ((1 : ℝ) / 4), by positivity, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num

lemma sqrt_fourth {u : ℝ} : √(u ^ 4) = u ^ 2 := by
  rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem psi_upper (hB : Psi1NatBound) {s : ℝ} (hs : 1000 ≤ s) : ψ s ≤ s + s ^ ((3 : ℝ) / 4) := by
  obtain ⟨u, hu0, hs4, h34⟩ := exists_fourth_root (by linarith : (0 : ℝ) ≤ s)
  rw [h34]
  subst hs4
  have hu : 5.6 ≤ u := by
    by_contra h
    push Not at h
    have : u ^ 4 < 5.6 ^ 4 := pow_lt_pow_left₀ h hu0 (by norm_num)
    norm_num at this; linarith
  have hu3 : 0 < u ^ 3 := by positivity
  have hd := (psi1_diff (u ^ 4) (u ^ 3) hu3.le).1
  have hb1 := abs_le.mp (psi1_bound' hB (r := u ^ 4 + u ^ 3) (by nlinarith))
  have hb2 := abs_le.mp (psi1_bound' hB (r := u ^ 4) (by nlinarith))
  rw [sqrt_fourth] at hb2
  have hW : √(u ^ 4 + u ^ 3) ≤ u ^ 2 + u / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hW' := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ u ^ 4 + u ^ 3)
  have hpoly : 0 ≤ 16 * u ^ 3 - 3 * u ^ 2 - 321 * u - 160 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u - 5.6) (by linarith : (0 : ℝ) ≤ u - 5.6),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ u - 5.6)
        (by linarith : (0 : ℝ) ≤ u - 5.6)) (by linarith : (0 : ℝ) ≤ u - 5.6)]
  have hp3 := mul_nonneg hu3.le hpoly
  refine le_of_mul_le_mul_left ?_ hu3
  nlinarith

theorem psi_lower (hB : Psi1NatBound) {s : ℝ} (hs : 1000 ≤ s) : s - s ^ ((3 : ℝ) / 4) ≤ ψ s := by
  obtain ⟨u, hu0, hs4, h34⟩ := exists_fourth_root (by linarith : (0 : ℝ) ≤ s)
  rw [h34]
  subst hs4
  have hu : 5.6 ≤ u := by
    by_contra h
    push Not at h
    have : u ^ 4 < 5.6 ^ 4 := pow_lt_pow_left₀ h hu0 (by norm_num)
    norm_num at this; linarith
  have hu3 : 0 < u ^ 3 := by positivity
  have hr : 16 ≤ u ^ 4 - u ^ 3 := by nlinarith
  have hd := (psi1_diff (u ^ 4 - u ^ 3) (u ^ 3) hu3.le).2
  rw [sub_add_cancel] at hd
  have hb1 := abs_le.mp (psi1_bound' hB hr)
  have hb2 := abs_le.mp (psi1_bound' hB (r := u ^ 4) (by nlinarith))
  rw [sqrt_fourth] at hb2
  have hW : √(u ^ 4 - u ^ 3) ≤ u ^ 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hW' := mul_le_mul_of_nonneg_left hW (by linarith : (0 : ℝ) ≤ u ^ 4 - u ^ 3)
  have hu2 : 20 ≤ u ^ 2 := by nlinarith
  have hp : 0 ≤ u ^ 4 * (u ^ 2 - 20) := mul_nonneg (by positivity) (by linarith)
  refine le_of_mul_le_mul_left ?_ hu3
  nlinarith

/-- `θ(t) − t = O(t^{3/4})`, the input for Mertens' theorem. -/
theorem theta_sub_bound (hB : Psi1NatBound) :
    ∃ C, ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4) := by
  obtain ⟨C0, hC0⟩ := psi_sub_theta_le_mul_sqrt
  refine ⟨25 + |C0|, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hp : 0 < t ^ ((3 : ℝ) / 4) := by positivity
  have hpa := mul_nonneg (abs_nonneg C0) hp.le
  rcases le_or_gt 1000 t with h | h
  · have hu := psi_upper hB h
    have hl := psi_lower hB h
    have hθψ := theta_le_psi t
    have hc := hC0 t
    have hsq : √t ≤ t ^ ((3 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have : C0 * √t ≤ |C0| * t ^ ((3 : ℝ) / 4) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
    rw [abs_le]; constructor <;> nlinarith
  · obtain ⟨u, hu0, hs4, h34⟩ := exists_fourth_root ht0.le
    rw [h34] at hp hpa ⊢
    subst hs4
    have hu6 : u ≤ 6 := by
      by_contra h'
      push Not at h'
      have : (6 : ℝ) ^ 4 < u ^ 4 := pow_lt_pow_left₀ h' (by norm_num) (by norm_num)
      norm_num at this; linarith
    have hθ := theta_le_log4_mul_x ht0.le
    have hθ0 := theta_nonneg (u ^ 4)
    have hlog : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have h3 : Real.log 4 * u ^ 4 ≤ 3 * u ^ 4 := mul_le_mul_of_nonneg_right hlog (by positivity)
    have h18 : u ^ 4 ≤ 6 * u ^ 3 := by
      have := mul_le_mul_of_nonneg_right hu6 hp.le; nlinarith
    rw [abs_le]; constructor <;> nlinarith

end Robin
