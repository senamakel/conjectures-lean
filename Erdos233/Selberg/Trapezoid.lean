import Erdos233.Gaps

/-!
# The trapezoid difference of `psi1`

For `a > 0`, `σ, D ≥ 0` and the four points `t₁ = ya`, `t₂ = y(a+σ)`, `t₃ = y(a+D)`,
`t₄ = y(a+D+σ)`, set

`trap a σ D y = psi1 t₄ − psi1 t₃ − psi1 t₂ + psi1 t₁ = Σ_n Λ(n) K(n)`,

where `K` is the trapezoid kernel: `0 ≤ K ≤ σy`, `K = σy` on `[t₂, t₃]` and `K = 0` off
`(t₁, t₄)`. So `trap` is squeezed between `σy` times sharp sums of `Λ`:

* `σy (ψ t₃ − ψ t₂) ≤ trap a σ D y` (`psi_window_le_trap`),
* `trap a σ D y ≤ σy (ψ t₄ − ψ t₁)` (`trap_le_psi_window`).

Through the explicit formula, `trap a σ D y = σD y² + R − y^{3/2}·zeroWave (tcoef a σ D) (log y)`
with `|R| ≤ 3` under RH (`trap_bound`): the four coefficients `1, −1, −1, 1` and the four
points both sum to zero, so the affine terms cancel.
-/

namespace Erdos233

open Complex ArithmeticFunction Erdos985.Analytic ExplicitAux Chebyshev

/-- The trapezoid difference of `psi1`. -/
noncomputable def trap (a σ D y : ℝ) : ℝ :=
  psi1 (y * (a + D + σ)) - psi1 (y * (a + D)) - psi1 (y * (a + σ)) + psi1 (y * a)

/-- The coefficient of `−y^{ρ+1}` in `trap a σ D y`. -/
noncomputable def tcoef (a σ D : ℝ) (ρ : ℂ) : ℂ :=
  ((((a + D + σ : ℝ) : ℂ) ^ (ρ + 1) - ((a + D : ℝ) : ℂ) ^ (ρ + 1)
    - ((a + σ : ℝ) : ℂ) ^ (ρ + 1) + ((a : ℝ) : ℂ) ^ (ρ + 1))) / (ρ * (ρ + 1))

/-- The wave of the coefficients `tcoef a σ D`. -/
noncomputable def TW (a σ D : ℝ) (u : ℝ) : ℂ := zeroWave (fun ρ => tcoef a σ D ρ) u

lemma trap_zero (y a σ D : ℝ) (hy : 0 < y) (ha : 0 < a) (hσ : 0 ≤ σ) (hD : 0 ≤ D) (ρ : ℂ) :
    ((y * (a + D + σ) : ℝ) : ℂ) * zeroTermR (y * (a + D + σ)) ρ
      - ((y * (a + D) : ℝ) : ℂ) * zeroTermR (y * (a + D)) ρ
      - ((y * (a + σ) : ℝ) : ℂ) * zeroTermR (y * (a + σ)) ρ
      + ((y * a : ℝ) : ℂ) * zeroTermR (y * a) ρ
      = -((y : ℂ) ^ (ρ + 1) * tcoef a σ D ρ) := by
  rw [t_zeroTermR _ (by positivity), t_zeroTermR _ (by positivity),
    t_zeroTermR _ (by positivity), t_zeroTermR _ (by positivity)]
  have e : ∀ l : ℝ, 0 ≤ l → (((y * l) : ℝ) : ℂ) ^ (ρ + 1) = (y : ℂ) ^ (ρ + 1) * ((l : ℝ) : ℂ) ^ (ρ + 1) :=
    fun l hl => by rw [ofReal_mul, mul_cpow_ofReal_nonneg hy.le hl]
  unfold tcoef
  rw [e _ (by positivity), e _ (by positivity), e _ (by positivity), e _ ha.le]
  push_cast
  ring

/-- **The trapezoid difference through the explicit formula, under RH.** -/
theorem trap_bound (hRH : RiemannHypothesis) {a σ D y : ℝ} (ha : 0 < a) (hσ : 0 ≤ σ)
    (hD : 0 ≤ D) (hy : 1 ≤ y * a) :
    |trap a σ D y - σ * D * y ^ 2| ≤ 3 + y ^ (3 / 2 : ℝ) * ‖TW a σ D (Real.log y)‖ := by
  have hy0 : (0 : ℝ) < y := by
    by_contra h
    push_neg at h
    nlinarith
  have h2 : 1 ≤ y * (a + σ) := by nlinarith
  have h3 : 1 ≤ y * (a + D) := by nlinarith
  have h4 : 1 ≤ y * (a + D + σ) := by nlinarith
  obtain ⟨s1, e1⟩ := psi1_formula _ hy
  obtain ⟨s2, e2⟩ := psi1_formula _ h2
  obtain ⟨s3, e3⟩ := psi1_formula _ h3
  obtain ⟨s4, e4⟩ := psi1_formula _ h4
  obtain ⟨l1, u1⟩ := th_bounds _ hy
  obtain ⟨l2, u2⟩ := th_bounds _ h2
  obtain ⟨l3, u3⟩ := th_bounds _ h3
  obtain ⟨l4, u4⟩ := th_bounds _ h4
  set A1 := y * a * ((gammaPartR (y * a)).re + Real.log (y * a)) with hA1
  set A2 := y * (a + σ) * ((gammaPartR (y * (a + σ))).re + Real.log (y * (a + σ))) with hA2
  set A3 := y * (a + D) * ((gammaPartR (y * (a + D))).re + Real.log (y * (a + D))) with hA3
  set A4 := y * (a + D + σ) * ((gammaPartR (y * (a + D + σ))).re
    + Real.log (y * (a + D + σ))) with hA4
  set R := A4 - A3 - A2 + A1 with hRdef
  have hlin : y * (a + D + σ) - y * (a + D) - y * (a + σ) + y * a = 0 := by ring
  have hR : |R| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  set W := ∑' ρ : Zeros, (mult ρ : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) * tcoef a σ D ρ) with hWdef
  have hZ : (∑' ρ : Zeros, (mult ρ : ℂ) * (((y * (a + D + σ) : ℝ) : ℂ)
        * zeroTermR (y * (a + D + σ)) ρ))
      - (∑' ρ : Zeros, (mult ρ : ℂ) * (((y * (a + D) : ℝ) : ℂ) * zeroTermR (y * (a + D)) ρ))
      - (∑' ρ : Zeros, (mult ρ : ℂ) * (((y * (a + σ) : ℝ) : ℂ) * zeroTermR (y * (a + σ)) ρ))
      + (∑' ρ : Zeros, (mult ρ : ℂ) * (((y * a : ℝ) : ℂ) * zeroTermR (y * a) ρ)) = -W := by
    rw [← (((s4.hasSum.sub s3.hasSum).sub s2.hasSum).add s1.hasSum).tsum_eq, hWdef, ← tsum_neg]
    exact tsum_congr fun ρ => by
      linear_combination (mult ρ : ℂ) * trap_zero y a σ D hy0 ha hσ hD ρ
  have hmain : ((trap a σ D y - σ * D * y ^ 2 : ℝ) : ℂ) = (R : ℂ) - W := by
    unfold trap
    rw [hRdef]
    push_cast at e1 e2 e3 e4 hZ ⊢
    linear_combination e4 - e3 - e2 + e1 + hZ
  have hW : W = ((y ^ (3 / 2 : ℝ) : ℝ) : ℂ) * TW a σ D (Real.log y) := by
    rw [hWdef, TW, zeroWave, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    rw [cpow_succ_of_RH hRH hy0 ρ]
    ring
  have hWn : ‖W‖ = y ^ (3 / 2 : ℝ) * ‖TW a σ D (Real.log y)‖ := by
    rw [hW, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc |trap a σ D y - σ * D * y ^ 2| = ‖((trap a σ D y - σ * D * y ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(R : ℂ) - W‖ := by rw [hmain]
    _ ≤ ‖(R : ℂ)‖ + ‖W‖ := norm_sub_le _ _
    _ ≤ 3 + y ^ (3 / 2 : ℝ) * ‖TW a σ D (Real.log y)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, hWn]
        linarith

/-! ### The kernel -/

lemma psi_eq_range {x : ℝ} (hx : 0 ≤ x) {M : ℕ} (hM : ⌊x⌋₊ + 1 ≤ M) :
    ψ x = ∑ n ∈ Finset.range M, (Λ n : ℝ) * (if (n : ℝ) ≤ x then 1 else 0) := by
  rw [psi_eq_sum_Icc]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range, zero_le, true_and]
  rw [Nat.le_floor_iff hx]
  constructor
  · intro h
    refine ⟨?_, h⟩
    have : n ≤ ⌊x⌋₊ := Nat.le_floor h
    omega
  · exact fun h => h.2

/-- The trapezoid kernel. -/
noncomputable def tk (t₁ t₂ t₃ t₄ u : ℝ) : ℝ :=
  max (t₄ - u) 0 - max (t₃ - u) 0 - max (t₂ - u) 0 + max (t₁ - u) 0

lemma tk_ge {t₁ t₂ t₃ t₄ s u : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃) (h34 : t₃ ≤ t₄)
    (hs1 : t₂ - t₁ = s) (hs2 : t₄ - t₃ = s) :
    s * ((if u ≤ t₃ then 1 else 0) - (if u ≤ t₂ then 1 else 0)) ≤ tk t₁ t₂ t₃ t₄ u := by
  unfold tk
  simp only [max_def]
  split_ifs <;> nlinarith

lemma tk_le {t₁ t₂ t₃ t₄ s u : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃) (h34 : t₃ ≤ t₄)
    (hs1 : t₂ - t₁ = s) (hs2 : t₄ - t₃ = s) :
    tk t₁ t₂ t₃ t₄ u ≤ s * ((if u ≤ t₄ then 1 else 0) - (if u ≤ t₁ then 1 else 0)) := by
  unfold tk
  simp only [max_def]
  split_ifs <;> nlinarith

lemma trap_eq_sum {a σ D y : ℝ} (hy : 0 < y) (ha : 0 < a) (hσ : 0 ≤ σ) (hD : 0 ≤ D) :
    trap a σ D y = ∑ n ∈ Finset.range (⌊y * (a + D + σ)⌋₊ + 1), (Λ n : ℝ) *
      tk (y * a) (y * (a + σ)) (y * (a + D)) (y * (a + D + σ)) n := by
  set M := ⌊y * (a + D + σ)⌋₊ + 1
  have hfl : ∀ l : ℝ, 0 ≤ l → l ≤ a + D + σ → ⌊y * l⌋₊ + 1 ≤ M := fun l hl hle => by
    have := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hle hy.le)
    omega
  unfold trap
  rw [psi1_eq_sum_pos (by positivity) (hfl _ (by positivity) le_rfl),
    psi1_eq_sum_pos (by positivity) (hfl _ (by positivity) (by linarith)),
    psi1_eq_sum_pos (by positivity) (hfl _ (by positivity) (by linarith)),
    psi1_eq_sum_pos (by positivity) (hfl _ ha.le (by linarith)),
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold tk
  ring

/-- The sharp sum of `Λ` over `(t₂, t₃]` is at most `trap / (σy)`. -/
lemma psi_window_le_trap {a σ D y : ℝ} (hy : 0 < y) (ha : 0 < a) (hσ : 0 ≤ σ) (hσD : σ ≤ D) :
    σ * y * (ψ (y * (a + D)) - ψ (y * (a + σ))) ≤ trap a σ D y := by
  have hD : 0 ≤ D := hσ.trans hσD
  set M := ⌊y * (a + D + σ)⌋₊ + 1
  have hfl : ∀ l : ℝ, 0 ≤ l → l ≤ a + D + σ → ⌊y * l⌋₊ + 1 ≤ M := fun l hl hle => by
    have := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hle hy.le)
    omega
  rw [trap_eq_sum hy ha hσ hD, psi_eq_range (by positivity) (hfl _ (by positivity) (by linarith)),
    psi_eq_range (by positivity) (hfl _ (by positivity) (by linarith)),
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
  have := tk_ge (u := (n : ℝ)) (s := σ * y)
    (t₁ := y * a) (t₂ := y * (a + σ)) (t₃ := y * (a + D)) (t₄ := y * (a + D + σ))
    (by nlinarith) (by nlinarith) (by nlinarith) (by ring) (by ring)
  calc σ * y * ((Λ n : ℝ) * (if (n : ℝ) ≤ y * (a + D) then 1 else 0)
        - (Λ n : ℝ) * (if (n : ℝ) ≤ y * (a + σ) then 1 else 0))
      = (Λ n : ℝ) * (σ * y * ((if (n : ℝ) ≤ y * (a + D) then 1 else 0)
        - (if (n : ℝ) ≤ y * (a + σ) then 1 else 0))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hΛ

/-- `trap / (σy)` is at most the sharp sum of `Λ` over `(t₁, t₄]`. -/
lemma trap_le_psi_window {a σ D y : ℝ} (hy : 0 < y) (ha : 0 < a) (hσ : 0 ≤ σ) (hσD : σ ≤ D) :
    trap a σ D y ≤ σ * y * (ψ (y * (a + D + σ)) - ψ (y * a)) := by
  have hD : 0 ≤ D := hσ.trans hσD
  set M := ⌊y * (a + D + σ)⌋₊ + 1
  have hfl : ∀ l : ℝ, 0 ≤ l → l ≤ a + D + σ → ⌊y * l⌋₊ + 1 ≤ M := fun l hl hle => by
    have := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hle hy.le)
    omega
  rw [trap_eq_sum hy ha hσ hD, psi_eq_range (by positivity) (hfl _ (by positivity) le_rfl),
    psi_eq_range (by positivity) (hfl _ ha.le (by linarith)),
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
  have := tk_le (u := (n : ℝ)) (s := σ * y)
    (t₁ := y * a) (t₂ := y * (a + σ)) (t₃ := y * (a + D)) (t₄ := y * (a + D + σ))
    (by nlinarith) (by nlinarith) (by nlinarith) (by ring) (by ring)
  calc (Λ n : ℝ) * tk (y * a) (y * (a + σ)) (y * (a + D)) (y * (a + D + σ)) n
      ≤ (Λ n : ℝ) * (σ * y * ((if (n : ℝ) ≤ y * (a + D + σ) then 1 else 0)
        - (if (n : ℝ) ≤ y * a then 1 else 0))) := mul_le_mul_of_nonneg_left this hΛ
    _ = _ := by ring

end Erdos233
