import Robin.Main.Gain.Basic

/-! # Splitting the gain at `Y` and Abel summation -/

namespace Robin.Gain

open Real Chebyshev

theorem sum_cP_eq_theta (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cP k = θ t := by
  rw [theta_eq_sum_Icc, Finset.sum_filter]; rfl

theorem theta_eq_sum_Ioc_cP (t : ℝ) : θ t = ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, cP k := by
  rw [theta, Finset.sum_filter]; rfl

/-- `t² log t` is monotone on `[1, ∞)`. -/
theorem sq_mul_log_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    s ^ 2 * Real.log s ≤ t ^ 2 * Real.log t := by
  have h0 : 0 ≤ Real.log s := Real.log_nonneg hs
  have h1 : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
  have h2 : s ^ 2 ≤ t ^ 2 := by gcongr
  exact mul_le_mul h2 h1 h0 (by positivity)

/-- Splitting the gain at `Y`. -/
theorem gain_split {x Y : ℝ} (hY1 : 1 < Y) (hYx : Y ≤ x)
    (hYeq : Y ^ 2 * Real.log Y = 1 / epsR x) (heps : 0 < epsR x) :
    epsR x * θ Y + ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊x⌋₊, gW k * cP k ≤ gainSum x := by
  set ε := epsR x
  set h : ℕ → ℝ := fun k => if k.Prime then min (1 / (k : ℝ) ^ 2) (ε * Real.log k) else 0
    with hh
  have hg : gainSum x = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, h k := by
    unfold gainSum primeSum
    rw [Finset.sum_filter]
    have : Finset.Iic ⌊x⌋₊ = Finset.Icc 0 ⌊x⌋₊ := by ext; simp
    rw [this, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
    rw [ite_eq_right Nat.not_prime_zero, zero_add]
  have hfl : ⌊Y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hYx
  rw [hg, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl, theta_eq_sum_Ioc_cP,
    Finset.mul_sum]
  have hεY : ε * (Y ^ 2 * Real.log Y) = 1 := by rw [hYeq]; field_simp
  apply add_le_add
  · apply Finset.sum_le_sum
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    simp only [hh, cP]
    split_ifs with hp
    · apply le_min _ le_rfl
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
      have hkY : (k : ℝ) ≤ Y := (Nat.le_floor_iff (by linarith)).1 hk.2
      have hm := sq_mul_log_mono hk1 hkY
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · simp
  · apply Finset.sum_le_sum
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    simp only [hh, cP]
    split_ifs with hp
    · have hk1 : (1 : ℝ) < k := by exact_mod_cast hp.one_lt
      have hkY : Y ≤ (k : ℝ) := ((Nat.floor_lt (by linarith)).1 hk.1).le
      have hm := sq_mul_log_mono hY1.le hkY
      have hl : 0 < Real.log k := Real.log_pos hk1
      have e : gW k * Real.log k = 1 / (k : ℝ) ^ 2 := by
        unfold gW; field_simp
      rw [e]
      apply le_min le_rfl
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · simp

theorem gain_ge_integral {x Y : ℝ} (hY1 : 1 < Y) (hYx : Y ≤ x)
    (hYeq : Y ^ 2 * Real.log Y = 1 / epsR x) (heps : 0 < epsR x) :
    ∫ t in Y..x, θ t * vW t ≤ gainSum x := by
  have hsplit := gain_split hY1 hYx hYeq heps
  have hdiff : ∀ t ∈ Set.Icc Y x, DifferentiableAt ℝ gW t := fun t ht =>
    (hasDerivAt_gW (by linarith [ht.1])).differentiableAt
  have hint : MeasureTheory.IntegrableOn (deriv gW) (Set.Icc Y x) := by
    have hc : ContinuousOn (fun t => -vW t) (Set.Icc Y x) :=
      (continuousOn_vW.mono fun t ht => show (1 : ℝ) < t by linarith [ht.1]).neg
    exact (hc.integrableOn_Icc).congr_fun
      (fun t ht => ((hasDerivAt_gW (by linarith [ht.1])).deriv).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul cP (by linarith : (0 : ℝ) ≤ Y) hYx hdiff hint
  simp only [sum_cP_eq_theta] at habel
  have hI : ∫ t in Set.Ioc Y x, deriv gW t * θ t = -∫ t in Y..x, θ t * vW t := by
    rw [intervalIntegral.integral_of_le hYx, ← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only
    rw [(hasDerivAt_gW (by linarith [ht.1])).deriv]
    ring
  have hgY : gW Y = epsR x := by
    unfold gW; rw [hYeq]; field_simp
  have hgx : 0 ≤ gW x * θ x := by
    have : 0 < Real.log x := Real.log_pos (by linarith)
    unfold gW
    exact mul_nonneg (by positivity) (theta_nonneg x)
  rw [habel, hI, hgY] at hsplit
  linarith

end Robin.Gain
