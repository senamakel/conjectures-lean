import Erdos233.MeanSquare

/-!
# Zero waves with general coefficients

`coef_sums`, `mean_square` and `large_wave_measure` are stated for the coefficients `coef δ` of
the second difference `D2`. The same arguments work for any coefficient family `c` with

* `‖c ρ‖ ≤ B / (1 + γ²)` (for absolute summability), and
* `‖c ρ‖² ≤ K · w D ⌊|γ|⌋`, `w D n = min(D⁴, 16D²/(n² + 1/4))` (`Erdos233/Coeff/Series.lean`),

giving `Σ m_ρ ‖c ρ‖² log(|γ|+2) ≤ C K D³ log²(2/D)`, the mean square
`∫_X^{4X} (y^{3/2} |zeroWave c (log y)|)² ≤ 256 C' X⁴ Σ m_ρ ‖c ρ‖² log(|γ|+2)`, and Chebyshev's
inequality for it.
-/

namespace Erdos233

open Complex Erdos985.Analytic Erdos233.CoeffAux MeasureTheory intervalIntegral

/-- `coef_sums` for a general coefficient family. -/
theorem wave_sums : ∃ C : ℝ, 0 < C ∧ ∀ D K B : ℝ, 0 < D → D ≤ 1 / 2 → 0 ≤ K → ∀ c : Zeros → ℂ,
    (∀ ρ : Zeros, ‖c ρ‖ ≤ B / (1 + (ρ : ℂ).im ^ 2)) →
    (∀ ρ : Zeros, ‖c ρ‖ ^ 2 ≤ K * w D ⌊|(ρ : ℂ).im|⌋₊) →
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖) ∧
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) ∧
    ∑' ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ C * K * D ^ 3 * Real.log (2 / D) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := zero_density
  refine ⟨1200 * C, by positivity, fun D K B hδ0 hδ hK c hcB hcw => ?_⟩
  have hS1 : Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖) := by
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) ((hC 0).1.mul_left B)
    have := hcB ρ
    have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
    calc (mult ρ : ℝ) * ‖c ρ‖ ≤ (mult ρ : ℝ) * (B / (1 + (ρ : ℂ).im ^ 2)) := by gcongr
      _ = B * ((mult ρ : ℝ) / (1 + (0 - (ρ : ℂ).im) ^ 2)) := by ring
  set P : ℕ → Zeros → ℝ := fun n ρ => (mult ρ : ℝ) / (1 + ((n : ℝ) - (ρ : ℂ).im) ^ 2) +
    (mult ρ : ℝ) / (1 + (-(n : ℝ) - (ρ : ℂ).im) ^ 2) with hP
  set f : ℕ → Zeros → ℝ := fun n ρ => 2 * K * w D n * Real.log (n + 4) * P n ρ with hf
  have hlog0 : ∀ n : ℕ, 0 ≤ Real.log ((n : ℝ) + 4) :=
    fun n => Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hP0 : ∀ n ρ, 0 ≤ P n ρ := fun n ρ => by simp only [hP]; positivity
  have hf0 : ∀ n ρ, 0 ≤ f n ρ := fun n ρ => by
    simp only [hf]
    have := w_nonneg D n; have := hlog0 n; have := hP0 n ρ
    positivity
  have hPs : ∀ n : ℕ, Summable (P n) := fun n => (hC n).1.add (hC (-(n : ℝ))).1
  have hPt : ∀ n : ℕ, ∑' ρ, P n ρ ≤ 2 * C * Real.log (n + 4) := by
    intro n
    simp only [hP]
    rw [Summable.tsum_add (hC n).1 (hC (-(n : ℝ))).1]
    have h1 := (hC n).2
    have h2 := (hC (-(n : ℝ))).2
    rw [abs_neg, Nat.abs_cast] at h2
    rw [Nat.abs_cast] at h1
    have : Real.log ((n : ℝ) + 2) ≤ Real.log (n + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    nlinarith
  have hfs : ∀ n, Summable (f n) := fun n => (hPs n).mul_left _
  have hft : ∀ n : ℕ, ∑' ρ, f n ρ ≤ 4 * C * K * (w D n * Real.log (n + 4) ^ 2) := by
    intro n
    simp only [hf]
    rw [tsum_mul_left]
    have := w_nonneg D n
    have := hlog0 n
    calc 2 * K * w D n * Real.log (n + 4) * ∑' ρ, P n ρ
        ≤ 2 * K * w D n * Real.log (n + 4) * (2 * C * Real.log (n + 4)) := by
          gcongr; exact hPt n
      _ = _ := by ring
  obtain ⟨hbS, hbT⟩ := series_bound D hδ0 hδ
  have hfsum : Summable (Function.uncurry f) := by
    refine (summable_prod_of_nonneg (f := Function.uncurry f) (fun p => hf0 p.1 p.2)).mpr
      ⟨fun n => hfs n, ?_⟩
    exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (hf0 n)) hft (hbS.mul_left _)
  have hslice : ∀ ρ, Summable (fun n => f n ρ) := fun ρ =>
    hfsum.comp_injective (i := fun n => (n, ρ)) (fun a b h => by simpa using h)
  have hsumρ : Summable (fun ρ => ∑' n, f n ρ) := hfsum.prod_symm.prod
  have hpt : ∀ ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ f ⌊|(ρ : ℂ).im|⌋₊ ρ := by
    intro ρ
    set γ := (ρ : ℂ).im with hγ
    set n := ⌊|γ|⌋₊ with hn
    have hn1 : (n : ℝ) ≤ |γ| := Nat.floor_le (abs_nonneg _)
    have hn2 : |γ| < n + 1 := Nat.lt_floor_add_one _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
    have hw : ‖c ρ‖ ^ 2 ≤ K * w D n := hcw ρ
    have hlog : Real.log (|γ| + 2) ≤ Real.log (n + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogγ : 0 ≤ Real.log (|γ| + 2) := Real.log_nonneg (by linarith [abs_nonneg γ])
    have hP2 : (mult ρ : ℝ) ≤ 2 * P n ρ := by
      simp only [hP]
      have key : ∀ x : ℝ, x ^ 2 < 1 → (mult ρ : ℝ) ≤ 2 * ((mult ρ : ℝ) / (1 + x ^ 2)) := by
        intro x hx
        have : (mult ρ : ℝ) / 2 ≤ (mult ρ : ℝ) / (1 + x ^ 2) :=
          div_le_div_of_nonneg_left hm (by positivity) (by linarith)
        linarith
      have ha : 0 ≤ (mult ρ : ℝ) / (1 + ((n : ℝ) - γ) ^ 2) := by positivity
      have hb : 0 ≤ (mult ρ : ℝ) / (1 + (-(n : ℝ) - γ) ^ 2) := by positivity
      rcases le_or_gt 0 γ with hg | hg
      · rw [abs_of_nonneg hg] at hn1 hn2
        have := key ((n : ℝ) - γ) (by nlinarith)
        linarith
      · rw [abs_of_neg hg] at hn1 hn2
        have := key (-(n : ℝ) - γ) (by nlinarith)
        linarith
    have hw0 := w_nonneg D n
    have hl0 := hlog0 n
    have hKw : 0 ≤ K * w D n := mul_nonneg hK hw0
    calc (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|γ| + 2)
        ≤ (mult ρ : ℝ) * (K * w D n) * Real.log (n + 4) := by gcongr
      _ ≤ (2 * P n ρ) * (K * w D n) * Real.log (n + 4) := by gcongr
      _ = f n ρ := by simp only [hf]; ring
  have hpt' : ∀ ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ ∑' n, f n ρ := fun ρ =>
    (hpt ρ).trans ((hslice ρ).le_tsum _ (fun j _ => hf0 j ρ))
  have hS2 : Summable (fun ρ : Zeros =>
      (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) :=
    Summable.of_nonneg_of_le (fun ρ => mul_nonneg (by positivity)
      (Real.log_nonneg (by linarith [abs_nonneg (ρ : ℂ).im]))) hpt' hsumρ
  refine ⟨hS1, hS2, ?_⟩
  calc ∑' ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)
      ≤ ∑' ρ, ∑' n, f n ρ := Summable.tsum_le_tsum hpt' hS2 hsumρ
    _ = ∑' n, ∑' ρ, f n ρ := hfsum.tsum_comm' hfs hslice
    _ ≤ ∑' n : ℕ, 4 * C * K * (w D n * Real.log (n + 4) ^ 2) :=
        Summable.tsum_le_tsum hft hfsum.prod (hbS.mul_left _)
    _ = 4 * C * K * ∑' n : ℕ, w D n * Real.log (n + 4) ^ 2 := tsum_mul_left
    _ ≤ 4 * C * K * (300 * D ^ 3 * Real.log (2 / D) ^ 2) := by gcongr
    _ = 1200 * C * K * D ^ 3 * Real.log (2 / D) ^ 2 := by ring

/-- `mean_square` for a general coefficient family. -/
theorem wave_mean_square : ∃ Cm : ℝ, 0 < Cm ∧ ∀ c : Zeros → ℂ,
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖) →
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) →
    ∀ x : ℝ, 1 ≤ x →
    IntervalIntegrable (fun y => (y ^ (3 / 2 : ℝ) * ‖zeroWave c (Real.log y)‖) ^ 2)
      volume x (4 * x) ∧
    ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖zeroWave c (Real.log y)‖) ^ 2
      ≤ 256 * Cm * x ^ 4 *
        ∑' ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2) := by
  obtain ⟨Cm, hCm, hM⟩ := mean_value
  refine ⟨Cm, hCm, fun c hs1 hs2 x hx => ?_⟩
  set F := zeroWave c with hFdef
  have hFc : Continuous F := continuous_zeroWave hs1
  have hx0 : 0 < x := by linarith
  have hx4 : x ≤ 4 * x := by linarith
  have hlogc : ContinuousOn Real.log (Set.Icc x (4 * x)) :=
    Real.continuousOn_log.mono fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (lt_of_lt_of_le hx0 hy.1).ne'
  have hG : ContinuousOn (fun y => ‖F (Real.log y)‖ ^ 2) (Set.Icc x (4 * x)) :=
    ((hFc.comp_continuousOn hlogc).norm).pow 2
  have hpow : ContinuousOn (fun y : ℝ => y ^ (3 / 2 : ℝ)) (Set.Icc x (4 * x)) :=
    fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).continuousWithinAt
  have hInt : ContinuousOn (fun y => (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2)
      (Set.Icc x (4 * x)) :=
    (hpow.mul ((hFc.comp_continuousOn hlogc).norm)).pow 2
  have hII : IntervalIntegrable (fun y => (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2)
      volume x (4 * x) :=
    (hInt.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  refine ⟨hII, ?_⟩
  have hGI : IntervalIntegrable (fun y => ‖F (Real.log y)‖ ^ 2) volume x (4 * x) :=
    (hG.mono (by rw [Set.uIcc_of_le hx4])).intervalIntegrable
  have h1 : ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2
      ≤ ∫ y in x..4 * x, 64 * x ^ 3 * ‖F (Real.log y)‖ ^ 2 := by
    refine integral_mono_on hx4 hII (hGI.const_mul _) fun y hy => ?_
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have e : (y ^ (3 / 2 : ℝ)) ^ 2 = y ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
    rw [mul_pow, e]
    have : y ^ 3 ≤ (4 * x) ^ 3 := pow_le_pow_left₀ hy0 hy.2 3
    have h0 : 0 ≤ ‖F (Real.log y)‖ ^ 2 := by positivity
    nlinarith
  have h2 : ∫ y in x..4 * x, ‖F (Real.log y)‖ ^ 2
      = ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 * Real.exp u := by
    have hsub := integral_comp_mul_deriv' (a := Real.log x) (b := Real.log (4 * x))
      (f := Real.exp) (f' := Real.exp) (g := fun y => ‖F (Real.log y)‖ ^ 2)
      (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn (by
        refine ContinuousOn.pow (ContinuousOn.norm (hFc.comp_continuousOn ?_)) 2
        exact Real.continuousOn_log.mono fun y hy => by
          obtain ⟨u, -, rfl⟩ := hy
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact (Real.exp_pos u).ne')
    rw [Real.exp_log hx0, Real.exp_log (by linarith)] at hsub
    rw [← hsub]
    refine integral_congr fun u _ => ?_
    simp [Function.comp, Real.log_exp]
  have hlog4 : Real.log (4 * x) = Real.log x + Real.log 4 := by
    rw [Real.log_mul (by norm_num) hx0.ne']; ring
  have hlog4' : Real.log 4 < 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hab : Real.log x ≤ Real.log (4 * x) := by rw [hlog4]; linarith
  have hFI : ∀ a b : ℝ, IntervalIntegrable (fun u => ‖F u‖ ^ 2) volume a b := fun a b =>
    ((hFc.norm).pow 2).intervalIntegrable _ _
  have h3 : ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 * Real.exp u
      ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F u‖ ^ 2 := by
    calc ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 * Real.exp u
        ≤ ∫ u in Real.log x..Real.log (4 * x), 4 * x * ‖F u‖ ^ 2 := by
          refine integral_mono_on hab
            ((((hFc.norm).pow 2).mul Real.continuous_exp).intervalIntegrable _ _)
            ((hFI _ _).const_mul _) fun u hu => ?_
          have : Real.exp u ≤ 4 * x := by
            calc Real.exp u ≤ Real.exp (Real.log (4 * x)) := Real.exp_le_exp.2 hu.2
              _ = 4 * x := Real.exp_log (by linarith)
          have h0 : 0 ≤ ‖F u‖ ^ 2 := by positivity
          nlinarith
      _ = 4 * x * ∫ u in Real.log x..Real.log (4 * x), ‖F u‖ ^ 2 := integral_const_mul _ _
      _ ≤ 4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F u‖ ^ 2 := by
          gcongr
          exact integral_mono_interval le_rfl hab (by rw [hlog4]; linarith)
            (Filter.Eventually.of_forall fun u => by positivity) (hFI _ _)
  have h4 := hM c hs1 hs2 (Real.log x)
  calc ∫ y in x..4 * x, (y ^ (3 / 2 : ℝ) * ‖F (Real.log y)‖) ^ 2
      ≤ ∫ y in x..4 * x, 64 * x ^ 3 * ‖F (Real.log y)‖ ^ 2 := h1
    _ = 64 * x ^ 3 * ∫ y in x..4 * x, ‖F (Real.log y)‖ ^ 2 := integral_const_mul _ _
    _ ≤ 64 * x ^ 3 * (4 * x * ∫ u in Real.log x..Real.log x + 2, ‖F u‖ ^ 2) := by
        rw [h2]; gcongr
    _ = 256 * x ^ 4 * ∫ u in Real.log x..Real.log x + 2, ‖F u‖ ^ 2 := by ring
    _ ≤ 256 * x ^ 4 * (Cm * ∑' ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 *
          Real.log (|(ρ : ℂ).im| + 2)) := by gcongr
    _ = _ := by ring

/-- Chebyshev's inequality for `wave_mean_square`. -/
theorem wave_large_measure : ∃ Cm : ℝ, 0 < Cm ∧ ∀ c : Zeros → ℂ,
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖) →
    Summable (fun ρ : Zeros => (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) →
    ∀ X : ℝ, 1 ≤ X → ∀ t : ℝ, 0 < t →
    volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖zeroWave c (Real.log y)‖}
      ≤ 256 * Cm * X ^ 4 *
        (∑' ρ : Zeros, (mult ρ : ℝ) * ‖c ρ‖ ^ 2 * Real.log (|(ρ : ℂ).im| + 2)) / t ^ 2 := by
  obtain ⟨Cm, hCm, hms⟩ := wave_mean_square
  refine ⟨Cm, hCm, fun c hs1 hs2 X hX t ht => ?_⟩
  obtain ⟨hII, hMS⟩ := hms c hs1 hs2 X hX
  set W : ℝ → ℝ := fun y => (y ^ (3 / 2 : ℝ) * ‖zeroWave c (Real.log y)‖) ^ 2 with hW
  have hX4 : X ≤ 4 * X := by linarith
  have hint : Integrable W (volume.restrict (Set.Ioc X (4 * X))) := hII.1
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc X (4 * X))] W :=
    ae_of_all _ fun y => by simp only [Pi.zero_apply, hW]; positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn hint (t ^ 2)
  have hI : ∫ y, W y ∂(volume.restrict (Set.Ioc X (4 * X))) = ∫ y in X..4 * X, W y :=
    (integral_of_le hX4).symm
  set E := {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ t ≤ y ^ (3 / 2 : ℝ) * ‖zeroWave c (Real.log y)‖}
    with hE
  set A := {y | t ^ 2 ≤ W y} ∩ Set.Ioc X (4 * X) with hA
  have hsub : E ⊆ A ∪ {X} := by
    rintro y ⟨⟨h1, h2⟩, h3⟩
    rcases eq_or_lt_of_le h1 with h | h
    · right; exact h.symm
    · left
      refine ⟨?_, h, by linarith⟩
      show t ^ 2 ≤ (y ^ (3 / 2 : ℝ) * ‖zeroWave c (Real.log y)‖) ^ 2
      exact pow_le_pow_left₀ ht.le h3 2
  have hμ : (volume.restrict (Set.Ioc X (4 * X))).real {y | t ^ 2 ≤ W y} = volume.real A := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply' measurableSet_Ioc]
  have hfin : volume (A ∪ {X}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 4 * X)).ne (measure_mono ?_)
    rintro y (⟨-, h1, h2⟩ | h)
    · exact ⟨h1.le, h2⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨le_rfl, hX4⟩
  have hEA : volume.real E ≤ volume.real A := by
    calc volume.real E ≤ volume.real (A ∪ {X}) := measureReal_mono hsub hfin
      _ ≤ volume.real A + volume.real ({X} : Set ℝ) := measureReal_union_le _ _
      _ = volume.real A := by simp [Measure.real]
  rw [le_div_iff₀ (by positivity)]
  calc volume.real E * t ^ 2 ≤ t ^ 2 * volume.real A := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hEA (by positivity)
    _ = t ^ 2 * (volume.restrict (Set.Ioc X (4 * X))).real {y | t ^ 2 ≤ W y} := by rw [hμ]
    _ ≤ ∫ y, W y ∂(volume.restrict (Set.Ioc X (4 * X))) := hmk
    _ = ∫ y in X..4 * X, W y := hI
    _ ≤ _ := hMS

end Erdos233
