import Schoenfeld.Rosser

/-!
# Summing a step function over the zeros with Rosser's zero count

Let `0 = T₀ < T₁ ≤ … ≤ Tₙ` and `B_i ≥ 0`, and let `β(t) = B_i` on `(T_i, T_{i+1}]`,
`β(t) = C/t²` for `t > Tₙ`. If `f ρ ≤ β(|γ|)` for every zero, then under RH

`Σ_ρ m_ρ f(ρ) ≤ 2 (Σ_i B_i (N₀(T_{i+1}) − N₀(T_i)) + E · TV(B) + C · τ(Tₙ)/Tₙ)`

(`tsum_le_of_step`), where `N₀(T) = (T/2π) log(T/2π) − T/2π + 7/8`, `E` is Rosser's error at
`Tₙ`, `TV(B) = B₀ + B_{n−1} + Σ |B_{i+1} − B_i|` and
`τ(T) = (log T − log 2π)/π + 2.613/T + 0.3 log T/T`. The proof: pair `ρ` with `1 − ρ`
(schoenfeld-rh's `reflect`), write each indicator through the zero count `cnt`, sum by parts
against `|cnt − N₀| ≤ E` (Rosser, `Schoenfeld.rosserZeroCount`), and bound the tail through
`Σ_{γ > T} m/γ² ≤ τ(T)/T`, which is the second half of schoenfeld-rh's `Gsum_le_Ub`.
-/

namespace Cramer.CMS

open Real Finset MeasureTheory Set Filter Topology
open Schoenfeld (Zeros mult cnt ind reflect)

/-- The main term of the zero count. -/
noncomputable def N0 (T : ℝ) : ℝ :=
  T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8

/-- Rosser's error term. -/
noncomputable def Ero (T : ℝ) : ℝ := 0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588

/-- The tail factor. -/
noncomputable def tau (T : ℝ) : ℝ :=
  (Real.log T - Real.log (2 * π)) / π + (2.463 + 0.3 / 2) / T + 0.3 * Real.log T / T

/-- **Increments of `N₀`**: `N₀(b) − N₀(a) ≤ (b − a) log(b/2π)/(2π)` for `0 ≤ a ≤ b`, `b > 0`. -/
lemma N0_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    N0 b - N0 a ≤ (b - a) * Real.log (b / (2 * π)) / (2 * π) := by
  have hpi := Real.pi_pos
  unfold N0
  rcases eq_or_lt_of_le ha with rfl | ha0
  · simp only [zero_div, Real.log_zero, mul_zero, sub_zero, zero_sub]
    have : 0 ≤ b / (2 * π) := by positivity
    rw [show b / (2 * π) * Real.log (b / (2 * π)) - b / (2 * π) + 7 / 8 - (0 + 7 / 8) =
      b / (2 * π) * Real.log (b / (2 * π)) - b / (2 * π) by ring]
    have e : b * Real.log (b / (2 * π)) / (2 * π) = b / (2 * π) * Real.log (b / (2 * π)) := by ring
    rw [e]; linarith
  · -- `a log(b/a) ≤ b − a`
    have h1 := Real.log_le_sub_one_of_pos (show 0 < b / a by positivity)
    have hlog : Real.log (b / (2 * π)) - Real.log (a / (2 * π)) = Real.log (b / a) := by
      rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
    have key : a * Real.log (b / a) ≤ b - a := by
      have := mul_le_mul_of_nonneg_left h1 ha0.le
      rw [mul_sub, mul_one, mul_div_cancel₀ _ ha0.ne'] at this; linarith
    have e : b / (2 * π) * Real.log (b / (2 * π)) - b / (2 * π) + 7 / 8 -
        (a / (2 * π) * Real.log (a / (2 * π)) - a / (2 * π) + 7 / 8) -
        (b - a) * Real.log (b / (2 * π)) / (2 * π) =
        (a * (Real.log (b / (2 * π)) - Real.log (a / (2 * π))) - (b - a)) / (2 * π) := by
      field_simp; ring
    have : (a * (Real.log (b / (2 * π)) - Real.log (a / (2 * π))) - (b - a)) / (2 * π) ≤ 0 := by
      rw [hlog]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith

lemma Ero_mono {T T' : ℝ} (hT : 2 ≤ T) (hTT : T ≤ T') : Ero T ≤ Ero T' := by
  unfold Ero
  have h1 : Real.log T ≤ Real.log T' := Real.log_le_log (by linarith) hTT
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have h2 : Real.log (Real.log T) ≤ Real.log (Real.log T') := Real.log_le_log hl h1
  linarith

lemma Ero_ge {T : ℝ} (hT : 4.4 ≤ T) : 1 ≤ Ero T := by
  unfold Ero
  have h1 : 1 < Real.log T := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h2 : 0 < Real.log (Real.log T) := Real.log_pos h1
  linarith

/-- `cnt 0 = 0`. -/
lemma cnt_zero : cnt 0 = 0 := by
  unfold cnt
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  rw [if_neg]; rintro ⟨h1, h2⟩; linarith

/-- **Rosser, two-sided**, at every `T ∈ {0} ∪ [2, T*]`. -/
lemma abs_cnt_sub_N0_le (hR : Schoenfeld.RosserZeroCount) {T Ts : ℝ} (hTs : 4.4 ≤ Ts)
    (hT : T = 0 ∨ (2 ≤ T ∧ T ≤ Ts)) : |cnt T - N0 T| ≤ Ero Ts := by
  rcases hT with rfl | ⟨h2, hle⟩
  · rw [cnt_zero]; unfold N0; simp only [zero_div, Real.log_zero, mul_zero, sub_zero, zero_sub]
    have := Ero_ge hTs; rw [abs_le]; constructor <;> norm_num <;> linarith
  · have h := hR T h2
    rw [Schoenfeld.positiveZeroCount_eq] at h
    have e : N0 T = T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 := rfl
    rw [e]
    exact h.le.trans (Ero_mono h2 hle)

/-! ### Summation by parts -/

/-- `Σ_{i<n} B_i (D_{i+1} − D_i) = B_{n−1} D_n − B₀ D₀ − Σ_{i<n−1} (B_{i+1} − B_i) D_{i+1}`. -/
lemma abel_id (B D : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range n, B i * (D (i + 1) - D i) =
      B (n - 1) * D n - B 0 * D 0 - ∑ i ∈ range (n - 1), (B (i + 1) - B i) * D (i + 1) := by
  induction n, hn using Nat.le_induction with
  | base => simp; ring
  | succ n hn ih =>
    rw [sum_range_succ, ih, show n + 1 - 1 = n by omega,
      show n = (n - 1) + 1 by omega, sum_range_succ, show n - 1 + 1 - 1 = n - 1 by omega]
    ring

lemma abel_le (B D : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) {E : ℝ} (hD : ∀ i ≤ n, |D i| ≤ E) :
    ∑ i ∈ range n, B i * (D (i + 1) - D i) ≤
      E * (|B 0| + |B (n - 1)| + ∑ i ∈ range (n - 1), |B (i + 1) - B i|) := by
  rw [abel_id B D n hn]
  have h1 : B (n - 1) * D n ≤ |B (n - 1)| * E := by
    calc _ ≤ |B (n - 1) * D n| := le_abs_self _
      _ = |B (n - 1)| * |D n| := abs_mul _ _
      _ ≤ |B (n - 1)| * E := mul_le_mul_of_nonneg_left (hD n le_rfl) (abs_nonneg _)
  have h2 : -(B 0 * D 0) ≤ |B 0| * E := by
    calc _ ≤ |B 0 * D 0| := neg_le_abs _
      _ = |B 0| * |D 0| := abs_mul _ _
      _ ≤ |B 0| * E := mul_le_mul_of_nonneg_left (hD 0 (by omega)) (abs_nonneg _)
  have h3 : -∑ i ∈ range (n - 1), (B (i + 1) - B i) * D (i + 1) ≤
      ∑ i ∈ range (n - 1), |B (i + 1) - B i| * E := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun i hi => ?_
    calc _ ≤ |(B (i + 1) - B i) * D (i + 1)| := neg_le_abs _
      _ = |B (i + 1) - B i| * |D (i + 1)| := abs_mul _ _
      _ ≤ |B (i + 1) - B i| * E :=
          mul_le_mul_of_nonneg_left (hD (i + 1) (by have := mem_range.1 hi; omega)) (abs_nonneg _)
  rw [mul_add, mul_add, mul_sum, mul_comm E, mul_comm E]
  rw [show ∑ i ∈ range (n - 1), E * |B (i + 1) - B i| = ∑ i ∈ range (n - 1), |B (i + 1) - B i| * E
    from sum_congr rfl fun i _ => mul_comm _ _]
  linarith

/-! ### Indicators through the zero count -/

lemma ite_split (m u a b : ℝ) (hu : 0 < u) (hab : a ≤ b) :
    m * (if a < u ∧ u ≤ b then 1 else 0) =
      (if 0 < u ∧ u ≤ b then m else 0) - (if 0 < u ∧ u ≤ a then m else 0) := by
  by_cases h1 : u ≤ a
  · have h2 : u ≤ b := le_trans h1 hab
    rw [if_neg (fun h => by linarith [h.1]), if_pos ⟨hu, h2⟩, if_pos ⟨hu, h1⟩]; ring
  · by_cases h2 : u ≤ b
    · rw [if_pos ⟨lt_of_not_ge h1, h2⟩, if_pos ⟨hu, h2⟩, if_neg (fun h => h1 h.2)]; ring
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (fun h => h1 h.2)]; ring

/-- `m · 1[a < |γ| ≤ b]` splits into the positive-ordinate indicators of `ρ` and `1 − ρ`. -/
lemma ind_abs_eq (hRH : RiemannHypothesis) {a b : ℝ} (hab : a ≤ b) (ρ : Zeros) :
    mult ρ * (if a < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ b then 1 else 0) =
      (ind b ρ - ind a ρ) + (ind b (reflect ρ) - ind a (reflect ρ)) := by
  have hp := Schoenfeld.im_sq_pos hRH ρ
  have hne : (ρ : ℂ).im ≠ 0 := fun h => by rw [h] at hp; norm_num at hp
  unfold ind
  rw [Schoenfeld.im_reflect, Schoenfeld.mult_reflect]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [abs_of_neg hneg, ite_split (mult ρ) _ a b (by linarith) hab,
      if_neg (show ¬(0 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ b) from fun h => by linarith [h.1]),
      if_neg (show ¬(0 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ a) from fun h => by linarith [h.1])]
    ring
  · rw [abs_of_pos hpos, ite_split (mult ρ) _ a b hpos hab,
      if_neg (show ¬(0 < -(ρ : ℂ).im ∧ -(ρ : ℂ).im ≤ b) from fun h => by linarith [h.1]),
      if_neg (show ¬(0 < -(ρ : ℂ).im ∧ -(ρ : ℂ).im ≤ a) from fun h => by linarith [h.1])]
    ring

lemma summable_ind (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun ρ => ind t (reflect ρ) :=
  (reflect.summable_iff).mpr (Schoenfeld.ind_summable hRH ht)

/-- `Σ_ρ m 1[a < |γ| ≤ b] = 2 (cnt b − cnt a)`. -/
lemma tsum_ind_abs (hRH : RiemannHypothesis) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑' ρ : Zeros, mult ρ * (if a < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ b then 1 else 0) =
      2 * (cnt b - cnt a) := by
  have hb : 0 ≤ b := ha.trans hab
  have s1 := Schoenfeld.ind_summable hRH hb
  have s2 := Schoenfeld.ind_summable hRH ha
  have s3 := summable_ind hRH hb
  have s4 := summable_ind hRH ha
  rw [tsum_congr (ind_abs_eq hRH hab), ((s1.sub s2)).tsum_add (s3.sub s4), s1.tsum_sub s2,
    s3.tsum_sub s4, reflect.tsum_eq (ind b), reflect.tsum_eq (ind a), Schoenfeld.cnt_eq,
    Schoenfeld.cnt_eq]
  ring

lemma summable_ind_abs (hRH : RiemannHypothesis) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Summable fun ρ : Zeros => mult ρ * (if a < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ b then 1 else 0) := by
  have hb : 0 ≤ b := ha.trans hab
  have s1 := Schoenfeld.ind_summable hRH hb
  have s2 := Schoenfeld.ind_summable hRH ha
  have s3 := summable_ind hRH hb
  have s4 := summable_ind hRH ha
  exact ((s1.sub s2).add (s3.sub s4)).congr fun ρ => (ind_abs_eq hRH hab ρ).symm

/-! ### The tail `Σ_{γ > T} m/γ²` -/

/-- `Σ_ρ ∫_{t > T} bF ≤ τ(T)`: the tail half of schoenfeld-rh's `Gsum_le_Ub`. -/
lemma tsum_int_bF_le (hRH : RiemannHypothesis) (hR : Schoenfeld.RosserZeroCount) {T : ℝ}
    (hT : 4.4 ≤ T) :
    Summable (fun ρ => ∫ t in Ioi T, Schoenfeld.bF T ρ t) ∧
      ∑' ρ, ∫ t in Ioi T, Schoenfeld.bF T ρ t ≤ tau T := by
  have hT0 : 0 < T := by linarith
  have hBi : ∀ ρ, Integrable (Schoenfeld.bF T ρ) (volume.restrict (Ioi T)) := by
    intro ρ; unfold Schoenfeld.bF
    split_ifs
    · exact (Schoenfeld.integrableOn_cube (mult ρ) hT0 (Schoenfeld.mult_nonneg ρ) le_rfl).indicator
        measurableSet_Ioi
    · exact integrable_zero _ _ _
  have hA0 : ∀ ρ, 0 ≤ ∫ t in (Ioc (4.4 : ℝ) T), Schoenfeld.aF ρ t :=
    fun ρ => integral_nonneg (Schoenfeld.aF_nonneg ρ)
  have hB0 : ∀ ρ, 0 ≤ ∫ t in (Ioi T), Schoenfeld.bF T ρ t := fun ρ =>
    setIntegral_nonneg measurableSet_Ioi fun t ht => Schoenfeld.bF_nonneg hT0.le ρ (by linarith [ht.out])
  have hps := Schoenfeld.posTerm_summable hRH hT0.le
  have hBs : Summable fun ρ => ∫ t in (Ioi T), Schoenfeld.bF T ρ t :=
    Summable.of_nonneg_of_le hB0 (fun ρ => by rw [Schoenfeld.posTerm_eq hRH hT ρ]; linarith [hA0 ρ]) hps
  refine ⟨hBs, ?_⟩
  have hBn : Summable fun ρ => ∫ t in (Ioi T), ‖Schoenfeld.bF T ρ t‖ := by
    refine hBs.congr fun ρ => ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact (Real.norm_of_nonneg (Schoenfeld.bF_nonneg hT0.le ρ (by linarith [ht.out]))).symm
  rw [integral_tsum_of_summable_integral_norm hBi hBn]
  have hd : ∀ x ∈ Ici T, HasDerivAt (Schoenfeld.Rt T) (Schoenfeld.Nc x * (2 * T / x ^ 3)) x :=
    fun x hx => Schoenfeld.hasDerivAt_Rt T (by linarith [hx.out])
  have hpos : ∀ x ∈ Ioi T, 0 ≤ Schoenfeld.Nc x * (2 * T / x ^ 3) := fun x hx => by
    have : T < x := hx.out
    exact mul_nonneg (Schoenfeld.Nc_pos (by linarith)).le
      (div_nonneg (by linarith) (pow_nonneg (by linarith) 3))
  have hI := integrableOn_Ioi_deriv_of_nonneg' hd hpos (Schoenfeld.tendsto_Rt T)
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos (Schoenfeld.tendsto_Rt T)
  have hle : ∫ t in (Ioi T), (∑' ρ, Schoenfeld.bF T ρ t) ≤
      ∫ t in (Ioi T), Schoenfeld.Nc t * (2 * T / t ^ 3) := by
    refine integral_mono_of_nonneg ?_ hI ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      exact tsum_nonneg fun ρ => Schoenfeld.bF_nonneg hT0.le ρ (by linarith [ht.out])
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 ≤ t := by linarith [ht.out]
    have hs := Schoenfeld.ind_summable hRH ht0
    have hb := fun ρ => Schoenfeld.bF_le hT0.le ρ ht0
    calc ∑' ρ, Schoenfeld.bF T ρ t ≤ ∑' ρ, ind t ρ * (2 * T / t ^ 3) :=
          (Summable.of_nonneg_of_le (fun ρ => Schoenfeld.bF_nonneg hT0.le ρ ht0) hb
            (hs.mul_right _)).tsum_le_tsum hb (hs.mul_right _)
      _ = cnt t * (2 * T / t ^ 3) := by rw [tsum_mul_right, Schoenfeld.cnt_eq]
      _ ≤ Schoenfeld.Nc t * (2 * T / t ^ 3) := by
          gcongr; exact Schoenfeld.cnt_le_Nc hR (by linarith [ht.out])
  refine hle.trans (le_of_eq ?_)
  rw [hval]
  unfold Schoenfeld.Rt tau
  field_simp
  ring

/-- `Σ_ρ m 1[|γ| > T]/γ² ≤ 2τ(T)/T`. -/
lemma tail_le (hRH : RiemannHypothesis) (hR : Schoenfeld.RosserZeroCount) {T : ℝ} (hT : 4.4 ≤ T) :
    Summable (fun ρ : Zeros => mult ρ * (if T < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0)) ∧
      ∑' ρ : Zeros, mult ρ * (if T < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0) ≤ 2 * (tau T / T) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hs, hle⟩ := tsum_int_bF_le hRH hR hT
  set P : Zeros → ℝ := fun ρ => (1 / T) * ∫ t in Ioi T, Schoenfeld.bF T ρ t
  have hP : ∀ ρ : Zeros, mult ρ * (if T < (ρ : ℂ).im then 1 / (ρ : ℂ).im ^ 2 else 0) ≤ P ρ := by
    intro ρ
    simp only [P]
    rw [Schoenfeld.integral_bF hRH hT ρ]
    by_cases h : T < (ρ : ℂ).im
    · rw [if_pos h, if_pos (by linarith), max_eq_right h.le]
      have : 0 < (ρ : ℂ).im := by linarith
      field_simp; rfl
    · rw [if_neg h, mul_zero]
      split_ifs
      · have := Schoenfeld.mult_nonneg ρ; positivity
      · simp
  have hsplit : ∀ ρ : Zeros, mult ρ * (if T < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0) ≤
      P ρ + P (reflect ρ) := by
    intro ρ
    have h1 := hP ρ
    have h2 := hP (reflect ρ)
    rw [Schoenfeld.im_reflect, Schoenfeld.mult_reflect, neg_sq] at h2
    have hm := Schoenfeld.mult_nonneg ρ
    have hP0 : ∀ ρ, 0 ≤ P ρ := fun ρ => mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Ioi fun t ht => Schoenfeld.bF_nonneg hT0.le ρ (by linarith [ht.out]))
    rcases le_or_gt 0 (ρ : ℂ).im with hpos | hneg
    · rw [abs_of_nonneg hpos]; linarith [hP0 (reflect ρ)]
    · rw [abs_of_neg hneg]; linarith [hP0 ρ]
  have hPs : Summable P := hs.mul_left _
  have hPs' : Summable fun ρ => P (reflect ρ) := (reflect.summable_iff).mpr hPs
  have hnn : ∀ ρ : Zeros, 0 ≤ mult ρ * (if T < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0) := by
    intro ρ; have := Schoenfeld.mult_nonneg ρ; split_ifs <;> positivity
  have hsum : Summable fun ρ : Zeros => mult ρ * (if T < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0) :=
    Summable.of_nonneg_of_le hnn hsplit (hPs.add hPs')
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' ρ, (P ρ + P (reflect ρ)) := hsum.tsum_le_tsum hsplit (hPs.add hPs')
    _ = 2 * ∑' ρ, P ρ := by rw [hPs.tsum_add hPs', reflect.tsum_eq P]; ring
    _ = 2 * ((1 / T) * ∑' ρ, ∫ t in Ioi T, Schoenfeld.bF T ρ t) := by simp only [P, tsum_mul_left]
    _ ≤ 2 * (tau T / T) := by
        gcongr
        rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hle hT0.le

/-! ### The step-function bound -/

/-- **Summing a step function over the zeros.** -/
theorem tsum_le_of_step (hRH : RiemannHypothesis) (hR : Schoenfeld.RosserZeroCount) {n : ℕ}
    (hn : 1 ≤ n) (T B : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hT0 : T 0 = 0)
    (hT2 : ∀ i, 1 ≤ i → i ≤ n → 2 ≤ T i) (hmono : ∀ i, i < n → T i ≤ T (i + 1))
    (hTn : 4.4 ≤ T n) (hB : ∀ i, i < n → 0 ≤ B i) (f : Zeros → ℝ) (hf0 : ∀ ρ, 0 ≤ f ρ)
    (hf : ∀ ρ : Zeros, f ρ ≤ ∑ i ∈ range n, B i *
      (if T i < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ T (i + 1) then 1 else 0) +
      C * (if T n < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0)) :
    Summable (fun ρ => mult ρ * f ρ) ∧
      ∑' ρ, mult ρ * f ρ ≤ 2 * (∑ i ∈ range n, B i * (N0 (T (i + 1)) - N0 (T i)) +
        Ero (T n) * (|B 0| + |B (n - 1)| + ∑ i ∈ range (n - 1), |B (i + 1) - B i|) +
        C * (tau (T n) / T n)) := by
  have hTnn : ∀ i, i ≤ n → 0 ≤ T i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h
    · rw [hT0]
    · linarith [hT2 i h hi]
  have hTle : ∀ i, i ≤ n → T i ≤ T n := by
    have key : ∀ k i, i + k ≤ n → T i ≤ T (i + k) := by
      intro k
      induction k with
      | zero => intro i _; simp
      | succ k ih =>
        intro i hik
        have := ih i (by omega)
        have h2 := hmono (i + k) (by omega)
        rw [show i + (k + 1) = i + k + 1 by ring]; linarith
    intro i hi
    have := key (n - i) i (by omega)
    rwa [show i + (n - i) = n by omega] at this
  -- the indicator series
  set ind' : ℕ → Zeros → ℝ := fun i ρ => mult ρ *
    (if T i < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ T (i + 1) then 1 else 0)
  set tl : Zeros → ℝ := fun ρ => mult ρ * (if T n < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0)
  have hsi : ∀ i ∈ range n, Summable (ind' i) := fun i hi =>
    summable_ind_abs hRH (hTnn i (by have := mem_range.1 hi; omega)) (hmono i (mem_range.1 hi))
  have hti : ∀ i ∈ range n, ∑' ρ, ind' i ρ = 2 * (cnt (T (i + 1)) - cnt (T i)) := fun i hi =>
    tsum_ind_abs hRH (hTnn i (by have := mem_range.1 hi; omega)) (hmono i (mem_range.1 hi))
  obtain ⟨htls, htl⟩ := tail_le hRH hR hTn
  set g : Zeros → ℝ := fun ρ => ∑ i ∈ range n, B i * ind' i ρ + C * tl ρ
  have hg : Summable g :=
    (summable_sum fun i hi => (hsi i hi).mul_left (B i)).add (htls.mul_left C)
  have hfg : ∀ ρ, mult ρ * f ρ ≤ g ρ := by
    intro ρ
    have hm := Schoenfeld.mult_nonneg ρ
    calc mult ρ * f ρ ≤ mult ρ * (∑ i ∈ range n, B i *
          (if T i < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ T (i + 1) then 1 else 0) +
          C * (if T n < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0)) :=
          mul_le_mul_of_nonneg_left (hf ρ) hm
      _ = g ρ := by
          simp only [g, ind', tl, mul_add, mul_sum]
          congr 1
          · refine sum_congr rfl fun i _ => by ring
          · ring
  have hfs : Summable fun ρ => mult ρ * f ρ :=
    Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Schoenfeld.mult_nonneg ρ) (hf0 ρ)) hfg hg
  refine ⟨hfs, ?_⟩
  have hgsum : ∑' ρ, g ρ = ∑ i ∈ range n, B i * (2 * (cnt (T (i + 1)) - cnt (T i))) +
      C * ∑' ρ, tl ρ := by
    simp only [g]
    rw [(summable_sum fun i hi => (hsi i hi).mul_left (B i)).tsum_add (htls.mul_left C),
      Summable.tsum_finsetSum (fun i hi => (hsi i hi).mul_left (B i)), tsum_mul_left]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [tsum_mul_left, hti i hi]
  -- summation by parts against `|cnt − N₀| ≤ E`
  set D : ℕ → ℝ := fun i => cnt (T i) - N0 (T i)
  have hD : ∀ i ≤ n, |D i| ≤ Ero (T n) := by
    intro i hi
    refine abs_cnt_sub_N0_le hR hTn ?_
    rcases Nat.eq_zero_or_pos i with rfl | h
    · left; exact hT0
    · right; exact ⟨hT2 i h hi, hTle i hi⟩
  have habel := abel_le B D n hn hD
  have hsplit : ∑ i ∈ range n, B i * (cnt (T (i + 1)) - cnt (T i)) =
      ∑ i ∈ range n, B i * (N0 (T (i + 1)) - N0 (T i)) + ∑ i ∈ range n, B i * (D (i + 1) - D i) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_; simp only [D]; ring
  have hC' : C * ∑' ρ, tl ρ ≤ C * (2 * (tau (T n) / T n)) := mul_le_mul_of_nonneg_left htl hC
  calc ∑' ρ, mult ρ * f ρ ≤ ∑' ρ, g ρ := hfs.tsum_le_tsum hfg hg
    _ = 2 * ∑ i ∈ range n, B i * (cnt (T (i + 1)) - cnt (T i)) + C * ∑' ρ, tl ρ := by
        rw [hgsum, mul_sum]; congr 1; refine sum_congr rfl fun i _ => by ring
    _ ≤ _ := by rw [hsplit]; nlinarith

end Cramer.CMS
