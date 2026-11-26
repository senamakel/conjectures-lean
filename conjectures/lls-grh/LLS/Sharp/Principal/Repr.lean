import LLS.Sharp.Principal.Mellin

/-!
# Integral representations of the principal sums

For a weight `g` decreasing on `(a, ∞)`, `H_g(t) = Σ_{n ≤ t} Λ(n) g(n) − ψ(t) g(t)` is continuous
(it is `Σ_n Λ(n) max(g(n) − g(t), 0)`) with right derivative `−ψ(t) g'(t)`. Comparing right
derivatives:

* `g = 1/u`: `H(t) − log t − E(t)/t² + 2∫_t^∞ E u^{−3} du` is constant on `[1, ∞)`, equal to
  `1/2 + 2∫_1^∞ E u^{−3} = −1 − γ` at `t = 1`;
* `g = 1/(u log u)`: `H(t) + 1/log t − log log t − E(t) w(t) − ∫_t^∞ E w'` is constant on
  `[100, ∞)`.
-/

namespace LLS.Sharp.Principal

open Filter Topology Real MeasureTheory Set ArithmeticFunction Robin Chebyshev

/-- `H_g(t) = Σ_{n ≤ t} Λ(n) g(n) − ψ(t) g(t)`. -/
noncomputable def Hg (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) * g n - ψ t * g t

lemma Hg_eq_sum {g : ℝ → ℝ} (t : ℝ) :
    Hg g t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) * (g n - g t) := by
  rw [Hg, psi_eq_sum_range, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

lemma Hg_eq_sum_max {g : ℝ → ℝ} {a : ℝ} (ha : a < 2)
    (hg : ∀ u v, a < u → u ≤ v → g v ≤ g u) (hg' : ∀ u v, a < u → u < v → g v < g u)
    {t : ℝ} (ht : a < t) (ht0 : 0 ≤ t) {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    Hg g t = ∑ n ∈ Finset.range (N + 1), (Λ n : ℝ) * max (g n - g t) 0 := by
  rw [Hg_eq_sum]
  refine sum_range_floor_eq t hN _ _ (by simp) (fun n _ hn => ?_) (fun n hn => ?_)
  · by_cases h0 : (Λ n : ℝ) = 0
    · simp [h0]
    have hpp : IsPrimePow n := by by_contra h; exact h0 (by simp [vonMangoldt_apply, h])
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hpp.two_le
    rw [max_eq_left (sub_nonneg.mpr (hg n t (by linarith) hn))]
  · by_cases h0 : (Λ n : ℝ) = 0
    · simp [h0]
    rw [max_eq_right (by linarith [hg' t n ht hn]), mul_zero]

lemma Hg_continuousAt {g : ℝ → ℝ} {a : ℝ} (ha : a < 2)
    (hg : ∀ u v, a < u → u ≤ v → g v ≤ g u) (hg' : ∀ u v, a < u → u < v → g v < g u)
    {t : ℝ} (ht : a < t) (ht0 : 0 < t) (hc : ContinuousAt g t) : ContinuousAt (Hg g) t := by
  set N := ⌊t⌋₊ + 1
  have hF : ContinuousAt (fun s : ℝ =>
      ∑ n ∈ Finset.range (N + 1), (Λ n : ℝ) * max (g n - g s) 0) t := by
    have : ∀ n ∈ Finset.range (N + 1), ContinuousAt
        (fun s : ℝ => (Λ n : ℝ) * max (g n - g s) 0) t := fun n _ =>
      continuousAt_const.mul ((continuousAt_const.sub hc).max continuousAt_const)
    exact tendsto_finsetSum _ this
  refine hF.congr ?_
  have htN : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one t
  filter_upwards [Iio_mem_nhds htN, Ioi_mem_nhds (show max a 0 < t from max_lt ht ht0)]
    with s hs hs1
  have hs1' := max_lt_iff.mp (show max a 0 < s from hs1)
  exact (Hg_eq_sum_max ha hg hg' hs1'.1 hs1'.2.le
    (Nat.le_of_lt ((Nat.floor_lt' (by omega)).mpr hs))).symm

lemma Hg_hasDerivWithinAt {g : ℝ → ℝ} {g' t : ℝ} (ht0 : 0 ≤ t) (hd : HasDerivAt g g' t) :
    HasDerivWithinAt (Hg g) (-ψ t * g') (Ioi t) t := by
  set m := ⌊t⌋₊ with hm
  set S := ∑ n ∈ Finset.range (m + 1), (Λ n : ℝ) * g n
  have hG : HasDerivAt (fun s => S - ψ t * g s) (-ψ t * g') t := by
    simpa using (hd.const_mul (ψ t)).const_sub S
  have htm : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
  have heq : ∀ s, t ≤ s → s < (m : ℝ) + 1 → Hg g s = S - ψ t * g s := by
    intro s hts hs
    have hfl : ⌊s⌋₊ = m := le_antisymm
      (Nat.lt_succ_iff.mp ((Nat.floor_lt' (by omega)).mpr (by push_cast; exact hs)))
      (Nat.floor_le_floor hts)
    have hψ : ψ s = ψ t := by rw [psi_eq_sum_range, psi_eq_sum_range, hfl]
    simp only [Hg, hfl, hψ, S]
  refine hG.hasDerivWithinAt.congr_of_eventuallyEq ?_ (heq t le_rfl htm)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds htm)] with s hs1 hs2
  exact heq s (le_of_lt hs1) hs2

/-! ### Tails `∫_t^∞ f` -/

lemma integrableOn_Ioi_of_cont {f : ℝ → ℝ} {b a : ℝ} (hf : ContinuousOn f (Ioi b))
    (hI : IntegrableOn f (Ioi a)) {s : ℝ} (hs : b < s) : IntegrableOn f (Ioi s) := by
  rcases le_or_gt a s with h | h
  · exact hI.mono_set (Ioi_subset_Ioi h)
  · rw [← Ioc_union_Ioi_eq_Ioi h.le]
    refine IntegrableOn.union ?_ hI
    exact ((hf.mono fun u (hu : u ∈ Icc s a) => show b < u from
      lt_of_lt_of_le hs hu.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self

lemma tail_hasDerivAt {f : ℝ → ℝ} {b : ℝ} (hf : ContinuousOn f (Ioi b))
    (hI : ∀ s, b < s → IntegrableOn f (Ioi s)) {t : ℝ} (ht : b < t) :
    HasDerivAt (fun s => ∫ u in Ioi s, f u) (-f t) t := by
  have hd : HasDerivAt (fun s => ∫ u in t..s, f u) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (IntervalIntegrable.refl)
      (hf.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hf.continuousAt (Ioi_mem_nhds ht))
  have hG : HasDerivAt (fun s => (∫ u in Ioi t, f u) - ∫ u in t..s, f u) (-f t) t := by
    simpa using hd.const_sub (∫ u in Ioi t, f u)
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [← intervalIntegral.integral_Ioi_sub_Ioi' (hI t ht) (hI s hs)]
  ring

/-- A function continuous on `[a, ∞)` with zero right derivative there is constant. -/
lemma const_of_right_deriv {F : ℝ → ℝ} {a : ℝ} (hc : ∀ x, a ≤ x → ContinuousAt F x)
    (hd : ∀ x, a ≤ x → HasDerivWithinAt F 0 (Ioi x) x) {x : ℝ} (hx : a ≤ x) : F x = F a :=
  constant_of_has_deriv_right_zero (fun y hy => (hc y hy.1).continuousWithinAt)
    (fun y hy => (hd y hy.1).Ici_of_Ioi) x ⟨hx, le_rfl⟩

/-! ### `P₂`: the weight `1/u` -/

/-- `f_P(u) = E(u) u^{−3}`. -/
noncomputable def fP (u : ℝ) : ℝ := E1 u * u ^ (-(3 : ℝ))

lemma rpow_neg_three {u : ℝ} (hu : 0 < u) : u ^ (-(3 : ℝ)) = (u ^ 3)⁻¹ := by
  rw [rpow_neg hu.le]; norm_cast

lemma continuousOn_fP : ContinuousOn fP (Ioi 0) :=
  E1_continuous.continuousOn.mul (continuousOn_rpow_const_pos _)

lemma integrableOn_fP (hB : Psi1NatBound) {s : ℝ} (hs : 0 < s) : IntegrableOn fP (Ioi s) := by
  refine integrableOn_Ioi_of_cont (a := 1) continuousOn_fP ?_ hs
  refine (integrableOn_abs_E1_mul hB).mono' ?_ ?_
  · exact (continuousOn_fP.mono fun u (hu : u ∈ Ioi (1:ℝ)) => show (0:ℝ) < u from
      lt_trans one_pos hu).aestronglyMeasurable measurableSet_Ioi
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 1 < u) => ?_
    rw [fP, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]

/-- `D_P(t) = H_{1/u}(t) − log t − E(t)/t² + 2 ∫_t^∞ f_P`. -/
noncomputable def DP (t : ℝ) : ℝ :=
  Hg (fun u => u⁻¹) t - Real.log t - E1 t / t ^ 2 + 2 * ∫ u in Ioi t, fP u

lemma inv_anti (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) : v⁻¹ ≤ u⁻¹ :=
  inv_anti₀ hu huv

lemma inv_strictAnti (u v : ℝ) (hu : 0 < u) (huv : u < v) : v⁻¹ < u⁻¹ :=
  inv_strictAnti₀ hu huv

lemma DP_continuousAt (hB : Psi1NatBound) {t : ℝ} (ht : 0 < t) : ContinuousAt DP t := by
  have h1 : ContinuousAt (Hg fun u => u⁻¹) t :=
    Hg_continuousAt (a := 0) (by norm_num) inv_anti inv_strictAnti ht ht
      (continuousAt_inv₀ ht.ne')
  have h2 : ContinuousAt (fun s => ∫ u in Ioi s, fP u) t :=
    (tail_hasDerivAt continuousOn_fP (fun s hs => integrableOn_fP hB hs) ht).continuousAt
  unfold DP
  exact ((h1.sub (continuousAt_log ht.ne')).sub
    (E1_continuous.continuousAt.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht.ne'))).add
    (continuousAt_const.mul h2)

lemma DP_deriv (hB : Psi1NatBound) {t : ℝ} (ht : 0 < t) : HasDerivWithinAt DP 0 (Ioi t) t := by
  have h1 := Hg_hasDerivWithinAt ht.le (hasDerivAt_inv ht.ne')
  have h2 := (Real.hasDerivAt_log ht.ne').hasDerivWithinAt (s := Ioi t)
  have h3 := (E1_hasDerivWithinAt t).div ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := Ioi t))
    (by positivity)
  have h4 := ((tail_hasDerivAt continuousOn_fP (fun s hs => integrableOn_fP hB hs) ht).const_mul
    2).hasDerivWithinAt (s := Ioi t)
  have h := ((h1.sub h2).sub h3).add h4
  unfold DP
  convert h using 1
  rw [fP, rpow_neg_three ht]
  field_simp
  ring

lemma DP_one (hB : Psi1NatBound) : DP 1 = -1 - Real.eulerMascheroniConstant := by
  have hH : Hg (fun u => u⁻¹) 1 = 0 := by
    simp [Hg, Finset.sum_range_succ, psi_eq_sum_range]
  have hE : E1 1 = -1 / 2 := by
    simp [E1, psi1, Finset.sum_range_succ]; norm_num
  have hI : ∫ u in Ioi 1, fP u = -Real.eulerMascheroniConstant / 2 - 3 / 4 :=
    integral_E1_mul_rpow hB
  rw [DP, hH, hE, hI, Real.log_one]
  ring

/-- **Representation of `P₂`.** For `t ≥ 1`,
`Σ_{n ≤ t} Λ(n)(1/n − 1/t) = log t − 1 − γ + E(t)/t² − 2∫_t^∞ E(u) u^{−3} du`. -/
theorem Hg_inv_eq (hB : Psi1NatBound) {t : ℝ} (ht : 1 ≤ t) :
    Hg (fun u => u⁻¹) t = Real.log t - 1 - Real.eulerMascheroniConstant + E1 t / t ^ 2
      - 2 * ∫ u in Ioi t, fP u := by
  have h := const_of_right_deriv (F := DP) (a := 1)
    (fun x hx => DP_continuousAt hB (by linarith)) (fun x hx => DP_deriv hB (by linarith)) ht
  rw [DP_one hB, DP] at h
  linarith

/-! ### `A`: the weight `1/(u log u)` -/

/-- `g_A(u) = 1/(u log u)`. -/
noncomputable def gA (u : ℝ) : ℝ := 1 / (u * Real.log u)

/-- `f_A(u) = E(u) w'(u)`. -/
noncomputable def fA (u : ℝ) : ℝ := E1 u * wM' u

lemma gA_anti (u v : ℝ) (hu : 1 < u) (huv : u ≤ v) : gA v ≤ gA u := by
  unfold gA
  have hl : 0 < Real.log u := Real.log_pos hu
  have hl' : Real.log u ≤ Real.log v := Real.log_le_log (by linarith) huv
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul huv hl' hl.le (by linarith)

lemma gA_strictAnti (u v : ℝ) (hu : 1 < u) (huv : u < v) : gA v < gA u := by
  unfold gA
  have hl : 0 < Real.log u := Real.log_pos hu
  have hl' : Real.log u ≤ Real.log v := Real.log_le_log (by linarith) huv.le
  apply one_div_lt_one_div_of_lt (by positivity)
  calc u * Real.log u < v * Real.log u := mul_lt_mul_of_pos_right huv hl
    _ ≤ v * Real.log v := mul_le_mul_of_nonneg_left hl' (by linarith)

lemma continuousOn_fA : ContinuousOn fA (Ioi 1) := fun u hu =>
  (E1_continuous.continuousAt.mul (continuousAt_wM' hu)).continuousWithinAt

/-- `|w'(u)| ≤ 2.875/(l u³)` for `4 ≤ l ≤ log u`. -/
lemma abs_wM'_le' {u l : ℝ} (hl : 4 ≤ l) (hu : 0 < u) (hlu : l ≤ Real.log u) :
    |wM' u| ≤ 2.875 / l * u ^ (-(3 : ℝ)) := by
  set L := Real.log u with hL
  have hL0 : 0 < L := by linarith
  rw [rpow_neg_three hu, wM', abs_div, abs_neg, abs_of_pos (by positivity),
    abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
  have key : (2 * L ^ 2 + 3 * L + 2) * l ≤ 2.875 * L ^ 3 := by
    have h1 : 2 * L ^ 2 + 3 * L + 2 ≤ 2.875 * L ^ 2 := by nlinarith
    have h2 : (2 * L ^ 2 + 3 * L + 2) * l ≤ 2.875 * L ^ 2 * l :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlu (by positivity : (0:ℝ) ≤ 2.875 * L ^ 2)]
  have hu3 : 0 < u ^ 3 := by positivity
  have e : 2.875 / l * (u ^ 3)⁻¹ * (u ^ 3 * L ^ 3) = 2.875 * L ^ 3 / l := by
    field_simp
  rw [e, le_div_iff₀ (by linarith)]
  exact key

lemma log_ge_four {x : ℝ} (hx : 100 ≤ x) : 4 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h2 : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := by gcongr
  have h3 : (2.7182818286 : ℝ) ^ 4 ≤ 100 := by norm_num
  linarith

/-- `|f_A(u)| ≤ (2.875/l) q(u)` for `u ≥ 16`, `4 ≤ l ≤ log u`. -/
lemma abs_fA_le (hB : Psi1NatBound) {u l : ℝ} (hu : 16 ≤ u) (hl : 4 ≤ l)
    (hlu : l ≤ Real.log u) : |fA u| ≤ 2.875 / l * qB u := by
  have hu0 : 0 < u := by linarith
  rw [fA, abs_mul]
  calc |E1 u| * |wM' u| ≤ |E1 u| * (2.875 / l * u ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (abs_wM'_le' hl hu0 hlu) (abs_nonneg _)
    _ = 2.875 / l * (|E1 u| * u ^ (-(3 : ℝ))) := by ring
    _ ≤ 2.875 / l * qB u :=
        mul_le_mul_of_nonneg_left (abs_E1_mul_le hB hu) (by positivity)

lemma integrableOn_fA (hB : Psi1NatBound) {s : ℝ} (hs : 1 < s) : IntegrableOn fA (Ioi s) := by
  refine integrableOn_Ioi_of_cont (a := 100) continuousOn_fA ?_ hs
  refine ((integrableOn_qB (by norm_num : (0:ℝ) < 100)).const_mul (2.875 / 4)).mono' ?_ ?_
  · exact (continuousOn_fA.mono fun u (hu : u ∈ Ioi (100:ℝ)) => show (1:ℝ) < u by
      have : (100:ℝ) < u := hu; linarith).aestronglyMeasurable measurableSet_Ioi
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 100 < u) => ?_
    rw [Real.norm_eq_abs]
    exact abs_fA_le hB (by linarith) le_rfl (log_ge_four hu.le)

/-- `D_A(t) = H_{g_A}(t) + 1/log t − log log t − E(t) w(t) − ∫_t^∞ f_A`. -/
noncomputable def DA (t : ℝ) : ℝ :=
  Hg gA t + (Real.log t)⁻¹ - Real.log (Real.log t) - E1 t * wM t - ∫ u in Ioi t, fA u

lemma DA_continuousAt (hB : Psi1NatBound) {t : ℝ} (ht : 1 < t) : ContinuousAt DA t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hgc : ContinuousAt gA t := by
    unfold gA
    exact continuousAt_const.div (continuousAt_id.mul (continuousAt_log ht0))
      (mul_ne_zero ht0 hl)
  have h1 : ContinuousAt (Hg gA) t :=
    Hg_continuousAt (a := 1) (by norm_num) gA_anti gA_strictAnti ht (by linarith) hgc
  have h2 : ContinuousAt (fun s => ∫ u in Ioi s, fA u) t :=
    (tail_hasDerivAt continuousOn_fA (fun s hs => integrableOn_fA hB hs) ht).continuousAt
  have hw : ContinuousAt wM t := (hasDerivAt_wM ht).continuousAt
  unfold DA
  exact (((h1.add ((continuousAt_log ht0).inv₀ hl)).sub ((continuousAt_log ht0).log hl)).sub
    (E1_continuous.continuousAt.mul hw)).sub h2

lemma DA_deriv (hB : Psi1NatBound) {t : ℝ} (ht : 1 < t) : HasDerivWithinAt DA 0 (Ioi t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hgd : HasDerivAt gA (-wM t) t := hasDerivAt_inv_mul_log ht
  have h1 := Hg_hasDerivWithinAt (by linarith) hgd
  have h2 := ((Real.hasDerivAt_log ht0).inv hl).hasDerivWithinAt (s := Ioi t)
  have h3 := ((Real.hasDerivAt_log ht0).log hl).hasDerivWithinAt (s := Ioi t)
  have h4 := (E1_hasDerivWithinAt t).mul (hasDerivAt_wM ht).hasDerivWithinAt
  have h5 := (tail_hasDerivAt continuousOn_fA (fun s hs => integrableOn_fA hB hs)
    ht).hasDerivWithinAt (s := Ioi t)
  have h := (((h1.add h2).sub h3).sub h4).sub h5
  unfold DA
  convert h using 1
  rw [fA, wM]
  field_simp
  ring

/-- **Representation of `A`.** For `t ≥ 100`, `D_A(t) = D_A(100)`. -/
theorem DA_eq (hB : Psi1NatBound) {t : ℝ} (ht : 100 ≤ t) : DA t = DA 100 :=
  const_of_right_deriv (fun x hx => DA_continuousAt hB (by linarith))
    (fun x hx => DA_deriv hB (by linarith)) ht

end LLS.Sharp.Principal
