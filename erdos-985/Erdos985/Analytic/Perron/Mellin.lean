import Mathlib

/-!
# Mellin-inversion helpers for the Perron kernels
-/

open Complex MeasureTheory Set Filter Topology

namespace Erdos985.Analytic.PerronAux

lemma inv_ofReal_cpow_neg {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm),
    cpow_neg, inv_inv]

/-- Mellin inversion, repackaged for vertical-line integrals `(1/2π) ∫ y^s F(s) dt`. -/
theorem perron_of_mellin {f : ℝ → ℂ} {F : ℂ → ℂ} {y c : ℝ} (hy : 0 < y)
    (hf : MellinConvergent f c) (hF : ∀ t : ℝ, mellin f (c + t * I) = F (c + t * I))
    (hFi : Integrable fun t : ℝ => F (c + t * I)) (hfc : ContinuousAt f y⁻¹) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
      = f y⁻¹ := by
  have hV : VerticalIntegrable (mellin f) c := by
    unfold VerticalIntegrable
    simp_rw [hF]; exact hFi
  have := mellinInv_mellin_eq c f (inv_pos.2 hy) hf hV hfc
  rw [← this, mellinInv]
  simp_rw [hF, inv_ofReal_cpow_neg hy, smul_eq_mul]
  rw [Complex.real_smul]
  push_cast; ring

/-- Continuity of `indicator (Ioc 0 1) h` at a point `t > 0`, given that `h` vanishes at `1`
when `t = 1`. -/
lemma continuousAt_indicator_Ioc {h : ℝ → ℂ} {t : ℝ} (ht : 0 < t) (hh : ContinuousAt h t)
    (h1 : t = 1 → h 1 = 0) : ContinuousAt (indicator (Ioc 0 1) h) t := by
  rcases lt_trichotomy t 1 with h' | rfl | h'
  · refine hh.congr ?_
    filter_upwards [Ioo_mem_nhds ht h'] with u hu
    rw [indicator_of_mem (show u ∈ Ioc (0:ℝ) 1 from ⟨hu.1, hu.2.le⟩)]
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · refine (hh.continuousWithinAt).congr_of_eventuallyEq ?_ (by simp)
      filter_upwards [Ioc_mem_nhdsLE (show (0:ℝ) < 1 by norm_num)] with u hu
      rw [indicator_of_mem hu]
    · have : ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Ici 1) 1 := continuousWithinAt_const
      refine this.congr_of_eventuallyEq ?_ (by simp [h1 rfl])
      filter_upwards [self_mem_nhdsWithin] with u hu
      rcases eq_or_lt_of_le (show (1:ℝ) ≤ u from hu) with rfl | hu'
      · simp [h1 rfl]
      · rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 hu'))]
  · refine continuousAt_const.congr (f := fun _ => (0:ℂ)) ?_
    filter_upwards [Ioi_mem_nhds h'] with u hu
    rw [indicator_of_notMem (fun hm : u ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 (show 1 < u from hu)))]


/-- The basic Mellin pair `t^a 1_{(0,1]}` with explicit name. -/
noncomputable def P (a : ℂ) : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ a)

lemma hasMellin_P (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) : HasMellin (P a) s (1 / (s + a)) :=
  hasMellin_cpow_Ioc a hs

lemma hasMellin_three (α β γ a b d : ℂ) {s : ℂ} (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re)
    (hd : 0 < s.re + d.re) :
    HasMellin (indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d)) s (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d))) := by
  have e : indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d) = fun t => (α • P a t + β • P b t) + γ • P d t := by
    funext t
    by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [P, ht]
  rw [e]
  have h1 := hasMellin_P a ha
  have h2 := hasMellin_P b hb
  have h3 := hasMellin_P d hd
  have k1 := hasMellin_const_smul h1.1 α
  have k2 := hasMellin_const_smul h2.1 β
  have k3 := hasMellin_const_smul h3.1 γ
  have k12 := hasMellin_add k1.1 k2.1
  have k := hasMellin_add k12.1 k3.1
  refine ⟨k.1, ?_⟩
  rw [k.2, k12.2, k1.2, k2.2, k3.2, h1.2, h2.2, h3.2]
  simp [smul_eq_mul]

lemma integrableOn_P (a : ℂ) (ha : -1 < a.re) : IntegrableOn (P a) (Ioi 0) := by
  have := (hasMellin_P a (s := 1) (by simp; linarith)).1
  unfold MellinConvergent at this
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

lemma hasMellin_log_P (a : ℂ) {s : ℂ} (ha : -1 < a.re) (hs : 0 < s.re + a.re) :
    HasMellin (fun t : ℝ => (Real.log t : ℂ) * P a t) s (-1 / (s + a) ^ 2) := by
  have hloc : LocallyIntegrableOn (P a) (Ioi 0) := (integrableOn_P a ha).locallyIntegrableOn
  have htop : P a =O[atTop] (· ^ (-(s.re + 1))) := by
    refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [P, indicator_of_notMem (fun hm : t ∈ Ioc (0:ℝ) 1 => absurd hm.2 (not_le.2 ht))]
  have hbot : P a =O[𝓝[>] 0] (· ^ (-(-a.re))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    rw [P, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht.1, ht.2.le⟩),
      norm_cpow_eq_rpow_re_of_pos ht.1, neg_neg, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  obtain ⟨hconv, hder⟩ := mellin_hasDerivAt_of_isBigO_rpow hloc htop (by linarith) hbot
    (by linarith)
  have hne : s + a ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hev : mellin (P a) =ᶠ[𝓝 s] fun z => (z + a)⁻¹ := by
    have hopen : IsOpen {z : ℂ | 0 < z.re + a.re} :=
      isOpen_lt continuous_const (continuous_re.add continuous_const)
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [(hasMellin_P a hz).2, one_div]
  have h2 : HasDerivAt (fun z => (z + a)⁻¹) (-1 / (s + a) ^ 2) s := by
    have := ((hasDerivAt_id s).add_const a).inv hne
    simp only [id] at this
    convert this using 1
  have h3 := (h2.congr_of_eventuallyEq hev).unique hder
  refine ⟨?_, ?_⟩
  · refine (hconv).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Complex.real_smul]
  · rw [h3]; unfold mellin; congr 1


/-- The general profile `1_{(0,1]}(t) (κ t^{a₀} log t + α t^a + β t^b + γ t^d)`. -/
noncomputable def prof (κ a₀ α β γ a b d : ℂ) : ℝ → ℂ :=
  indicator (Ioc 0 1) (fun t : ℝ => κ * ((Real.log t : ℂ) * (t : ℂ) ^ a₀) +
    (α * (t : ℂ) ^ a + β * (t : ℂ) ^ b + γ * (t : ℂ) ^ d))

lemma hasMellin_prof (κ a₀ α β γ a b d : ℂ) {s : ℂ} (ha₀ : -1 < a₀.re) (ha₀' : 0 < s.re + a₀.re)
    (ha : 0 < s.re + a.re) (hb : 0 < s.re + b.re) (hd : 0 < s.re + d.re) :
    HasMellin (prof κ a₀ α β γ a b d) s (κ * (-1 / (s + a₀) ^ 2) +
      (α * (1 / (s + a)) + β * (1 / (s + b)) + γ * (1 / (s + d)))) := by
  have e : prof κ a₀ α β γ a b d = fun t => κ • ((Real.log t : ℂ) * P a₀ t) +
      indicator (Ioc 0 1) (fun t : ℝ => α * (t : ℂ) ^ a + β * (t : ℂ) ^ b +
      γ * (t : ℂ) ^ d) t := by
    funext t
    by_cases ht : t ∈ Ioc (0:ℝ) 1 <;> simp [prof, P, ht]
  rw [e]
  have h1 := hasMellin_log_P a₀ ha₀ ha₀'
  have k1 := hasMellin_const_smul h1.1 κ
  have h2 := hasMellin_three α β γ a b d ha hb hd
  have k := hasMellin_add k1.1 h2.1
  refine ⟨k.1, ?_⟩
  rw [k.2, k1.2, h1.2, h2.2, smul_eq_mul]

lemma continuousAt_prof (κ a₀ α β γ a b d : ℂ) {t : ℝ} (ht : 0 < t)
    (h1 : t = 1 → α + β + γ = 0) : ContinuousAt (prof κ a₀ α β γ a b d) t := by
  refine continuousAt_indicator_Ioc ht ?_ (fun h => by simp [h1 h])
  have hc : ∀ e : ℂ, ContinuousAt (fun u : ℝ => (u : ℂ) ^ e) t :=
    fun e => continuousAt_ofReal_cpow_const t e (Or.inr ht.ne')
  have hl : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t :=
    continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht.ne')
  exact (continuousAt_const.mul (hl.mul (hc a₀))).add
    (((continuousAt_const.mul (hc a)).add (continuousAt_const.mul (hc b))).add
      (continuousAt_const.mul (hc d)))

/-- Generic Perron evaluation via Mellin inversion. -/
theorem perron_prof {y c : ℝ} (hy : 0 < y) (κ a₀ α β γ a b d : ℂ)
    (ha₀ : -1 < a₀.re) (ha₀' : 0 < c + a₀.re) (ha : 0 < c + a.re) (hb : 0 < c + b.re)
    (hd : 0 < c + d.re) (h1 : y⁻¹ = 1 → α + β + γ = 0) {F : ℂ → ℂ}
    (hF : ∀ t : ℝ, κ * (-1 / ((c : ℂ) + t * I + a₀) ^ 2) +
      (α * (1 / ((c : ℂ) + t * I + a)) + β * (1 / ((c : ℂ) + t * I + b)) +
        γ * (1 / ((c : ℂ) + t * I + d))) = F (c + t * I))
    (hFi : Integrable fun t : ℝ => F (c + t * I)) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) * F (c + t * I)
      = prof κ a₀ α β γ a b d y⁻¹ := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  refine perron_of_mellin hy ?_ ?_ hFi (continuousAt_prof _ _ _ _ _ _ _ _ (inv_pos.2 hy) h1)
  · exact (hasMellin_prof κ a₀ α β γ a b d (s := (c : ℂ)) ha₀ (by simpa using ha₀')
      (by simpa using ha) (by simpa using hb) (by simpa using hd)).1
  · intro t
    rw [(hasMellin_prof κ a₀ α β γ a b d (s := (c : ℂ) + t * I) ha₀ (by rw [hre]; exact ha₀')
      (by rw [hre]; exact ha) (by rw [hre]; exact hb) (by rw [hre]; exact hd)).2, hF]

end Erdos985.Analytic.PerronAux
