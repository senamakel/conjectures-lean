import Lindelof.RH
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Step 5: a logarithm of `ζ₁(s) / (s + 1)` on `Re s > 1/2`

`ζ₁(s) / (s + 1) = ζ(s) (s - 1)/(s + 1)` is holomorphic and, under RH, nonvanishing on the
half-plane; the half-plane is simply connected, so it has a holomorphic logarithm. Normalized
against the Euler product, that logarithm is bounded on `2 ≤ σ ≤ 5`. (Dividing by `s + 1`
removes the `log (s - 1)` growth, which would otherwise spoil the three-lines step.)
-/

namespace Lindelof

open Complex Set Filter Topology ArithmeticFunction

/-- The half-plane `Re s > 1/2`. -/
def halfPlane : Set ℂ := {s | 1 / 2 < s.re}

/-- The function whose logarithm we take: `ζ₁(s) / (s + 1)`. -/
noncomputable def zetaQ (s : ℂ) : ℂ := riemannZeta₁ s / (s + 1)

/-- Two distinct solutions of `exp z = 1` are at least `2π` apart. -/
lemma two_pi_le_norm_sub_of_exp_eq_one {z w : ℂ} (hz : exp z = 1) (hw : exp w = 1)
    (hne : z ≠ w) : 2 * Real.pi ≤ ‖z - w‖ := by
  have h : exp (z - w) = 1 := by rw [exp_sub, hz, hw, div_one]
  obtain ⟨n, hn⟩ := exp_eq_one_iff.mp h
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (sub_eq_zero.mp (by simpa using hn))
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  rw [hn, norm_mul, norm_intCast, norm_mul, norm_mul, norm_I, mul_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  nlinarith [Real.pi_pos]

/-- The solution set of `exp z = 1` is discrete. -/
lemma isDiscrete_exp_eq_one : IsDiscrete {z : ℂ | exp z = 1} :=
  ⟨DiscreteTopology.of_forall_le_dist (r := 2 * Real.pi) (by positivity) fun a b hab => by
    show 2 * Real.pi ≤ dist a b
    rw [Subtype.dist_eq, dist_eq_norm]
    exact two_pi_le_norm_sub_of_exp_eq_one a.2 b.2 (Subtype.coe_injective.ne hab)⟩

/-- Two continuous logarithms of the same function on a preconnected set differ by a
constant. -/
lemma sub_eq_sub_of_exp_eq {U : Set ℂ} (hU : IsPreconnected U) {f g : ℂ → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (h : ∀ s ∈ U, exp (f s) = exp (g s))
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) : f x - g x = f y - g y :=
  hU.constant_of_mapsTo isDiscrete_exp_eq_one (hf.sub hg)
    (fun s hs => by simp [exp_sub, h s hs]) hx hy

/-- A continuous logarithm of a holomorphic function on an open set is holomorphic. -/
lemma differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U) {g M : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hM : ContinuousOn M U) (h : ∀ s ∈ U, exp (M s) = g s) :
    DifferentiableOn ℂ M U := by
  intro s₀ hs₀
  have hg0 : g s₀ ≠ 0 := by rw [← h s₀ hs₀]; exact exp_ne_zero _
  have hgd : ∀ s ∈ U, DifferentiableAt ℂ g s := fun s hs => hg.differentiableAt (hU.mem_nhds hs)
  have hcont : ContinuousAt (fun s => g s / g s₀) s₀ := (hgd s₀ hs₀).continuousAt.div_const _
  have hball : Metric.ball (1 : ℂ) 1 ∈ 𝓝 (g s₀ / g s₀) := by
    rw [div_self hg0]; exact Metric.ball_mem_nhds _ one_pos
  have hev : ∀ᶠ s in 𝓝 s₀, s ∈ U ∧ g s / g s₀ ∈ Metric.ball (1 : ℂ) 1 :=
    (hU.eventually_mem hs₀).and (hcont.preimage_mem_nhds hball)
  obtain ⟨ε, hε, hB⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hslit : ∀ s ∈ Metric.ball s₀ ε, g s / g s₀ ∈ slitPlane := by
    intro s hs
    have h1 := (hB s hs).2
    rw [Metric.mem_ball, dist_eq_norm] at h1
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (abs_re_le_norm (g s / g s₀ - 1)).trans_lt h1
    rw [sub_re, one_re] at this
    linarith [neg_abs_le ((g s / g s₀).re - 1)]
  set L : ℂ → ℂ := fun s => log (g s / g s₀) + M s₀ with hL
  have hLd : ∀ s ∈ Metric.ball s₀ ε, DifferentiableAt ℂ L s := fun s hs =>
    (((hgd s (hB s hs).1).div_const _).clog (hslit s hs)).add_const _
  have hLc : ContinuousOn L (Metric.ball s₀ ε) := fun s hs =>
    (hLd s hs).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Metric.ball s₀ ε) :=
    hM.mono fun s hs => (hB s hs).1
  have hexp : ∀ s ∈ Metric.ball s₀ ε, exp (M s) = exp (L s) := by
    intro s hs
    rw [hL, exp_add, exp_log ((div_ne_zero_iff.mpr ⟨?_, hg0⟩)), h s (hB s hs).1, h s₀ hs₀,
      div_mul_cancel₀ _ hg0]
    rw [← h s (hB s hs).1]; exact exp_ne_zero _
  have hs₀B : s₀ ∈ Metric.ball s₀ ε := Metric.mem_ball_self hε
  have heq : ∀ s ∈ Metric.ball s₀ ε, M s = L s := by
    intro s hs
    have := sub_eq_sub_of_exp_eq (convex_ball s₀ ε).isPreconnected hMc hLc hexp hs hs₀B
    simp only [hL, div_self hg0, log_one, zero_add, sub_self] at this
    exact sub_eq_zero.mp this
  have hevEq : M =ᶠ[𝓝 s₀] L :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds s₀ hε) heq
  exact ((hLd s₀ hs₀B).congr_of_eventuallyEq hevEq).differentiableWithinAt

/-- The coefficients `Λ(n) / log n` of `log ζ`. -/
noncomputable def logZetaCoeff : ℕ → ℂ := fun n ↦ Λ n / Real.log n

lemma norm_logZetaCoeff_le (n : ℕ) : ‖logZetaCoeff n‖ ≤ 1 := by
  simp only [logZetaCoeff, norm_div, norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg vonMangoldt_nonneg, abs_of_nonneg (Real.log_natCast_nonneg n)]
  exact div_le_one_of_le₀ vonMangoldt_le_log (Real.log_natCast_nonneg n)

lemma LSeriesSummable_logZetaCoeff {s : ℂ} (hs : 1 < s.re) : LSeriesSummable logZetaCoeff s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => norm_logZetaCoeff_le n) hs

lemma continuousOn_LSeries_logZetaCoeff :
    ContinuousOn (LSeries logZetaCoeff) {s | 1 < s.re} := by
  refine (LSeries_differentiableOn logZetaCoeff).continuousOn.mono fun s (hs : 1 < s.re) => ?_
  show LSeries.abscissaOfAbsConv logZetaCoeff < s.re
  refine lt_of_le_of_lt ?_ (EReal.coe_lt_coe_iff.mpr hs)
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_logZetaCoeff (by simpa using hy)

lemma norm_LSeries_logZetaCoeff_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LSeries logZetaCoeff s‖ ≤ ∑' n, ‖LSeries.term logZetaCoeff 2 n‖ := by
  have h2 : LSeriesSummable logZetaCoeff 2 := LSeriesSummable_logZetaCoeff (by norm_num)
  have hs' : LSeriesSummable logZetaCoeff s := LSeriesSummable_logZetaCoeff (by linarith)
  refine (norm_tsum_le_tsum_norm (summable_norm_iff.mpr hs')).trans ?_
  exact Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n)
    (summable_norm_iff.mpr hs') (summable_norm_iff.mpr h2)

/-- The logarithm of `(s - 1)/(s + 1)` used for normalization is bounded on `σ ≥ 2`. -/
lemma norm_log_sub_log_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖log (s - 1) - log (s + 1)‖ ≤ Real.log 3 + 2 * Real.pi := by
  refine (norm_le_abs_re_add_abs_im _).trans (add_le_add ?_ ?_)
  · rw [sub_re, log_re, log_re]
    set a := ‖s - 1‖
    set b := ‖s + 1‖
    have ha : 1 ≤ a := by
      have := re_le_norm (s - 1); rw [sub_re, one_re] at this; linarith
    have hb : 1 ≤ b := by
      have := re_le_norm (s + 1); rw [add_re, one_re] at this; linarith
    have hab : b ≤ a + 2 := by
      have := norm_add_le (s - 1) 2; rw [show s - 1 + 2 = s + 1 by ring] at this
      simpa using this
    have hba : a ≤ b + 2 := by
      have := norm_sub_le (s + 1) 2; rw [show s + 1 - 2 = s - 1 by ring] at this
      simpa using this
    have h1 : Real.log b ≤ Real.log 3 + Real.log a := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log a ≤ Real.log 3 + Real.log b := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by linarith)
    rw [abs_le]; constructor <;> linarith
  · rw [sub_im, log_im, log_im]
    have := abs_arg_le_pi (s - 1)
    have := abs_arg_le_pi (s + 1)
    rw [abs_le] at *
    constructor <;> linarith

theorem exists_log_zetaQ (hRH : RiemannHypothesis) :
    ∃ M : ℂ → ℂ, DifferentiableOn ℂ M halfPlane ∧
      (∀ s ∈ halfPlane, exp (M s) = zetaQ s) ∧
      ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ 5 → ‖M s‖ ≤ C := by
  have hne1 : ∀ s ∈ halfPlane, s + 1 ≠ 0 := by
    intro s (hs : 1 / 2 < s.re) h
    have := congrArg re h; simp at this; linarith
  have hzd : DifferentiableOn ℂ zetaQ halfPlane :=
    differentiable_riemannZeta₁.differentiableOn.div
      (differentiableOn_id.add_const 1) hne1
  have hz0 : ∀ s ∈ halfPlane, zetaQ s ≠ 0 := fun s hs =>
    div_ne_zero (riemannZeta₁_ne_zero_of_RH hRH hs) (hne1 s hs)
  have hopen : IsOpen halfPlane := isOpen_lt continuous_const continuous_re
  have hsc : IsSimplyConnected halfPlane := by
    have : ContractibleSpace halfPlane := (convex_halfSpace_re_gt (1 / 2 : ℝ)).contractibleSpace
      ⟨2, show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num⟩
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨M₀, hM₀c, hM₀e⟩ := exists_continuousOn_eqOn_exp_comp hsc hopen hzd.continuousOn
    (by rintro ⟨s, hs, h0⟩; exact hz0 s hs h0)
  have hM₀e' : ∀ s ∈ halfPlane, exp (M₀ s) = zetaQ s := fun s hs => hM₀e hs
  -- the Euler-product logarithm on `σ > 1`
  set V : Set ℂ := {s | 1 < s.re} with hV
  let G : ℂ → ℂ := fun s => log (s - 1) - log (s + 1) + LSeries logZetaCoeff s
  have hVH : V ⊆ halfPlane := fun s (hs : 1 < s.re) =>
    show 1 / 2 < s.re by linarith
  have hGc : ContinuousOn G V := by
    refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) continuousOn_LSeries_logZetaCoeff
    · exact (continuousOn_id.sub continuousOn_const).clog fun s (hs : 1 < s.re) =>
        mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    · exact (continuousOn_id.add continuousOn_const).clog fun s (hs : 1 < s.re) =>
        mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have hGe : ∀ s ∈ V, exp (M₀ s) = exp (G s) := by
    intro s (hs : 1 < s.re)
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hs2 : s + 1 ≠ 0 := hne1 s (hVH hs)
    rw [hM₀e' s (hVH hs)]
    simp only [G, exp_add, exp_sub, exp_log hs1', exp_log hs2]
    rw [show LSeries logZetaCoeff s = LSeries (fun n : ℕ ↦ (Λ n / Real.log n : ℂ)) s from rfl,
      riemannZeta_eq_exp_LSeries hs, riemannZeta_eq_inv_sub_mul hs1, zetaQ]
    field_simp
  have h2V : (2 : ℂ) ∈ V := show (1 : ℝ) < (2 : ℂ).re by norm_num
  set c := M₀ 2 - G 2 with hc
  have hconst : ∀ s ∈ V, M₀ s - G s = c := fun s hs =>
    sub_eq_sub_of_exp_eq (convex_halfSpace_re_gt (1 : ℝ)).isPreconnected
      (hM₀c.mono hVH) hGc hGe hs h2V
  have hc1 : exp c = 1 := by
    rw [hc, exp_sub, hGe 2 h2V, div_self (exp_ne_zero _)]
  refine ⟨fun s => M₀ s - c, ?_, ?_, ?_⟩
  · exact (differentiableOn_of_exp_eq hopen hzd hM₀c hM₀e').sub_const c
  · intro s hs
    simp only [exp_sub, hc1, div_one, hM₀e' s hs]
  · refine ⟨Real.log 3 + 2 * Real.pi + ∑' n, ‖LSeries.term logZetaCoeff 2 n‖, ?_⟩
    intro s hs _
    have hsV : s ∈ V := show 1 < s.re by linarith
    have : M₀ s - c = G s := by rw [← hconst s hsV]; ring
    show ‖M₀ s - c‖ ≤ _
    rw [this]
    exact (norm_add_le _ _).trans (add_le_add (norm_log_sub_log_le hs)
      (norm_LSeries_logZetaCoeff_le hs))

end Lindelof
