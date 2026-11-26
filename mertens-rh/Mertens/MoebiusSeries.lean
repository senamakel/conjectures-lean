import Mertens.Statement2
import Mertens.Uniform
import Mertens.Main

/-!
# Convergence of `∑ μ(n) n^{-s}` on `Re s > 1/2` under RH (Littlewood 1912)

1. **Partial summation.** With `w_s(n) = n^{-s}` and `M(n) = ∑_{k ≤ n} μ(k)`,
   `∑_{n ≤ N} μ(n) w_s(n) = M(N) w_s(N) - ∑_{n < N} M(n) (w_s(n+1) - w_s(n))`.
   With `|M(n)| ≤ K (n+1)^β` (`1/2 < β < σ₁ ≤ Re s`, from `MertensBound`) and
   `|w_s(n+1) - w_s(n)| ≤ |s| n^{-Re s - 1}` (mean value theorem), the boundary term tends to `0`
   and the series `T(s) = -∑ M(n)(w_s(n+1) - w_s(n))` converges absolutely, uniformly on
   `{σ₁ < Re s, |s| < R}`. So the partial sums converge to `T(s)`, and `T` is holomorphic on
   `Re s > 1/2` (Weierstrass).
2. **Identification.** Let `Z(s) = (s-1)ζ(s)`, with its removable singularity at `1` filled by
   `Z(1) = 1`; `Z` is entire. On `Re s > 1`, `T(s) = L(μ, s) = 1/ζ(s)`, so `T Z = s - 1` there.
   Both sides are holomorphic on the connected half-plane `Re s > 1/2`, so `T(s) Z(s) = s - 1`
   on all of it (identity theorem). Hence `T(s) = 1/ζ(s)` for `s ≠ 1` and `T(1) = 0`.

No RH is used beyond `MertensBound`.
-/

namespace Mertens

open Filter Topology Finset Complex Asymptotics Set
open scoped ArithmeticFunction.Moebius

/-! ### Step 1: partial summation -/

/-- Abel's summation identity over a commutative ring. -/
lemma abel_identity_ring {R : Type*} [CommRing R] (c w : ℕ → R) (N : ℕ) :
    ∑ n ∈ range (N + 1), c n * w n =
      (∑ k ∈ range (N + 1), c k) * w N -
        ∑ n ∈ range N, (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun n => (∑ k ∈ range (n + 1), c k) *
      (w (n + 1) - w n)), sum_range_succ c (N + 1)]
    ring

/-- Abel summation in `ℂ`: a vanishing boundary term and a summable remainder give convergence. -/
lemma abel_tendsto_complex {c w : ℕ → ℂ}
    (hs : Summable fun n => (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n))
    (hlim : Tendsto (fun N => (∑ k ∈ range (N + 1), c k) * w N) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ n ∈ range N, c n * w n) atTop
      (𝓝 (-∑' n, (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n))) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have := hlim.sub hs.hasSum.tendsto_sum_nat
  rw [zero_sub] at this
  refine this.congr fun N => ?_
  rw [abel_identity_ring]

/-- The weight `n^{-s}`. -/
noncomputable def wt (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)

lemma norm_wt {s : ℂ} {n : ℕ} (hn : 1 ≤ n) : ‖wt s n‖ = (n : ℝ) ^ (-s.re) := by
  rw [wt, norm_natCast_cpow_of_pos (by omega), neg_re]

lemma norm_wt_sub_le {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖wt s (n + 1) - wt s n‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : ∀ u ∈ Icc (n : ℝ) (n + 1),
      HasDerivWithinAt f (-s * (u : ℂ) ^ (-s - 1)) (Icc (n : ℝ) (n + 1)) u := by
    intro u hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have h := hasDerivAt_ofReal_cpow_const (r := -s) hu0 (neg_ne_zero.2 hs0)
    exact h.hasDerivWithinAt
  have hb : ∀ u ∈ Ico (n : ℝ) (n + 1), ‖-s * (u : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu0]
    gcongr
    simp only [sub_re, neg_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos hN0 hu.1 (by linarith)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb ((n : ℝ) + 1) ⟨by linarith, le_rfl⟩
  simp only [f, add_sub_cancel_left, mul_one] at this
  rw [wt, wt]
  push_cast at this ⊢
  exact this

lemma wt_zero {s : ℂ} (hs : s ≠ 0) : wt s 0 = 0 := by
  simp [wt, zero_cpow (neg_ne_zero.2 hs)]

/-- The Abel remainder term `M(n) (w_s(n+1) - w_s(n))`. -/
noncomputable def abelTerm (s : ℂ) (n : ℕ) : ℂ :=
  (∑ k ∈ range (n + 1), (μ k : ℂ)) * (wt s (n + 1) - wt s n)

/-- The limit function `T(s) = -∑ M(n)(w_s(n+1) - w_s(n))`. -/
noncomputable def moebiusT (s : ℂ) : ℂ := -∑' n, abelTerm s n

lemma sum_moebius_complex (n : ℕ) : ∑ k ∈ range (n + 1), (μ k : ℂ) = ((mertens n : ℤ) : ℂ) := by
  rw [← sum_range_succ_moebius_int]; push_cast; rfl

/-- The uniform estimate behind step 1. -/
lemma abelTerm_bound (hMB : MertensBound) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) :
    ∃ K β : ℝ, 0 ≤ K ∧ β < σ₁ ∧ 0 ≤ β ∧
      (∀ n : ℕ, |(mertens n : ℝ)| ≤ K * ((n : ℝ) + 1) ^ β) ∧
      ∀ R : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → ‖s‖ ≤ R → ∀ n : ℕ,
        ‖abelTerm s n‖ ≤ 2 ^ β * K * R * (n : ℝ) ^ (β - σ₁ - 1) := by
  set β := (1 / 2 + σ₁) / 2 with hβ
  obtain ⟨K, hK0, hK⟩ := abs_mertens_le_of_mertensBound hMB (β := β) (by rw [hβ]; linarith)
  refine ⟨K, β, hK0, by rw [hβ]; linarith, by rw [hβ]; linarith, hK, fun R s hs hR n => ?_⟩
  have hsre : 0 < s.re := by linarith
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [abelTerm]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abelTerm, norm_mul, sum_moebius_complex, Complex.norm_intCast]
  have hM : |(mertens n : ℝ)| ≤ 2 ^ β * K * (n : ℝ) ^ β := by
    calc |(mertens n : ℝ)| ≤ K * ((n : ℝ) + 1) ^ β := hK n
      _ ≤ K * (2 * (n : ℝ)) ^ β := by gcongr; linarith
      _ = 2 ^ β * K * (n : ℝ) ^ β := by rw [Real.mul_rpow (by norm_num) hn0.le]; ring
  have hW : ‖wt s (n + 1) - wt s n‖ ≤ R * (n : ℝ) ^ (-σ₁ - 1) := by
    calc ‖wt s (n + 1) - wt s n‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := norm_wt_sub_le hsre hn
      _ ≤ R * (n : ℝ) ^ (-σ₁ - 1) :=
          mul_le_mul hR (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by positivity) hR0
  calc |(mertens n : ℝ)| * ‖wt s (n + 1) - wt s n‖
      ≤ (2 ^ β * K * (n : ℝ) ^ β) * (R * (n : ℝ) ^ (-σ₁ - 1)) := by
        gcongr
    _ = 2 ^ β * K * R * ((n : ℝ) ^ β * (n : ℝ) ^ (-σ₁ - 1)) := by ring
    _ = 2 ^ β * K * R * (n : ℝ) ^ (β - σ₁ - 1) := by
        rw [← Real.rpow_add hn0]; ring_nf

lemma summable_rpow_aux {β σ₁ : ℝ} (h : β < σ₁) :
    Summable fun n : ℕ => (n : ℝ) ^ (β - σ₁ - 1) :=
  Real.summable_nat_rpow.2 (by linarith)

/-- **Step 1**: for `Re s > 1/2` the partial sums of `∑ μ(n) n^{-s}` converge to `T(s)`. -/
theorem tendsto_moebiusPartial (hMB : MertensBound) {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (moebiusPartial s) atTop (𝓝 (moebiusT s)) := by
  set σ₁ := s.re
  obtain ⟨K, β, hK0, hβ, hβ0, hK, hT⟩ := abelTerm_bound hMB hs
  have hs0 : s ≠ 0 := by rintro rfl; simp [σ₁] at hs; linarith
  have hsum : Summable (abelTerm s) :=
    Summable.of_norm_bounded ((summable_rpow_aux hβ).mul_left (2 ^ β * K * ‖s‖))
      fun n => hT ‖s‖ s le_rfl le_rfl n
  have hlim : Tendsto (fun N => (∑ k ∈ range (N + 1), (μ k : ℂ)) * wt s N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 2 ^ β * K * (N : ℝ) ^ (β - σ₁)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := σ₁ - β) (by linarith)).comp
        tendsto_natCast_atTop_atTop
      have := this.const_mul (2 ^ β * K)
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      simp only [Function.comp, neg_sub]
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [norm_mul, sum_moebius_complex, Complex.norm_intCast, norm_wt hN]
    have hM : |(mertens N : ℝ)| ≤ 2 ^ β * K * (N : ℝ) ^ β := by
      calc |(mertens N : ℝ)| ≤ K * ((N : ℝ) + 1) ^ β := hK N
        _ ≤ K * (2 * (N : ℝ)) ^ β := by
            gcongr; linarith [(by exact_mod_cast hN : (1 : ℝ) ≤ N)]
        _ = 2 ^ β * K * (N : ℝ) ^ β := by rw [Real.mul_rpow (by norm_num) hN0.le]; ring
    calc |(mertens N : ℝ)| * (N : ℝ) ^ (-σ₁) ≤ 2 ^ β * K * (N : ℝ) ^ β * (N : ℝ) ^ (-σ₁) := by
          gcongr
      _ = 2 ^ β * K * (N : ℝ) ^ (β - σ₁) := by
          rw [mul_assoc, ← Real.rpow_add hN0]; ring_nf
  have := abel_tendsto_complex hsum hlim
  refine this.congr fun N => ?_
  rw [moebiusPartial]
  refine sum_congr rfl fun n _ => ?_
  rw [wt, cpow_neg, div_eq_mul_inv]

/-- **Step 1**, holomorphy: `T` is holomorphic on `Re s > 1/2`. -/
theorem differentiableOn_moebiusT (hMB : MertensBound) :
    DifferentiableOn ℂ moebiusT {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ hs₀
  simp only [mem_ofPred_eq] at hs₀
  set σ₁ := (1 / 2 + s₀.re) / 2
  set R := ‖s₀‖ + 1
  set U : Set ℂ := {s : ℂ | σ₁ < s.re} ∩ Metric.ball 0 R
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := ⟨by simp only [mem_ofPred_eq, σ₁]; linarith,
    by simp [R]⟩
  obtain ⟨K, β, hK0, hβ, -, -, hT⟩ := abelTerm_bound hMB (σ₁ := σ₁) (by simp only [σ₁]; linarith)
  have hdiff : DifferentiableOn ℂ (fun s => ∑' n, abelTerm s n) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_rpow_aux hβ).mul_left (2 ^ β * K * R)) (fun n s hs => ?_) hUo
      (fun n s hs => hT R s hs.1.le (by simpa using (mem_ball_zero_iff.1 hs.2).le) n)
    have hs0 : s ≠ 0 := by
      rintro rfl
      have := hs.1
      simp only [mem_ofPred_eq, zero_re, σ₁] at this
      linarith
    have hd : ∀ m : ℕ, DifferentiableAt ℂ (fun s : ℂ => wt s m) s := fun m =>
      (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.2 hs0))
    exact (((hd (n + 1)).sub (hd n)).const_mul _).differentiableWithinAt
  exact ((hdiff.neg.differentiableAt (hUo.mem_nhds hs₀U))).differentiableWithinAt

/-! ### Step 2: identification with `1/ζ` -/

/-- `(s - 1) ζ(s)`, with the value `1` at `s = 1`. -/
noncomputable def zetaZ (s : ℂ) : ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1 s

lemma zetaZ_of_ne {s : ℂ} (hs : s ≠ 1) : zetaZ s = (s - 1) * riemannZeta s := by
  simp [zetaZ, Function.update_of_ne hs]

lemma differentiable_zetaZ : Differentiable ℂ zetaZ := by
  have hd : DifferentiableOn ℂ zetaZ (univ \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    refine (DifferentiableAt.congr_of_eventuallyEq (f := fun s => (s - 1) * riemannZeta s)
      ?_ ?_).differentiableWithinAt
    · exact (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)
    · filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
      exact zetaZ_of_ne hz
  have hc : ContinuousAt zetaZ 1 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    have : zetaZ 1 = 1 := by simp [zetaZ]
    rw [this]
    refine riemannZeta_residue_one.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (zetaZ_of_ne hz).symm
  have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (s := univ) (c := 1) Filter.univ_mem).1 ⟨hd, hc⟩
  exact fun s => (this s (mem_univ s)).differentiableAt Filter.univ_mem

/-- On `Re s > 1`, `T(s) = 1/ζ(s)`. -/
lemma moebiusT_eq_of_one_lt (hMB : MertensBound) {s : ℂ} (hs : 1 < s.re) :
    moebiusT s * riemannZeta s = 1 := by
  have hT := tendsto_moebiusPartial hMB (s := s) (by linarith)
  have hsum : LSeriesSummable (fun n => (μ n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.2 hs
  have hL : Tendsto (moebiusPartial s) atTop (𝓝 (LSeries (fun n => (μ n : ℂ)) s)) := by
    have := hsum.hasSum.tendsto_sum_nat
    refine this.congr fun N => ?_
    rw [moebiusPartial]
    refine sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne']
  rw [tendsto_nhds_unique hT hL, mul_comm, ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs

/-- **Step 2**: `T(s) Z(s) = s - 1` on `Re s > 1/2`. -/
theorem moebiusT_mul_zetaZ (hMB : MertensBound) {s : ℂ} (hs : 1 / 2 < s.re) :
    moebiusT s * zetaZ s = s - 1 := by
  set V : Set ℂ := {s : ℂ | 1 / 2 < s.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ (fun s => moebiusT s * zetaZ s) V :=
    ((differentiableOn_moebiusT hMB).mul differentiable_zetaZ.differentiableOn).analyticOnNhd hVo
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) V :=
    (differentiable_id.sub_const 1).differentiableOn.analyticOnNhd hVo
  have h2 : (2 : ℂ) ∈ V := by simp [V]; norm_num
  have heq : (fun s => moebiusT s * zetaZ s) =ᶠ[𝓝 2] fun s => s - 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with z hz
    change 1 < z.re at hz
    have hz1 : z ≠ 1 := by rintro rfl; simp at hz
    rw [zetaZ_of_ne hz1, ← mul_assoc, mul_comm (moebiusT z), mul_assoc,
      moebiusT_eq_of_one_lt hMB hz, mul_one]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt _).isPreconnected
    h2 heq hs

/-- **Littlewood (1912), from the Mertens bound**: `M(x) = O(x^{1/2+ε})` implies that
`∑ μ(n) n^{-s}` converges to `1/ζ(s)` on `Re s > 1/2` (and to `0` at `s = 1`). -/
theorem moebiusSeries_of_mertensBound (hMB : MertensBound) : MoebiusSeriesConverges := by
  refine ⟨fun s hs hs1 => ?_, ?_⟩
  · have h := moebiusT_mul_zetaZ hMB hs
    rw [zetaZ_of_ne hs1] at h
    have hsub : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    have hT : moebiusT s = (riemannZeta s)⁻¹ := by
      have hz : riemannZeta s ≠ 0 := by
        intro hz; rw [hz, mul_zero, mul_zero] at h; exact hsub h.symm
      field_simp
      calc moebiusT s * riemannZeta s = (moebiusT s * ((s - 1) * riemannZeta s)) / (s - 1) := by
            field_simp
        _ = 1 := by rw [h, div_self hsub]
    rw [← hT]
    exact tendsto_moebiusPartial hMB hs
  · have h := moebiusT_mul_zetaZ hMB (s := 1) (by simp; norm_num)
    have hZ : zetaZ 1 = 1 := by simp [zetaZ]
    rw [hZ, mul_one, sub_self] at h
    rw [← h]
    exact tendsto_moebiusPartial hMB (by simp; norm_num)

/-- **Littlewood (1912)**: under RH, `∑ μ(n) n^{-s}` converges to `1/ζ(s)` for every
`Re s > 1/2`. -/
theorem moebiusSeries_of_RH (hRH : RiemannHypothesis) : MoebiusSeriesConverges :=
  moebiusSeries_of_mertensBound (mertens_of_RH hRH)

end Mertens
