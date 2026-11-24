import Speiser.Band.EulerMaclaurin

/-!
# Euler–Maclaurin for `ζ` on boxes left of `Re s = 2`

`zetaEM N s = Σ_{n<N} n^{-s} + N^{-s}/2 + N^{1-s}/(s-1) + s N^{-s-1}/12 + Σ_{n≥N} r_n(s)`.
For `Re s > 1` this is `ζ(s)` (telescoping); the tail converges locally uniformly on
`Re s > -2`, so the identity theorem carries the equality to any convex open set that avoids
`1`, stays in `Re s > -2`, is bounded, and meets `Re s > 1`.
-/

open Complex Filter Topology

namespace Speiser.Band

/-- The Euler–Maclaurin tail `Σ_{n ≥ N} r_n(s)`. -/
noncomputable def tailT (N : ℕ) (s : ℂ) : ℂ := ∑' k : ℕ, emR ((N + k : ℕ) : ℝ) s

/-- The explicit main part. -/
noncomputable def mainM (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (N - 1), ((k : ℂ) + 1) ^ (-s) + (N : ℂ) ^ (-s) / 2 +
    (N : ℂ) ^ (1 - s) / (s - 1) + s * (N : ℂ) ^ (-s - 1) / 12

noncomputable def zetaEM (N : ℕ) (s : ℂ) : ℂ := mainM N s + tailT N s

lemma norm_P4_le (s : ℂ) : ‖P4 s‖ ≤ (‖s‖ + 3) ^ 4 := by
  unfold P4
  have h1 : ‖s + 1‖ ≤ ‖s‖ + 3 := by
    have := norm_add_le s 1; norm_num at this ⊢; linarith
  have h2 : ‖s + 2‖ ≤ ‖s‖ + 3 := by
    have := norm_add_le s 2; norm_num at this ⊢; linarith
  have h3 : ‖s + 3‖ ≤ ‖s‖ + 3 := by
    have := norm_add_le s 3; norm_num at this ⊢; linarith
  have h0 : ‖s‖ ≤ ‖s‖ + 3 := by linarith
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ ≤ (‖s‖ + 3) * (‖s‖ + 3) * (‖s‖ + 3) * (‖s‖ + 3) := by
        gcongr
    _ = _ := by ring

lemma natCast_add_pos (N k : ℕ) (hN : 1 ≤ N) : (0 : ℝ) < ((N + k : ℕ) : ℝ) := by
  have : (1 : ℝ) ≤ ((N + k : ℕ) : ℝ) := by exact_mod_cast le_add_right hN
  linarith

/-- Uniform bound on the tail terms for `Re s ≥ -2`. -/
lemma norm_emR_le_sq (N k : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : s ≠ 1) (hσ : -2 ≤ s.re) :
    ‖emR ((N + k : ℕ) : ℝ) s‖ ≤ (‖s‖ + 3) ^ 4 / 384 * ((N + k : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hpos := natCast_add_pos N k hN
  have h1 := norm_emR_le hpos hs (by linarith)
  have hge : (1 : ℝ) ≤ ((N + k : ℕ) : ℝ) := by exact_mod_cast le_add_right hN
  have h2 : ((N + k : ℕ) : ℝ) ^ (-s.re - 4) ≤ ((N + k : ℕ) : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hge (by linarith)
  calc ‖emR ((N + k : ℕ) : ℝ) s‖ ≤ ‖P4 s‖ * ((N + k : ℕ) : ℝ) ^ (-s.re - 4) / 384 := h1
    _ ≤ (‖s‖ + 3) ^ 4 * ((N + k : ℕ) : ℝ) ^ (-2 : ℝ) / 384 := by
        gcongr
        exact norm_P4_le s
    _ = _ := by ring

lemma summable_shift_rpow (N : ℕ) {a : ℝ} (ha : a < -1) :
    Summable fun k : ℕ => ((N + k : ℕ) : ℝ) ^ a := by
  have h := (Real.summable_nat_rpow.mpr ha)
  have := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ a) N).mpr h
  refine this.congr fun k => ?_
  simp [add_comm]

lemma summable_emR (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : s ≠ 1) (hσ : -2 ≤ s.re) :
    Summable fun k : ℕ => emR ((N + k : ℕ) : ℝ) s := by
  refine Summable.of_norm_bounded ((summable_shift_rpow N (a := -2) (by norm_num)).mul_left
    ((‖s‖ + 3) ^ 4 / 384)) fun k => norm_emR_le_sq N k hN hs hσ

/-- The finite telescoping identity. -/
lemma sum_emR (N : ℕ) (s : ℂ) (K : ℕ) :
    ∑ k ∈ Finset.range K, emR ((N + k : ℕ) : ℝ) s =
      ∑ k ∈ Finset.range K, ((N + k : ℕ) : ℂ) ^ (-s) - (N : ℂ) ^ (-s) / 2 +
        ((N + K : ℕ) : ℂ) ^ (-s) / 2 -
        ((N : ℂ) ^ (1 - s) - ((N + K : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
        (-s * ((N + K : ℕ) : ℂ) ^ (-s - 1) - (-s * (N : ℂ) ^ (-s - 1))) / 12 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have e1 : (((N + K : ℕ) : ℝ) : ℂ) = ((N + K : ℕ) : ℂ) := by push_cast; ring
    have e2 : (((N + K : ℕ) : ℝ) : ℂ) + 1 = ((N + (K + 1) : ℕ) : ℂ) := by push_cast; ring
    simp only [emR, e1]
    push_cast
    ring

lemma tendsto_cpow_zero (N : ℕ) (hN : 1 ≤ N) {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun K : ℕ => ((N + K : ℕ) : ℂ) ^ a) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ K : ℕ, ‖((N + K : ℕ) : ℂ) ^ a‖ = ((N + K : ℕ) : ℝ) ^ a.re := fun K => by
    rw [show ((N + K : ℕ) : ℂ) = (((N + K : ℕ) : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (natCast_add_pos N K hN)]
  simp_rw [hnorm]
  have h := (tendsto_rpow_neg_atTop (y := -a.re) (by linarith)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N))
  refine h.congr fun K => ?_
  simp [Function.comp, neg_neg, add_comm]

/-- **Euler–Maclaurin for `Re s > 1`.** -/
theorem riemannZeta_eq_zetaEM (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = zetaEM N s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  -- the shifted Dirichlet series
  have hsumf : Summable fun k : ℕ => ((N + k : ℕ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded (summable_shift_rpow N (a := -s.re) (by linarith))
      fun k => le_of_eq ?_
    rw [show ((N + k : ℕ) : ℂ) = (((N + k : ℕ) : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (natCast_add_pos N k hN)]
    simp
  have hT := (summable_emR N hN hs1 (by linarith)).hasSum.tendsto_sum_nat
  simp_rw [sum_emR] at hT
  have hlim : Tendsto (fun K : ℕ =>
      ∑ k ∈ Finset.range K, ((N + k : ℕ) : ℂ) ^ (-s) - (N : ℂ) ^ (-s) / 2 +
        ((N + K : ℕ) : ℂ) ^ (-s) / 2 -
        ((N : ℂ) ^ (1 - s) - ((N + K : ℕ) : ℂ) ^ (1 - s)) / (s - 1) -
        (-s * ((N + K : ℕ) : ℂ) ^ (-s - 1) - (-s * (N : ℂ) ^ (-s - 1))) / 12) atTop
      (𝓝 ((∑' k : ℕ, ((N + k : ℕ) : ℂ) ^ (-s)) - (N : ℂ) ^ (-s) / 2 + 0 / 2 -
        ((N : ℂ) ^ (1 - s) - 0) / (s - 1) - (-s * 0 - (-s * (N : ℂ) ^ (-s - 1))) / 12)) := by
    have t0 := tendsto_cpow_zero N hN (a := -s) (by simp; linarith)
    have t1 := tendsto_cpow_zero N hN (a := 1 - s) (by simp; linarith)
    have t2 := tendsto_cpow_zero N hN (a := -s - 1) (by simp; linarith)
    exact ((((hsumf.hasSum.tendsto_sum_nat.sub tendsto_const_nhds).add (t0.div_const 2)).sub
      ((tendsto_const_nhds.sub t1).div_const _)).sub
      (((t2.const_mul (-s)).sub tendsto_const_nhds).div_const 12))
  have heq := tendsto_nhds_unique hT hlim
  -- ζ as a Dirichlet series, split at `N - 1`
  have hsumz : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) 1).mpr
      (Complex.summable_one_div_nat_cpow.mpr hs)
    refine this.congr fun n => ?_
    push_cast; ring_nf
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← hsumz.sum_add_tsum_nat_add (N - 1)]
  have hshift : ∀ k : ℕ, (1 : ℂ) / ((((k + (N - 1) : ℕ) : ℂ)) + 1) ^ s =
      ((N + k : ℕ) : ℂ) ^ (-s) := fun k => by
    rw [cpow_neg, one_div]
    congr 2
    push_cast
    rw [Nat.cast_sub hN]
    ring
  simp_rw [hshift]
  have hT' : tailT N s = ∑' k : ℕ, emR ((N + k : ℕ) : ℝ) s := rfl
  unfold zetaEM mainM
  rw [hT', heq]
  have hfin : ∑ k ∈ Finset.range (N - 1), (1 : ℂ) / ((k : ℂ) + 1) ^ s =
      ∑ k ∈ Finset.range (N - 1), ((k : ℂ) + 1) ^ (-s) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cpow_neg, one_div]
  rw [hfin]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

lemma differentiableAt_const_cpow {a : ℂ} (ha : a ≠ 0) {g : ℂ → ℂ} {s : ℂ}
    (hg : DifferentiableAt ℂ g s) : DifferentiableAt ℂ (fun z => a ^ g z) s :=
  hg.const_cpow (Or.inl ha)

lemma differentiableAt_emR {n : ℝ} (hn : 0 < n) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (emR n) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    rw [show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring]; exact_mod_cast (by linarith : n + 1 ≠ 0)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold emR
  have d1 := differentiableAt_const_cpow hn0 (g := fun z => -z) (s := s) (by fun_prop)
  have d2 := differentiableAt_const_cpow hn1 (g := fun z => -z) (s := s) (by fun_prop)
  have d3 := differentiableAt_const_cpow hn0 (g := fun z => 1 - z) (s := s) (by fun_prop)
  have d4 := differentiableAt_const_cpow hn1 (g := fun z => 1 - z) (s := s) (by fun_prop)
  have d5 := differentiableAt_const_cpow hn0 (g := fun z => -z - 1) (s := s) (by fun_prop)
  have d6 := differentiableAt_const_cpow hn1 (g := fun z => -z - 1) (s := s) (by fun_prop)
  have dl : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  exact (((d1.add d2).div_const 2).sub ((d3.sub d4).div dl hs1)).sub
    ((((differentiableAt_id.neg).mul d6).sub ((differentiableAt_id.neg).mul d5)).div_const 12)

lemma differentiableAt_mainM (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (mainM N) s := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold mainM
  have hsum : DifferentiableAt ℂ
      (fun z : ℂ => ∑ k ∈ Finset.range (N - 1), ((k : ℂ) + 1) ^ (-z)) s := by
    refine DifferentiableAt.fun_sum fun k _ => differentiableAt_const_cpow ?_ (by fun_prop)
    exact_mod_cast (Nat.succ_ne_zero k)
  have d1 := differentiableAt_const_cpow hN0 (g := fun z => -z) (s := s) (by fun_prop)
  have d3 := differentiableAt_const_cpow hN0 (g := fun z => 1 - z) (s := s) (by fun_prop)
  have d5 := differentiableAt_const_cpow hN0 (g := fun z => -z - 1) (s := s) (by fun_prop)
  have dl : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  exact ((hsum.add (d1.div_const 2)).add (d3.div dl hs1)).add
    ((differentiableAt_id.mul d5).div_const 12)

/-- The tail is holomorphic on any open set avoiding `1`, inside `Re s > -2`, bounded. -/
theorem differentiableOn_tailT (N : ℕ) (hN : 1 ≤ N) {U : Set ℂ} (hUo : IsOpen U) {R : ℝ}
    (hU : ∀ s ∈ U, s ≠ 1 ∧ -2 < s.re ∧ ‖s‖ ≤ R) : DifferentiableOn ℂ (tailT N) U := by
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k : ℕ => (R + 3) ^ 4 / 384 * ((N + k : ℕ) : ℝ) ^ (-2 : ℝ))
    ((summable_shift_rpow N (a := -2) (by norm_num)).mul_left _)
    (fun k => fun w hw => (differentiableAt_emR (natCast_add_pos N k hN)
      (hU w hw).1).differentiableWithinAt) hUo fun k w hw => ?_
  refine (norm_emR_le_sq N k hN (hU w hw).1 (hU w hw).2.1.le).trans ?_
  have := (hU w hw).2.2
  gcongr

/-- **Euler–Maclaurin on a convex open set** avoiding `1`, inside `Re s > -2`, bounded, and
meeting `Re s > 1`. -/
theorem riemannZeta_eqOn_zetaEM (N : ℕ) (hN : 1 ≤ N) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : Convex ℝ U) {R : ℝ} (hU : ∀ s ∈ U, s ≠ 1 ∧ -2 < s.re ∧ ‖s‖ ≤ R) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hz₀' : 1 < z₀.re) : Set.EqOn riemannZeta (zetaEM N) U := by
  have hdT := differentiableOn_tailT N hN hUo hU
  have hdZ : DifferentiableOn ℂ (zetaEM N) U := fun w hw =>
    ((differentiableAt_mainM N hN (hU w hw).1).differentiableWithinAt).add (hdT w hw)
  have hdζ : DifferentiableOn ℂ riemannZeta U := fun w hw =>
    (differentiableAt_riemannZeta (hU w hw).1).differentiableWithinAt
  refine (hdζ.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hdZ.analyticOnNhd hUo)
    hUc.isPreconnected hz₀ ?_
  have hV : {s : ℂ | 1 < s.re} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hz₀'
  filter_upwards [hV] with w hw
  exact riemannZeta_eq_zetaEM N hN hw

end Speiser.Band
