import Erdos969.MV.Perron
import Erdos969.Series

/-!
# Uniform bounds under RH: the twisted Mertens function and the tail of `1/ζ`

* `norm_invZ_le_right`: `‖1/ζ(s)‖ ≤ C (|t|+2)^ε` on all of `σ ≥ 1/2 + δ`.
* `norm_zeta_le_strip`, `norm_zeta_le_line`: `‖ζ(s)‖ ≤ C (|t|+2)^ε` on `1/2 + δ ≤ σ ≤ 2`,
  `|t| ≥ 1`, and on a whole vertical line `σ = σ₀ ∈ (1/2, 1)`. Both come from lindelof-rh's
  logarithm of `ζ` (Borel–Carathéodory and three lines), as mertens-rh's `norm_invZ_le` does.
* `twisted_mertens`: `‖∑_{n ≤ N} μ(n) n^{-it}‖ ≤ K (|t|+2)^ε (N+1)^{1/2+3ε}`, uniformly in `t`.
  This is the Cesàro–Perron bound (`Erdos969.MV.norm_sum_Icc_le`) with `Φ(s) = 1/ζ(s + it)`.
* `tail_le`: for `σ > max(1, 1/2+3ε)`,
  `‖1/ζ(σ+it) − ∑_{d ≤ Y} μ(d) d^{-σ-it}‖ ≤ K (1 + σ/(σ−β)) (|t|+2)^ε Y^{β−σ}`, `β = 1/2+3ε`,
  by partial summation against the real weights `d^{-σ}`. Only `|t|^ε` is lost: partial
  summation against `d^{-σ-it}` straight from `M(x) ≪ x^{1/2+ε}` would lose a factor `|t|`.
-/

namespace Erdos969.MV

open Complex Filter Finset Lindelof
open scoped ArithmeticFunction.Moebius

lemma rpow_abs_add_le {t τ ε : ℝ} (hε : 0 ≤ ε) :
    (|τ + t| + 2) ^ ε ≤ (|t| + 2) ^ ε * (|τ| + 2) ^ ε := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ hε
  have := abs_add_le τ t
  nlinarith [abs_nonneg t, abs_nonneg τ]

/-- `‖1/ζ‖ ≪ (|t|+2)^ε` on the whole half-plane `σ ≥ 1/2 + δ`. -/
theorem norm_invZ_le_right (hRH : RiemannHypothesis) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδ' : δ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → ‖Mertens.invZ s‖ ≤ C * (|s.im| + 2) ^ ε := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Mertens.norm_invZ_le hRH hε hδ hδ'
  obtain ⟨C₂, hC₂⟩ := Mertens.norm_inv_zeta_le_of_two_le
  refine ⟨C₁ + |C₂|, by positivity, fun s hs => ?_⟩
  have hp : 1 ≤ (|s.im| + 2) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hε.le
  rcases le_or_gt s.re 2 with h2 | h2
  · calc ‖Mertens.invZ s‖ ≤ C₁ * (|s.im| + 2) ^ ε := hC₁ s hs h2
      _ ≤ (C₁ + |C₂|) * (|s.im| + 2) ^ ε :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C₂]) (by positivity)
  · have hs1 : s ≠ 1 := by rintro rfl; simp at h2
    rw [Mertens.invZ_eq hs1]
    calc ‖(riemannZeta s)⁻¹‖ ≤ C₂ := hC₂ s h2.le
      _ ≤ |C₂| := le_abs_self _
      _ ≤ |C₂| * (|s.im| + 2) ^ ε := le_mul_of_one_le_right (abs_nonneg _) hp
      _ ≤ (C₁ + |C₂|) * (|s.im| + 2) ^ ε := by gcongr; linarith

/-- Under RH, `‖ζ(s)‖ ≤ C (|t|+2)^ε` on `1/2 + δ ≤ σ ≤ 2`, `|t| ≥ 1`. -/
theorem norm_zeta_le_strip (hRH : RiemannHypothesis) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδ' : δ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 2) ^ ε := by
  obtain ⟨M, hMd, hexp, C₀, hC₀⟩ := exists_log_zetaQ hRH
  obtain ⟨C₂, hC₂⟩ := norm_log_zetaQ_le hRH hMd hexp ⟨C₀, hC₀⟩ (δ / 2) (by positivity)
  set a : ℝ := 1 / 2 + δ / 2 with ha
  have hab : a < 2 := by linarith
  have hsub : {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} ⊆ halfPlane := fun s hs => by
    show 1 / 2 < s.re
    linarith [hs.1]
  obtain ⟨C₃, hC₃⟩ := norm_le_log_rpow_of_strip (B := C₀) hab (hMd.mono hsub)
    (fun s h1 h2 => hC₂ s h1 h2) (fun s h => hC₀ s (by linarith) (by linarith))
  set α : ℝ := (3 / 2 - δ) / (2 - a) with hα
  have h2a : 0 < 2 - a := by linarith
  have hα1 : α < 1 := by rw [hα, div_lt_one h2a]; linarith
  have hα0 : 0 ≤ α := div_nonneg (by linarith) h2a.le
  obtain ⟨K, hK0, hK⟩ := Mertens.exists_log_rpow_le (C := |C₃|) hα1 hα0 hε
  refine ⟨3 * Real.exp (|C₃| + K), by positivity, fun s h1 h2 him => ?_⟩
  have hs : (s.re : ℂ) + s.im * I = s := re_add_im s
  have hM := hC₃ s.re s.im (by linarith) h2
  rw [hs] at hM
  set L := Real.log (|s.im| + 2) with hLdef
  have hL0 : 0 < L := Real.log_pos (by linarith [abs_nonneg s.im])
  have hβ0 : 0 ≤ (2 - s.re) / (2 - a) := div_nonneg (by linarith) h2a.le
  have hβα : (2 - s.re) / (2 - a) ≤ α := div_le_div_of_nonneg_right (by linarith) h2a.le
  have hβ := Mertens.rpow_le_one_add_rpow hL0 hβ0 hβα
  have hMb : ‖M s‖ ≤ |C₃| + ε * L + K := by
    have e1 : C₃ * L ^ ((2 - s.re) / (2 - a)) ≤ |C₃| * (1 + L ^ α) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C₃) (Real.rpow_nonneg hL0.le _)).trans
        (mul_le_mul_of_nonneg_left hβ (abs_nonneg _))
    have e2 := hK s.im
    rw [← hLdef] at e2
    nlinarith
  have hsH : s ∈ halfPlane := show 1 / 2 < s.re by linarith
  calc ‖riemannZeta s‖ ≤ 3 * Real.exp ‖M s‖ := norm_riemannZeta_le_exp hexp hsH him
    _ ≤ 3 * Real.exp (|C₃| + K + ε * L) := by gcongr; linarith
    _ = 3 * Real.exp (|C₃| + K) * (|s.im| + 2) ^ ε := by
      rw [Real.exp_add, Real.rpow_def_of_pos (by linarith [abs_nonneg s.im]), hLdef, mul_comm ε]
      ring

/-- Under RH, `‖ζ(σ₀ + it)‖ ≤ C (|t|+2)^ε` for every `t`, when `1/2 < σ₀ < 1`. -/
theorem norm_zeta_le_line (hRH : RiemannHypothesis) {ε σ₀ : ℝ} (hε : 0 < ε) (h1 : 1 / 2 < σ₀)
    (h2 : σ₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖riemannZeta ((σ₀ : ℂ) + t * I)‖ ≤ C * (|t| + 2) ^ ε := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_zeta_le_strip hRH hε (δ := σ₀ - 1 / 2) (by linarith)
    (by linarith)
  have hne : ∀ t : ℝ, (σ₀ : ℂ) + t * I ≠ 1 := fun t h => by
    have := congrArg re h; simp at this; linarith
  have hcont : ContinuousOn (fun t : ℝ => riemannZeta ((σ₀ : ℂ) + t * I)) (Set.Icc (-1) 1) :=
    fun t _ => ((differentiableAt_riemannZeta (hne t)).continuousAt.comp
      (f := fun t : ℝ => (σ₀ : ℂ) + t * I)
      (Mertens.continuous_line σ₀).continuousAt).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨C₁ + |C₂|, by positivity, fun t => ?_⟩
  have hp : 1 ≤ (|t| + 2) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg t]) hε.le
  rcases le_or_gt 1 |t| with ht | ht
  · have := hC₁ ((σ₀ : ℂ) + t * I) (by simp) (by simp; linarith) (by simpa using ht)
    simp only [Mertens.line_im] at this
    calc _ ≤ C₁ * (|t| + 2) ^ ε := this
      _ ≤ (C₁ + |C₂|) * (|t| + 2) ^ ε := by gcongr; linarith [abs_nonneg C₂]
  · have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    calc _ ≤ C₂ := hC₂ t hmem
      _ ≤ |C₂| := le_abs_self _
      _ ≤ |C₂| * (|t| + 2) ^ ε := le_mul_of_one_le_right (abs_nonneg _) hp
      _ ≤ (C₁ + |C₂|) * (|t| + 2) ^ ε := by gcongr; linarith

lemma norm_natCast_cpow_neg_I (n : ℕ) (t : ℝ) (hn : n ≠ 0) :
    ‖(n : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := by
  rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma norm_twist_le (n : ℕ) (t : ℝ) : ‖(μ n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I))‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [norm_mul, norm_natCast_cpow_neg_I n t hn.ne', mul_one, Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one

lemma summable_div_cube {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) :
    Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (3 : ℝ) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 3))
  exact div_le_div_of_nonneg_right (ha n) (by positivity)

lemma LSeries_twist (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I))) s = Mertens.invZ (s + t * I) := by
  have hs' : 1 < (s + t * I).re := by simpa using hs
  rw [← Mertens.LSeries_moebius_eq_invZ hs']
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', cpow_add _ _ hn0,
      cpow_neg]
    field_simp

/-- **Twisted Littlewood bound**: under RH, uniformly in `t`,
`‖∑_{n ≤ N} μ(n) n^{-it}‖ ≤ K (|t|+2)^ε (N+1)^{1/2+3ε}`. -/
theorem twisted_mertens (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (N : ℕ), 1 ≤ N →
      ‖∑ n ∈ Icc 1 N, (μ n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I))‖ ≤
        K * (|t| + 2) ^ ε * ((N : ℝ) + 1) ^ (1 / 2 + 3 * ε) := by
  set σ₀ : ℝ := 1 / 2 + ε with hσ₀
  obtain ⟨K₀, hK₀, hK⟩ := norm_sum_Icc_le hε (by linarith) (σ₀ := σ₀) (by linarith) (by linarith)
  obtain ⟨Cε, hCε0, hCε⟩ := norm_invZ_le_right hRH hε (δ := ε) hε (by linarith)
  obtain ⟨Ch, hCh0, hCh⟩ := norm_invZ_le_right hRH (ε := 1 / 2) (by norm_num) (δ := ε) hε
    (by linarith)
  refine ⟨K₀ * Cε, by positivity, fun t N hN => ?_⟩
  set a : ℕ → ℂ := fun n => (μ n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) with ha
  set Φ : ℂ → ℂ := fun s => Mertens.invZ (s + t * I) with hΦ
  have hsh : ∀ s : ℂ, (s + t * I).re = s.re := fun s => by simp
  have hsi : ∀ s : ℂ, (s + t * I).im = s.im + t := fun s => by simp
  have hd : DifferentiableOn ℂ Φ (strip σ₀) := by
    have h := Mertens.differentiableOn_invZ hRH
    refine h.comp (by fun_prop) fun s hs => ?_
    show 1 / 2 < (s + t * I).re
    rw [hsh]; have := hs.1; linarith
  have hL : ∀ τ : ℝ, Φ ((3 : ℝ) + τ * I) = LSeries a ((3 : ℝ) + τ * I) := fun τ =>
    (LSeries_twist t (by simp)).symm
  have hgen : ∀ (e C : ℝ), 0 ≤ e → (∀ s : ℂ, 1 / 2 + ε ≤ s.re →
      ‖Mertens.invZ s‖ ≤ C * (|s.im| + 2) ^ e) → 0 ≤ C → ∀ s : ℂ, σ₀ ≤ s.re →
      ‖Φ s‖ ≤ C * (|t| + 2) ^ e * (|s.im| + 2) ^ e := fun e C he hC hC0 s hs => by
    have := hC (s + t * I) (by rw [hsh]; exact hs)
    rw [hsi] at this
    calc ‖Φ s‖ ≤ C * (|s.im + t| + 2) ^ e := this
      _ ≤ C * ((|t| + 2) ^ e * (|s.im| + 2) ^ e) := by gcongr; exact rpow_abs_add_le he
      _ = _ := by ring
  obtain ⟨C₂, hC₂⟩ := Mertens.norm_inv_zeta_le_of_two_le
  have hB : ∀ τ : ℝ, ‖Φ ((3 : ℝ) + τ * I)‖ ≤ C₂ := by
    intro τ
    have hre : (((3 : ℝ) : ℂ) + τ * I + t * I).re = 3 := by simp
    have hne : ((3 : ℝ) : ℂ) + τ * I + t * I ≠ 1 := fun h => by
      have := congrArg re h; rw [hre] at this; simp at this
    simp only [hΦ]
    rw [Mertens.invZ_eq hne]
    exact hC₂ _ (by rw [hre]; norm_num)
  have hD : ∀ s ∈ strip σ₀, 1 ≤ |s.im| →
      ‖Φ s‖ ≤ Ch * (|t| + 2) ^ (1 / 2 : ℝ) * (|s.im| + 2) ^ (3 / 2 : ℝ) := by
    intro s hs _
    refine (hgen (1 / 2) Ch (by norm_num) hCh hCh0.le s hs.1).trans ?_
    gcongr
    · linarith [abs_nonneg s.im]
    · norm_num
  have hA : ∀ τ : ℝ, ‖Φ ((σ₀ : ℂ) + τ * I)‖ ≤ (Cε * (|t| + 2) ^ ε) * (|τ| + 2) ^ ε := by
    intro τ
    have := hgen ε Cε hε.le hCε hCε0.le ((σ₀ : ℂ) + τ * I) (by simp)
    simpa using this
  have hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (3 : ℝ) :=
    summable_div_cube fun n => norm_twist_le n t
  have := hK a Φ _ _ _ hsum hd hL hB hD hA N hN
  calc _ ≤ K₀ * (Cε * (|t| + 2) ^ ε) * ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) := this
    _ = K₀ * Cε * (|t| + 2) ^ ε * ((N : ℝ) + 1) ^ (1 / 2 + 3 * ε) := by
      rw [hσ₀, show 1 / 2 + ε + 2 * ε = 1 / 2 + 3 * ε by ring]; ring

/-- Summation by parts, in any commutative ring. -/
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

/-- `|(u+1)^{-σ} - u^{-σ}| ≤ σ u^{-σ-1}` for `u > 0`, `σ > 0`. -/
lemma abs_rpow_neg_succ_sub_le {u σ : ℝ} (hu : 0 < u) (hσ : 0 < σ) :
    |(u + 1) ^ (-σ) - u ^ (-σ)| ≤ σ * u ^ (-σ - 1) := by
  have hf : ∀ x ∈ Set.Icc u (u + 1), HasDerivWithinAt (fun x : ℝ => x ^ (-σ))
      (-σ * x ^ (-σ - 1)) (Set.Icc u (u + 1)) x := fun x hx =>
    (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : x ≠ 0))).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico u (u + 1), ‖-σ * x ^ (-σ - 1)‖ ≤ σ * u ^ (-σ - 1) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [norm_mul, norm_neg, Real.norm_of_nonneg hσ.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu hx.1 (by linarith)) hσ.le
  have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb (u + 1) ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hf : f 0 = 0) (n : ℕ) :
    ∑ d ∈ Icc 1 n, f d = ∑ d ∈ range (n + 1), f d := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), hf, zero_add]
  rfl

lemma moebius_mul_cpow_eq_term {σ t : ℝ} (d : ℕ) :
    (μ d : ℂ) * (d : ℂ) ^ (-((σ : ℂ) + t * I)) =
      LSeries.term (fun n => (μ n : ℂ)) ((σ : ℂ) + t * I) d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [LSeries.term_of_ne_zero hd.ne', cpow_neg, div_eq_mul_inv]

/-- **The tail of `1/ζ` under RH**: for `σ > 1`, `σ > β = 1/2 + 3ε`,
`‖1/ζ(σ+it) − ∑_{d ≤ Y} μ(d) d^{-σ-it}‖ ≤ K (1 + σ/(σ−β)) (|t|+2)^ε Y^{β−σ}`. -/
theorem tail_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) :
    ∃ K : ℝ, 0 < K ∧ ∀ (σ t : ℝ), 1 < σ → 1 / 2 + 3 * ε < σ → ∀ Y : ℕ, 1 ≤ Y →
      ‖Mertens.invZ ((σ : ℂ) + t * I) -
          ∑ d ∈ Icc 1 Y, (μ d : ℂ) * (d : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤
        K * (1 + σ / (σ - (1 / 2 + 3 * ε))) * (|t| + 2) ^ ε * (Y : ℝ) ^ (1 / 2 + 3 * ε - σ) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := twisted_mertens hRH hε (by linarith)
  refine ⟨4 * K₁, by positivity, fun σ t hσ1 hσβ Y hY => ?_⟩
  set β : ℝ := 1 / 2 + 3 * ε with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβ1 : β ≤ 1 := by rw [hβ]; linarith
  have hσ0 : 0 < σ := by linarith
  have hσβ' : 0 < σ - β := by linarith
  set w : ℂ := (σ : ℂ) + t * I with hw
  have hwre : 1 < w.re := by simp [hw]; exact hσ1
  set K₂ : ℝ := K₁ * (|t| + 2) ^ ε with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  set f : ℕ → ℂ := fun n => (μ n : ℂ) * (n : ℂ) ^ (-((t : ℂ) * I)) with hf
  have hf0 : f 0 = 0 := by simp [hf]
  set S : ℕ → ℂ := fun n => ∑ d ∈ range (n + 1), f d with hS
  have hSb : ∀ n : ℕ, ‖S n‖ ≤ K₂ * ((n : ℝ) + 1) ^ β := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hS, hf0]; positivity
    · have := hK₁ t n hn
      rw [sum_Icc_eq_sum_range f hf0] at this
      simpa [hS, hK₂, mul_assoc] using this
  set c : ℕ → ℂ := fun j => f (Y + 1 + j) with hc
  set wt : ℕ → ℂ := fun j => ((((Y + 1 + j : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) with hwt
  have hu : ∀ n : ℕ, (1 : ℝ) ≤ (Y : ℝ) + n + 1 := fun n => by
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hP : ∀ n, ∑ j ∈ range (n + 1), c j = S (Y + n + 1) - S Y := by
    intro n
    simp only [hS, hc]
    have : Y + n + 1 + 1 = (Y + 1) + (n + 1) := by omega
    rw [this, sum_range_add f (Y + 1) (n + 1)]; ring
  have hPb : ∀ n, ‖∑ j ∈ range (n + 1), c j‖ ≤ 4 * K₂ * ((Y : ℝ) + n + 1) ^ β := by
    intro n
    rw [hP n]
    have h1 := hSb (Y + n + 1)
    have h2 := hSb Y
    push_cast at h1
    have hmono : ((Y : ℝ) + 1) ^ β ≤ ((Y : ℝ) + n + 1 + 1) ^ β :=
      Real.rpow_le_rpow (by positivity) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hβ0
    have h2β : ((Y : ℝ) + n + 1 + 1) ^ β ≤ 2 * ((Y : ℝ) + n + 1) ^ β := by
      have := rpow_add_two_le (u := (Y : ℝ) + n) (by positivity) hβ0 hβ1
      calc ((Y : ℝ) + n + 1 + 1) ^ β = ((Y : ℝ) + n + 2) ^ β := by ring_nf
        _ ≤ 2 * (1 + ((Y : ℝ) + n)) ^ β := this
        _ = 2 * ((Y : ℝ) + n + 1) ^ β := by ring_nf
    calc ‖S (Y + n + 1) - S Y‖ ≤ ‖S (Y + n + 1)‖ + ‖S Y‖ := norm_sub_le _ _
      _ ≤ K₂ * ((Y : ℝ) + n + 1 + 1) ^ β + K₂ * ((Y : ℝ) + 1) ^ β := add_le_add h1 h2
      _ ≤ K₂ * ((Y : ℝ) + n + 1 + 1) ^ β + K₂ * ((Y : ℝ) + n + 1 + 1) ^ β := by gcongr
      _ ≤ 4 * K₂ * ((Y : ℝ) + n + 1) ^ β := by nlinarith
  have hwt0 : ∀ n : ℕ, wt n = ((((Y : ℝ) + n + 1) ^ (-σ) : ℝ) : ℂ) := fun n => by
    simp only [hwt]; push_cast; ring_nf
  have hcw : ∀ j, c j * wt j = LSeries.term (fun n => (μ n : ℂ)) w (Y + 1 + j) := by
    intro j
    rw [← moebius_mul_cpow_eq_term]
    have hd : (0 : ℝ) < ((Y + 1 + j : ℕ) : ℝ) := by positivity
    have hd0 : ((Y + 1 + j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [hc, hf, hwt]
    rw [Complex.ofReal_cpow hd.le, neg_add, cpow_add _ _ hd0]
    push_cast
    ring
  have hpart : ∀ N : ℕ, ‖∑ j ∈ range (N + 1), LSeries.term (fun n => (μ n : ℂ)) w (Y + 1 + j)‖ ≤
      4 * K₂ * (1 + σ / (σ - β)) * (Y : ℝ) ^ (β - σ) := by
    intro N
    rw [show ∑ j ∈ range (N + 1), LSeries.term (fun n => (μ n : ℂ)) w (Y + 1 + j) =
      ∑ j ∈ range (N + 1), c j * wt j from sum_congr rfl fun j _ => (hcw j).symm,
      abel_identity_ring]
    have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
    have hfirst : ‖(∑ j ∈ range (N + 1), c j) * wt N‖ ≤ 4 * K₂ * (Y : ℝ) ^ (β - σ) := by
      have hpos : 0 < (Y : ℝ) + N + 1 := by linarith [hu N]
      rw [norm_mul, hwt0 N, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖∑ j ∈ range (N + 1), c j‖ * ((Y : ℝ) + N + 1) ^ (-σ)
          ≤ (4 * K₂ * ((Y : ℝ) + N + 1) ^ β) * ((Y : ℝ) + N + 1) ^ (-σ) :=
            mul_le_mul_of_nonneg_right (hPb N) (by positivity)
        _ = 4 * K₂ * ((Y : ℝ) + N + 1) ^ (β - σ) := by
            rw [mul_assoc, ← Real.rpow_add hpos, ← sub_eq_add_neg]
        _ ≤ 4 * K₂ * (Y : ℝ) ^ (β - σ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hY'
              (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]) (by linarith)) (by positivity)
    have hterm : ∀ n : ℕ, ‖(∑ j ∈ range (n + 1), c j) * (wt (n + 1) - wt n)‖ ≤
        4 * K₂ * σ * ((Y : ℝ) + n + 1) ^ (-(σ + 1 - β)) := by
      intro n
      have hpos : 0 < (Y : ℝ) + n + 1 := by linarith [hu n]
      have hw1 : wt (n + 1) = (((((Y : ℝ) + n + 1) + 1) ^ (-σ) : ℝ) : ℂ) := by
        simp only [hwt]; push_cast; ring_nf
      rw [norm_mul, hw1, hwt0 n, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hd := abs_rpow_neg_succ_sub_le hpos hσ0
      calc ‖∑ j ∈ range (n + 1), c j‖ * |(((Y : ℝ) + n + 1) + 1) ^ (-σ) - ((Y : ℝ) + n + 1) ^ (-σ)|
          ≤ (4 * K₂ * ((Y : ℝ) + n + 1) ^ β) * (σ * ((Y : ℝ) + n + 1) ^ (-σ - 1)) :=
            mul_le_mul (hPb n) hd (abs_nonneg _) (by positivity)
        _ = 4 * K₂ * σ * (((Y : ℝ) + n + 1) ^ β * ((Y : ℝ) + n + 1) ^ (-σ - 1)) := by ring
        _ = 4 * K₂ * σ * ((Y : ℝ) + n + 1) ^ (-(σ + 1 - β)) := by
            rw [← Real.rpow_add hpos]; ring_nf
    have hsum : ‖∑ n ∈ range N, (∑ j ∈ range (n + 1), c j) * (wt (n + 1) - wt n)‖ ≤
        4 * K₂ * σ / (σ - β) * (Y : ℝ) ^ (β - σ) := by
      calc _ ≤ ∑ n ∈ range N, ‖(∑ j ∈ range (n + 1), c j) * (wt (n + 1) - wt n)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ n ∈ range N, 4 * K₂ * σ * ((Y : ℝ) + n + 1) ^ (-(σ + 1 - β)) :=
            sum_le_sum fun n _ => hterm n
        _ = 4 * K₂ * σ * ∑ n ∈ range N, ((Y : ℝ) + n + 1) ^ (-(σ + 1 - β)) := by rw [mul_sum]
        _ ≤ 4 * K₂ * σ * ((Y : ℝ) ^ (1 - (σ + 1 - β)) / ((σ + 1 - β) - 1)) :=
            mul_le_mul_of_nonneg_left (sum_rpow_neg_le_of_gt (by linarith) Y hY N)
              (by positivity)
        _ = 4 * K₂ * σ / (σ - β) * (Y : ℝ) ^ (β - σ) := by
            rw [show 1 - (σ + 1 - β) = β - σ by ring, show (σ + 1 - β) - 1 = σ - β by ring]
            ring
    calc ‖(∑ j ∈ range (N + 1), c j) * wt N -
          ∑ n ∈ range N, (∑ j ∈ range (n + 1), c j) * (wt (n + 1) - wt n)‖
        ≤ ‖(∑ j ∈ range (N + 1), c j) * wt N‖ +
          ‖∑ n ∈ range N, (∑ j ∈ range (n + 1), c j) * (wt (n + 1) - wt n)‖ := norm_sub_le _ _
      _ ≤ 4 * K₂ * (Y : ℝ) ^ (β - σ) + 4 * K₂ * σ / (σ - β) * (Y : ℝ) ^ (β - σ) :=
          add_le_add hfirst hsum
      _ = 4 * K₂ * (1 + σ / (σ - β)) * (Y : ℝ) ^ (β - σ) := by ring
  -- pass to the limit
  have hsumm : LSeriesSummable (fun n => (μ n : ℂ)) w :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one) hwre
  have hHS : HasSum (LSeries.term (fun n => (μ n : ℂ)) w) (Mertens.invZ w) := by
    rw [← Mertens.LSeries_moebius_eq_invZ hwre]; exact hsumm.LSeriesHasSum
  have hT := hHS.tendsto_sum_nat
  have hlim : Tendsto (fun N : ℕ => ∑ d ∈ range (Y + 1 + (N + 1)),
      LSeries.term (fun n => (μ n : ℂ)) w d) atTop (nhds (Mertens.invZ w)) :=
    hT.comp (tendsto_atTop_mono (fun N : ℕ => (by omega : N ≤ Y + 1 + (N + 1))) tendsto_id)
  have hY : ∑ d ∈ Icc 1 Y, (μ d : ℂ) * (d : ℂ) ^ (-w) =
      ∑ d ∈ range (Y + 1), LSeries.term (fun n => (μ n : ℂ)) w d := by
    rw [sum_Icc_eq_sum_range _ (by simp)]
    exact sum_congr rfl fun d _ => moebius_mul_cpow_eq_term d
  rw [hY]
  have h2 : Tendsto (fun N : ℕ => ‖∑ d ∈ range (Y + 1 + (N + 1)),
      LSeries.term (fun n => (μ n : ℂ)) w d -
        ∑ d ∈ range (Y + 1), LSeries.term (fun n => (μ n : ℂ)) w d‖) atTop
      (nhds ‖Mertens.invZ w - ∑ d ∈ range (Y + 1), LSeries.term (fun n => (μ n : ℂ)) w d‖) :=
    (hlim.sub_const _).norm
  refine le_of_tendsto' h2 fun N => ?_
  rw [sum_range_add, add_sub_cancel_left]
  calc _ ≤ 4 * K₂ * (1 + σ / (σ - β)) * (Y : ℝ) ^ (β - σ) := hpart N
    _ = 4 * K₁ * (1 + σ / (σ - β)) * (|t| + 2) ^ ε * (Y : ℝ) ^ (β - σ) := by rw [hK₂]; ring

end Erdos969.MV
