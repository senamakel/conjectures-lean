import Mertens.Perron

/-!
# Steps D–E: Littlewood's bound `M(x) = O(x^{1/2+ε})` under RH

Let `A(N) = ∑_{0<n<N} μ(n)(N - n)`. Then `M(N) = A(N+1) - A(N)` exactly (Step D), and by Step C

    M(N) = (1/2π) ∫ invZ(s) ((N+1)^{s+1} - N^{s+1}) / (s(s+1)) dt,   s = σ₀ + it.

Step E bounds the integrand pointwise. The difference `d = (N+1)^{s+1} - N^{s+1}` satisfies both
`‖d‖ ≤ 2 (N+1)^{σ+1}` and (mean value theorem) `‖d‖ ≤ ‖s+1‖ (N+1)^σ`, hence
`‖d‖ ≤ 2^θ (N+1)^{σ+θ} ‖s+1‖^{1-θ}` for `θ ∈ [0,1]`. With `‖invZ‖ ≪ (1+|t|)^ε` (Step A) the
integrand is `≪ (N+1)^{σ₀+θ} (1+|t|)^{ε-θ-1}`; `θ = 2ε` makes it integrable, and
`σ₀ = 1/2 + ε` gives `M(N) ≪ (N+1)^{1/2+3ε}`.

So no sharp-cutoff Perron formula is needed: the difference of two Cesàro means at consecutive
integers *is* the sharp sum, and the interpolation between the two bounds on `d` recovers the
convergence that the sharp kernel `y^s/s` lacks.
-/

namespace Mertens

open Complex MeasureTheory Filter Set Topology Asymptotics
open scoped ArithmeticFunction.Moebius

/-- `A(N) = ∑_{0<n<N} μ(n)(N - n) = ∑_{m<N} M(m)`. -/
noncomputable def cesA (N : ℕ) : ℂ := ∑ n ∈ Finset.Ioo 0 N, (μ n : ℂ) * ((N : ℂ) - n)

lemma cesA_eq_Icc (N : ℕ) : cesA N = ∑ n ∈ Finset.Icc 1 N, (μ n : ℂ) * ((N : ℂ) - n) := by
  unfold cesA
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioo, Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn hn'
    simp only [Finset.mem_Ioo, Finset.mem_Icc, not_and, not_lt] at hn hn'
    have : n = N := by have := hn' (by omega); omega
    subst this
    simp

/-- **Step D**: `M(N) = A(N+1) - A(N)`. -/
theorem mertens_nat_eq (N : ℕ) : ((mertens N : ℤ) : ℂ) = cesA (N + 1) - cesA N := by
  have hI : Finset.Ioo 0 (N + 1) = Finset.Icc 1 N := by
    ext n; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
  rw [cesA, hI, cesA_eq_Icc, ← Finset.sum_sub_distrib, mertens, Nat.floor_natCast]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem cesA_eq (hRH : RiemannHypothesis) {σ₀ : ℝ} (h1 : 1 / 2 < σ₀) (h2 : σ₀ < 2)
    (N : ℕ) (hN : 1 ≤ N) :
    cesA N = (1 / (2 * Real.pi)) * ∫ t : ℝ, (N : ℂ) * F N ((σ₀ : ℂ) + t * I) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have : cesA N = (N : ℂ) * ∑ n ∈ Finset.Ioo 0 N, (μ n : ℂ) * (1 - (n : ℂ) / N) := by
    rw [cesA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  rw [this, cesaro_moebius_eq hRH h1 h2 N hN, integral_const_mul]
  ring

/-- `min`-interpolation: `z ≤ X`, `z ≤ Y` give `z ≤ X^θ Y^{1-θ}`. -/
lemma le_rpow_mul_rpow {z X Y θ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hzX : z ≤ X) (hzY : z ≤ Y)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : z ≤ X ^ θ * Y ^ (1 - θ) := by
  have hsplit : ∀ W : ℝ, 0 ≤ W → W = W ^ θ * W ^ (1 - θ) := fun W hW => by
    rw [← Real.rpow_add' hW (by norm_num), add_sub_cancel, Real.rpow_one]
  rcases le_total X Y with h | h
  · calc z ≤ X := hzX
      _ = X ^ θ * X ^ (1 - θ) := hsplit X hX
      _ ≤ X ^ θ * Y ^ (1 - θ) := by
        gcongr
  · calc z ≤ Y := hzY
      _ = Y ^ θ * Y ^ (1 - θ) := hsplit Y hY
      _ ≤ X ^ θ * Y ^ (1 - θ) := by gcongr

/-- `(N+1)·(N+1)^s - N·N^s`, bounded by the mean value theorem. -/
lemma norm_diff_le_mvt {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ) (hN : 1 ≤ N) :
    ‖((N + 1 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ s - (N : ℂ) * (N : ℂ) ^ s‖
      ≤ ‖s + 1‖ * ((N : ℝ) + 1) ^ s.re := by
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (s + 1)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : ∀ u ∈ Icc (N : ℝ) (N + 1), HasDerivWithinAt f ((s + 1) * (u : ℂ) ^ s) (Icc (N : ℝ) (N + 1)) u := by
    intro u hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have := hasDerivAt_ofReal_cpow_const hu0 hs1
    rw [add_sub_cancel_right] at this
    exact this.hasDerivWithinAt
  have hb : ∀ u ∈ Ico (N : ℝ) (N + 1), ‖(s + 1) * (u : ℂ) ^ s‖ ≤ ‖s + 1‖ * ((N : ℝ) + 1) ^ s.re := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu0]
    gcongr
    exact hu.2.le
  have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb ((N : ℝ) + 1) ⟨by linarith, le_rfl⟩
  have hfeq : ∀ u : ℝ, 0 < u → f u = (u : ℂ) * (u : ℂ) ^ s := fun u hu => by
    simp only [f]
    rw [cpow_add _ _ (ofReal_ne_zero.2 hu.ne'), cpow_one, mul_comm]
  rw [hfeq _ (by linarith), hfeq _ hN0] at this
  push_cast at this ⊢
  linarith

lemma norm_diff_le_triv {s : ℂ} (hs : 0 ≤ s.re) (N : ℕ) :
    ‖((N + 1 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ s - (N : ℂ) * (N : ℂ) ^ s‖
      ≤ 2 * ((N : ℝ) + 1) ^ (s.re + 1) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : ‖((N + 1 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ s‖ = ((N : ℝ) + 1) ^ (s.re + 1) := by
    rw [norm_mul, show ((N + 1 : ℕ) : ℂ) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos hN1, Complex.norm_real, Real.norm_of_nonneg hN1.le,
      Real.rpow_add hN1, Real.rpow_one, mul_comm]
  have h2 : ‖(N : ℂ) * (N : ℂ) ^ s‖ ≤ ((N : ℝ) + 1) ^ (s.re + 1) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast h
      rw [norm_mul, show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; ring,
        norm_cpow_eq_rpow_re_of_pos hN0, Complex.norm_real, Real.norm_of_nonneg hN0.le]
      calc (N : ℝ) * (N : ℝ) ^ s.re = (N : ℝ) ^ (s.re + 1) := by
            rw [Real.rpow_add hN0, Real.rpow_one, mul_comm]
        _ ≤ ((N : ℝ) + 1) ^ (s.re + 1) :=
            Real.rpow_le_rpow hN0.le (by linarith) (by linarith)
  calc _ ≤ ‖((N + 1 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ s‖ + ‖(N : ℂ) * (N : ℂ) ^ s‖ :=
        norm_sub_le _ _
    _ ≤ _ := by rw [h1]; linarith

/-- **Step E**, pointwise: the difference integrand is `≤ K (N+1)^{σ₀+θ} (1+|t|)^{ε-θ-1}`. -/
theorem norm_diff_F_le (hRH : RiemannHypothesis) {ε θ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {σ₀ : ℝ} (h1 : 1 / 2 < σ₀) (h2 : σ₀ < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 1 ≤ N → ∀ t : ℝ,
      ‖((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) - (N : ℂ) * F N ((σ₀ : ℂ) + t * I)‖
        ≤ K * ((N : ℝ) + 1) ^ (σ₀ + θ) * (1 + |t|) ^ (ε - θ - 1) := by
  obtain ⟨C, hC0, hC⟩ := norm_invZ_le hRH hε (δ := σ₀ - 1 / 2) (by linarith) (by linarith)
  set m := min σ₀ 1 with hm
  have hm0 : 0 < m := lt_min (by linarith) one_pos
  refine ⟨2 * C * 2 * 2 * (2 / m), by positivity, fun N hN t => ?_⟩
  set s : ℂ := (σ₀ : ℂ) + t * I with hsdef
  have hsre : s.re = σ₀ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hre0 : 0 < s.re := by linarith
  set u := 1 + |t| with hu
  have hu0 : 0 < u := by positivity
  set P : ℝ := (N : ℝ) + 1 with hP
  have hP0 : 0 < P := by positivity
  have ha : m * u / 2 ≤ ‖s‖ := by
    have := norm_ge_of_re_pos hre0
    rw [hsre, hsim] at this
    exact this
  have hb : u / 2 ≤ ‖s + 1‖ := by
    have := norm_add_one_ge hre0.le
    rwa [hsim] at this
  have ha0 : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) ha
  have hb0 : 0 < ‖s + 1‖ := lt_of_lt_of_le (by positivity) hb
  -- the algebraic form of the difference
  set d : ℂ := ((N + 1 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ s - (N : ℂ) * (N : ℂ) ^ s with hd
  have hD : ((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) s - (N : ℂ) * F N s = invZ s * d / (s * (s + 1)) := by
    simp only [F, hd]
    push_cast
    ring
  rw [hD, norm_div, norm_mul, norm_mul]
  -- bounds on the pieces
  have hinv : ‖invZ s‖ ≤ 2 * C * u ^ ε := by
    have := hC s (by rw [hsre]; linarith) (by rw [hsre]; linarith)
    rw [hsim] at this
    refine this.trans ?_
    have : (|t| + 2) ^ ε ≤ 2 * u ^ ε := by
      calc (|t| + 2) ^ ε ≤ (2 * u) ^ ε := Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hε.le
        _ = 2 ^ ε * u ^ ε := Real.mul_rpow (by norm_num) hu0.le
        _ ≤ 2 * u ^ ε := by
          gcongr
          exact Real.rpow_le_self_of_one_le (by norm_num) hε1
    nlinarith
  have hdX := norm_diff_le_triv hre0.le N
  have hdY := norm_diff_le_mvt hre0.le N hN
  rw [hsre] at hdX hdY
  have hdI := le_rpow_mul_rpow (by positivity) (by positivity) hdX hdY hθ0 hθ1
  have hPexp : P ^ ((σ₀ + 1) * θ) * P ^ (σ₀ * (1 - θ)) = P ^ (σ₀ + θ) := by
    rw [← Real.rpow_add hP0]; ring_nf
  have h2θ : (2 : ℝ) ^ θ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hθ1
  have hdI' : ‖d‖ ≤ 2 * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ)) := by
    calc ‖d‖ ≤ (2 * P ^ (σ₀ + 1)) ^ θ * (‖s + 1‖ * P ^ σ₀) ^ (1 - θ) := hdI
      _ = 2 ^ θ * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← hPexp]
        ring
      _ ≤ 2 * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ)) := by gcongr
  have hbθ : ‖s + 1‖ ^ (1 - θ) / ‖s + 1‖ ≤ 2 * u ^ (-θ) := by
    have e1 : ‖s + 1‖ ^ (1 - θ) / ‖s + 1‖ = (‖s + 1‖ ^ θ)⁻¹ := by
      rw [Real.rpow_sub hb0, Real.rpow_one]
      have : 0 < ‖s + 1‖ ^ θ := Real.rpow_pos_of_pos hb0 θ
      field_simp
    have e2 : ((u / 2) ^ θ)⁻¹ = 2 ^ θ * u ^ (-θ) := by
      rw [Real.div_rpow hu0.le (by norm_num), Real.rpow_neg hu0.le]
      have : 0 < u ^ θ := Real.rpow_pos_of_pos hu0 θ
      have : 0 < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
      field_simp
    rw [e1]
    calc (‖s + 1‖ ^ θ)⁻¹ ≤ ((u / 2) ^ θ)⁻¹ := by
          apply inv_anti₀ (Real.rpow_pos_of_pos (by positivity) θ)
          exact Real.rpow_le_rpow (by positivity) hb hθ0
      _ = 2 ^ θ * u ^ (-θ) := e2
      _ ≤ 2 * u ^ (-θ) := by gcongr
  have ha' : 1 / ‖s‖ ≤ 2 / m * u ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    calc 1 / ‖s‖ ≤ 1 / (m * u / 2) := one_div_le_one_div_of_le (by positivity) ha
      _ = 2 / m * u⁻¹ := by field_simp
  have hinv0 : 0 ≤ 2 * C * u ^ ε := by positivity
  calc ‖invZ s‖ * ‖d‖ / (‖s‖ * ‖s + 1‖)
      = ‖invZ s‖ * ‖d‖ * (1 / ‖s‖) * (1 / ‖s + 1‖) := by field_simp
    _ ≤ (2 * C * u ^ ε) * (2 * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ))) * (1 / ‖s‖) *
          (1 / ‖s + 1‖) := by gcongr
    _ = (2 * C * u ^ ε) * (2 * P ^ (σ₀ + θ)) * (1 / ‖s‖) *
          (‖s + 1‖ ^ (1 - θ) / ‖s + 1‖) := by ring
    _ ≤ (2 * C * u ^ ε) * (2 * P ^ (σ₀ + θ)) * (2 / m * u ^ (-1 : ℝ)) *
          (2 * u ^ (-θ)) := by gcongr
    _ = 2 * C * 2 * 2 * (2 / m) * P ^ (σ₀ + θ) * (u ^ ε * u ^ (-1 : ℝ) * u ^ (-θ)) := by ring
    _ = 2 * C * 2 * 2 * (2 / m) * P ^ (σ₀ + θ) * u ^ (ε - θ - 1) := by
        rw [show ε - θ - 1 = ε + (-1) + (-θ) by ring, Real.rpow_add hu0, Real.rpow_add hu0]

end Mertens
