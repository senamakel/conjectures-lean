import Mertens.Littlewood

/-!
# A Cesàro–Perron bound for partial sums of a Dirichlet series

This is mertens-rh's proof of Littlewood's bound (`Mertens/Littlewood.lean`) with `1/ζ` replaced
by an arbitrary function `Φ`. Let `a : ℕ → ℂ` have `∑ ‖a n‖/n³ < ∞`, and let `Φ` be holomorphic
on the strip `σ₀ ≤ σ ≤ 3`, equal to `L(a, s)` on `σ = 3`, bounded there, of at most polynomial
growth `(|t|+2)^{3/2}` on the strip, and with `‖Φ(σ₀ + it)‖ ≤ A (|t| + 2)^ε` on the left edge.
Then

    ‖∑_{n ≤ N} a n‖ ≤ K A (N + 1)^{σ₀ + 2ε},

with `K` depending only on `σ₀` and `ε`.

Proof: `A(N) = ∑_{0<n<N} a n (N - n)` is a Cesàro mean; erdos-985's `perron_weighted` writes it
as `(1/2π) ∫ Φ(s) N^{s+1}/(s(s+1)) dt` on `σ = 3`, the line moves to `σ₀` (Cauchy on rectangles,
`Mertens.integral_vertical_eq_of_strip`), and `∑_{n ≤ N} a n = A(N+1) - A(N)` exactly. The
difference `(N+1)^{s+1} - N^{s+1}` is at most `2^θ (N+1)^{σ+θ} ‖s+1‖^{1-θ}`; `θ = 2ε` makes the
integrand `O((1+|t|)^{-1-ε})`. No sharp-cutoff Perron formula is needed.
-/

namespace Erdos969.MV

open Complex MeasureTheory Filter Set Topology

/-- The closed strip `σ₀ ≤ σ ≤ 3`. -/
def strip (σ₀ : ℝ) : Set ℂ := {s : ℂ | σ₀ ≤ s.re ∧ s.re ≤ 3}

/-- The Perron integrand `Φ(s) y^s / (s(s+1))`. -/
noncomputable def kern (Φ : ℂ → ℂ) (y : ℝ) (s : ℂ) : ℂ := Φ s * (y : ℂ) ^ s / (s * (s + 1))

/-- The Cesàro mean `∑_{0<n<N} a n (N - n)`. -/
noncomputable def ces (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Ioo 0 N, a n * ((N : ℂ) - n)

lemma sum_Icc_eq_ces_sub (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, a n = ces a (N + 1) - ces a N := by
  have hI : Finset.Ioo 0 (N + 1) = Finset.Icc 1 N := by
    ext n; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
  have hJ : ces a N = ∑ n ∈ Finset.Icc 1 N, a n * ((N : ℂ) - n) := by
    unfold ces
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Ioo, Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_Ioo, Finset.mem_Icc, not_and, not_lt] at hn hn'
      have : n = N := by have := hn' (by omega); omega
      subst this
      simp
  rw [ces, hI, hJ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring

lemma line_mem_strip {σ₀ c : ℝ} (h1 : σ₀ ≤ c) (h2 : c ≤ 3) (t : ℝ) :
    (c : ℂ) + t * I ∈ strip σ₀ := by
  simp only [strip, mem_ofPred_eq, Mertens.line_re]; exact ⟨h1, h2⟩

lemma rpow_add_two_le {u ε : ℝ} (hu : 0 ≤ u) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (u + 2) ^ ε ≤ 2 * (1 + u) ^ ε := by
  calc (u + 2) ^ ε ≤ (2 * (1 + u)) ^ ε := Real.rpow_le_rpow (by positivity) (by linarith) hε
    _ = 2 ^ ε * (1 + u) ^ ε := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 2 * (1 + u) ^ ε := by
      gcongr
      exact Real.rpow_le_self_of_one_le (by norm_num) hε1

section

variable {Φ : ℂ → ℂ} {σ₀ : ℝ}

theorem differentiableOn_kern (h0 : 0 < σ₀) (hd : DifferentiableOn ℂ Φ (strip σ₀)) {y : ℝ}
    (hy : 0 < y) : DifferentiableOn ℂ (kern Φ y) (strip σ₀) := by
  intro s hs
  have hre : 0 < s.re := lt_of_lt_of_le h0 hs.1
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (ofReal_ne_zero.2 hy.ne'))
  have h3 : DifferentiableAt ℂ (fun s : ℂ => s * (s + 1)) s := by fun_prop
  have h4 : s * (s + 1) ≠ 0 :=
    mul_ne_zero (Mertens.ne_zero_of_re_pos hre) (Mertens.add_one_ne_zero_of_re_pos hre)
  exact ((hd s hs).mul h2.differentiableWithinAt).div h3.differentiableWithinAt h4

lemma norm_kern_eq {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖kern Φ y s‖ = ‖Φ s‖ * y ^ s.re * (1 / (‖s‖ * ‖s + 1‖)) := by
  rw [kern, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
  ring

/-- Integrability of the integrand on a line where `Φ` grows at most like `(|t|+2)^{1/2}`. -/
theorem integrable_kern_line (h0 : 0 < σ₀) (hd : DifferentiableOn ℂ Φ (strip σ₀)) {y c A : ℝ}
    (hy : 0 < y) (hc1 : σ₀ ≤ c) (hc2 : c ≤ 3)
    (hA : ∀ t : ℝ, ‖Φ ((c : ℂ) + t * I)‖ ≤ A * (|t| + 2) ^ (1 / 2 : ℝ)) :
    Integrable fun t : ℝ => kern Φ y ((c : ℂ) + t * I) := by
  set m := min σ₀ 1 with hm
  have hm0 : 0 < m := lt_min h0 one_pos
  have hcont : Continuous fun t : ℝ => kern Φ y ((c : ℂ) + t * I) :=
    (differentiableOn_kern h0 hd hy).continuousOn.comp_continuous (Mertens.continuous_line c)
      (fun t => line_mem_strip hc1 hc2 t)
  refine Mertens.integrable_of_le_rpow hcont (r := 3 / 2) (K := |A| * 2 * y ^ c * (4 / m))
    (by norm_num) fun t => ?_
  have hre : ((c : ℂ) + t * I).re = c := Mertens.line_re c t
  have him : ((c : ℂ) + t * I).im = t := Mertens.line_im c t
  have hden := Mertens.inv_norm_mul_le hm0 (min_le_right _ _)
    (s := (c : ℂ) + t * I) (by rw [hre]; exact (min_le_left _ _).trans hc1)
  rw [him] at hden
  rw [norm_kern_eq hy, hre]
  have hu : 0 < 1 + |t| := by positivity
  have hΦ : ‖Φ ((c : ℂ) + t * I)‖ ≤ |A| * (2 * (1 + |t|) ^ (1 / 2 : ℝ)) :=
    (hA t).trans (mul_le_mul (le_abs_self A) (rpow_add_two_le (abs_nonneg t) (by norm_num)
      (by norm_num)) (by positivity) (abs_nonneg A))
  have hcomb : (1 + |t|) ^ (1 / 2 : ℝ) * (1 + |t|) ^ (-2 : ℝ) = (1 + |t|) ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hu]; norm_num
  calc ‖Φ ((c : ℂ) + t * I)‖ * y ^ c * (1 / (‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖))
      ≤ (|A| * (2 * (1 + |t|) ^ (1 / 2 : ℝ))) * y ^ c * (4 / m * (1 + |t|) ^ (-2 : ℝ)) := by
        gcongr
    _ = |A| * 2 * y ^ c * (4 / m) * ((1 + |t|) ^ (1 / 2 : ℝ) * (1 + |t|) ^ (-2 : ℝ)) := by ring
    _ = |A| * 2 * y ^ c * (4 / m) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by rw [hcomb]

/-- The line `σ = 3` moves to `σ = σ₀`. -/
theorem integral_kern_shift (h0 : 0 < σ₀) (h3 : σ₀ < 3) (hd : DifferentiableOn ℂ Φ (strip σ₀))
    {y A B D : ℝ} (hy : 0 < y)
    (hB : ∀ t : ℝ, ‖Φ ((3 : ℝ) + t * I)‖ ≤ B)
    (hD : ∀ s ∈ strip σ₀, 1 ≤ |s.im| → ‖Φ s‖ ≤ D * (|s.im| + 2) ^ (3 / 2 : ℝ))
    (hA : ∀ t : ℝ, ‖Φ ((σ₀ : ℂ) + t * I)‖ ≤ A * (|t| + 2) ^ (1 / 2 : ℝ)) :
    ∫ t : ℝ, kern Φ y ((σ₀ : ℂ) + t * I) = ∫ t : ℝ, kern Φ y ((3 : ℝ) + t * I) := by
  have hB' : ∀ t : ℝ, ‖Φ (((3 : ℝ) : ℂ) + t * I)‖ ≤ |B| * (|t| + 2) ^ (1 / 2 : ℝ) := fun t =>
    (hB t).trans ((le_abs_self B).trans (le_mul_of_one_le_right (abs_nonneg B)
      (Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num))))
  refine Mertens.integral_vertical_eq_of_strip h3.le (differentiableOn_kern h0 hd hy)
    (integrable_kern_line h0 hd hy le_rfl h3.le hA)
    (integrable_kern_line h0 hd hy h3.le le_rfl hB') ?_
  intro η hη
  set m := min σ₀ 1 with hm
  have hm0 : 0 < m := lt_min h0 one_pos
  set K' := |D| * 4 * max (y ^ σ₀) (y ^ (3 : ℝ)) * (4 / m) + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  filter_upwards [eventually_ge_atTop ((K' / η) ^ 2), eventually_ge_atTop (1 : ℝ)] with T hT hT1
  intro σ hσ1 hσ2
  have hyσ : y ^ σ ≤ max (y ^ σ₀) (y ^ (3 : ℝ)) := by
    rcases le_or_gt 1 y with hy1 | hy1
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hy1 hσ2)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hy hy1.le hσ1)
  have hbound : ∀ u : ℝ, |u| = T → ‖kern Φ y ((σ : ℂ) + u * I)‖ ≤ η := by
    intro u hu
    have hre : ((σ : ℂ) + u * I).re = σ := Mertens.line_re σ u
    have him : ((σ : ℂ) + u * I).im = u := Mertens.line_im σ u
    have hmem : ((σ : ℂ) + u * I) ∈ strip σ₀ := line_mem_strip hσ1 hσ2 u
    have hΦ := hD _ hmem (by rw [him, hu]; exact hT1)
    rw [him, hu] at hΦ
    have hden := Mertens.inv_norm_mul_le hm0 (min_le_right _ _)
      (s := (σ : ℂ) + u * I) (by rw [hre]; exact (min_le_left _ _).trans hσ1)
    rw [him, hu] at hden
    rw [norm_kern_eq hy, hre]
    have hT0 : 0 < 1 + T := by linarith
    have hT2 : (T + 2) ^ (3 / 2 : ℝ) ≤ 4 * (1 + T) ^ (3 / 2 : ℝ) := by
      calc (T + 2) ^ (3 / 2 : ℝ) ≤ (2 * (1 + T)) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ = 2 ^ (3 / 2 : ℝ) * (1 + T) ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
        _ ≤ 4 * (1 + T) ^ (3 / 2 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := by norm_num
    have hcomb : (1 + T) ^ (3 / 2 : ℝ) * (1 + T) ^ (-2 : ℝ) = ((1 + T) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_add hT0, ← Real.rpow_neg hT0.le]; norm_num
    have hsq : K' / η ≤ (1 + T) ^ (1 / 2 : ℝ) := by
      have h1 : K' / η = ((K' / η) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hfin : K' * ((1 + T) ^ (1 / 2 : ℝ))⁻¹ ≤ η := by
      have hp : 0 < (1 + T) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
      rw [mul_inv_le_iff₀ hp]
      rw [div_le_iff₀ hη] at hsq
      linarith
    calc ‖Φ ((σ : ℂ) + u * I)‖ * y ^ σ * (1 / (‖(σ : ℂ) + u * I‖ * ‖(σ : ℂ) + u * I + 1‖))
        ≤ (|D| * (4 * (1 + T) ^ (3 / 2 : ℝ))) * max (y ^ σ₀) (y ^ (3 : ℝ)) *
            (4 / m * (1 + T) ^ (-2 : ℝ)) := by
          gcongr
          exact hΦ.trans (mul_le_mul (le_abs_self D) hT2 (by positivity) (abs_nonneg D))
      _ = (|D| * 4 * max (y ^ σ₀) (y ^ (3 : ℝ)) * (4 / m)) *
            ((1 + T) ^ (3 / 2 : ℝ) * (1 + T) ^ (-2 : ℝ)) := by ring
      _ ≤ K' * ((1 + T) ^ (1 / 2 : ℝ))⁻¹ := by
          rw [hcomb]
          gcongr
          linarith
      _ ≤ η := hfin
  exact ⟨hbound T (abs_of_nonneg (by linarith)),
    hbound (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)])⟩

/-- The Cesàro mean as a line integral on `σ = σ₀`. -/
theorem ces_eq {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (3 : ℝ))
    (h0 : 0 < σ₀) (h3 : σ₀ < 3) (hd : DifferentiableOn ℂ Φ (strip σ₀))
    (hL : ∀ t : ℝ, Φ ((3 : ℝ) + t * I) = LSeries a ((3 : ℝ) + t * I)) {A B D : ℝ}
    (hB : ∀ t : ℝ, ‖Φ ((3 : ℝ) + t * I)‖ ≤ B)
    (hD : ∀ s ∈ strip σ₀, 1 ≤ |s.im| → ‖Φ s‖ ≤ D * (|s.im| + 2) ^ (3 / 2 : ℝ))
    (hA : ∀ t : ℝ, ‖Φ ((σ₀ : ℂ) + t * I)‖ ≤ A * (|t| + 2) ^ (1 / 2 : ℝ))
    (N : ℕ) (hN : 1 ≤ N) :
    ces a N = (1 / (2 * Real.pi)) * ∫ t : ℝ, (N : ℂ) * kern Φ N ((σ₀ : ℂ) + t * I) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : ces a N = (N : ℂ) * ∑ n ∈ Finset.Ioo 0 N, a n * (1 - (n : ℂ) / N) := by
    rw [ces, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  have hP := Erdos985.Analytic.PerronKernel.perron_weighted a 3 (by norm_num) ha N hN
  rw [e1, hP, integral_const_mul, integral_kern_shift h0 h3 hd hNr hB hD hA]
  have : (fun t : ℝ => LSeries a (((3 : ℝ) : ℂ) + t * I) * (N : ℂ) ^ (((3 : ℝ) : ℂ) + t * I) /
      ((((3 : ℝ) : ℂ) + t * I) * (((3 : ℝ) : ℂ) + t * I + 1))) =
      fun t : ℝ => kern Φ N (((3 : ℝ) : ℂ) + t * I) := by
    funext t
    rw [kern, hL t]
    push_cast
    ring
  rw [this]
  ring

/-- The difference integrand, pointwise. -/
theorem norm_diff_kern_le {ε θ A : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h0 : 0 < σ₀) (hA : ∀ t : ℝ, ‖Φ ((σ₀ : ℂ) + t * I)‖ ≤ A * (|t| + 2) ^ ε)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    ‖((N + 1 : ℕ) : ℂ) * kern Φ (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) -
        (N : ℂ) * kern Φ N ((σ₀ : ℂ) + t * I)‖
      ≤ (2 * 2 * 2 * (2 / min σ₀ 1)) * A * ((N : ℝ) + 1) ^ (σ₀ + θ) * (1 + |t|) ^ (ε - θ - 1) := by
  set m := min σ₀ 1 with hm
  have hm0 : 0 < m := lt_min h0 one_pos
  set s : ℂ := (σ₀ : ℂ) + t * I with hsdef
  have hsre : s.re = σ₀ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hre0 : 0 < s.re := by linarith
  set u := 1 + |t| with hu
  have hu0 : 0 < u := by positivity
  set P : ℝ := (N : ℝ) + 1 with hP
  have hP0 : 0 < P := by positivity
  have ha : m * u / 2 ≤ ‖s‖ := by
    have := Mertens.norm_ge_of_re_pos hre0
    rw [hsre, hsim] at this
    exact this
  have hb : u / 2 ≤ ‖s + 1‖ := by
    have := Mertens.norm_add_one_ge hre0.le
    rwa [hsim] at this
  have ha0 : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) ha
  have hb0 : 0 < ‖s + 1‖ := lt_of_lt_of_le (by positivity) hb
  set d : ℂ := ((N + 1 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ s - (N : ℂ) * (N : ℂ) ^ s with hd
  have hD : ((N + 1 : ℕ) : ℂ) * kern Φ (N + 1 : ℕ) s - (N : ℂ) * kern Φ N s =
      Φ s * d / (s * (s + 1)) := by
    simp only [kern, hd]
    push_cast
    ring
  rw [hD, norm_div, norm_mul, norm_mul]
  have hA0 : 0 ≤ A := by
    have h := (norm_nonneg _).trans (hA 0)
    have : 0 < (|(0 : ℝ)| + 2) ^ ε := by positivity
    exact nonneg_of_mul_nonneg_left h this
  have hΦ : ‖Φ s‖ ≤ 2 * A * u ^ ε := by
    refine (hA t).trans ?_
    have := rpow_add_two_le (abs_nonneg t) hε hε1
    rw [← hu] at this
    nlinarith
  have hdX := Mertens.norm_diff_le_triv hre0.le N
  have hdY := Mertens.norm_diff_le_mvt hre0.le N hN
  rw [hsre] at hdX hdY
  have hdI := Mertens.le_rpow_mul_rpow (by positivity) (by positivity) hdX hdY hθ0 hθ1
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
  calc ‖Φ s‖ * ‖d‖ / (‖s‖ * ‖s + 1‖)
      = ‖Φ s‖ * ‖d‖ * (1 / ‖s‖) * (1 / ‖s + 1‖) := by field_simp
    _ ≤ (2 * A * u ^ ε) * (2 * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ))) * (1 / ‖s‖) *
          (1 / ‖s + 1‖) := by gcongr
    _ = (2 * A * u ^ ε) * (2 * P ^ (σ₀ + θ)) * (1 / ‖s‖) *
          (‖s + 1‖ ^ (1 - θ) / ‖s + 1‖) := by ring
    _ ≤ (2 * A * u ^ ε) * (2 * P ^ (σ₀ + θ)) * (2 / m * u ^ (-1 : ℝ)) *
          (2 * u ^ (-θ)) := by gcongr
    _ = 2 * 2 * 2 * (2 / m) * A * P ^ (σ₀ + θ) * (u ^ ε * u ^ (-1 : ℝ) * u ^ (-θ)) := by ring
    _ = 2 * 2 * 2 * (2 / m) * A * P ^ (σ₀ + θ) * u ^ (ε - θ - 1) := by
        rw [show ε - θ - 1 = ε + (-1) + (-θ) by ring, Real.rpow_add hu0, Real.rpow_add hu0]

end

/-- **The Cesàro–Perron bound.** -/
theorem norm_sum_Icc_le {ε σ₀ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (h0 : 0 < σ₀) (h3 : σ₀ < 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℕ → ℂ) (Φ : ℂ → ℂ) (A B D : ℝ),
      (Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (3 : ℝ)) →
      DifferentiableOn ℂ Φ (strip σ₀) →
      (∀ t : ℝ, Φ ((3 : ℝ) + t * I) = LSeries a ((3 : ℝ) + t * I)) →
      (∀ t : ℝ, ‖Φ ((3 : ℝ) + t * I)‖ ≤ B) →
      (∀ s ∈ strip σ₀, 1 ≤ |s.im| → ‖Φ s‖ ≤ D * (|s.im| + 2) ^ (3 / 2 : ℝ)) →
      (∀ t : ℝ, ‖Φ ((σ₀ : ℂ) + t * I)‖ ≤ A * (|t| + 2) ^ ε) →
      ∀ N : ℕ, 1 ≤ N → ‖∑ n ∈ Finset.Icc 1 N, a n‖ ≤ K * A * ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) := by
  set K₀ : ℝ := 2 * 2 * 2 * (2 / min σ₀ 1) with hK₀
  have hm0 : 0 < min σ₀ 1 := lt_min h0 one_pos
  have hK₀0 : 0 < K₀ := by positivity
  set J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(1 + ε)) with hJ
  have hint : Integrable fun t : ℝ => (1 + |t|) ^ (-(1 + ε)) := by
    simpa using Erdos985.Analytic.PerronAux.integrable_one_add_abs_rpow
      (show (1 : ℝ) < 1 + ε by linarith) 0
  have hJ0 : 0 ≤ J := integral_nonneg fun t => by positivity
  refine ⟨1 / (2 * Real.pi) * K₀ * J + 1, by positivity, ?_⟩
  intro a Φ A B D ha hd hL hB hD hA N hN
  have hA0 : 0 ≤ A := by
    have h := (norm_nonneg _).trans (hA 0)
    have : 0 < (|(0 : ℝ)| + 2) ^ ε := by positivity
    exact nonneg_of_mul_nonneg_left h this
  have hA' : ∀ t : ℝ, ‖Φ ((σ₀ : ℂ) + t * I)‖ ≤ A * (|t| + 2) ^ (1 / 2 : ℝ) := fun t =>
    (hA t).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [abs_nonneg t]) hε1) hA0)
  have hpos : ∀ M : ℕ, 1 ≤ M → (0 : ℝ) < M := fun M hM => by exact_mod_cast hM
  have hcont : ∀ (y : ℝ), 0 < y → Continuous fun t : ℝ => kern Φ y ((σ₀ : ℂ) + t * I) :=
    fun y hy => (differentiableOn_kern h0 hd hy).continuousOn.comp_continuous
      (Mertens.continuous_line σ₀) (fun t => line_mem_strip le_rfl h3.le t)
  have hi : ∀ M : ℕ, 1 ≤ M → Integrable fun t : ℝ => (M : ℂ) * kern Φ M ((σ₀ : ℂ) + t * I) :=
    fun M hM => (integrable_kern_line h0 hd (hpos M hM) le_rfl h3.le hA').const_mul _
  have e := sum_Icc_eq_ces_sub a N
  rw [ces_eq ha h0 h3 hd hL hB hD hA' (N + 1) (by omega), ces_eq ha h0 h3 hd hL hB hD hA' N hN,
    ← mul_sub, ← integral_sub (hi (N + 1) (by omega)) (hi N hN)] at e
  have hexp : ε - 2 * ε - 1 = -(1 + ε) := by ring
  have hbound : ‖∫ t : ℝ, (((N + 1 : ℕ) : ℂ) * kern Φ (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) -
      (N : ℂ) * kern Φ N ((σ₀ : ℂ) + t * I))‖ ≤ K₀ * A * ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) * J := by
    rw [hJ, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun t => ?_)
    have := norm_diff_kern_le hε.le (by linarith) (by linarith : (0 : ℝ) ≤ 2 * ε)
      (by linarith) h0 hA N hN t
    rwa [hexp] at this
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [e, norm_mul, hpi]
  have hP : 0 ≤ ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) := by positivity
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, (((N + 1 : ℕ) : ℂ) * kern Φ (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) -
        (N : ℂ) * kern Φ N ((σ₀ : ℂ) + t * I))‖
      ≤ 1 / (2 * Real.pi) * (K₀ * A * ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) * J) := by gcongr
    _ = (1 / (2 * Real.pi) * K₀ * J) * A * ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) := by ring
    _ ≤ (1 / (2 * Real.pi) * K₀ * J + 1) * A * ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) := by
        have : 0 ≤ A * ((N : ℝ) + 1) ^ (σ₀ + 2 * ε) := by positivity
        nlinarith

end Erdos969.MV
