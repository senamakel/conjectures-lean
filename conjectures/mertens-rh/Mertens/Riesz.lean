import Mertens.HardyLittlewood

/-!
# Step J: Riesz's bound for `∑_{k≥1} (-1)^{k+1} x^k / ((k-1)! ζ(2k)) = O(x^{1/4+ε})` under RH

Expanding `1/ζ(2k) = ∑ μ(n) n^{-2k}` and summing the exponential series (the double series is
absolutely convergent), the Riesz function is `∑_n μ(n) W_R(n)` with
`W_R(t) = (x/t²) e^{-x/t²}`. Abel summation (Step G) with `|Δw(n)| ≤ 2x n^{-3}` and
`|Δw(n)| ≤ 32 n/x` (Step H), interpolated with `θ = (β + 2 + ε)/4`, gives
`(n+1)^β |Δw(n)| ≪ x^{2θ-1} n^{-(1+ε)}`, and `2θ - 1 = 1/4 + 2ε`.
-/

namespace Mertens

open Filter Topology Finset Asymptotics Complex
open scoped ArithmeticFunction.Moebius Nat

/-- `1/ζ(2k) = ∑ μ(n)/n^{2k}`, as real numbers. -/
lemma inv_zeta_two_mul_re (j : ℕ) :
    ((riemannZeta (2 * ((j : ℂ) + 1))).re)⁻¹ =
      ∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ (2 * (j + 1)) := by
  set m : ℕ := 2 * (j + 1) with hm
  have hs : (2 * ((j : ℂ) + 1)) = (m : ℂ) := by rw [hm]; push_cast; ring
  have hre : 1 < (m : ℂ).re := by
    rw [Complex.natCast_re, hm]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hinv : (riemannZeta (m : ℂ))⁻¹ = LSeries (fun n => (μ n : ℂ)) m := by
    apply inv_eq_of_mul_eq_one_right
    rw [← LSeries_one_eq_riemannZeta hre]
    exact LSeries_one_mul_Lseries_moebius hre
  have hL : LSeries (fun n => (μ n : ℂ)) m =
      ((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    congr 1
    funext n
    rw [LSeries.term_def]
    split_ifs with hn
    · simp [hn]
    · rw [cpow_natCast]; push_cast; rfl
  have hz : riemannZeta (m : ℂ) = (((∑' n : ℕ, (μ n : ℝ) / (n : ℝ) ^ m)⁻¹ : ℝ) : ℂ) := by
    rw [← inv_inv (riemannZeta (m : ℂ)), hinv, hL, Complex.ofReal_inv]
  rw [hs, hz, Complex.ofReal_re, inv_inv]

lemma abs_moebius_real_le (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **The Riesz function is a Möbius sum**: `riesz x = ∑ μ(n) (x/n²) e^{-x/n²}`. -/
theorem riesz_eq (x : ℝ) : riesz x = ∑' n : ℕ, (μ n : ℝ) * wR x n := by
  set F : ℕ → ℕ → ℝ := fun j n =>
    (-1 : ℝ) ^ j * x ^ (j + 1) / (j ! : ℝ) * ((μ n : ℝ) / (n : ℝ) ^ (2 * (j + 1))) with hF
  have hterm : ∀ j : ℕ, (-1 : ℝ) ^ j * x ^ (j + 1) /
      ((j ! : ℝ) * (riemannZeta (2 * ((j : ℂ) + 1))).re) = ∑' n, F j n := by
    intro j
    rw [div_mul_eq_div_div, div_eq_mul_inv _ (riemannZeta _).re, inv_zeta_two_mul_re,
      ← tsum_mul_left]
  have hg1 : Summable fun j : ℕ => |x| ^ (j + 1) / (j ! : ℝ) := by
    have := (Real.summable_pow_div_factorial |x|).mul_left |x|
    refine this.congr fun j => ?_
    rw [pow_succ]; ring
  have hg2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 one_lt_two
  have hsum : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded (hg1.mul_of_nonneg hg2 (fun j => by positivity)
      (fun n => by positivity)) fun p => ?_
    obtain ⟨j, n⟩ := p
    have hb : |(μ n : ℝ)| / (n : ℝ) ^ (2 * (j + 1)) ≤ 1 / (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        apply div_le_div₀ (by norm_num) (abs_moebius_real_le n) (by positivity)
        exact pow_le_pow_right₀ hn1 (by omega)
    have key : ‖Function.uncurry F (j, n)‖ =
        |x| ^ (j + 1) / (j ! : ℝ) * (|(μ n : ℝ)| / (n : ℝ) ^ (2 * (j + 1))) := by
      simp only [Function.uncurry_apply_pair, hF, Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
        abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    rw [key]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  rw [riesz]
  simp_rw [hterm]
  rw [hsum.tsum_comm.symm]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hF]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hexp : Real.exp (-(x / (n : ℝ) ^ 2)) =
        ∑' j : ℕ, (-(x / (n : ℝ) ^ 2)) ^ j / (j ! : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hFj : ∀ j, F j n = (μ n : ℝ) * (x / (n : ℝ) ^ 2) * ((-(x / (n : ℝ) ^ 2)) ^ j / (j ! : ℝ)) := by
      intro j
      have e1 : (-(x / (n : ℝ) ^ 2)) ^ j = (-1) ^ j * x ^ j / (n : ℝ) ^ (2 * j) := by
        rw [neg_eq_neg_one_mul, mul_pow, div_pow, ← pow_mul]; ring
      rw [e1]
      simp only [hF]
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
      field_simp
      ring
    simp_rw [hFj]
    rw [tsum_mul_left, ← hexp, wR]
    ring

/-- **Riesz (1916)**: under RH, the Riesz function is `O(x^{1/4+ε})` for every `ε > 0`. -/
theorem riesz_of_RH (hRH : RiemannHypothesis) : RieszBound := by
  intro ε' hε'
  set ε := min (ε' / 2) (1 / 16) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε2 : 2 * ε ≤ ε' := by have := min_le_left (ε' / 2) (1 / 16); linarith
  have hε16 : ε ≤ 1 / 16 := min_le_right _ _
  obtain ⟨K, hK0, hK⟩ := abs_sum_moebius_le hRH hε0 (by linarith)
  set β : ℝ := 1 / 2 + 3 * ε with hβ
  set θ : ℝ := (β + 2 + ε) / 4 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ, hβ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ, hβ]; linarith
  set A : ℝ := 2 * 2 ^ θ * 32 ^ (1 - θ) with hA
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + ε)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  set P : ℝ := 1 / 4 + 2 * ε with hP
  refine IsBigO.of_bound (K * (1 + A * Z)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hxP1 : 1 ≤ x ^ P := Real.one_le_rpow hx (by rw [hP]; linarith)
  have hB : ∀ N : ℕ, ∑ n ∈ range N, ((n : ℝ) + 1) ^ β * |wR x (n + 1 : ℕ) - wR x n| ≤
      x ^ P + A * x ^ P * Z := by
    intro N
    refine sum_range_le_of_terms hε0 (by positivity) hx0 (by positivity) ?_ ?_ N
    · simp only [Nat.cast_zero, zero_add, Real.one_rpow, one_mul, Nat.cast_one]
      have : wR x 1 - wR x 0 = x * Real.exp (-x) := by simp [wR]
      rw [this, abs_of_pos (by positivity)]
      refine le_trans ?_ hxP1
      have := Real.add_one_le_exp x
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos x)]
      linarith
    · intro n hn
      obtain ⟨h₁, h₂⟩ := wR_diff_le hx0 hn
      have := interp_term (β := β) hn hx0 (by norm_num) (by norm_num) hθ0 hθ1
        (by rw [hβ]; linarith) (by rw [hβ]; linarith) h₁ h₂
      have hexpx : (1 : ℝ) * θ + -1 * (1 - θ) = P := by rw [hP, hθ, hβ]; ring
      have hexpn : β + (-3 * θ + 1 * (1 - θ)) = -(1 + ε) := by rw [hθ]; ring
      rw [hexpx, hexpn] at this
      push_cast
      exact this
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ β * |wR x n|) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_inv_nat (β := β) (by rw [hβ]; linarith) (by rw [hβ]; linarith) x
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ this
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    gcongr
    rw [wR, abs_mul, abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)]
    calc x / (n : ℝ) ^ 2 * Real.exp (-(x / (n : ℝ) ^ 2)) ≤ x / (n : ℝ) ^ 2 * 1 := by
          gcongr
          rw [Real.exp_le_one_iff, neg_nonpos]
          positivity
      _ ≤ x / n := by
          rw [mul_one]
          apply div_le_div_of_nonneg_left hx0.le (by positivity)
          nlinarith
  obtain ⟨L, hL, hLb⟩ := abel_tendsto (c := fun n => (μ n : ℝ)) (w := fun n => wR x n)
    hK0.le hK hB hlim
  have hsum : Summable fun n : ℕ => (μ n : ℝ) * wR x n := by
    refine Summable.of_norm_bounded
      ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left x) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [wR]
    · rw [wR, abs_mul (x / (n : ℝ) ^ 2), abs_of_nonneg (show (0 : ℝ) ≤ x / (n : ℝ) ^ 2 by positivity),
        abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-(x / (n : ℝ) ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      calc |(μ n : ℝ)| * (x / (n : ℝ) ^ 2 * Real.exp (-(x / (n : ℝ) ^ 2)))
          ≤ 1 * (x / (n : ℝ) ^ 2 * 1) := by
            gcongr
            exact abs_moebius_real_le n
        _ = x * (1 / (n : ℝ) ^ 2) := by ring
  have hLeq : ∑' n : ℕ, (μ n : ℝ) * wR x n = L :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hL
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _), riesz_eq,
    hLeq]
  have hxP : x ^ P ≤ x ^ (1 / 4 + ε') := Real.rpow_le_rpow_of_exponent_le hx (by rw [hP]; linarith)
  calc |L| ≤ K * (x ^ P + A * x ^ P * Z) := hLb
    _ = K * (1 + A * Z) * x ^ P := by ring
    _ ≤ K * (1 + A * Z) * x ^ (1 / 4 + ε') := by gcongr

end Mertens
