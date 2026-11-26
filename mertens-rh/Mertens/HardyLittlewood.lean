import Mertens.Main
import Mertens.Abel
import Mertens.Weights

/-!
# Step I: Hardy–Littlewood's bound `∑ μ(n)/n · e^{-x/n²} = O(x^{-1/4+ε})` under RH

Abel summation (Step G) against `w(n) = W_H(n) = (1/n) e^{-x/n²}` with `|M(n)| ≪ (n+1)^β`,
`β = 1/2 + 3ε` (Step F). Interpolating `|Δw(n)| ≤ 2 n^{-2}` and `|Δw(n)| ≤ 5/x` (Step H) with
`θ = (β + 1 + ε)/2` gives `(n+1)^β |Δw(n)| ≪ x^{θ-1} n^{-(1+ε)}`, and `θ - 1 = -1/4 + 2ε`.
-/

namespace Mertens

open Filter Topology Finset Asymptotics
open scoped ArithmeticFunction.Moebius

lemma sum_range_succ_moebius (n : ℕ) :
    ∑ k ∈ range (n + 1), (μ k : ℝ) = (mertens n : ℝ) := by
  rw [sum_range_succ', ArithmeticFunction.map_zero, Int.cast_zero, add_zero, mertens,
    Nat.floor_natCast, Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => (μ j : ℝ)) 0 n 1]
  push_cast
  rfl

/-- The Mertens bound in the form used by Abel summation (all `n`, including `n = 0`). -/
lemma abs_sum_moebius_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      |∑ k ∈ range (n + 1), (μ k : ℝ)| ≤ K * ((n : ℝ) + 1) ^ (1 / 2 + 3 * ε) := by
  obtain ⟨K, hK0, hK⟩ := abs_mertens_nat_le hRH hε hε'
  refine ⟨K, hK0, fun n => ?_⟩
  rw [sum_range_succ_moebius]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mertens]; positivity
  · exact hK n hn

lemma tendsto_rpow_mul_inv_nat {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1) (C : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ β * (C / n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - β))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h2 := h1.const_mul (2 * |C|)
  rw [mul_zero] at h2
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_div, abs_of_pos hn0]
  have hpow : ((n : ℝ) + 1) ^ β ≤ 2 * (n : ℝ) ^ β := by
    calc ((n : ℝ) + 1) ^ β ≤ (2 * (n : ℝ)) ^ β := Real.rpow_le_rpow (by positivity) (by linarith) hβ0
      _ = 2 ^ β * (n : ℝ) ^ β := Real.mul_rpow (by norm_num) hn0.le
      _ ≤ 2 * (n : ℝ) ^ β := by
        gcongr; exact Real.rpow_le_self_of_one_le (by norm_num) hβ.le
  have heq : (n : ℝ) ^ β * (1 / n) = (n : ℝ) ^ (-(1 - β)) := by
    rw [show -(1 - β) = β + (-1) by ring, Real.rpow_add hn0, Real.rpow_neg_one, one_div]
  calc ((n : ℝ) + 1) ^ β * (|C| / n) ≤ (2 * (n : ℝ) ^ β) * (|C| / n) := by gcongr
    _ = 2 * |C| * ((n : ℝ) ^ β * (1 / n)) := by ring
    _ = 2 * |C| * (n : ℝ) ^ (-(1 - β)) := by rw [heq]

lemma hlPartial_eq (x : ℝ) (N : ℕ) :
    hlPartial x N = ∑ n ∈ range N, (μ n : ℝ) * wH x n := by
  unfold hlPartial wH
  refine sum_congr rfl fun n _ => ?_
  ring

/-- The per-`x` estimate: the series converges, with sum at most `K (A₀ + A x^{θ-1} Z)`. -/
theorem hl_tendsto (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 16) :
    ∃ K A Z : ℝ, 0 < K ∧ 0 ≤ A ∧ 0 ≤ Z ∧ ∀ x : ℝ, 0 < x → ∀ A₀ : ℝ, Real.exp (-x) ≤ A₀ →
      ∃ L : ℝ, Tendsto (hlPartial x) atTop (𝓝 L) ∧
        |L| ≤ K * (A₀ + A * x ^ (-1 / 4 + 2 * ε) * Z) := by
  obtain ⟨K, hK0, hK⟩ := abs_sum_moebius_le hRH hε (by linarith)
  set β : ℝ := 1 / 2 + 3 * ε with hβ
  set θ : ℝ := (β + 1 + ε) / 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ, hβ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ, hβ]; linarith
  set A : ℝ := 2 * 2 ^ θ * 5 ^ (1 - θ) with hA
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + ε)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  refine ⟨K, A, Z, hK0, by positivity, hZ0, fun x hx A₀ hA₀ => ?_⟩
  have hA₀0 : 0 ≤ A₀ := le_trans (Real.exp_pos _).le hA₀
  have hB : ∀ N : ℕ, ∑ n ∈ range N, ((n : ℝ) + 1) ^ β * |wH x (n + 1 : ℕ) - wH x n| ≤
      A₀ + A * x ^ (-1 / 4 + 2 * ε) * Z := by
    intro N
    refine sum_range_le_of_terms hε (by positivity) hx hA₀0 ?_ ?_ N
    · simp only [Nat.cast_zero, zero_add, Real.one_rpow, one_mul, Nat.cast_one]
      have : wH x 1 - wH x 0 = Real.exp (-x) := by simp [wH]
      rw [this, abs_of_pos (Real.exp_pos _)]
      exact hA₀
    · intro n hn
      obtain ⟨h₁, h₂⟩ := wH_diff_le hx hn
      have := interp_term (β := β) hn hx (by norm_num) (by norm_num) hθ0 hθ1
        (by rw [hβ]; linarith) (by rw [hβ]; linarith) h₁ h₂
      have hexpx : (0 : ℝ) * θ + -1 * (1 - θ) = -1 / 4 + 2 * ε := by rw [hθ, hβ]; ring
      have hexpn : β + (-2 * θ + 0 * (1 - θ)) = -(1 + ε) := by rw [hθ]; ring
      rw [hexpx, hexpn] at this
      push_cast
      exact this
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ β * |wH x n|) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_inv_nat (β := β) (by rw [hβ]; linarith) (by rw [hβ]; linarith) 1
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ this
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    gcongr
    rw [wH, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n), abs_of_pos (Real.exp_pos _)]
    calc 1 / (n : ℝ) * Real.exp (-x / (n : ℝ) ^ 2) ≤ 1 / n * 1 := by
          gcongr
          rw [Real.exp_le_one_iff]
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      _ = 1 / n := mul_one _
  obtain ⟨L, hL, hLb⟩ := abel_tendsto (c := fun n => (μ n : ℝ)) (w := fun n => wH x n)
    hK0.le hK hB hlim
  refine ⟨L, ?_, hLb⟩
  refine hL.congr fun N => ?_
  rw [hlPartial_eq]

/-- **Hardy–Littlewood (1916)**: under RH the series converges for every `x > 0` and
`∑ μ(n)/n · e^{-x/n²} = O(x^{-1/4+ε})`. -/
theorem hardyLittlewood_of_RH (hRH : RiemannHypothesis) : HardyLittlewoodBound := by
  refine ⟨fun x hx => ?_, fun ε' hε' => ?_⟩
  · obtain ⟨K, A, Z, -, -, -, h⟩ := hl_tendsto hRH (ε := 1 / 16) (by norm_num) le_rfl
    obtain ⟨L, hL, -⟩ := h x hx 1 (Real.exp_le_one_iff.2 (by linarith))
    exact ⟨L, hL⟩
  · set ε := min (ε' / 2) (1 / 16) with hεdef
    have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
    have hε2 : 2 * ε ≤ ε' := by have := min_le_left (ε' / 2) (1 / 16); linarith
    obtain ⟨K, A, Z, hK0, hA0, hZ0, h⟩ := hl_tendsto hRH hε0 (min_le_right _ _)
    refine IsBigO.of_bound (K * (1 + A * Z)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    set P : ℝ := -1 / 4 + 2 * ε with hP
    have hexp : Real.exp (-x) ≤ x ^ P := by
      have h1 : Real.exp (-x) ≤ x ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, Real.exp_neg]
        apply inv_anti₀ hx0
        linarith [Real.add_one_le_exp x]
      exact h1.trans (Real.rpow_le_rpow_of_exponent_le hx (by rw [hP]; linarith))
    obtain ⟨L, hL, hLb⟩ := h x hx0 (x ^ P) hexp
    rw [hardyLittlewood, hL.limUnder_eq, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    have hxP : x ^ P ≤ x ^ (-1 / 4 + ε') := Real.rpow_le_rpow_of_exponent_le hx (by rw [hP]; linarith)
    calc |L| ≤ K * (x ^ P + A * x ^ P * Z) := hLb
      _ = K * (1 + A * Z) * x ^ P := by ring
      _ ≤ K * (1 + A * Z) * x ^ (-1 / 4 + ε') := by gcongr

end Mertens
