import Erdos969.Hyperbola
import Erdos969.Identity
import Mertens.Main

/-!
# Axer's bound for the squarefree error term, from a bound on the Mertens function

* `abs_error_le`: for `1 ≤ Y ≤ N`, `|E(N)| ≤ Y + C N Y^{α-2}` whenever `|M(k)| ≤ K (k+1)^α`.
* `squarefreeError_le`: choosing `Y ≍ N^{1/(3-α)}` gives `|E(N)| ≤ C N^{1/(3-α)}`.
* `axer_of_RH`: with `α = 1/2 + 3ε'` from `Mertens.abs_mertens_nat_le`, `E(x) = O(x^{2/5+ε})`.
-/

namespace Erdos969

open Finset ArithmeticFunction Filter Asymptotics
open scoped ArithmeticFunction.Moebius

/-- Error decomposition for a fixed split point `Y`. -/
theorem abs_error_le {K α : ℝ} (hα0 : 0 ≤ α) (hα2 : α < 2) (hM : MBound K α) {N Y : ℕ}
    (hY : 1 ≤ Y) (hYN : Y ≤ N) :
    |squarefreeCountingError N| ≤ (Y : ℝ) +
      (2 * K * 2 ^ α * (1 + 3 / (2 - α)) + K * 2 ^ α * (1 / (1 - α / 2) + 1)) *
        ((N : ℝ) * (Y : ℝ) ^ (α - 2)) := by
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hQ : (squarefreeCounting N : ℝ) =
      ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) (squarefreeCounting_eq N)
    push_cast at this
    exact this
  have hsplit : Icc 1 N = Icc 1 Y ∪ Ioc Y N := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 Y) (Ioc Y N) := by
    rw [Finset.disjoint_left]; intro d h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj] at hQ
  set T := ∑ d ∈ Ioc Y N, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) with hT
  set P := ∑ d ∈ Icc 1 Y, (μ d : ℝ) / ((d : ℝ) ^ 2) with hP
  set R := ∑ d ∈ Icc 1 Y, (μ d : ℝ) * ((N : ℝ) / ((d : ℝ) ^ 2) - ((N / (d * d) : ℕ) : ℝ)) with hR
  have hE : squarefreeCountingError N = -R + (N : ℝ) * (P - 6 / Real.pi ^ 2) + T := by
    unfold squarefreeCountingError
    rw [hQ]
    have : ∑ d ∈ Icc 1 Y, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) = (N : ℝ) * P - R := by
      rw [hP, hR, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun d _ => ?_
      ring
    rw [this]; ring
  have hRb : |R| ≤ Y := by
    calc |R| ≤ ∑ d ∈ Icc 1 Y, |(μ d : ℝ) * ((N : ℝ) / ((d : ℝ) ^ 2) - ((N / (d * d) : ℕ) : ℝ))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 Y, (1 : ℝ) := by
          refine sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
          have hdd : (0 : ℝ) < ((d * d : ℕ) : ℝ) := by
            have : 0 < d * d := Nat.mul_pos hd1 hd1
            exact_mod_cast this
          have hfl : ((N / (d * d) : ℕ) : ℝ) = ⌊(N : ℝ) / ((d * d : ℕ) : ℝ)⌋₊ := by
            rw [Nat.floor_div_eq_div]
          have hx : (N : ℝ) / ((d : ℝ) ^ 2) = (N : ℝ) / ((d * d : ℕ) : ℝ) := by
            push_cast; ring_nf
          rw [abs_mul, hx, hfl]
          have h0 : 0 ≤ (N : ℝ) / ((d * d : ℕ) : ℝ) - ⌊(N : ℝ) / ((d * d : ℕ) : ℝ)⌋₊ :=
            sub_nonneg.2 (Nat.floor_le (by positivity))
          have h1 : (N : ℝ) / ((d * d : ℕ) : ℝ) - ⌊(N : ℝ) / ((d * d : ℕ) : ℝ)⌋₊ ≤ 1 := by
            have := Nat.lt_floor_add_one ((N : ℝ) / ((d * d : ℕ) : ℝ)); linarith
          rw [abs_of_nonneg h0]
          have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
          calc |(μ d : ℝ)| * _ ≤ 1 * 1 := mul_le_mul hmu h1 h0 zero_le_one
            _ = 1 := one_mul 1
      _ = Y := by simp
  have hPb := abs_tail_le hα0 hα2 hM hY
  have hTb := abs_T_le hα0 hα2 hM hY hYN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hE]
  have hPb' : |(N : ℝ) * (P - 6 / Real.pi ^ 2)| ≤
      (2 * K * 2 ^ α * (1 + 3 / (2 - α))) * ((N : ℝ) * (Y : ℝ) ^ (α - 2)) := by
    rw [abs_mul, abs_of_nonneg hN0, abs_sub_comm]
    calc (N : ℝ) * |6 / Real.pi ^ 2 - P| ≤ (N : ℝ) * ((2 * K * 2 ^ α * (1 + 3 / (2 - α))) * (Y : ℝ) ^ (α - 2)) :=
          mul_le_mul_of_nonneg_left hPb hN0
      _ = _ := by ring
  calc |-R + (N : ℝ) * (P - 6 / Real.pi ^ 2) + T|
      ≤ |-R| + |(N : ℝ) * (P - 6 / Real.pi ^ 2)| + |T| := abs_add_three _ _ _
    _ ≤ Y + (2 * K * 2 ^ α * (1 + 3 / (2 - α))) * ((N : ℝ) * (Y : ℝ) ^ (α - 2)) +
          (K * 2 ^ α * (1 / (1 - α / 2) + 1)) * ((N : ℝ) * (Y : ℝ) ^ (α - 2)) := by
        rw [abs_neg]; linarith
    _ = _ := by ring

/-- With `Y ≍ N^{1/(3-α)}`: `E(N) ≪ N^{1/(3-α)}`. -/
theorem squarefreeError_le {K α : ℝ} (hα0 : 0 ≤ α) (hα2 : α < 2) (hM : MBound K α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |squarefreeCountingError N| ≤ C * (N : ℝ) ^ (1 / (3 - α)) := by
  set C' : ℝ := 2 * K * 2 ^ α * (1 + 3 / (2 - α)) + K * 2 ^ α * (1 / (1 - α / 2) + 1) with hC'
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have hC'0 : 0 ≤ C' := by
    have h1 : 0 ≤ 3 / (2 - α) := by apply div_nonneg <;> linarith
    have h2 : 0 ≤ 1 / (1 - α / 2) := by apply div_nonneg <;> linarith
    positivity
  refine ⟨2 + C', by linarith, fun N hN => ?_⟩
  set θ : ℝ := 1 / (3 - α) with hθ
  have h3 : 0 < 3 - α := by linarith
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one h3]; linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set y : ℝ := (N : ℝ) ^ θ with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hN' hθ0.le
  have hyN : y ≤ N := by
    calc y ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN' hθ1
      _ = N := Real.rpow_one _
  set Y : ℕ := ⌈y⌉₊ with hYdef
  have hYy : y ≤ Y := Nat.le_ceil y
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := hy1.trans hYy
    exact_mod_cast this
  have hYle : (Y : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hYN : Y ≤ N := by
    calc Y = ⌈y⌉₊ := rfl
      _ ≤ ⌈(N : ℝ)⌉₊ := Nat.ceil_mono hyN
      _ = N := Nat.ceil_natCast N
  have h := abs_error_le hα0 hα2 hM hY1 hYN
  rw [← hC'] at h
  have hpow : (Y : ℝ) ^ (α - 2) ≤ y ^ (α - 2) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hYy (by linarith)
  have hNy : (N : ℝ) * y ^ (α - 2) = y := by
    have hN0 : (0 : ℝ) < N := by linarith
    rw [hy]
    calc (N : ℝ) * ((N : ℝ) ^ θ) ^ (α - 2) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (θ * (α - 2)) := by
          rw [Real.rpow_one, ← Real.rpow_mul hN0.le]
      _ = (N : ℝ) ^ θ := by
          rw [← Real.rpow_add hN0]
          congr 1
          rw [hθ]; field_simp; ring
  calc |squarefreeCountingError N| ≤ (Y : ℝ) + C' * ((N : ℝ) * (Y : ℝ) ^ (α - 2)) := h
    _ ≤ (y + 1) + C' * ((N : ℝ) * y ^ (α - 2)) := by
        gcongr
    _ = (y + 1) + C' * y := by rw [hNy]
    _ ≤ (2 + C') * y := by nlinarith
    _ = (2 + C') * (N : ℝ) ^ (1 / (3 - α)) := rfl


lemma Mr_eq_mertens (k : ℕ) : Mr k = (Mertens.mertens (k : ℝ) : ℝ) := by
  unfold Mr Mertens.mertens
  rw [Nat.floor_natCast]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]
    push_cast; ring

/-- **Axer (1911)**: RH implies `E(x) = O(x^{2/5+ε})` for every `ε > 0`. -/
theorem axer_of_RH (hRH : RiemannHypothesis) : AxerBound := by
  intro ε hε
  set ε₁ : ℝ := min ε (1 / 12) with hε₁
  have h0 : 0 < ε₁ := lt_min hε (by norm_num)
  have h1 : ε₁ ≤ ε := min_le_left _ _
  have h2 : ε₁ ≤ 1 / 12 := min_le_right _ _
  obtain ⟨K, hK0, hK⟩ := Mertens.abs_mertens_nat_le hRH h0 (by linarith)
  set α : ℝ := 1 / 2 + 3 * ε₁ with hα
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hα2 : α < 2 := by rw [hα]; linarith
  have hM : MBound K α := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Mr]; positivity
    · rw [Mr_eq_mertens]; exact hK k hk
  obtain ⟨C, hC0, hC⟩ := squarefreeError_le hα0 hα2 hM
  have hθ : 1 / (3 - α) ≤ 2 / 5 + ε := by
    have h3 : 0 < 3 - α := by linarith
    rw [div_le_iff₀ h3, hα]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 3 - (1 / 2 + 3 * ε₁)),
      mul_nonneg h0.le (by linarith : (0 : ℝ) ≤ 13 / 10 - 3 * ε₁)]
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [Real.norm_eq_abs, abs_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc |squarefreeCountingError N| ≤ C * (N : ℝ) ^ (1 / (3 - α)) := hC N hN
    _ ≤ C * (N : ℝ) ^ (2 / 5 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN' hθ) hC0


/-- A free corollary: under RH, `E(x) = o(√x)`, the conclusion of the formal-conjectures statement
`erdos_969.variants.prime_number_theorem` (which is a theorem of the literature, via the prime
number theorem; the proof here is the weaker one, through RH). -/
theorem erdos_969_prime_number_theorem_of_RH (hRH : RiemannHypothesis) :
    (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ).sqrt) := by
  refine (axer_of_RH hRH (1 / 20) (by norm_num)).trans_isLittleO ?_
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · have : (x : ℝ) = 0 := by
      rw [Real.sqrt_eq_zero (Nat.cast_nonneg _)] at hx; exact hx
    rw [this]; norm_num
  · have h : Tendsto (fun x : ℕ => (x : ℝ) ^ (-(1 / 20 : ℝ))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx' : (0 : ℝ) < x := by exact_mod_cast hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx']
    congr 1; norm_num

end Erdos969
