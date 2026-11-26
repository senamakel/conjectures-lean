import Erdos969.KFree.Hyperbola
import Erdos969.KFree.Identity
import Erdos969.Main

/-!
# Axer's bound for `k`-free numbers, from a bound on the Mertens function

* `abs_error_le_pow`: for `1 ≤ Y ≤ N`, `|E_k(N)| ≤ Y + C N Y^{α-k}` whenever `|M(m)| ≤ K (m+1)^α`.
* `kFreeError_le`: choosing `Y ≍ N^{1/(k+1-α)}` gives `|E_k(N)| ≤ C N^{1/(k+1-α)}`.
* `axerKFree_of_RH`: with `α = 1/2 + ε` from `Mertens.abs_mertens_nat_le`,
  `E_k(x) = O(x^{2/(2k+1)+ε})` for every `k ≥ 2`.
* `axerKFreeBound_two_iff`: at `k = 2` the new target is `AxerBound`.

The argument is `Erdos969.Main` with `2` replaced by `k`; at `k = 2` it gives back `2/5`.
-/

namespace Erdos969.KFree

open Finset ArithmeticFunction Filter Asymptotics
open scoped ArithmeticFunction.Moebius

/-- Error decomposition for a fixed split point `Y`. -/
theorem abs_error_le_pow {k : ℕ} (hk : 2 ≤ k) {K α : ℝ} (hα0 : 0 ≤ α) (hαk : α < k)
    (hM : MBound K α) {N Y : ℕ} (hY : 1 ≤ Y) (hYN : Y ≤ N) :
    |kFreeCountingError k N| ≤ (Y : ℝ) +
      (2 * K * 2 ^ α * (1 + k / (k - α)) + K * 2 ^ α * (1 / (1 - α / k) + 1)) *
        ((N : ℝ) * (Y : ℝ) ^ (α - k)) := by
  have hk1 : 1 ≤ k := by omega
  have hQ : (kFreeCounting k N : ℝ) =
      ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) (kFreeCounting_eq hk1 N)
    push_cast at this
    exact this
  have hsplit : Icc 1 N = Icc 1 Y ∪ Ioc Y N := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 Y) (Ioc Y N) := by
    rw [Finset.disjoint_left]; intro d h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj] at hQ
  set T := ∑ d ∈ Ioc Y N, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) with hT
  set P := ∑ d ∈ Icc 1 Y, (μ d : ℝ) / ((d : ℝ) ^ k) with hP
  set R := ∑ d ∈ Icc 1 Y, (μ d : ℝ) * ((N : ℝ) / ((d : ℝ) ^ k) - ((N / d ^ k : ℕ) : ℝ)) with hR
  have hE : kFreeCountingError k N = -R + (N : ℝ) * (P - 1 / (riemannZeta k).re) + T := by
    unfold kFreeCountingError
    rw [hQ]
    have : ∑ d ∈ Icc 1 Y, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) = (N : ℝ) * P - R := by
      rw [hP, hR, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun d _ => ?_
      ring
    rw [this]; ring
  have hRb : |R| ≤ Y := by
    calc |R| ≤ ∑ d ∈ Icc 1 Y,
          |(μ d : ℝ) * ((N : ℝ) / ((d : ℝ) ^ k) - ((N / d ^ k : ℕ) : ℝ))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 Y, (1 : ℝ) := by
          refine sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
          have hdd : (0 : ℝ) < ((d ^ k : ℕ) : ℝ) := by
            have : 0 < d ^ k := Nat.pow_pos hd1
            exact_mod_cast this
          have hfl : ((N / d ^ k : ℕ) : ℝ) = ⌊(N : ℝ) / ((d ^ k : ℕ) : ℝ)⌋₊ := by
            rw [Nat.floor_div_eq_div]
          have hx : (N : ℝ) / ((d : ℝ) ^ k) = (N : ℝ) / ((d ^ k : ℕ) : ℝ) := by
            push_cast; ring_nf
          rw [abs_mul, hx, hfl]
          have h0 : 0 ≤ (N : ℝ) / ((d ^ k : ℕ) : ℝ) - ⌊(N : ℝ) / ((d ^ k : ℕ) : ℝ)⌋₊ :=
            sub_nonneg.2 (Nat.floor_le (by positivity))
          have h1 : (N : ℝ) / ((d ^ k : ℕ) : ℝ) - ⌊(N : ℝ) / ((d ^ k : ℕ) : ℝ)⌋₊ ≤ 1 := by
            have := Nat.lt_floor_add_one ((N : ℝ) / ((d ^ k : ℕ) : ℝ)); linarith
          rw [abs_of_nonneg h0]
          have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
          calc |(μ d : ℝ)| * _ ≤ 1 * 1 := mul_le_mul hmu h1 h0 zero_le_one
            _ = 1 := one_mul 1
      _ = Y := by simp
  have hPb := abs_tail_le_pow hk hα0 hαk hM hY
  have hTb := abs_T_le_pow hk1 hα0 hαk hM hY hYN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hE]
  have hPb' : |(N : ℝ) * (P - 1 / (riemannZeta k).re)| ≤
      (2 * K * 2 ^ α * (1 + k / (k - α))) * ((N : ℝ) * (Y : ℝ) ^ (α - k)) := by
    rw [abs_mul, abs_of_nonneg hN0, abs_sub_comm]
    calc (N : ℝ) * |1 / (riemannZeta k).re - P|
        ≤ (N : ℝ) * ((2 * K * 2 ^ α * (1 + k / (k - α))) * (Y : ℝ) ^ (α - k)) :=
          mul_le_mul_of_nonneg_left hPb hN0
      _ = _ := by ring
  calc |-R + (N : ℝ) * (P - 1 / (riemannZeta k).re) + T|
      ≤ |-R| + |(N : ℝ) * (P - 1 / (riemannZeta k).re)| + |T| := abs_add_three _ _ _
    _ ≤ Y + (2 * K * 2 ^ α * (1 + k / (k - α))) * ((N : ℝ) * (Y : ℝ) ^ (α - k)) +
          (K * 2 ^ α * (1 / (1 - α / k) + 1)) * ((N : ℝ) * (Y : ℝ) ^ (α - k)) := by
        rw [abs_neg]; linarith
    _ = _ := by ring

/-- With `Y ≍ N^{1/(k+1-α)}`: `E_k(N) ≪ N^{1/(k+1-α)}`. -/
theorem kFreeError_le {k : ℕ} (hk : 2 ≤ k) {K α : ℝ} (hα0 : 0 ≤ α) (hαk : α < k)
    (hM : MBound K α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |kFreeCountingError k N| ≤ C * (N : ℝ) ^ (1 / ((k : ℝ) + 1 - α)) := by
  set C' : ℝ := 2 * K * 2 ^ α * (1 + k / (k - α)) + K * 2 ^ α * (1 / (1 - α / k) + 1) with hC'
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hC'0 : 0 ≤ C' := by
    have h1 : 0 ≤ (k : ℝ) / (k - α) := by apply div_nonneg <;> linarith
    have h2 : 0 ≤ 1 / (1 - α / k) := by
      apply div_nonneg zero_le_one
      rw [sub_nonneg, div_le_one hk']; linarith
    positivity
  refine ⟨2 + C', by linarith, fun N hN => ?_⟩
  set θ : ℝ := 1 / ((k : ℝ) + 1 - α) with hθ
  have h3 : 0 < (k : ℝ) + 1 - α := by linarith
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
  have h := abs_error_le_pow hk hα0 hαk hM hY1 hYN
  rw [← hC'] at h
  have hpow : (Y : ℝ) ^ (α - k) ≤ y ^ (α - k) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hYy (by linarith)
  have hNy : (N : ℝ) * y ^ (α - k) = y := by
    have hN0 : (0 : ℝ) < N := by linarith
    rw [hy]
    calc (N : ℝ) * ((N : ℝ) ^ θ) ^ (α - k) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (θ * (α - k)) := by
          rw [Real.rpow_one, ← Real.rpow_mul hN0.le]
      _ = (N : ℝ) ^ θ := by
          rw [← Real.rpow_add hN0]
          congr 1
          rw [hθ]; field_simp; ring
  calc |kFreeCountingError k N| ≤ (Y : ℝ) + C' * ((N : ℝ) * (Y : ℝ) ^ (α - k)) := h
    _ ≤ (y + 1) + C' * ((N : ℝ) * y ^ (α - k)) := by
        gcongr
    _ = (y + 1) + C' * y := by rw [hNy]
    _ ≤ (2 + C') * y := by nlinarith
    _ = (2 + C') * (N : ℝ) ^ (1 / ((k : ℝ) + 1 - α)) := rfl

/-- **Axer (1911)** for `k`-free numbers: RH implies `E_k(x) = O(x^{2/(2k+1)+ε})` for every
`ε > 0` and every `k ≥ 2`. -/
theorem axerKFree_of_RH (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) : AxerKFreeBound k := by
  intro ε hε
  set ε₁ : ℝ := min ε (1 / 12) with hε₁
  have h0 : 0 < ε₁ := lt_min hε (by norm_num)
  have h1 : ε₁ ≤ ε := min_le_left _ _
  have h2 : ε₁ ≤ 1 / 12 := min_le_right _ _
  obtain ⟨K, hK0, hK⟩ := Mertens.abs_mertens_nat_le hRH (ε := ε₁ / 3) (by positivity)
    (by linarith)
  set α : ℝ := 1 / 2 + 3 * (ε₁ / 3) with hα
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hαk : α < k := by rw [hα]; linarith
  have hM : MBound K α := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Mr]; positivity
    · rw [Mr_eq_mertens]; exact hK m hm
  obtain ⟨C, hC0, hC⟩ := kFreeError_le hk hα0 hαk hM
  set t : ℝ := 2 / (2 * (k : ℝ) + 1) with htdef
  have ht : t * (2 * (k : ℝ) + 1) = 2 := by rw [htdef]; field_simp
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 2 / 5 := by
    rw [htdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hθ : 1 / ((k : ℝ) + 1 - α) ≤ t + ε := by
    have h3 : 0 < (k : ℝ) + 1 - α := by linarith
    rw [div_le_iff₀ h3]
    have key : (t + ε₁) * ((k : ℝ) + 1 - α) = 1 + ε₁ * ((k : ℝ) + 1 / 2 - t - ε₁) := by
      rw [hα]; linear_combination (1 / 2 : ℝ) * ht
    have hpos : 0 ≤ ε₁ * ((k : ℝ) + 1 / 2 - t - ε₁) :=
      mul_nonneg h0.le (by linarith)
    have hmono : (t + ε₁) * ((k : ℝ) + 1 - α) ≤ (t + ε) * ((k : ℝ) + 1 - α) :=
      mul_le_mul_of_nonneg_right (by linarith) h3.le
    linarith
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [Real.norm_eq_abs, abs_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc |kFreeCountingError k N| ≤ C * (N : ℝ) ^ (1 / ((k : ℝ) + 1 - α)) := hC N hN
    _ ≤ C * (N : ℝ) ^ (t + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN' hθ) hC0

/-- At `k = 2` the `k`-free target is Axer's squarefree target. -/
theorem axerKFreeBound_two_iff : AxerKFreeBound 2 ↔ AxerBound := by
  unfold AxerKFreeBound AxerBound
  have e : (2 : ℝ) / (2 * ((2 : ℕ) : ℝ) + 1) = 2 / 5 := by norm_num
  simp only [kFreeCountingError_two, e]

end Erdos969.KFree
