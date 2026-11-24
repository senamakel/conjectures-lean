import Erdos969.Series
import Erdos969.Statement2

/-!
# The Dirichlet series for `1/ζ(k)` and its tail, from a Mertens bound

* `hasSum_moebius_pow`: `∑ μ(n)/n^k = 1/ζ(k)` for `k ≥ 2`.
* `abs_weight_diff_le_pow`: `|1/(u+1)^k − 1/u^k| ≤ k/u^{k+1}`.
* `abs_tail_le_pow`: if `|M(m)| ≤ K (m+1)^α` with `0 ≤ α < k`, the tail
  `|1/ζ(k) − ∑_{d ≤ Y} μ(d)/d^k|` is at most `C Y^{α−k}` (Abel summation). This is
  `Erdos969.abs_tail_le` with `2` replaced by `k`.
-/

namespace Erdos969.KFree

open Finset ArithmeticFunction LSeries Complex
open scoped LSeries.notation ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem hasSum_moebius_pow {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun n : ℕ => (μ n : ℝ) / ((n : ℝ) ^ k)) (1 / (riemannZeta k).re) := by
  have hs : 1 < ((k : ℂ)).re := by
    simp only [Complex.natCast_re]; exact_mod_cast hk
  have hsum : LSeriesSummable ↗μ k := LSeriesSummable_moebius_iff.2 hs
  have h := hsum.LSeriesHasSum
  have hterm : ∀ n : ℕ, LSeries.term ↗μ k n = (((μ n : ℝ) / ((n : ℝ) ^ k) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      rw [Complex.cpow_natCast]
  have h' : HasSum (fun n : ℕ => (((μ n : ℝ) / ((n : ℝ) ^ k) : ℝ) : ℂ)) (L ↗μ k) := by
    have e : (fun n : ℕ => (((μ n : ℝ) / ((n : ℝ) ^ k) : ℝ) : ℂ)) = LSeries.term ↗μ k :=
      (funext hterm).symm
    rw [e]; exact h
  have hre : HasSum (fun n : ℕ => (μ n : ℝ) / ((n : ℝ) ^ k)) (L ↗μ k).re := by
    have := Complex.hasSum_re h'
    simp only [Complex.ofReal_re] at this
    exact this
  set S := (L ↗μ k).re with hSdef
  have hL : L ↗μ k = (S : ℂ) := h'.unique (Complex.hasSum_ofReal.2 hre)
  have hmul := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, hL] at hmul
  have hS : (S : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact zero_ne_one hmul
  have hz : riemannZeta k = ((1 / S : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff hS]
    exact hmul
  rw [hz, Complex.ofReal_re, one_div_one_div]
  exact hre

lemma pow_sub_pow_le_mul {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (n : ℕ) :
    x ^ n - y ^ n ≤ n * x ^ (n - 1) * (x - y) := by
  rw [← geom_sum₂_mul]
  refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 hyx)
  calc ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) ≤ ∑ _i ∈ range n, x ^ (n - 1) := by
        refine sum_le_sum fun i hi => ?_
        have hi' := mem_range.1 hi
        calc x ^ i * y ^ (n - 1 - i) ≤ x ^ i * x ^ (n - 1 - i) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyx _) (pow_nonneg (hy.trans hyx) _)
          _ = x ^ (n - 1) := by rw [← pow_add]; congr 1; omega
    _ = n * x ^ (n - 1) := by simp

lemma abs_weight_diff_le_pow (k : ℕ) {u : ℝ} (hu : 0 < u) :
    |1 / (u + 1) ^ k - 1 / u ^ k| ≤ k / u ^ (k + 1) := by
  have hle : 1 / (u + 1) ^ k ≤ 1 / u ^ k :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hu.le (by linarith) k)
  rw [abs_of_nonpos (by linarith), neg_sub, div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := pow_sub_pow_le_mul hu.le (by linarith : u ≤ u + 1) (j + 1)
  rw [show u + 1 - u = 1 by ring, mul_one, Nat.add_sub_cancel] at h
  calc (1 * (u + 1) ^ (j + 1) - u ^ (j + 1) * 1) * u ^ (j + 1 + 1)
      = ((u + 1) ^ (j + 1) - u ^ (j + 1)) * u ^ (j + 1 + 1) := by ring
    _ ≤ (((j + 1 : ℕ) : ℝ) * (u + 1) ^ j) * u ^ (j + 1 + 1) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = ((j + 1 : ℕ) : ℝ) * (u ^ (j + 1) * ((u + 1) ^ j * u)) := by ring
    _ ≤ ((j + 1 : ℕ) : ℝ) * (u ^ (j + 1) * ((u + 1) ^ j * (u + 1))) := by
        gcongr; linarith
    _ = ((j + 1 : ℕ) : ℝ) * (u ^ (j + 1) * (u + 1) ^ (j + 1)) := by ring

/-- The tail of the series for `1/ζ(k)`, from a Mertens bound. -/
theorem abs_tail_le_pow {k : ℕ} (hk : 2 ≤ k) {K α : ℝ} (hα0 : 0 ≤ α) (hαk : α < k)
    (hM : MBound K α) {Y : ℕ} (hY : 1 ≤ Y) :
    |1 / (riemannZeta k).re - ∑ d ∈ Icc 1 Y, (μ d : ℝ) / ((d : ℝ) ^ k)| ≤
      (2 * K * 2 ^ α * (1 + k / (k - α))) * (Y : ℝ) ^ (α - k) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hkα : 0 < (k : ℝ) - α := by linarith
  set K1 : ℝ := 2 * K * 2 ^ α with hK1
  have hK1' : 0 ≤ K1 := by positivity
  set c : ℕ → ℝ := fun j => (μ (Y + 1 + j) : ℝ) with hc
  set w : ℕ → ℝ := fun j => 1 / (((Y + 1 + j : ℕ) : ℝ)) ^ k with hw
  set a : ℕ → ℝ := fun d => (μ d : ℝ) / ((d : ℝ) ^ k) with ha
  have hB : ∀ n, ∑ j ∈ range (n + 1), c j = Mr (Y + n + 1) - Mr Y := by
    intro n
    unfold Mr
    have : Y + n + 1 + 1 = (Y + 1) + (n + 1) := by omega
    rw [this, sum_range_add (fun x => (μ x : ℝ)) (Y + 1) (n + 1)]; simp only [hc]; ring
  have hcw : ∀ j, c j * w j = a (Y + 1 + j) := by
    intro j; simp only [hc, hw, ha]; rw [mul_one_div]
  have hpart : ∀ N : ℕ, |∑ j ∈ range (N + 1), a (Y + 1 + j)| ≤
      K1 * (1 + k / (k - α)) * (Y : ℝ) ^ (α - k) := by
    intro N
    have hab := Mertens.abel_identity c w N
    rw [show ∑ j ∈ range (N + 1), a (Y + 1 + j) = ∑ j ∈ range (N + 1), c j * w j from
      sum_congr rfl fun j _ => (hcw j).symm, hab]
    have hu : ∀ n : ℕ, (1 : ℝ) ≤ (Y : ℝ) + n + 1 := fun n => by
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hw0 : ∀ n : ℕ, w n = 1 / ((Y : ℝ) + n + 1) ^ k := fun n => by
      simp only [hw]; push_cast; ring_nf
    have hwd : ∀ n : ℕ, |w (n + 1) - w n| ≤ k / ((Y : ℝ) + n + 1) ^ (k + 1) := fun n => by
      have : w (n + 1) = 1 / (((Y : ℝ) + n + 1) + 1) ^ k := by
        simp only [hw]; push_cast; ring_nf
      rw [this, hw0 n]; exact abs_weight_diff_le_pow k (by linarith [hu n])
    have hterm : ∀ n : ℕ, |(∑ j ∈ range (n + 1), c j) * (w (n + 1) - w n)| ≤
        k * K1 * ((Y : ℝ) + n + 1) ^ (-((k : ℝ) + 1 - α)) := fun n => by
      have hpos : 0 < (Y : ℝ) + n + 1 := by linarith [hu n]
      rw [abs_mul, hB n]
      have h1 := abs_Mr_sub_le' hα0 hM Y n
      have h2 := hwd n
      calc |Mr (Y + n + 1) - Mr Y| * |w (n + 1) - w n|
          ≤ (K1 * ((Y : ℝ) + n + 1) ^ α) * (k / ((Y : ℝ) + n + 1) ^ (k + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = k * K1 * ((Y : ℝ) + n + 1) ^ (-((k : ℝ) + 1 - α)) := by
            rw [show -((k : ℝ) + 1 - α) = α - ((k + 1 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_sub hpos, Real.rpow_natCast]
            ring
    have hfirst : |(∑ j ∈ range (N + 1), c j) * w N| ≤ K1 * (Y : ℝ) ^ (α - k) := by
      have hpos : 0 < (Y : ℝ) + N + 1 := by linarith [hu N]
      rw [abs_mul, hB N, hw0 N, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((Y : ℝ) + N + 1) ^ k)]
      calc |Mr (Y + N + 1) - Mr Y| * (1 / ((Y : ℝ) + N + 1) ^ k)
          ≤ (K1 * ((Y : ℝ) + N + 1) ^ α) * (1 / ((Y : ℝ) + N + 1) ^ k) :=
            mul_le_mul_of_nonneg_right (abs_Mr_sub_le' hα0 hM Y N) (by positivity)
        _ = K1 * ((Y : ℝ) + N + 1) ^ (α - k) := by
            rw [Real.rpow_sub hpos, Real.rpow_natCast]
            ring
        _ ≤ K1 * (Y : ℝ) ^ (α - k) := by
            exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < Y)
              (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (Y : ℝ) ≤ (Y : ℝ) + N + 1)
              (by linarith : α - k ≤ 0)) hK1'
    have hsum : |∑ n ∈ range N, (∑ j ∈ range (n + 1), c j) * (w (n + 1) - w n)| ≤
        k * K1 / (k - α) * (Y : ℝ) ^ (α - k) := by
      calc _ ≤ ∑ n ∈ range N, |(∑ j ∈ range (n + 1), c j) * (w (n + 1) - w n)| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ range N, k * K1 * ((Y : ℝ) + n + 1) ^ (-((k : ℝ) + 1 - α)) :=
            sum_le_sum fun n _ => hterm n
        _ = k * K1 * ∑ n ∈ range N, ((Y : ℝ) + n + 1) ^ (-((k : ℝ) + 1 - α)) := by rw [mul_sum]
        _ ≤ k * K1 * ((Y : ℝ) ^ (1 - ((k : ℝ) + 1 - α)) / (((k : ℝ) + 1 - α) - 1)) :=
            mul_le_mul_of_nonneg_left (sum_rpow_neg_le_of_gt (by linarith) Y hY N) (by positivity)
        _ = k * K1 / (k - α) * (Y : ℝ) ^ (α - k) := by
            rw [show 1 - ((k : ℝ) + 1 - α) = α - k by ring,
              show ((k : ℝ) + 1 - α) - 1 = k - α by ring]; ring
    calc |(∑ j ∈ range (N + 1), c j) * w N -
          ∑ n ∈ range N, (∑ j ∈ range (n + 1), c j) * (w (n + 1) - w n)|
        ≤ |(∑ j ∈ range (N + 1), c j) * w N| +
          |∑ n ∈ range N, (∑ j ∈ range (n + 1), c j) * (w (n + 1) - w n)| := abs_sub _ _
      _ ≤ K1 * (Y : ℝ) ^ (α - k) + k * K1 / (k - α) * (Y : ℝ) ^ (α - k) :=
          add_le_add hfirst hsum
      _ = K1 * (1 + k / (k - α)) * (Y : ℝ) ^ (α - k) := by ring
  have hS := (hasSum_moebius_pow hk).tendsto_sum_nat
  have hSY : ∑ d ∈ Icc 1 Y, a d = ∑ d ∈ range (Y + 1), a d := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    have h0 : a 0 = 0 := by simp [ha]
    rw [h0, zero_add]
    rfl
  rw [hSY]
  have hlim : Filter.Tendsto (fun N : ℕ => ∑ d ∈ range (Y + 1 + (N + 1)), a d) Filter.atTop
      (nhds (1 / (riemannZeta k).re)) :=
    hS.comp (Filter.tendsto_atTop_mono (fun N : ℕ => (by omega : N ≤ Y + 1 + (N + 1)))
      Filter.tendsto_id)
  have h2 : Filter.Tendsto
      (fun N : ℕ => |∑ d ∈ range (Y + 1 + (N + 1)), a d - ∑ d ∈ range (Y + 1), a d|)
      Filter.atTop (nhds |1 / (riemannZeta k).re - ∑ d ∈ range (Y + 1), a d|) :=
    (hlim.sub_const _).abs
  refine le_of_tendsto' h2 fun N => ?_
  have h3 := hpart N
  have h4 := sum_range_add a (Y + 1) (N + 1)
  rw [h4]
  simpa using h3

end Erdos969.KFree
