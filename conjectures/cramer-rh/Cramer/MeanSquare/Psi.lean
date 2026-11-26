import Erdos233.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Mean square, step 3: `ψ` against the first difference of `psi1`

* `h ψ(y) ≤ psi1(y + h) − psi1(y) ≤ h ψ(y + h)` for `y, h ≥ 0`, since `psi1 = ∫ ψ`;
* `ψ(y + 4) − ψ(y) ≤ 4 log(y + 4)`;
* `(ψ(x) − x)²` is interval integrable (`ψ` is monotone).
-/

namespace Cramer.MeanSq

open ArithmeticFunction Erdos233 Chebyshev Finset

lemma psi1_eq_sum_max {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    psi1 t = ∑ n ∈ range (N + 1), (Λ n : ℝ) * max (t - n) 0 := by
  unfold psi1
  calc ∑ n ∈ range (⌊t⌋₊ + 1), (Λ n : ℝ) * (t - n)
      = ∑ n ∈ range (⌊t⌋₊ + 1), (Λ n : ℝ) * max (t - n) 0 := by
        refine sum_congr rfl fun n hn => ?_
        have h1 : n ≤ ⌊t⌋₊ := Nat.lt_succ_iff.1 (mem_range.1 hn)
        have h2 : (n : ℝ) ≤ t := (Nat.le_floor_iff ht).1 h1
        rw [max_eq_left (by linarith)]
    _ = ∑ n ∈ range (N + 1), (Λ n : ℝ) * max (t - n) 0 := by
        refine sum_subset (range_subset_range.2 (by omega)) fun n _ hn => ?_
        have h1 : ⌊t⌋₊ < n := by
          simp only [mem_range, not_lt] at hn; omega
        have h2 : t < n := Nat.lt_of_floor_lt h1
        rw [max_eq_right (by linarith), mul_zero]

lemma psi_eq_sum_ind {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    ψ t = ∑ n ∈ range (N + 1), (Λ n : ℝ) * (if (n : ℝ) ≤ t then 1 else 0) := by
  rw [psi_eq_sum_Icc]
  have e : Icc 0 ⌊t⌋₊ = (range (N + 1)).filter (fun n : ℕ => (n : ℝ) ≤ t) := by
    ext n
    simp only [mem_Icc, mem_filter, mem_range, ← Nat.le_floor_iff ht]
    omega
  rw [e, sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

lemma tri (n y h : ℝ) (hh : 0 ≤ h) :
    h * (if n ≤ y then 1 else 0) ≤ max (y + h - n) 0 - max (y - n) 0 ∧
      max (y + h - n) 0 - max (y - n) 0 ≤ h * (if n ≤ y + h then 1 else 0) := by
  constructor
  · split_ifs with h1
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (b := (0 : ℝ)) (by linarith : y - n ≤ 0)]
      simp only [mul_zero, sub_zero]; exact le_max_right _ _
  · split_ifs with h1
    · rw [mul_one]
      have : y + h - n - (y - n) = h := by ring
      have h3 : max (y + h - n) 0 ≤ max (y - n) 0 + h := by
        rcases le_total 0 (y - n) with h4 | h4
        · rw [max_eq_left (by linarith), max_eq_left h4]; linarith
        · rw [max_eq_right h4]; exact max_le (by linarith) (by linarith)
      linarith
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; simp

theorem psi1_diff_bounds {y h : ℝ} (hy : 0 ≤ y) (hh : 0 ≤ h) :
    h * ψ y ≤ psi1 (y + h) - psi1 y ∧ psi1 (y + h) - psi1 y ≤ h * ψ (y + h) := by
  set N := ⌊y + h⌋₊
  have hN : ⌊y⌋₊ ≤ N := Nat.floor_mono (by linarith)
  have hyh : 0 ≤ y + h := by linarith
  rw [psi1_eq_sum_max hyh le_rfl, psi1_eq_sum_max hy hN, psi_eq_sum_ind hy hN,
    psi_eq_sum_ind hyh le_rfl, mul_sum, mul_sum, ← sum_sub_distrib]
  constructor
  · refine sum_le_sum fun n _ => ?_
    have := (tri n y h hh).1
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    rw [← mul_sub]
    nlinarith
  · refine sum_le_sum fun n _ => ?_
    have := (tri n y h hh).2
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    rw [← mul_sub]
    nlinarith

theorem psi_add_four_sub_le {y : ℝ} (hy : 0 ≤ y) :
    ψ (y + 4) - ψ y ≤ 4 * Real.log (y + 4) := by
  set m := ⌊y⌋₊ with hm
  have hf : ⌊y + 4⌋₊ = m + 4 := by
    have := Nat.floor_add_natCast hy 4
    simpa using this
  have hmy : (m : ℝ) ≤ y := Nat.floor_le hy
  unfold psi
  rw [hf, ← sum_Ioc_consecutive _ (Nat.zero_le m) (by omega : m ≤ m + 4), add_sub_cancel_left]
  have hb : ∀ n ∈ Ioc m (m + 4), (Λ n : ℝ) ≤ Real.log (y + 4) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ioc.1 hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hn2 : (n : ℝ) ≤ y + 4 := by
      have : (n : ℝ) ≤ m + 4 := by exact_mod_cast h2
      linarith
    exact vonMangoldt_le_log.trans (Real.log_le_log (by linarith) hn2)
  calc ∑ n ∈ Ioc m (m + 4), (Λ n : ℝ) ≤ #(Ioc m (m + 4)) • Real.log (y + 4) :=
        sum_le_card_nsmul _ _ _ hb
    _ = 4 * Real.log (y + 4) := by
        rw [Nat.card_Ioc, show m + 4 - m = 4 by omega, nsmul_eq_mul]; norm_num

theorem intervalIntegrable_sq (a b : ℝ) :
    IntervalIntegrable (fun x => (ψ x - x) ^ 2) MeasureTheory.volume a b := by
  have hm : Monotone fun x => ψ x ^ 2 := fun u v huv =>
    pow_le_pow_left₀ (psi_nonneg u) (psi_mono huv) 2
  have h1 : IntervalIntegrable (fun x => ψ x ^ 2) MeasureTheory.volume a b := hm.intervalIntegrable
  have h2 : IntervalIntegrable (fun x => x * ψ x) MeasureTheory.volume a b :=
    (psi_mono.intervalIntegrable).continuousOn_mul continuousOn_id
  have h3 : IntervalIntegrable (fun x : ℝ => x ^ 2) MeasureTheory.volume a b :=
    (continuous_pow 2).intervalIntegrable _ _
  have e : (fun x => (ψ x - x) ^ 2) = fun x => ψ x ^ 2 - 2 * (x * ψ x) + x ^ 2 := by
    funext x; ring
  rw [e]
  exact (h1.sub (h2.const_mul 2)).add h3

end Cramer.MeanSq
