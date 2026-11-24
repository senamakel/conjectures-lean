import Erdos969.Series

/-!
# The hyperbola split

For `Y ≤ N`, the part `∑_{Y < d ≤ N} μ(d) ⌊N/d²⌋` of `Q(N)` is bounded through the Mertens function,
by writing `⌊N/d²⌋ = #{m ≥ 1 : m d² ≤ N}` and exchanging the sums over `d` and `m`.
-/

namespace Erdos969

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma card_filter_sqrt (N d : ℕ) (hd : 1 ≤ d) :
    ((Icc 1 N).filter (fun m => d ≤ Nat.sqrt (N / m))).card = N / (d * d) := by
  have hdd : 0 < d * d := Nat.mul_pos hd hd
  have : (Icc 1 N).filter (fun m => d ≤ Nat.sqrt (N / m)) = Icc 1 (N / (d * d)) := by
    ext m
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      rw [Nat.le_div_iff_mul_le hdd]
      have h4 : d * d ≤ N / m := Nat.le_sqrt.1 h3
      rw [Nat.le_div_iff_mul_le (by omega)] at h4
      linarith
    · rintro ⟨h1, h2⟩
      rw [Nat.le_div_iff_mul_le hdd] at h2
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · nlinarith
      · apply Nat.le_sqrt.2
        rw [Nat.le_div_iff_mul_le (by omega)]
        linarith
  rw [this]; simp

lemma T_eq (N Y : ℕ) :
    ∑ d ∈ Ioc Y N, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 N, ∑ d ∈ Ioc Y (Nat.sqrt (N / m)), (μ d : ℝ) := by
  have h1 : ∀ d ∈ Ioc Y N, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 N, if d ≤ Nat.sqrt (N / m) then (μ d : ℝ) else 0 := by
    intro d hd
    have hd1 : 1 ≤ d := by have := (mem_Ioc.1 hd).1; omega
    rw [← sum_filter, sum_const, card_filter_sqrt N d hd1]
    simp [mul_comm]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  have hm' := mem_Icc.1 hm
  have hs : Nat.sqrt (N / m) ≤ N := (Nat.sqrt_le_self _).trans (Nat.div_le_self _ _)
  ext d
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hs⟩, h3⟩

lemma inner_eq_zero {N Y m : ℕ} (hY : 1 ≤ Y) (hm : 1 ≤ m) (h : N / (Y * Y) < m) :
    Ioc Y (Nat.sqrt (N / m)) = ∅ := by
  rw [Ioc_eq_empty_iff, not_lt]
  by_contra hlt
  rw [not_le] at hlt
  have h1 : (Y + 1) * (Y + 1) ≤ N / m := Nat.le_sqrt.1 hlt
  rw [Nat.le_div_iff_mul_le (by omega)] at h1
  have h2 : m ≤ N / (Y * Y) := by
    rw [Nat.le_div_iff_mul_le (Nat.mul_pos hY hY)]
    nlinarith
  omega


lemma sqrt_succ_rpow_le {α : ℝ} (hα : 0 ≤ α) {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    ((Nat.sqrt (N / m) : ℝ) + 1) ^ α ≤ 2 ^ α * ((N : ℝ) / m) ^ (α / 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : (1 : ℝ) ≤ (N : ℝ) / m := by
    rw [le_div_iff₀ hm']; simpa using (by exact_mod_cast hmN : (m : ℝ) ≤ N)
  have hs2 : ((Nat.sqrt (N / m) : ℝ)) ^ 2 ≤ (N : ℝ) / m := by
    have h1 : Nat.sqrt (N / m) * Nat.sqrt (N / m) ≤ N / m := Nat.sqrt_le _
    have h2 : (((N / m : ℕ)) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
    calc ((Nat.sqrt (N / m) : ℝ)) ^ 2 = ((Nat.sqrt (N / m) * Nat.sqrt (N / m) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((N / m : ℕ)) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
  have hs : (Nat.sqrt (N / m) : ℝ) ≤ Real.sqrt ((N : ℝ) / m) := by
    have := Real.abs_le_sqrt hs2
    rwa [abs_of_nonneg (Nat.cast_nonneg _)] at this
  have h1 : (1 : ℝ) ≤ Real.sqrt ((N : ℝ) / m) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hr
  have h2 : (Nat.sqrt (N / m) : ℝ) + 1 ≤ 2 * ((N : ℝ) / m) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; linarith
  calc ((Nat.sqrt (N / m) : ℝ) + 1) ^ α ≤ (2 * ((N : ℝ) / m) ^ (1 / 2 : ℝ)) ^ α :=
        Real.rpow_le_rpow (by positivity) h2 hα
    _ = 2 ^ α * ((N : ℝ) / m) ^ (α / 2) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
        congr 2; ring

lemma sum_Icc_rpow (β : ℝ) (X : ℕ) :
    ∑ m ∈ Icc 1 X, (m : ℝ) ^ (-β) = ∑ i ∈ range X, ((i : ℝ) + 1) ^ (-β) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]
    push_cast; rfl


lemma sum_Ioc_moebius {Y s : ℕ} (h : Y ≤ s) :
    ∑ d ∈ Ioc Y s, (μ d : ℝ) = Mr s - Mr Y := by
  have : Ioc Y s = Ico (Y + 1) (s + 1) := by ext d; simp only [mem_Ioc, mem_Ico]; omega
  rw [this, sum_Ico_eq_sub _ (by omega)]
  rfl

lemma abs_inner_le {K α : ℝ} (hM : MBound K α) (Y s : ℕ) :
    |∑ d ∈ Ioc Y s, (μ d : ℝ)| ≤ K * ((s : ℝ) + 1) ^ α + K * ((Y : ℝ) + 1) ^ α := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  by_cases h : Y ≤ s
  · rw [sum_Ioc_moebius h]
    exact (abs_sub _ _).trans (add_le_add (hM s) (hM Y))
  · rw [Ioc_eq_empty (by omega)]
    simp only [sum_empty, abs_zero]
    positivity

/-- The key rpow algebra: `N^β (N/Y²)^{1-β} = N Y^{2β-2}`. -/
lemma rpow_alg {β : ℝ} (N Y : ℝ) (hN : 0 < N) (hY : 0 < Y) :
    N ^ β * (N / Y ^ 2) ^ (1 - β) = N * Y ^ (2 * β - 2) := by
  rw [Real.div_rpow hN.le (by positivity), show (Y ^ 2 : ℝ) = Y ^ (2 : ℝ) by norm_cast,
    ← Real.rpow_mul hY.le]
  have h1 : N ^ β * N ^ (1 - β) = N := by
    rw [← Real.rpow_add hN]; simp
  have h2 : Y ^ (2 * β - 2) = (Y ^ ((2 : ℝ) * (1 - β)))⁻¹ := by
    rw [← Real.rpow_neg hY.le]; congr 1; ring
  rw [h2]
  calc N ^ β * (N ^ (1 - β) / Y ^ ((2 : ℝ) * (1 - β)))
      = (N ^ β * N ^ (1 - β)) * (Y ^ ((2 : ℝ) * (1 - β)))⁻¹ := by rw [div_eq_mul_inv]; ring
    _ = _ := by rw [h1]

/-- **The hyperbola bound.** -/
theorem abs_T_le {K α : ℝ} (hα0 : 0 ≤ α) (hα2 : α < 2) (hM : MBound K α) {N Y : ℕ}
    (hY : 1 ≤ Y) (hYN : Y ≤ N) :
    |∑ d ∈ Ioc Y N, (μ d : ℝ) * ((N / (d * d) : ℕ) : ℝ)| ≤
      (K * 2 ^ α * (1 / (1 - α / 2) + 1)) * ((N : ℝ) * (Y : ℝ) ^ (α - 2)) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hN' : (1 : ℝ) ≤ N := hY'.trans (by exact_mod_cast hYN)
  set X := N / (Y * Y) with hX
  set β := α / 2 with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hXN : X ≤ N := (Nat.div_le_self _ _)
  have hXr : (X : ℝ) ≤ (N : ℝ) / (Y : ℝ) ^ 2 := by
    have : ((N / (Y * Y) : ℕ) : ℝ) ≤ (N : ℝ) / ((Y * Y : ℕ) : ℝ) := Nat.cast_div_le
    simpa [pow_two] using this
  rw [T_eq]
  calc |∑ m ∈ Icc 1 N, ∑ d ∈ Ioc Y (Nat.sqrt (N / m)), (μ d : ℝ)|
      ≤ ∑ m ∈ Icc 1 N, |∑ d ∈ Ioc Y (Nat.sqrt (N / m)), (μ d : ℝ)| := abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Icc 1 X, |∑ d ∈ Ioc Y (Nat.sqrt (N / m)), (μ d : ℝ)| := by
        symm
        refine sum_subset (Icc_subset_Icc le_rfl hXN) fun m hm hm' => ?_
        have hm1 := mem_Icc.1 hm
        have : ¬ (1 ≤ m ∧ m ≤ X) := fun h => hm' (mem_Icc.2 h)
        rw [inner_eq_zero hY hm1.1 (by omega)]; simp
    _ ≤ ∑ m ∈ Icc 1 X, (K * 2 ^ α * ((N : ℝ) / m) ^ β + K * 2 ^ α * (Y : ℝ) ^ α) := by
        refine sum_le_sum fun m hm => ?_
        have hm1 := mem_Icc.1 hm
        refine (abs_inner_le hM Y _).trans ?_
        have hmN : m ≤ N := hm1.2.trans hXN
        have h1 := sqrt_succ_rpow_le hα0 hm1.1 hmN
        have h2 : ((Y : ℝ) + 1) ^ α ≤ 2 ^ α * (Y : ℝ) ^ α := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
          exact Real.rpow_le_rpow (by positivity) (by linarith) hα0
        calc K * ((Nat.sqrt (N / m) : ℝ) + 1) ^ α + K * ((Y : ℝ) + 1) ^ α
            ≤ K * (2 ^ α * ((N : ℝ) / m) ^ β) + K * (2 ^ α * (Y : ℝ) ^ α) := by gcongr
          _ = _ := by ring
    _ = K * 2 ^ α * ((N : ℝ) ^ β * ∑ m ∈ Icc 1 X, (m : ℝ) ^ (-β)) + (X : ℝ) * (K * 2 ^ α * (Y : ℝ) ^ α) := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_sum, mul_sum]
        congr 1
        refine sum_congr rfl fun m hm => ?_
        have hm' : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.1 hm).1
        rw [Real.div_rpow (by positivity) hm'.le, Real.rpow_neg hm'.le]
        field_simp
    _ ≤ K * 2 ^ α * ((N : ℝ) ^ β * ((X : ℝ) ^ (1 - β) / (1 - β))) + (N / (Y : ℝ) ^ 2) * (K * 2 ^ α * (Y : ℝ) ^ α) := by
        rw [sum_Icc_rpow]
        have := sum_rpow_neg_le hβ0 hβ1 X
        gcongr
    _ ≤ K * 2 ^ α * ((N : ℝ) ^ β * (((N : ℝ) / (Y : ℝ) ^ 2) ^ (1 - β) / (1 - β))) + (N / (Y : ℝ) ^ 2) * (K * 2 ^ α * (Y : ℝ) ^ α) := by
        have hb : 0 < 1 - β := by linarith
        gcongr
    _ = (K * 2 ^ α * (1 / (1 - α / 2) + 1)) * ((N : ℝ) * (Y : ℝ) ^ (α - 2)) := by
        have hN0 : (0 : ℝ) < N := by linarith
        have hY0 : (0 : ℝ) < Y := by linarith
        have e1 := rpow_alg (β := β) (N : ℝ) (Y : ℝ) hN0 hY0
        have e2 : (Y : ℝ) ^ (α - 2) * ((Y : ℝ) ^ 2) = (Y : ℝ) ^ α := by
          rw [show (Y : ℝ) ^ 2 = (Y : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hY0]; congr 1; ring
        have e3 : 2 * β - 2 = α - 2 := by rw [hβ]; ring
        rw [e3] at e1
        calc K * 2 ^ α * ((N : ℝ) ^ β * (((N : ℝ) / (Y : ℝ) ^ 2) ^ (1 - β) / (1 - β))) +
              (N / (Y : ℝ) ^ 2) * (K * 2 ^ α * (Y : ℝ) ^ α)
            = K * 2 ^ α * (((N : ℝ) ^ β * ((N : ℝ) / (Y : ℝ) ^ 2) ^ (1 - β)) / (1 - β)) +
              (N / (Y : ℝ) ^ 2) * (K * 2 ^ α * ((Y : ℝ) ^ (α - 2) * (Y : ℝ) ^ 2)) := by rw [e2]; ring
          _ = _ := by rw [e1, hβ]; field_simp

end Erdos969
