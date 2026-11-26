import Erdos969.Hyperbola
import Erdos969.KFree.Series

/-!
# The hyperbola split for `k`-free numbers

For `Y ≤ N`, the part `∑_{Y<d≤N} μ(d) ⌊N/d^k⌋` of `Q_k(N)` is bounded through the Mertens
function, by writing `⌊N/d^k⌋ = #{m ≥ 1 : m d^k ≤ N}` and exchanging the sums over `d` and `m`.
The inner sum runs over `Y < d ≤ ⌊(N/m)^{1/k}⌋`; `iroot k n` is the integer `k`-th root.
This is `Erdos969.abs_T_le` with `2` replaced by `k`.
-/

namespace Erdos969.KFree

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The integer `k`-th root `⌊n^{1/k}⌋`. -/
def iroot (k n : ℕ) : ℕ := Nat.findGreatest (fun d => d ^ k ≤ n) n

lemma iroot_le (k n : ℕ) : iroot k n ≤ n := Nat.findGreatest_le n

lemma le_iroot_iff {k n d : ℕ} (hk : 1 ≤ k) : d ≤ iroot k n ↔ d ^ k ≤ n := by
  constructor
  · intro h
    have hspec : (iroot k n) ^ k ≤ n := by
      unfold iroot
      exact Nat.findGreatest_spec (P := fun d => d ^ k ≤ n) (Nat.zero_le n)
        (by rw [zero_pow (by omega)]; exact Nat.zero_le n)
    exact (Nat.pow_le_pow_left h k).trans hspec
  · intro h
    unfold iroot
    refine Nat.le_findGreatest ?_ h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact Nat.zero_le _
    · exact (Nat.le_self_pow (by omega) d).trans h

lemma card_filter_iroot {k : ℕ} (hk : 1 ≤ k) (N d : ℕ) (hd : 1 ≤ d) :
    ((Icc 1 N).filter (fun m => d ≤ iroot k (N / m))).card = N / d ^ k := by
  have hdd : 0 < d ^ k := Nat.pow_pos hd
  have : (Icc 1 N).filter (fun m => d ≤ iroot k (N / m)) = Icc 1 (N / d ^ k) := by
    ext m
    simp only [mem_filter, mem_Icc, le_iroot_iff hk]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      rw [Nat.le_div_iff_mul_le hdd]
      rw [Nat.le_div_iff_mul_le (by omega)] at h3
      linarith
    · rintro ⟨h1, h2⟩
      rw [Nat.le_div_iff_mul_le hdd] at h2
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · nlinarith
      · rw [Nat.le_div_iff_mul_le (by omega)]
        linarith
  rw [this]; simp

lemma T_eq_pow {k : ℕ} (hk : 1 ≤ k) (N Y : ℕ) :
    ∑ d ∈ Ioc Y N, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 N, ∑ d ∈ Ioc Y (iroot k (N / m)), (μ d : ℝ) := by
  have h1 : ∀ d ∈ Ioc Y N, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 N, if d ≤ iroot k (N / m) then (μ d : ℝ) else 0 := by
    intro d hd
    have hd1 : 1 ≤ d := by have := (mem_Ioc.1 hd).1; omega
    rw [← sum_filter, sum_const, card_filter_iroot hk N d hd1]
    simp [mul_comm]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  have hs : iroot k (N / m) ≤ N := (iroot_le _ _).trans (Nat.div_le_self _ _)
  ext d
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hs⟩, h3⟩

lemma inner_eq_zero_pow {k N Y m : ℕ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hm : 1 ≤ m)
    (h : N / Y ^ k < m) : Ioc Y (iroot k (N / m)) = ∅ := by
  rw [Ioc_eq_empty_iff, not_lt]
  by_contra hlt
  rw [not_le] at hlt
  have h1 : (Y + 1) ^ k ≤ N / m := (le_iroot_iff hk).1 hlt
  rw [Nat.le_div_iff_mul_le (by omega)] at h1
  have h2 : m ≤ N / Y ^ k := by
    rw [Nat.le_div_iff_mul_le (Nat.pow_pos hY)]
    have : Y ^ k ≤ (Y + 1) ^ k := Nat.pow_le_pow_left (by omega) k
    nlinarith
  omega

lemma iroot_succ_rpow_le {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) {N m : ℕ} (hm : 1 ≤ m)
    (hmN : m ≤ N) :
    ((iroot k (N / m) : ℝ) + 1) ^ α ≤ 2 ^ α * ((N : ℝ) / m) ^ (α / k) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : k ≠ 0 := by omega
  set x : ℝ := (N : ℝ) / m with hx
  have hr : (1 : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ hm']; simpa using (by exact_mod_cast hmN : (m : ℝ) ≤ N)
  set r := iroot k (N / m) with hrdef
  have hrk : (r : ℝ) ^ k ≤ x := by
    have h1 : r ^ k ≤ N / m := (le_iroot_iff hk).1 le_rfl
    have h2 : (((N / m : ℕ)) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
    calc (r : ℝ) ^ k = ((r ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((N / m : ℕ)) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
  have hrs : (r : ℝ) ≤ x ^ ((k : ℝ)⁻¹) := by
    calc (r : ℝ) = ((r : ℝ) ^ k) ^ ((k : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (Nat.cast_nonneg r) hk0).symm
      _ ≤ x ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hrk (by positivity)
  have h1 : (1 : ℝ) ≤ x ^ ((k : ℝ)⁻¹) := Real.one_le_rpow hr (by positivity)
  have h2 : (r : ℝ) + 1 ≤ 2 * x ^ ((k : ℝ)⁻¹) := by linarith
  calc ((r : ℝ) + 1) ^ α ≤ (2 * x ^ ((k : ℝ)⁻¹)) ^ α :=
        Real.rpow_le_rpow (by positivity) h2 hα
    _ = 2 ^ α * x ^ (α / k) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
        congr 2; field_simp

/-- `N^β (N/Y^k)^{1-β} = N Y^{kβ-k}`. -/
lemma rpow_alg_pow {β : ℝ} (k : ℕ) (N Y : ℝ) (hN : 0 < N) (hY : 0 < Y) :
    N ^ β * (N / Y ^ k) ^ (1 - β) = N * Y ^ (k * β - k) := by
  rw [Real.div_rpow hN.le (by positivity), ← Real.rpow_natCast Y k, ← Real.rpow_mul hY.le]
  have h1 : N ^ β * N ^ (1 - β) = N := by
    rw [← Real.rpow_add hN]; simp
  have h2 : Y ^ ((k : ℝ) * β - k) = (Y ^ ((k : ℝ) * (1 - β)))⁻¹ := by
    rw [← Real.rpow_neg hY.le]; congr 1; ring
  rw [h2]
  calc N ^ β * (N ^ (1 - β) / Y ^ ((k : ℝ) * (1 - β)))
      = (N ^ β * N ^ (1 - β)) * (Y ^ ((k : ℝ) * (1 - β)))⁻¹ := by rw [div_eq_mul_inv]; ring
    _ = _ := by rw [h1]

/-- **The hyperbola bound** for `k`-free numbers. -/
theorem abs_T_le_pow {k : ℕ} (hk : 1 ≤ k) {K α : ℝ} (hα0 : 0 ≤ α) (hαk : α < k)
    (hM : MBound K α) {N Y : ℕ} (hY : 1 ≤ Y) (hYN : Y ≤ N) :
    |∑ d ∈ Ioc Y N, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ)| ≤
      (K * 2 ^ α * (1 / (1 - α / k) + 1)) * ((N : ℝ) * (Y : ℝ) ^ (α - k)) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hN' : (1 : ℝ) ≤ N := hY'.trans (by exact_mod_cast hYN)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set X := N / Y ^ k with hX
  set β := α / k with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβ1 : β < 1 := by rw [hβ, div_lt_one hk']; exact hαk
  have hXN : X ≤ N := (Nat.div_le_self _ _)
  have hXr : (X : ℝ) ≤ (N : ℝ) / (Y : ℝ) ^ k := by
    have : ((N / Y ^ k : ℕ) : ℝ) ≤ (N : ℝ) / ((Y ^ k : ℕ) : ℝ) := Nat.cast_div_le
    simpa using this
  rw [T_eq_pow hk]
  calc |∑ m ∈ Icc 1 N, ∑ d ∈ Ioc Y (iroot k (N / m)), (μ d : ℝ)|
      ≤ ∑ m ∈ Icc 1 N, |∑ d ∈ Ioc Y (iroot k (N / m)), (μ d : ℝ)| := abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ Icc 1 X, |∑ d ∈ Ioc Y (iroot k (N / m)), (μ d : ℝ)| := by
        symm
        refine sum_subset (Icc_subset_Icc le_rfl hXN) fun m hm hm' => ?_
        have hm1 := mem_Icc.1 hm
        have : ¬ (1 ≤ m ∧ m ≤ X) := fun h => hm' (mem_Icc.2 h)
        rw [inner_eq_zero_pow hk hY hm1.1 (by omega)]; simp
    _ ≤ ∑ m ∈ Icc 1 X, (K * 2 ^ α * ((N : ℝ) / m) ^ β + K * 2 ^ α * (Y : ℝ) ^ α) := by
        refine sum_le_sum fun m hm => ?_
        have hm1 := mem_Icc.1 hm
        refine (abs_inner_le hM Y _).trans ?_
        have hmN : m ≤ N := hm1.2.trans hXN
        have h1 := iroot_succ_rpow_le hk hα0 hm1.1 hmN
        have h2 : ((Y : ℝ) + 1) ^ α ≤ 2 ^ α * (Y : ℝ) ^ α := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
          exact Real.rpow_le_rpow (by positivity) (by linarith) hα0
        calc K * ((iroot k (N / m) : ℝ) + 1) ^ α + K * ((Y : ℝ) + 1) ^ α
            ≤ K * (2 ^ α * ((N : ℝ) / m) ^ β) + K * (2 ^ α * (Y : ℝ) ^ α) := by gcongr
          _ = _ := by ring
    _ = K * 2 ^ α * ((N : ℝ) ^ β * ∑ m ∈ Icc 1 X, (m : ℝ) ^ (-β)) +
          (X : ℝ) * (K * 2 ^ α * (Y : ℝ) ^ α) := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_sum,
          mul_sum]
        congr 1
        refine sum_congr rfl fun m hm => ?_
        have hm' : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.1 hm).1
        rw [Real.div_rpow (by positivity) hm'.le, Real.rpow_neg hm'.le]
        field_simp
    _ ≤ K * 2 ^ α * ((N : ℝ) ^ β * ((X : ℝ) ^ (1 - β) / (1 - β))) +
          (N / (Y : ℝ) ^ k) * (K * 2 ^ α * (Y : ℝ) ^ α) := by
        rw [sum_Icc_rpow]
        have := sum_rpow_neg_le hβ0 hβ1 X
        gcongr
    _ ≤ K * 2 ^ α * ((N : ℝ) ^ β * (((N : ℝ) / (Y : ℝ) ^ k) ^ (1 - β) / (1 - β))) +
          (N / (Y : ℝ) ^ k) * (K * 2 ^ α * (Y : ℝ) ^ α) := by
        have hb : 0 < 1 - β := by linarith
        gcongr
    _ = (K * 2 ^ α * (1 / (1 - α / k) + 1)) * ((N : ℝ) * (Y : ℝ) ^ (α - k)) := by
        have hN0 : (0 : ℝ) < N := by linarith
        have hY0 : (0 : ℝ) < Y := by linarith
        have e1 := rpow_alg_pow (β := β) k (N : ℝ) (Y : ℝ) hN0 hY0
        have e2 : (Y : ℝ) ^ (α - k) * ((Y : ℝ) ^ k) = (Y : ℝ) ^ α := by
          rw [← Real.rpow_natCast (Y : ℝ) k, ← Real.rpow_add hY0]; congr 1; ring
        have e3 : (k : ℝ) * β - k = α - k := by rw [hβ]; field_simp
        rw [e3] at e1
        calc K * 2 ^ α * ((N : ℝ) ^ β * (((N : ℝ) / (Y : ℝ) ^ k) ^ (1 - β) / (1 - β))) +
              (N / (Y : ℝ) ^ k) * (K * 2 ^ α * (Y : ℝ) ^ α)
            = K * 2 ^ α * (((N : ℝ) ^ β * ((N : ℝ) / (Y : ℝ) ^ k) ^ (1 - β)) / (1 - β)) +
              (N / (Y : ℝ) ^ k) * (K * 2 ^ α * ((Y : ℝ) ^ (α - k) * (Y : ℝ) ^ k)) := by
                rw [e2]; ring
          _ = _ := by
                have hYk : (0 : ℝ) < (Y : ℝ) ^ k := by positivity
                rw [e1, hβ]; field_simp

end Erdos969.KFree
