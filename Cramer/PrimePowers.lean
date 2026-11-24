import Mathlib

/-!
# Prime powers in a short interval

For `1 ≤ a < b ≤ 2a`, the proper prime powers `p^j` (`j ≥ 2`) in `[a, b)` contribute
`Σ_{a ≤ k < b, k not prime} Λ(k) ≤ log b · ((√b − √a + 1) + (b^{1/3} + 1))`.

Since `b ≤ 2a`, each prime `p` has at most one power in `[a, b)`, so `k ↦ minFac k` is
injective on them; its image lies in `{p : a ≤ p² < b}` (squares) or `{p : p³ < b}`.
-/

namespace Cramer

open ArithmeticFunction Finset

/-- The number of `p` with `a ≤ p² < b` is at most `√b − √a + 1`. -/
lemma card_sq_mem_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (((range b).filter fun p => a ≤ p ^ 2 ∧ p ^ 2 < b).card : ℝ)
      ≤ √(b : ℝ) - √(a : ℝ) + 1 := by
  have hsub : (range b).filter (fun p => a ≤ p ^ 2 ∧ p ^ 2 < b)
      ⊆ Ico (Nat.sqrt (a - 1) + 1) (Nat.sqrt (b - 1) + 1) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    simp only [mem_Ico]
    constructor
    · by_contra h
      push Not at h
      have h1 : p ≤ Nat.sqrt (a - 1) := by omega
      have h2 := Nat.le_sqrt'.mp h1
      omega
    · have : p ≤ Nat.sqrt (b - 1) := Nat.le_sqrt'.mpr (by omega)
      omega
  have hc := card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hcR : (((range b).filter fun p => a ≤ p ^ 2 ∧ p ^ 2 < b).card : ℝ)
      ≤ (Nat.sqrt (b - 1) : ℝ) + 1 - (Nat.sqrt (a - 1) + 1) := by
    have hle : Nat.sqrt (a - 1) ≤ Nat.sqrt (b - 1) := Nat.sqrt_le_sqrt (by omega)
    have : (((range b).filter fun p => a ≤ p ^ 2 ∧ p ^ 2 < b).card : ℝ)
        ≤ ((Nat.sqrt (b - 1) + 1 - (Nat.sqrt (a - 1) + 1) : ℕ) : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this
    linarith
  have h1 : (Nat.sqrt (b - 1) : ℝ) ≤ √(b : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have := Nat.sqrt_le' (b - 1)
    have h2 : ((Nat.sqrt (b - 1) ^ 2 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega)
    exact_mod_cast h2
  have h2 : √(a : ℝ) ≤ (Nat.sqrt (a - 1) : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Nat.lt_succ_sqrt' (a - 1)
    rw [Nat.succ_eq_add_one] at this
    have h3 : (a : ℝ) ≤ ((Nat.sqrt (a - 1) + 1) ^ 2 : ℕ) := by exact_mod_cast (by omega)
    push_cast at h3
    exact h3
  linarith

/-- The number of `p < b` with `p³ < b` is at most `b^{1/3} + 1`. -/
lemma card_cube_lt_le (b : ℕ) :
    (((range b).filter fun p => p ^ 3 < b).card : ℝ) ≤ (b : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
  have hsub : (range b).filter (fun p => p ^ 3 < b) ⊆ range (⌊(b : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    have hp3 : ((p : ℝ) ^ 3) < b := by exact_mod_cast hp.2
    have : (p : ℝ) < (b : ℝ) ^ ((1 : ℝ) / 3) := by
      have e : (p : ℝ) = ((p : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [e]
      exact Real.rpow_lt_rpow (by positivity) hp3 (by norm_num)
    have := Nat.le_floor this.le
    omega
  have hc := card_le_card hsub
  rw [card_range] at hc
  have hfl := Nat.floor_le (show (0 : ℝ) ≤ (b : ℝ) ^ ((1 : ℝ) / 3) by positivity)
  have : (((range b).filter fun p => p ^ 3 < b).card : ℝ) ≤ (⌊(b : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1 := by
    exact_mod_cast hc
  linarith

/-- **Prime powers in `[a, b)`.** -/
theorem sum_vonMangoldt_not_prime_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * a) :
    ∑ k ∈ (Ico a b).filter (fun k => ¬ k.Prime), (Λ k : ℝ)
      ≤ Real.log b * ((√(b : ℝ) - √(a : ℝ) + 1) + ((b : ℝ) ^ ((1 : ℝ) / 3) + 1)) := by
  set T := ((Ico a b).filter (fun k => ¬ k.Prime)).filter (fun k => IsPrimePow k)
  set S2 := (range b).filter fun p => a ≤ p ^ 2 ∧ p ^ 2 < b
  set S3 := (range b).filter fun p => p ^ 3 < b
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
  -- reduce to the prime powers
  have hsum : ∑ k ∈ (Ico a b).filter (fun k => ¬ k.Prime), (Λ k : ℝ) = ∑ k ∈ T, (Λ k : ℝ) := by
    exact (sum_filter_of_ne fun k _ hk => vonMangoldt_ne_zero_iff.mp hk).symm
  have hT : ∑ k ∈ T, (Λ k : ℝ) ≤ T.card * Real.log b := by
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun k hk => ?_
    simp only [T, mem_filter, mem_Ico] at hk
    refine vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
    · exact_mod_cast (show 0 < k by omega)
    · exact_mod_cast hk.1.1.2.le
  -- the minFac map
  have hrep : ∀ k ∈ T, ∃ j, 2 ≤ j ∧ k.minFac ^ j = k ∧ k.minFac.Prime := by
    intro k hk
    simp only [T, mem_filter] at hk
    obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hk.2
    refine ⟨j, ?_, ?_, ?_⟩
    · by_contra h
      have : j = 1 := by omega
      subst this
      exact hk.1.2 (by simpa using hp)
    · rw [hp.pow_minFac (by omega)]
    · rw [hp.pow_minFac (by omega)]; exact hp
  have hmaps : Set.MapsTo Nat.minFac (T : Set ℕ) ((S2 ∪ S3 : Finset ℕ) : Set ℕ) := by
    intro k hk
    obtain ⟨j, hj, hk', hp⟩ := hrep k hk
    have hk2 := hk
    simp only [T, mem_coe, mem_filter, mem_Ico] at hk2
    have hkb := hk2.1.1.2
    have hak := hk2.1.1.1
    have hp1 := hp.one_lt
    rw [mem_coe, mem_union]
    have hle : k.minFac ≤ k.minFac ^ j := Nat.le_self_pow (by omega) _
    rcases Nat.lt_or_ge j 3 with h | h
    · have : j = 2 := by omega
      subst this
      left; simp only [S2, mem_filter, mem_range]; refine ⟨by omega, by omega, by omega⟩
    · right
      have : k.minFac ^ 3 ≤ k.minFac ^ j := Nat.pow_le_pow_right (by omega) h
      simp only [S3, mem_filter, mem_range]; refine ⟨by omega, by omega⟩
  have hinj : Set.InjOn Nat.minFac T := by
    intro k hk k' hk' he
    obtain ⟨j, hj, hkj, hp⟩ := hrep k hk
    obtain ⟨j', hj', hkj', -⟩ := hrep k' hk'
    simp only [T, mem_coe, mem_filter, mem_Ico] at hk hk'
    rw [← hkj, ← hkj', he]
    rw [he] at hp
    have hp2 := hp.two_le
    congr 1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · -- `p^{j'} ≥ p · p^j ≥ 2a ≥ b`
      have : k'.minFac ^ j * 2 ≤ k'.minFac ^ j' := by
        calc k'.minFac ^ j * 2 ≤ k'.minFac ^ j * k'.minFac := Nat.mul_le_mul_left _ hp2
          _ = k'.minFac ^ (j + 1) := (pow_succ _ _).symm
          _ ≤ k'.minFac ^ j' := Nat.pow_le_pow_right (by omega) h
      have e1 : k'.minFac ^ j = k := by rw [← he]; exact hkj
      omega
    · have : k'.minFac ^ j' * 2 ≤ k'.minFac ^ j := by
        calc k'.minFac ^ j' * 2 ≤ k'.minFac ^ j' * k'.minFac := Nat.mul_le_mul_left _ hp2
          _ = k'.minFac ^ (j' + 1) := (pow_succ _ _).symm
          _ ≤ k'.minFac ^ j := Nat.pow_le_pow_right (by omega) h
      have e1 : k'.minFac ^ j = k := by rw [← he]; exact hkj
      omega
  have hcard := card_le_card_of_injOn Nat.minFac hmaps hinj
  have hcard' : (T.card : ℝ) ≤ S2.card + S3.card := by
    have := hcard.trans (card_union_le S2 S3)
    exact_mod_cast this
  have h2 := card_sq_mem_le a b ha hab
  have h3 := card_cube_lt_le b
  rw [hsum]
  calc _ ≤ T.card * Real.log b := hT
    _ ≤ ((√(b : ℝ) - √(a : ℝ) + 1) + ((b : ℝ) ^ ((1 : ℝ) / 3) + 1)) * Real.log b := by
        apply mul_le_mul_of_nonneg_right _ hlogb
        linarith
    _ = _ := by ring

end Cramer
