import Erdos233.AlmostAll
import LegendreExceptions.Statement

/-!
# Counting disjoint prime-free intervals under RH

The single analytic input is erdos-233's `Erdos233.large_gaps_of_RH`:
`Σ_{X ≤ p_k < 2X, d_k ≥ h} d_k ≤ C X log² X / h` for `256 log²(5X)/log 2 ≤ h ≤ 2X`.

1. `exists_gap`: a prime-free interval `(a, b)` with `a ≥ 2` lies inside one prime gap
   `(p_k, p_{k+1})`, and `p_k ≤ a < b ≤ p_{k+1}`.
2. `family_card_of_RH`: pairwise disjoint prime-free intervals `(a_i, b_i)` with
   `2X ≤ a_i < 4X` and `b_i − a_i ≥ h` number at most `9 C X log² X / (h (h − 1))`: their union
   is covered by the gaps of length `≥ h` starting in `[X, 4X)`, i.e. in the two blocks
   `[X, 2X)` and `[2X, 4X)`.
3. `window_card_of_RH`: with `h = √X / 2` and `b_i − a_i ≥ √a_i / 2`, at most `8 C log² X`.
4. `count_le_of_RH`: summing over the dyadic windows `a ∈ [2^{j+1}, 2^{j+2})`, a family of
   such intervals with `a < B` has `≤ K + C' log³ B` members.
5. `isBigO_of_RH`: if the members indexed by `m ≤ N` have `a_m < (N+2)^8`, their number is
   `O(log³ N)`.
-/

namespace LegendreExceptions

open Finset Real Nat Erdos233

/-- A prime-free open interval `(a, b)` lies inside one prime gap. -/
lemma exists_gap {a b : ℕ} (ha : 2 ≤ a) (hfree : ∀ y, a < y → y < b → ¬ y.Prime) :
    ∃ k, nth Nat.Prime k ≤ a ∧ a < nth Nat.Prime (k + 1) ∧ b ≤ nth Nat.Prime (k + 1) := by
  have hc : Nat.primeCounting a ≠ 0 := by
    rw [Ne, Nat.primeCounting_eq_zero_iff]; omega
  have hc' : Nat.primeCounting a = idx (a + 1) := rfl
  have h0 : Nat.primeCounting a - 1 < idx (a + 1) := by rw [← hc']; omega
  have h1 : idx (a + 1) ≤ Nat.primeCounting a - 1 + 1 := by rw [← hc']; omega
  have hlt := nth_lt_of_lt_idx h0
  have hge := le_nth_of_idx_le h1
  refine ⟨Nat.primeCounting a - 1, by omega, by omega, ?_⟩
  by_contra hb
  push_neg at hb
  exact hfree _ (by omega) hb (Nat.prime_nth_prime _)

/-- **Disjoint prime-free intervals with left ends in `[2X, 4X)`, under RH.** -/
theorem family_card_of_RH (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℕ, X₀ ≤ X →
    ∀ h : ℝ, 256 * (Real.log (10 * X) ^ 2 / Real.log 2) ≤ h → h ≤ 2 * X →
    ∀ (s : Finset ℕ) (a b : ℕ → ℕ),
      (∀ i ∈ s, 2 * X ≤ a i ∧ a i < 4 * X ∧ h ≤ (b i : ℝ) - a i ∧
        ∀ y, a i < y → y < b i → ¬ y.Prime) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (s.card : ℝ) * (h - 1) ≤ C * X * Real.log X ^ 2 / h := by
  obtain ⟨C, X₀, hC, hg⟩ := large_gaps_of_RH hRH
  refine ⟨9 * C, max X₀ 2, by positivity, ?_⟩
  intro X hX h hh1 hh2 s a b hs hdisj
  have hX2 : (2 : ℝ) ≤ X := le_of_max_le_right hX
  have hX0 : X₀ ≤ (X : ℝ) := le_of_max_le_left hX
  have hX2n : 2 ≤ X := by exact_mod_cast hX2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh0 : 0 < h := by
    have : 0 < Real.log (10 * X) := Real.log_pos (by linarith)
    have : 0 < 256 * (Real.log (10 * X) ^ 2 / Real.log 2) := by positivity
    linarith
  set K := (block X ∪ block (2 * X)).filter (fun k => h ≤ (primeGap k : ℝ)) with hK
  have hsub : s.biUnion (fun i => Ioo (a i) (b i)) ⊆
      K.biUnion (fun k => Ioo (nth Nat.Prime k) (nth Nat.Prime (k + 1))) := by
    intro y hy
    simp only [mem_biUnion] at hy ⊢
    obtain ⟨i, hi, hyi⟩ := hy
    obtain ⟨ha1, ha2, hlen, hfree⟩ := hs i hi
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_gap (a := a i) (b := b i) (by omega) hfree
    have hk4 := nth_succ_le_two_mul k
    refine ⟨k, ?_, ?_⟩
    · rw [hK, mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.Ico_union_Ico_eq_Ico (Nat.monotone_primeCounting' (by omega))
          (Nat.monotone_primeCounting' (by omega)), mem_Ico]
        constructor
        · have hXk : X ≤ nth Nat.Prime k := by omega
          exact (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).2 hXk
        · by_contra hc
          push_neg at hc
          have := le_nth_of_idx_le hc
          omega
      · rw [primeGap_cast]
        have : (b i : ℝ) ≤ nth Nat.Prime (k + 1) := by exact_mod_cast hk3
        have : (nth Nat.Prime k : ℝ) ≤ a i := by exact_mod_cast hk1
        linarith
    · rw [mem_Ioo] at hyi ⊢
      omega
  have hcard_K : (K.biUnion (fun k => Ioo (nth Nat.Prime k) (nth Nat.Prime (k + 1)))).card ≤
      ∑ k ∈ K, primeGap k := by
    refine card_biUnion_le.trans (sum_le_sum fun k _ => ?_)
    rw [Nat.card_Ioo]; unfold primeGap; omega
  have hnat : ∑ i ∈ s, (Ioo (a i) (b i)).card ≤ ∑ k ∈ K, primeGap k := by
    rw [← card_biUnion hdisj]; exact (card_le_card hsub).trans hcard_K
  have hlow : (s.card : ℝ) * (h - 1) ≤ ∑ i ∈ s, ((Ioo (a i) (b i)).card : ℝ) := by
    rw [← nsmul_eq_mul]
    apply card_nsmul_le_sum
    intro i hi
    obtain ⟨-, -, hlen, -⟩ := hs i hi
    rw [Nat.card_Ioo]
    have hab : a i + 1 ≤ b i := by
      have : (a i : ℝ) < b i := by linarith
      exact_mod_cast this
    rw [Nat.sub_sub, Nat.cast_sub hab]
    push_cast
    linarith
  have hsum_cast : (∑ i ∈ s, ((Ioo (a i) (b i)).card : ℝ)) ≤ ∑ k ∈ K, (primeGap k : ℝ) := by
    exact_mod_cast hnat
  have hsplit : ∑ k ∈ K, (primeGap k : ℝ) =
      ∑ k ∈ (block X).filter (fun k => h ≤ (primeGap k : ℝ)), (primeGap k : ℝ) +
      ∑ k ∈ (block (2 * X)).filter (fun k => h ≤ (primeGap k : ℝ)), (primeGap k : ℝ) := by
    rw [hK, filter_union, sum_union]
    exact disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)
  have hlog5 : Real.log (5 * X) ≤ Real.log (10 * X) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog5' : 0 ≤ Real.log (5 * X) := Real.log_nonneg (by linarith)
  have hsq5 : Real.log (5 * X) ^ 2 ≤ Real.log (10 * X) ^ 2 := by nlinarith
  have c1 : 256 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ h := by
    have := div_le_div_of_nonneg_right hsq5 hl2.le
    linarith
  have g1 := hg X hX0 h c1 (by linarith)
  have g2 := hg (2 * X) (by push_cast; linarith) h
    (by push_cast; rw [show (5 : ℝ) * (2 * (X : ℝ)) = 10 * X by ring]; exact hh1)
    (by push_cast; linarith)
  push_cast at g2
  have hlX : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
  have hlX0 : 0 ≤ Real.log X := by linarith
  have hl2X : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) (by positivity)]; linarith
  have hl2X0 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have hsq : Real.log (2 * X) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  have h2' : C * (2 * X) * Real.log (2 * X) ^ 2 / h ≤ 8 * C * X * Real.log X ^ 2 / h := by
    apply div_le_div_of_nonneg_right _ hh0.le
    have : 0 ≤ C * (2 * (X : ℝ)) := by positivity
    nlinarith
  calc (s.card : ℝ) * (h - 1) ≤ ∑ k ∈ K, (primeGap k : ℝ) := hlow.trans hsum_cast
    _ ≤ C * X * Real.log X ^ 2 / h + 8 * C * X * Real.log X ^ 2 / h := by
        rw [hsplit]; linarith
    _ = 9 * C * X * Real.log X ^ 2 / h := by ring

/-- `512 log²(10X)/log 2 ≤ √X` for large `X`. -/
lemma eventually_log_sq_le_sqrt' : ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X →
    512 * (Real.log (10 * X) ^ 2 / Real.log 2) ≤ Real.sqrt X := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho := (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show 0 < Real.log 2 / 2048 by positivity)
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 ho
  refine ⟨max X₁ 10, fun X hX => ?_⟩
  have hX10 : 10 ≤ X := le_of_max_le_right hX
  have hX0 : 0 < X := by linarith
  have h := hX₁ X (le_of_max_le_left hX)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlX _),
    abs_of_nonneg (Real.rpow_nonneg hX0.le _), Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have h5 : Real.log (10 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 10 ≤ Real.log X := Real.log_le_log (by norm_num) hX10
    linarith
  have h5' : 0 ≤ Real.log (10 * X) := Real.log_nonneg (by linarith)
  have hsq : Real.log (10 * X) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  have : 512 * (Real.log (10 * X) ^ 2 / Real.log 2) ≤ 2048 * Real.log X ^ 2 / Real.log 2 := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hl2.le
  refine this.trans ?_
  rw [div_le_iff₀ hl2]
  nlinarith

/-- **One dyadic window, under RH**: disjoint prime-free intervals `(a_i, b_i)` with
`2X ≤ a_i < 4X` and `√a_i ≤ 2 (b_i − a_i)` number at most `C log² X`. -/
theorem window_card_of_RH (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℕ, X₀ ≤ X →
    ∀ (s : Finset ℕ) (a b : ℕ → ℕ),
      (∀ i ∈ s, 2 * X ≤ a i ∧ a i < 4 * X ∧ Real.sqrt (a i) ≤ 2 * ((b i : ℝ) - a i) ∧
        ∀ y, a i < y → y < b i → ¬ y.Prime) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (s.card : ℝ) ≤ C * Real.log X ^ 2 := by
  obtain ⟨C, X₀, hC, hf⟩ := family_card_of_RH hRH
  obtain ⟨X₁, hX₁⟩ := eventually_log_sq_le_sqrt'
  refine ⟨8 * C, max (max X₀ X₁) 16, by positivity, ?_⟩
  intro X hX s a b hs hdisj
  have hX16 : (16 : ℝ) ≤ X := le_of_max_le_right hX
  have hX0 : X₀ ≤ (X : ℝ) := le_trans (le_max_left _ _) (le_of_max_le_left hX)
  have hX1 : X₁ ≤ (X : ℝ) := le_trans (le_max_right _ _) (le_of_max_le_left hX)
  have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt (by positivity)
  have hs4 : 4 ≤ Real.sqrt X := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX16
  set h := Real.sqrt X / 2 with hhdef
  have hh1 : 256 * (Real.log (10 * X) ^ 2 / Real.log 2) ≤ h := by
    have := hX₁ X hX1; rw [hhdef]; linarith
  have hh2 : h ≤ 2 * X := by rw [hhdef]; nlinarith
  have hs' : ∀ i ∈ s, 2 * X ≤ a i ∧ a i < 4 * X ∧ h ≤ (b i : ℝ) - a i ∧
      ∀ y, a i < y → y < b i → ¬ y.Prime := by
    intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := hs i hi
    refine ⟨h1, h2, ?_, h4⟩
    have : (X : ℝ) ≤ a i := by
      have : ((2 * X : ℕ) : ℝ) ≤ a i := by exact_mod_cast h1
      push_cast at this; linarith
    have := Real.sqrt_le_sqrt this
    rw [hhdef]; linarith
  have key := hf X hX0 h hh1 hh2 s a b hs' hdisj
  have hpos : 0 < Real.sqrt X := by linarith
  have e : C * X * Real.log X ^ 2 / h = 2 * C * Real.sqrt X * Real.log X ^ 2 := by
    rw [hhdef, div_eq_iff (by positivity)]
    linear_combination (-(C * Real.log X ^ 2)) * hsq
  have hc0 : (0 : ℝ) ≤ s.card := by positivity
  have hhm : h / 2 ≤ h - 1 := by rw [hhdef]; linarith
  have : (s.card : ℝ) * (Real.sqrt X / 4) ≤ (8 * C * Real.log X ^ 2) * (Real.sqrt X / 4) := by
    calc (s.card : ℝ) * (Real.sqrt X / 4) = s.card * (h / 2) := by rw [hhdef]; ring
      _ ≤ s.card * (h - 1) := mul_le_mul_of_nonneg_left hhm hc0
      _ ≤ C * X * Real.log X ^ 2 / h := key
      _ = (8 * C * Real.log X ^ 2) * (Real.sqrt X / 4) := by rw [e]; ring
  exact le_of_mul_le_mul_right this (by positivity)

/-- **All windows, under RH.** Let `E` be a set of indices with prime-free intervals
`(a m, b m)`, pairwise disjoint, `m ≤ a m` and `√(a m) ≤ 2 (b m − a m)`. Then the members with
`a m < B` number at most `K + C log³ B`. -/
theorem count_le_of_RH (hRH : RiemannHypothesis) (E : ℕ → Prop) (a b : ℕ → ℕ)
    (hE : ∀ m, E m → m ≤ a m ∧ Real.sqrt (a m) ≤ 2 * ((b m : ℝ) - a m) ∧
      ∀ y, a m < y → y < b m → ¬ y.Prime)
    (hdisj : ∀ m n, E m → E n → m ≠ n → Disjoint (Ioo (a m) (b m)) (Ioo (a n) (b n))) :
    ∃ K C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, ∀ S : Finset ℕ, (∀ m ∈ S, E m ∧ a m < B) →
      (S.card : ℝ) ≤ K + C * Real.log B ^ 3 := by
  obtain ⟨C, X₀, hC, hw⟩ := window_card_of_RH hRH
  obtain ⟨j₀, hj₀⟩ := pow_unbounded_of_one_lt X₀ (by norm_num : (1 : ℝ) < 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 ^ (j₀ + 1), C / Real.log 2, by positivity, ?_⟩
  intro B S hS
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · have : S = ∅ := by
      ext m; simp only [Finset.notMem_empty, iff_false]; intro hm; have := (hS m hm).2; omega
    subst this; simp only [card_empty, Nat.cast_zero, CharP.cast_eq_zero, Real.log_zero]
    positivity
  set J := Nat.log 2 B with hJ
  let W : ℕ → Finset ℕ := fun j => S.filter (fun m => 2 * 2 ^ j ≤ a m ∧ a m < 4 * 2 ^ j)
  have hcover : S ⊆ S.filter (fun m => a m < 2 ^ (j₀ + 1)) ∪ (Ico j₀ J).biUnion W := by
    intro m hm
    rw [mem_union, mem_filter, mem_biUnion]
    by_cases hlow : a m < 2 ^ (j₀ + 1)
    · exact Or.inl ⟨hm, hlow⟩
    · right
      push_neg at hlow
      have ham : a m ≠ 0 := by have := Nat.one_le_two_pow (n := j₀ + 1); omega
      set L := Nat.log 2 (a m) with hL
      have hL1 : j₀ + 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) hlow
      have hLJ : L ≤ J := Nat.log_mono_right (hS m hm).2.le
      obtain ⟨j, hj⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
      refine ⟨j, mem_Ico.2 ⟨by omega, by omega⟩, mem_filter.2 ⟨hm, ?_, ?_⟩⟩
      · have := Nat.pow_log_le_self 2 ham
        rw [← hL, hj, pow_succ] at this; linarith
      · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (a m)
        rw [← hL, hj, pow_succ, pow_succ] at this; linarith
  have hfirst : (S.filter (fun m => a m < 2 ^ (j₀ + 1))).card ≤ 2 ^ (j₀ + 1) := by
    calc _ ≤ (range (2 ^ (j₀ + 1))).card := by
          apply card_le_card
          intro m hm
          rw [mem_filter] at hm
          have := (hE m (hS m hm.1).1).1
          rw [mem_range]; omega
      _ = 2 ^ (j₀ + 1) := card_range _
  have hW : ∀ j ∈ Ico j₀ J, ((W j).card : ℝ) ≤ C * ((J : ℝ) * Real.log 2) ^ 2 := by
    intro j hj
    rw [mem_Ico] at hj
    have hX : X₀ ≤ ((2 ^ j : ℕ) : ℝ) := by
      push_cast
      exact hj₀.le.trans (pow_le_pow_right₀ (by norm_num) hj.1)
    have := hw (2 ^ j) hX (W j) a b (fun i hi => by
      rw [mem_filter] at hi
      obtain ⟨h1, h2, h3⟩ := hE i (hS i hi.1).1
      exact ⟨hi.2.1, hi.2.2, h2, h3⟩)
      (fun i hi i' hi' hne => hdisj i i' (hS i (mem_filter.1 hi).1).1
        (hS i' (mem_filter.1 hi').1).1 hne)
    refine this.trans ?_
    push_cast
    rw [Real.log_pow]
    have : (j : ℝ) ≤ J := by exact_mod_cast hj.2.le
    have : (0 : ℝ) ≤ j := by positivity
    gcongr
  have hJlog : (J : ℝ) * Real.log 2 ≤ Real.log B := by
    have h2J : ((2 ^ J : ℕ) : ℝ) ≤ B := by exact_mod_cast Nat.pow_log_le_self 2 hB.ne'
    push_cast at h2J
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2J
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) * Real.log 2 := by positivity
  calc (S.card : ℝ)
      ≤ ((S.filter (fun m => a m < 2 ^ (j₀ + 1))).card : ℝ) + ∑ j ∈ Ico j₀ J, ((W j).card : ℝ) := by
        have h1 := card_le_card hcover
        have h2 := card_union_le (S.filter (fun m => a m < 2 ^ (j₀ + 1))) ((Ico j₀ J).biUnion W)
        have h3 : ((Ico j₀ J).biUnion W).card ≤ ∑ j ∈ Ico j₀ J, (W j).card := card_biUnion_le
        have : S.card ≤ (S.filter (fun m => a m < 2 ^ (j₀ + 1))).card +
            ∑ j ∈ Ico j₀ J, (W j).card := by omega
        exact_mod_cast this
    _ ≤ 2 ^ (j₀ + 1) + ∑ j ∈ Ico j₀ J, C * ((J : ℝ) * Real.log 2) ^ 2 := by
        gcongr with j hj
        · exact_mod_cast hfirst
        · exact hW j hj
    _ ≤ 2 ^ (j₀ + 1) + J * (C * ((J : ℝ) * Real.log 2) ^ 2) := by
        rw [sum_const, card_Ico, nsmul_eq_mul]
        gcongr
        exact_mod_cast Nat.sub_le J j₀
    _ = 2 ^ (j₀ + 1) + C / Real.log 2 * ((J : ℝ) * Real.log 2) ^ 3 := by
        field_simp
    _ ≤ 2 ^ (j₀ + 1) + C / Real.log 2 * Real.log B ^ 3 := by
        gcongr

/-- **The `O(log³ N)` bound, under RH.** If the members of the family indexed by `m ≤ N` (the
set `S N`) have `a m < (N + 2)^8`, then `#S N = O(log³ N)`. -/
theorem isBigO_of_RH (hRH : RiemannHypothesis) (E : ℕ → Prop) (a b : ℕ → ℕ)
    (hE : ∀ m, E m → m ≤ a m ∧ Real.sqrt (a m) ≤ 2 * ((b m : ℝ) - a m) ∧
      ∀ y, a m < y → y < b m → ¬ y.Prime)
    (hdisj : ∀ m n, E m → E n → m ≠ n → Disjoint (Ioo (a m) (b m)) (Ioo (a n) (b n)))
    (S : ℕ → Finset ℕ) (hS : ∀ N, ∀ m ∈ S N, E m ∧ a m < (N + 2) ^ 8) :
    (fun N : ℕ => ((S N).card : ℝ)) =O[Filter.atTop] fun N => Real.log N ^ 3 := by
  obtain ⟨K, C, hC, hc⟩ := count_le_of_RH hRH E a b hE hdisj
  refine Asymptotics.IsBigO.of_bound (|K| + 4096 * C) (Filter.eventually_atTop.2 ⟨3, ?_⟩)
  intro N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hb := hc ((N + 2) ^ 8) (S N) (hS N)
  have hlogB : Real.log (((N + 2) ^ 8 : ℕ) : ℝ) ≤ 16 * Real.log N := by
    push_cast
    rw [Real.log_pow]
    have : Real.log ((N : ℝ) + 2) ≤ 2 * Real.log N := by
      rw [← Real.log_rpow (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [show ((N : ℝ) ^ (2 : ℝ)) = (N : ℝ) ^ 2 by norm_cast]
      nlinarith
    push_cast; linarith
  have hlogB0 : 0 ≤ Real.log (((N + 2) ^ 8 : ℕ) : ℝ) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ ((N + 2) ^ 8 : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
    exact this)
  have hL3 : 1 ≤ Real.log N ^ 3 := one_le_pow₀ hL1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log N ^ 3)]
  have hcube : Real.log (((N + 2) ^ 8 : ℕ) : ℝ) ^ 3 ≤ 4096 * Real.log N ^ 3 := by
    calc _ ≤ (16 * Real.log N) ^ 3 := pow_le_pow_left₀ hlogB0 hlogB 3
      _ = 4096 * Real.log N ^ 3 := by ring
  have hK : K ≤ |K| * Real.log N ^ 3 :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hL3)
  have := mul_le_mul_of_nonneg_left hcube hC
  calc ((S N).card : ℝ) ≤ K + C * Real.log (((N + 2) ^ 8 : ℕ) : ℝ) ^ 3 := hb
    _ ≤ |K| * Real.log N ^ 3 + C * (4096 * Real.log N ^ 3) := by linarith
    _ = (|K| + 4096 * C) * Real.log N ^ 3 := by ring

end LegendreExceptions
