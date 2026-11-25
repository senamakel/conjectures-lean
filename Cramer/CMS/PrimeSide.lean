import Cramer.CMS.ZeroBound
import Cramer.CMS.BrunTitchmarsh
import Cramer.PrimePowers

/-!
# The prime side of the weight

With knots `n_j = B + j s` (`8 ∣ s`) the weight is linear on each segment,
`w(n_j + t) = s α_j − t β_j` (`wt_seg`, `α_j = Σ_{i>j} a_i (i−j)`, `β_j = Σ_{i>j} a_i`). Cut every
segment into eight pieces of length `s' = s/8`. On a piece the weight is at most `s'·v_{j,i}`
(`v` the larger end value, scale `8·2²⁰`). If no prime lies in `[n_8, n_24)`, the primes of the
other pieces are counted by the Brun–Titchmarsh bound `π ≤ s'/W(√(2s'/3))`, and the proper prime
powers of the whole support `[n_0, n_32)` by `Cramer.sum_vonMangoldt_not_prime_le`
(`sum_Lambda_wt_le`):

`Σ_n Λ(n) w(n) ≤ s'² log n_32 · V_out / W + s' · V_max · PP`,

`V_out = 18838744` (`Vout_val`), `V_max = 8 · 2²⁰`.
-/

namespace Cramer.CMS

open Finset Real ArithmeticFunction
open CramerCompute (D0)

/-- `α_j = Σ_{i>j} a_i (i − j)`. -/
def alph (j : ℕ) : ℤ := ∑ i ∈ range 33, if j < i then aco cdat i * ((i : ℤ) - j) else 0
/-- `β_j = Σ_{i>j} a_i`. -/
def bet (j : ℕ) : ℤ := ∑ i ∈ range 33, if j < i then aco cdat i else 0

/-- The bound on a piece (scale `8 · 2²⁰`). -/
def vpc (j i : ℕ) : ℤ := max (max (8 * alph j - i * bet j) (8 * alph j - (i + 1) * bet j)) 0

/-- The pieces outside the gap. -/
def outside (j : ℕ) : Bool := decide (j < 8) || decide (24 ≤ j)

theorem Vout_val : ∑ j ∈ range 32, (if outside j then ∑ i ∈ range 8, vpc j i else 0) = 18838744 := by
  decide +kernel

theorem vpc_le : ∀ j ∈ range 32, ∀ i ∈ range 8, vpc j i ≤ 8388608 := by decide +kernel

/-- **The weight on a segment.** -/
lemma wt_seg (B s j t : ℕ) (ht : t ≤ s) :
    wt cdat 32 B s (kn B s j + t) = (s : ℝ) * alph j - t * bet j := by
  unfold wt alph bet
  push_cast
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  have e : ((kn B s i : ℕ) : ℝ) - (((kn B s j : ℕ) : ℝ) + t) = ((i : ℝ) - j) * s - t := by
    unfold kn; push_cast; ring
  rw [e]
  by_cases hji : j < i
  · rw [if_pos hji, if_pos hji]
    have : (1 : ℝ) ≤ (i : ℝ) - j := by
      have : j + 1 ≤ i := hji
      have : ((j + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast this
      push_cast at this; linarith
    have ht' : (t : ℝ) ≤ s := by exact_mod_cast ht
    rw [max_eq_left (by nlinarith)]
    ring
  · rw [if_neg hji, if_neg hji]
    have : (i : ℝ) - j ≤ 0 := by
      have : (i : ℝ) ≤ j := by exact_mod_cast not_lt.1 hji
      linarith
    rw [max_eq_right (by nlinarith [Nat.cast_nonneg (α := ℝ) s, Nat.cast_nonneg (α := ℝ) t])]
    ring

/-- `Σ_{m < K s'} F m = Σ_{q < K} Σ_{r < s'} F(q s' + r)`. -/
lemma sum_range_blocks (F : ℕ → ℝ) (K s' : ℕ) :
    ∑ m ∈ range (K * s'), F m = ∑ q ∈ range K, ∑ r ∈ range s', F (q * s' + r) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

lemma wt_zero_of_le {B s n : ℕ} (hn : n ≤ kn B s 0) : wt cdat 32 B s n = 0 := by
  unfold wt
  have h1 : ∀ j ∈ range (32 + 1), max ((kn B s j : ℝ) - n) 0 = (kn B s j : ℝ) - n := by
    intro j _
    have : (n : ℝ) ≤ kn B s j := by
      have : kn B s 0 ≤ kn B s j := by unfold kn; nlinarith
      exact_mod_cast hn.trans this
    rw [max_eq_left (by linarith)]
  rw [sum_congr rfl fun j hj => by rw [h1 j hj]]
  obtain ⟨m1, -⟩ := sum_aco_kn cdat cdat_zero cdat_high B s
  have m0 := sum_aco cdat cdat_zero cdat_high
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, m1, m0, zero_mul, sub_zero]

lemma wt_zero_of_ge {B s n : ℕ} (hn : kn B s 32 ≤ n) : wt cdat 32 B s n = 0 := by
  unfold wt
  refine sum_eq_zero fun j hj => ?_
  have : (kn B s j : ℝ) ≤ n := by
    have : kn B s j ≤ kn B s 32 := by unfold kn; have := mem_range.1 hj; nlinarith
    exact_mod_cast this.trans hn
  rw [max_eq_right (by linarith), mul_zero]

/-- The weight on a piece: `w ≤ s' v_{j,i}` on `[n_j + i s', n_j + (i+1) s')`. -/
lemma wt_piece_le {B s' j i r : ℕ} (hi : i < 8) (hr : r < s') :
    wt cdat 32 B (8 * s') (kn B (8 * s') j + (i * s' + r)) ≤ (s' : ℝ) * vpc j i := by
  have ht : i * s' + r ≤ 8 * s' := by nlinarith
  rw [wt_seg _ _ _ _ ht]
  unfold vpc
  push_cast
  have hs' : (0 : ℝ) ≤ s' := Nat.cast_nonneg _
  set α := (alph j : ℝ); set β := (bet j : ℝ)
  -- linear in `t = i s' + r ∈ [i s', (i+1) s']`
  have hr' : (r : ℝ) ≤ s' := by exact_mod_cast hr.le
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have key : (8 * (s' : ℝ)) * α - ((i : ℝ) * s' + r) * β ≤
      (s' : ℝ) * max (8 * α - i * β) (8 * α - (i + 1) * β) := by
    rcases le_total 0 β with hb | hb
    · calc (8 * (s' : ℝ)) * α - ((i : ℝ) * s' + r) * β ≤ (s' : ℝ) * (8 * α - i * β) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hs'
    · calc (8 * (s' : ℝ)) * α - ((i : ℝ) * s' + r) * β ≤ (s' : ℝ) * (8 * α - (i + 1) * β) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hs'
  have key2 := key.trans (mul_le_mul_of_nonneg_left (le_max_left
    (max (8 * α - i * β) (8 * α - (i + 1) * β)) 0) hs')
  convert key2 using 1

lemma vpc_nonneg (j i : ℕ) : 0 ≤ vpc j i := le_max_right _ _

/-- The prime-power part of `[a, b)`. -/
noncomputable def PPb (a b : ℕ) : ℝ := Real.log b * ((√(b : ℝ) - √(a : ℝ) + 1) + ((b : ℝ) ^ ((1 : ℝ) / 3) + 1))

/-- `Σ_{piece} Λ(n) ≤ log b · #primes + Σ_{piece, not prime} Λ(n)`. -/
lemma sum_Lambda_piece_le (u s' b : ℕ) (hb : u + s' ≤ b) :
    ∑ r ∈ range s', (Λ (u + r) : ℝ) ≤
      Real.log b * (#((Ico u (u + s')).filter Nat.Prime) : ℝ) +
        ∑ r ∈ range s', (if (u + r).Prime then 0 else (Λ (u + r) : ℝ)) := by
  have hsplit : ∀ r ∈ range s', (Λ (u + r) : ℝ) = (if (u + r).Prime then (Λ (u + r) : ℝ) else 0) +
      (if (u + r).Prime then 0 else (Λ (u + r) : ℝ)) := fun r _ => by split_ifs <;> simp
  rw [sum_congr rfl hsplit, sum_add_distrib]
  gcongr
  have h1 : ∑ r ∈ range s', (if (u + r).Prime then (Λ (u + r) : ℝ) else 0) ≤
      ∑ r ∈ range s', (if (u + r).Prime then Real.log b else 0) := by
    refine sum_le_sum fun r hr => ?_
    split_ifs with hp
    · rw [vonMangoldt_apply_prime hp]
      have : (u + r : ℕ) ≤ b := by have := mem_range.1 hr; omega
      exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast this)
    · exact le_rfl
  refine h1.trans (le_of_eq ?_)
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  rw [card_eq_of_equiv]
  exact {
    toFun := fun r => ⟨u + r.1, by
      obtain ⟨r, hr⟩ := r; simp only [mem_filter, mem_range] at hr
      simp only [mem_filter, mem_Ico]; exact ⟨⟨by omega, by omega⟩, hr.2⟩⟩
    invFun := fun n => ⟨n.1 - u, by
      obtain ⟨n, hn⟩ := n; simp only [mem_filter, mem_Ico] at hn
      simp only [mem_filter, mem_range]; exact ⟨by omega, by rw [show u + (n - u) = n by omega]; exact hn.2⟩⟩
    left_inv := fun r => by obtain ⟨r, hr⟩ := r; simp
    right_inv := fun n => by
      obtain ⟨n, hn⟩ := n; simp only [mem_filter, mem_Ico] at hn
      simp only [Subtype.mk.injEq]; omega }

/-- **The prime side.** -/
theorem sum_Lambda_wt_le {B s' : ℕ} (hs' : 1 ≤ s') (hB : 1 ≤ B)
    (hb2 : kn B (8 * s') 32 ≤ 2 * kn B (8 * s') 0)
    (hR : Real.sqrt (2 * (s' : ℕ) / 3) + 1 ≤ B) (hW : 0 < W (Real.sqrt (2 * (s' : ℕ) / 3)))
    (hnop : ∀ p : ℕ, p.Prime → kn B (8 * s') 8 ≤ p → p < kn B (8 * s') 24 → False) :
    ∑ n ∈ range (kn B (8 * s') 32 + 1), (Λ n : ℝ) * wt cdat 32 B (8 * s') n ≤
      (s' : ℝ) ^ 2 * Real.log (kn B (8 * s') 32) * 18838744 / W (Real.sqrt (2 * (s' : ℕ) / 3)) +
        s' * 8388608 * PPb (kn B (8 * s') 0) (kn B (8 * s') 32) := by
  set s := 8 * s'
  set a := kn B s 0 with ha
  set b := kn B s 32 with hb
  set WR := W (Real.sqrt (2 * (s' : ℕ) / 3))
  have hab : a ≤ b := by simp only [ha, hb, kn]; omega
  have hba : b - a = 32 * 8 * s' := by simp only [ha, hb, kn, s]; omega
  set f : ℕ → ℝ := fun n => (Λ n : ℝ) * wt cdat 32 B s n
  -- only `[a, b)` contributes
  have h1 : ∑ n ∈ range (b + 1), f n = ∑ n ∈ Ico a b, f n := by
    rw [← sum_range_add_sum_Ico _ (show a ≤ b + 1 by omega), sum_Ico_succ_top hab]
    have z1 : ∑ n ∈ range a, f n = 0 :=
      sum_eq_zero fun n hn => by
        simp only [f]; rw [wt_zero_of_le (by have := mem_range.1 hn; omega), mul_zero]
    have z2 : f b = 0 := by simp only [f]; rw [wt_zero_of_ge le_rfl, mul_zero]
    rw [z1, z2]; ring
  -- the pieces
  have h2 : ∑ n ∈ Ico a b, f n = ∑ j ∈ range 32, ∑ i ∈ range 8, ∑ r ∈ range s',
      f (kn B s j + (i * s' + r)) := by
    rw [sum_Ico_eq_sum_range, hba, sum_range_blocks, sum_range_blocks]
    refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => sum_congr rfl fun r _ => ?_
    congr 1; simp only [ha, kn, s]; ring
  have hPP : ∑ n ∈ Ico a b, (if n.Prime then 0 else (Λ n : ℝ)) = ∑ j ∈ range 32, ∑ i ∈ range 8,
      ∑ r ∈ range s', (if (kn B s j + (i * s' + r)).Prime then 0 else (Λ (kn B s j + (i * s' + r)) : ℝ)) := by
    rw [sum_Ico_eq_sum_range, hba, sum_range_blocks, sum_range_blocks]
    refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => sum_congr rfl fun r _ => ?_
    have : a + ((j * 8 + i) * s' + r) = kn B s j + (i * s' + r) := by simp only [ha, kn, s]; ring
    rw [this]
  have hPPb : ∑ n ∈ Ico a b, (if n.Prime then 0 else (Λ n : ℝ)) ≤ PPb a b := by
    have e : ∑ n ∈ Ico a b, (if n.Prime then 0 else (Λ n : ℝ)) =
        ∑ n ∈ (Ico a b).filter (fun k => ¬ k.Prime), (Λ n : ℝ) := by
      rw [sum_filter]; refine sum_congr rfl fun n _ => by split_ifs <;> simp_all
    rw [e]
    exact sum_vonMangoldt_not_prime_le a b (by simp only [ha, kn]; omega) hab hb2
  -- each piece
  have hpiece : ∀ j ∈ range 32, ∀ i ∈ range 8, ∑ r ∈ range s', f (kn B s j + (i * s' + r)) ≤
      (s' : ℝ) * vpc j i * (Real.log b * (if outside j then (s' : ℝ) / WR else 0) +
        ∑ r ∈ range s', (if (kn B s j + (i * s' + r)).Prime then 0 else
          (Λ (kn B s j + (i * s' + r)) : ℝ))) := by
    intro j hj i hi
    have hvpc : (0 : ℝ) ≤ vpc j i := by exact_mod_cast vpc_nonneg j i
    have hs0 : (0 : ℝ) ≤ s' := Nat.cast_nonneg _
    set u := kn B s j + i * s'
    have hu : ∀ r, kn B s j + (i * s' + r) = u + r := fun r => by simp only [u]; ring
    have step1 : ∑ r ∈ range s', f (kn B s j + (i * s' + r)) ≤
        (s' : ℝ) * vpc j i * ∑ r ∈ range s', (Λ (u + r) : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun r hr => ?_
      simp only [f]
      rw [hu r, mul_comm ((s' : ℝ) * vpc j i)]
      refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
      rw [← hu r]
      exact wt_piece_le (mem_range.1 hi) (mem_range.1 hr)
    have hub : u + s' ≤ b := by
      simp only [u, hb, kn, s]; have := mem_range.1 hj; have := mem_range.1 hi; nlinarith
    have step2 := sum_Lambda_piece_le u s' b hub
    have hcount : Real.log b * (#((Ico u (u + s')).filter Nat.Prime) : ℝ) ≤
        Real.log b * (if outside j then (s' : ℝ) / WR else 0) := by
      have hlb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by simp only [hb, kn]; omega : 1 ≤ b))
      apply mul_le_mul_of_nonneg_left _ hlb
      by_cases ho : outside j
      · rw [if_pos ho]
        -- Brun–Titchmarsh on `(u − 1, u − 1 + s']`
        have hu1 : 1 ≤ u := by simp only [u, kn]; omega
        have hset : (Ico u (u + s')).filter Nat.Prime = (Ioc (u - 1) (u - 1 + s')).filter Nat.Prime := by
          congr 1; ext n; simp only [mem_Ico, mem_Ioc]; omega
        rw [hset]
        have hRu : Real.sqrt (2 * (s' : ℕ) / 3) ≤ ((u - 1 : ℕ) : ℝ) := by
          have : (B : ℝ) ≤ u := by exact_mod_cast (by simp only [u, kn]; omega : B ≤ u)
          rw [Nat.cast_sub hu1]; push_cast; linarith
        have hbt := card_primes_mul_W_le (M₀ := u - 1) hs' hRu
        rw [le_div_iff₀ hW]; exact hbt
      · rw [if_neg ho]
        have : (Ico u (u + s')).filter Nat.Prime = ∅ := by
          refine filter_eq_empty_iff.2 fun n hn hp => ?_
          simp only [mem_Ico] at hn
          have hj8 : 8 ≤ j ∧ j < 24 := by
            simp only [outside, Bool.or_eq_true, decide_eq_true_eq, not_or] at ho; omega
          refine hnop n hp ?_ ?_
          · simp only [kn, u, s] at hn ⊢; nlinarith
          · simp only [kn, u, s] at hn ⊢; have := mem_range.1 hi; nlinarith
        rw [this]; simp
    calc _ ≤ (s' : ℝ) * vpc j i * ∑ r ∈ range s', (Λ (u + r) : ℝ) := step1
      _ ≤ (s' : ℝ) * vpc j i * (Real.log b * (if outside j then (s' : ℝ) / WR else 0) +
          ∑ r ∈ range s', (if (u + r).Prime then 0 else (Λ (u + r) : ℝ))) := by
          gcongr; exact step2.trans (by linarith)
      _ = _ := by simp only [hu]
  -- assemble
  rw [h1, h2]
  refine (sum_le_sum fun j hj => sum_le_sum fun i hi => hpiece j hj i hi).trans ?_
  simp only [mul_add, sum_add_distrib]
  have hA : ∑ j ∈ range 32, ∑ i ∈ range 8, (s' : ℝ) * vpc j i *
      (Real.log b * (if outside j then (s' : ℝ) / WR else 0)) =
      (s' : ℝ) ^ 2 * Real.log b * 18838744 / WR := by
    have hv := Vout_val
    have : ∑ j ∈ range 32, ∑ i ∈ range 8, (s' : ℝ) * vpc j i *
        (Real.log b * (if outside j then (s' : ℝ) / WR else 0)) =
        (s' : ℝ) ^ 2 * Real.log b / WR *
          ((∑ j ∈ range 32, (if outside j then ∑ i ∈ range 8, vpc j i else 0) : ℤ) : ℝ) := by
      push_cast
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [mul_sum]; refine sum_congr rfl fun i _ => by field_simp
      · simp
    rw [this, hv]; push_cast; ring
  have hB2 : ∑ j ∈ range 32, ∑ i ∈ range 8, (s' : ℝ) * vpc j i *
      ∑ r ∈ range s', (if (kn B s j + (i * s' + r)).Prime then 0 else (Λ (kn B s j + (i * s' + r)) : ℝ)) ≤
      (s' : ℝ) * 8388608 * PPb a b := by
    calc _ ≤ ∑ j ∈ range 32, ∑ i ∈ range 8, (s' : ℝ) * 8388608 *
          ∑ r ∈ range s', (if (kn B s j + (i * s' + r)).Prime then 0 else
            (Λ (kn B s j + (i * s' + r)) : ℝ)) := by
          refine sum_le_sum fun j hj => sum_le_sum fun i hi => ?_
          have hv : (vpc j i : ℝ) ≤ 8388608 := by exact_mod_cast vpc_le j hj i hi
          have hnn : 0 ≤ ∑ r ∈ range s', (if (kn B s j + (i * s' + r)).Prime then 0 else
              (Λ (kn B s j + (i * s' + r)) : ℝ)) :=
            sum_nonneg fun r _ => by split_ifs; exact le_rfl; exact vonMangoldt_nonneg
          gcongr
      _ = (s' : ℝ) * 8388608 * ∑ n ∈ Ico a b, (if n.Prime then 0 else (Λ n : ℝ)) := by
          rw [hPP, mul_sum]; refine sum_congr rfl fun j _ => by rw [mul_sum]
      _ ≤ _ := by gcongr
  linarith

end Cramer.CMS
