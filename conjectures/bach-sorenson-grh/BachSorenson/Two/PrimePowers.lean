import Mathlib

/-!
# Log-weighted prime powers that are not primes

`PPl x = Σ_{n ≤ x, n not prime} Λ(n) log(x/n)`. Grouping `n = p^k` by the exponent `k ≥ 2`,
`PPl x ≤ Σ_{2 ≤ k ≤ log₂ x} k Σ_{p ≤ x^{1/k}} log p · log(x^{1/k}/p)`, and Chebyshev's
`θ(N) ≤ N log 4` (Mathlib) gives `Σ_{p ≤ y} log p · log(y/p) ≤ y log 4` by summation by parts.
So (`ppl_le`)

`PPl x ≤ log 4 · (2 x^{1/2} + 3 x^{1/3} + 60 x^{1/4} + (log₂ x)² x^{1/12})`.

Bach–Sorenson's corresponding term is their `p(x)` (Lemma 4.11), bounded with Costa Pereira's
`ψ − θ`; here only Chebyshev's bound is used.
-/

namespace BachSorenson.Two

open ArithmeticFunction Finset Real Chebyshev

/-- `Σ_{n ≤ x, n not prime} Λ(n) log(x/n)`. -/
noncomputable def PPl (x : ℕ) : ℝ :=
  ∑ n ∈ (range (x + 1)).filter (fun n => ¬ n.Prime), (Λ n : ℝ) * Real.log ((x : ℝ) / n)

/-- `G(Y) = Σ_{p ≤ Y} log p · log(Y/p)`. -/
noncomputable def Gs (Y : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p * Real.log (y / p)

lemma sum_log_primes_le (Y : ℕ) :
    ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ Real.log 4 * Y := by
  have h := theta_le_log4_mul_x (x := (Y : ℝ)) (Nat.cast_nonneg Y)
  rw [theta_eq_sum_Icc, Nat.floor_natCast] at h
  have e : (range (Y + 1)).filter Nat.Prime = (Icc 0 Y).filter Nat.Prime := by
    ext p; simp [Nat.lt_succ_iff]
  rw [e]; exact h

lemma Gs_succ (Y : ℕ) (hY : 1 ≤ Y) :
    Gs (Y + 1) (Y + 1 : ℕ) = Gs Y Y + (Real.log (Y + 1) - Real.log Y)
      * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p := by
  unfold Gs
  rw [sum_filter, sum_range_succ, ← sum_filter]
  have hlast : (if (Y + 1).Prime then Real.log ((Y + 1 : ℕ) : ℝ) * Real.log (((Y + 1 : ℕ) : ℝ)
      / ((Y + 1 : ℕ) : ℝ)) else 0) = 0 := by
    split_ifs
    · rw [div_self (by positivity), Real.log_one, mul_zero]
    · rfl
  rw [hlast, add_zero, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  have hpp := (mem_filter.1 hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  rw [Real.log_div (by positivity) hp0.ne', Real.log_div hY0.ne' hp0.ne']
  push_cast
  ring

lemma Gs_self_le (Y : ℕ) (hY : 1 ≤ Y) : Gs Y Y ≤ Real.log 4 * (Y - 1) := by
  induction Y, hY using Nat.le_induction with
  | base => simp [Gs, Finset.sum_filter, Finset.sum_range_succ, Nat.not_prime_zero,
      Nat.not_prime_one]
  | succ Y hY ih =>
    rw [Gs_succ Y hY]
    have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
    have hl : Real.log (Y + 1) - Real.log Y ≤ 1 / Y := by
      rw [← Real.log_div (by positivity) hY0.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (Y + 1) / Y by positivity)
      have e : ((Y : ℝ) + 1) / Y - 1 = 1 / Y := by field_simp; ring
      linarith
    have hl0 : 0 ≤ Real.log (Y + 1) - Real.log Y := by
      rw [sub_nonneg]; exact Real.log_le_log hY0 (by linarith)
    have hθ := sum_log_primes_le Y
    have hθ0 : 0 ≤ ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p :=
      sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_lt.le)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : (Real.log (Y + 1) - Real.log Y) * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p
        ≤ (1 / Y) * (Real.log 4 * Y) := mul_le_mul hl hθ hθ0 (by positivity)
    rw [show (1 / (Y : ℝ)) * (Real.log 4 * Y) = Real.log 4 by field_simp] at this
    push_cast
    linarith

/-- `Σ_{p ≤ y} log p · log(y/p) ≤ y log 4` for real `y ≥ 1`. -/
lemma Gs_floor_le {y : ℝ} (hy : 1 ≤ y) : Gs ⌊y⌋₊ y ≤ Real.log 4 * y := by
  set Y := ⌊y⌋₊ with hYdef
  have hY : 1 ≤ Y := Nat.le_floor (by simpa using hy)
  have hYy : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have e : Gs Y y = Gs Y Y + Real.log (y / Y) * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p := by
    unfold Gs
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.1 hp).2.pos
    rw [Real.log_div (by linarith) hp0.ne', Real.log_div hY0.ne' hp0.ne',
      Real.log_div (by linarith) hY0.ne']
    ring
  rw [e]
  have h1 := Gs_self_le Y hY
  have hθ := sum_log_primes_le Y
  have hθ0 : 0 ≤ ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p :=
    sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (mem_filter.1 hp).2.one_lt.le)
  have hl : Real.log (y / Y) ≤ y / Y - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hl0 : 0 ≤ Real.log (y / Y) := Real.log_nonneg (by rw [le_div_iff₀ hY0]; linarith)
  have : Real.log (y / Y) * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p
      ≤ (y / Y - 1) * (Real.log 4 * Y) := mul_le_mul hl hθ hθ0 (by linarith [hl0])
  have e2 : (y / Y - 1) * (Real.log 4 * Y) = Real.log 4 * (y - Y) := by field_simp
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith

/-- The `k`-th group: `Σ_{p prime, p^k ≤ x} log p · log(x/p^k) ≤ k log 4 · x^{1/k}`. -/
lemma group_le (x : ℕ) (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    ∑ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ p ^ k ≤ x),
        Real.log p * Real.log ((x : ℝ) / ((p ^ k : ℕ) : ℝ))
      ≤ k * (Real.log 4 * (x : ℝ) ^ ((k : ℝ)⁻¹)) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  set y := (x : ℝ) ^ ((k : ℝ)⁻¹) with hy
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by positivity)
  have hy0 : 0 < y := by linarith
  have hyk : y ^ k = x := by rw [hy]; exact Real.rpow_inv_natCast_pow hx0.le (by omega)
  have hle : ∀ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ p ^ k ≤ x),
      Real.log p * Real.log ((x : ℝ) / ((p ^ k : ℕ) : ℝ)) = k * (Real.log p * Real.log (y / p)) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.1 hp).2.1.pos
    rw [Nat.cast_pow, Real.log_div hx0.ne' (by positivity), Real.log_div hy0.ne' hp0.ne',
      Real.log_pow, ← hyk, Real.log_pow]
    ring
  rw [sum_congr rfl hle, ← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hk0.le
  refine le_trans ?_ (Gs_floor_le hy1)
  unfold Gs
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
  · intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    refine ⟨?_, hp.2.1⟩
    have hpy : (p : ℝ) ≤ y := by
      have h1 : ((p : ℝ) ^ k) ≤ x := by exact_mod_cast hp.2.2
      by_contra h
      push Not at h
      have : y ^ k < (p : ℝ) ^ k := pow_lt_pow_left₀ h hy0.le (by omega)
      linarith
    have := Nat.le_floor hpy
    omega
  · simp only [mem_filter, mem_range] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hpY : (p : ℝ) ≤ y := by
      have := hp.1
      have h2 : (p : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.lt_succ_iff.1 this
      exact h2.trans (Nat.floor_le hy0.le)
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))
      (Real.log_nonneg (by rw [le_div_iff₀ hp0]; linarith))

/-- `PPl x ≤ Σ_{2 ≤ k ≤ log₂ x} Σ_{p prime, p^k ≤ x} log p · log(x/p^k)`. -/
lemma ppl_le_groups (x : ℕ) (hx : 1 ≤ x) :
    PPl x ≤ ∑ k ∈ Icc 2 (Nat.log 2 x), ∑ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ p ^ k ≤ x),
        Real.log p * Real.log ((x : ℝ) / ((p ^ k : ℕ) : ℝ)) := by
  classical
  set f : ℕ → ℝ := fun n => (Λ n : ℝ) * Real.log ((x : ℝ) / n) with hf
  have hf0 : ∀ n ≤ x, 0 ≤ f n := fun n hn => by
    refine mul_nonneg vonMangoldt_nonneg ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · apply Real.log_nonneg
      rw [le_div_iff₀ (by exact_mod_cast hn0)]
      simpa using (show (n : ℝ) ≤ x by exact_mod_cast hn)
  set B := ((Icc 2 (Nat.log 2 x)) ×ˢ (range (x + 1))).filter
    (fun kp : ℕ × ℕ => kp.2.Prime ∧ kp.2 ^ kp.1 ≤ x) with hB
  set g : ℕ × ℕ → ℕ := fun kp => kp.2 ^ kp.1
  have hinj : Set.InjOn g B := by
    intro a ha b hb hab
    simp only [hB, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at ha hb
    have := Nat.Prime.pow_inj' ha.2.1 hb.2.1 (by omega) (by omega) hab
    exact Prod.ext this.2 this.1
  -- the non-prime terms live on `g '' B`
  have h1 : PPl x ≤ ∑ n ∈ B.image g, f n := by
    unfold PPl
    rw [sum_filter]
    have : ∑ n ∈ range (x + 1), (if ¬ n.Prime then (Λ n : ℝ) * Real.log ((x : ℝ) / n) else 0)
        = ∑ n ∈ (range (x + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime), f n := by
      rw [sum_filter]
      refine sum_congr rfl fun n _ => ?_
      by_cases hp : n.Prime
      · simp [hp]
      · by_cases hpp : IsPrimePow n
        · simp [hp, hpp, f]
        · simp [hp, hpp, vonMangoldt_eq_zero_iff.2 hpp]
    rw [this]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun n hn _ => ?_
    · intro n hn
      simp only [mem_filter, mem_range] at hn
      obtain ⟨hnx, hpp, hnp⟩ := hn
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      have hk2 : 2 ≤ k := by
        by_contra h
        have : k = 1 := by omega
        subst this; exact hnp (by simpa using hr)
      refine mem_image.2 ⟨(k, r), ?_, rfl⟩
      simp only [hB, mem_filter, mem_product, mem_Icc, mem_range]
      have hrk : r ^ k ≤ x := by omega
      refine ⟨⟨⟨hk2, Nat.le_log_of_pow_le (by norm_num) ((Nat.pow_le_pow_left hr.two_le k).trans hrk)⟩,
        ?_⟩, hr, hrk⟩
      have : r ≤ r ^ k := Nat.le_self_pow (by omega) r
      omega
    · simp only [mem_image, hB, mem_filter, mem_product, mem_range] at hn
      obtain ⟨kp, hkp, rfl⟩ := hn
      exact hf0 _ hkp.2.2
  rw [sum_image hinj] at h1
  refine h1.trans (le_of_eq ?_)
  rw [hB, sum_filter, sum_product]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_filter]
  refine sum_congr rfl fun p hp => ?_
  split_ifs with h
  · simp only [f, g]
    rw [vonMangoldt_apply_pow (by simp at hk; omega), vonMangoldt_apply_prime h.1]
  · rfl

/-- `PPl x ≤ log 4 · (2 x^{1/2} + 3 x^{1/3} + 60 x^{1/4} + (log₂ x)² x^{1/12})`. -/
theorem ppl_le (x : ℕ) (hx : 1 ≤ x) :
    PPl x ≤ Real.log 4 * (2 * (x : ℝ) ^ ((2 : ℝ)⁻¹) + 3 * (x : ℝ) ^ ((3 : ℝ)⁻¹)
      + 60 * (x : ℝ) ^ ((4 : ℝ)⁻¹) + ((Nat.log 2 x : ℕ) : ℝ) ^ 2 * (x : ℝ) ^ ((12 : ℝ)⁻¹)) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  set K := Nat.log 2 x
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine (ppl_le_groups x hx).trans ?_
  set B : ℕ → ℝ := fun k => if k = 2 then 2 * (x : ℝ) ^ ((2 : ℝ)⁻¹)
    else if k = 3 then 3 * (x : ℝ) ^ ((3 : ℝ)⁻¹)
    else if k ≤ 11 then k * (x : ℝ) ^ ((4 : ℝ)⁻¹) else K * (x : ℝ) ^ ((12 : ℝ)⁻¹) with hBdef
  have hB0 : ∀ k, 0 ≤ B k := fun k => by simp only [hBdef]; split_ifs <;> positivity
  have hstep : ∀ k ∈ Icc 2 K, ∑ p ∈ (range (x + 1)).filter (fun p => p.Prime ∧ p ^ k ≤ x),
      Real.log p * Real.log ((x : ℝ) / ((p ^ k : ℕ) : ℝ)) ≤ Real.log 4 * B k := by
    intro k hk
    have hk' := mem_Icc.1 hk
    refine (group_le x hx (by omega)).trans ?_
    have hmono : ∀ {m : ℕ}, 1 ≤ m → m ≤ k → (x : ℝ) ^ ((k : ℝ)⁻¹) ≤ (x : ℝ) ^ ((m : ℝ)⁻¹) :=
      fun {m} hm hmk => Real.rpow_le_rpow_of_exponent_le hx1
        (inv_anti₀ (by exact_mod_cast hm) (by exact_mod_cast hmk))
    simp only [hBdef]
    split_ifs with h2 h3 h11
    · subst h2; norm_num; nlinarith
    · subst h3; norm_num; nlinarith
    · have := hmono (m := 4) (by norm_num) (by omega)
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      calc (k : ℝ) * (Real.log 4 * (x : ℝ) ^ ((k : ℝ)⁻¹))
          = Real.log 4 * (k * (x : ℝ) ^ ((k : ℝ)⁻¹)) := by ring
        _ ≤ Real.log 4 * (k * (x : ℝ) ^ (((4 : ℕ) : ℝ)⁻¹)) := by gcongr
        _ = _ := by norm_num
    · have := hmono (m := 12) (by norm_num) (by omega)
      have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk'.2
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      calc (k : ℝ) * (Real.log 4 * (x : ℝ) ^ ((k : ℝ)⁻¹))
          = Real.log 4 * (k * (x : ℝ) ^ ((k : ℝ)⁻¹)) := by ring
        _ ≤ Real.log 4 * (K * (x : ℝ) ^ (((12 : ℕ) : ℝ)⁻¹)) := by
          gcongr
        _ = _ := by norm_num
  refine (sum_le_sum hstep).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ h4
  have hsplit : ∑ k ∈ Icc 2 K, B k ≤ ∑ k ∈ Icc 2 11, B k + ∑ k ∈ Icc 12 K, B k := by
    rw [← sum_union (by
      rw [disjoint_left]; intro k h1 h2; simp only [mem_Icc] at h1 h2; omega)]
    exact sum_le_sum_of_subset_of_nonneg (fun k hk => by
      simp only [mem_union, mem_Icc] at hk ⊢; omega) fun k _ _ => hB0 k
  have hsmall : ∑ k ∈ Icc 2 11, B k = 2 * (x : ℝ) ^ ((2 : ℝ)⁻¹) + 3 * (x : ℝ) ^ ((3 : ℝ)⁻¹)
      + 60 * (x : ℝ) ^ ((4 : ℝ)⁻¹) := by
    simp only [hBdef]
    rw [show Icc 2 11 = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11} by decide]
    simp [Finset.sum_insert]
    ring
  have hlarge : ∑ k ∈ Icc 12 K, B k ≤ (K : ℝ) ^ 2 * (x : ℝ) ^ ((12 : ℝ)⁻¹) := by
    have hB : ∀ k ∈ Icc 12 K, B k = K * (x : ℝ) ^ ((12 : ℝ)⁻¹) := fun k hk => by
      have := (mem_Icc.1 hk).1
      simp only [hBdef]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [sum_congr rfl hB, sum_const, nsmul_eq_mul]
    have hc : ((Icc 12 K).card : ℝ) ≤ K := by
      rw [Nat.card_Icc]; exact_mod_cast (by omega : K + 1 - 12 ≤ K)
    have : (0 : ℝ) ≤ K * (x : ℝ) ^ ((12 : ℝ)⁻¹) := by positivity
    calc ((Icc 12 K).card : ℝ) * (K * (x : ℝ) ^ ((12 : ℝ)⁻¹))
        ≤ K * (K * (x : ℝ) ^ ((12 : ℝ)⁻¹)) := mul_le_mul_of_nonneg_right hc this
      _ = _ := by ring
  linarith

end BachSorenson.Two
