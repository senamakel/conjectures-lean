import Mathlib

/-!
# Prime powers below `x`

`Σ_{n < x, n = p^k} Λ(n) ≤ log p · Nat.log p x ≤ log x`, and `Nat.log p x ≤ (2/3)√x` once
`x ≥ 144`. A sum of `Λ` over a set of `n < x` whose prime-power members all have `minFac` in `S`
is bounded by the sum of these fibre sums over `S`.
-/

namespace Ankeny

open ArithmeticFunction Finset

/-- The fibre of prime powers of `p` below `x`. -/
def ppFiber (x p : ℕ) : Finset ℕ := (range x).filter fun n => IsPrimePow n ∧ n.minFac = p

lemma ppFiber_subset (x p : ℕ) (hp : p.Prime) :
    ppFiber x p ⊆ (Icc 1 (Nat.log p x)).image (p ^ ·) := by
  intro n hn
  simp only [ppFiber, mem_filter, mem_range] at hn
  obtain ⟨hnx, hpp, hmin⟩ := hn
  obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
  have hrp : r = p := by rw [← hmin, Nat.Prime.pow_minFac hr hk.ne']
  subst hrp
  refine mem_image.2 ⟨k, mem_Icc.2 ⟨hk, ?_⟩, rfl⟩
  exact Nat.le_log_of_pow_le hr.one_lt hnx.le

lemma card_ppFiber_le (x p : ℕ) (hp : p.Prime) : (ppFiber x p).card ≤ Nat.log p x :=
  (card_le_card (ppFiber_subset x p hp)).trans (card_image_le.trans (by simp))

lemma sum_ppFiber_le (x p : ℕ) (hp : p.Prime) :
    ∑ n ∈ ppFiber x p, (Λ n : ℝ) ≤ Real.log p * Nat.log p x := by
  have h : ∀ n ∈ ppFiber x p, (Λ n : ℝ) = Real.log p := by
    intro n hn
    simp only [ppFiber, mem_filter] at hn
    rw [vonMangoldt_apply, ite_eq_left hn.2.1, hn.2.2]
  rw [sum_congr rfl h, sum_const, nsmul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_ppFiber_le x p hp)
    (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))

lemma log_mul_natLog_le (x p : ℕ) (hp : p.Prime) (hx : 1 ≤ x) :
    Real.log p * Nat.log p x ≤ Real.log x := by
  have h := Nat.pow_log_le_self p (by omega : x ≠ 0)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc Real.log p * Nat.log p x = Real.log ((p : ℝ) ^ Nat.log p x) := by
        rw [Real.log_pow]; ring
    _ ≤ Real.log x := Real.log_le_log (by positivity) (by exact_mod_cast h)

lemma nine_sq_le_four_two_pow (k : ℕ) (hk : 9 ≤ k) : 9 * k ^ 2 ≤ 4 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have : 9 * (k + 1) ^ 2 ≤ 2 * (9 * k ^ 2) := by nlinarith
    calc 9 * (k + 1) ^ 2 ≤ 2 * (9 * k ^ 2) := this
      _ ≤ 2 * (4 * 2 ^ k) := by omega
      _ = 4 * (2 ^ k * 2) := by ring

lemma natLog_le_sqrt (x p : ℕ) (hp : p.Prime) (hx : 144 ≤ x) :
    (Nat.log p x : ℝ) ≤ (2 / 3) * √(x : ℝ) := by
  have h2 : Nat.log p x ≤ Nat.log 2 x := Nat.log_anti_left (by norm_num) hp.two_le
  set k := Nat.log 2 x
  have hxR : (144 : ℝ) ≤ x := by exact_mod_cast hx
  have hs : (12 : ℝ) ≤ √(x : ℝ) := by
    rw [show (12 : ℝ) = √144 by rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hxR
  have h2R : (Nat.log p x : ℝ) ≤ k := by exact_mod_cast h2
  refine le_trans h2R ?_
  rcases le_or_gt k 8 with hk | hk
  · have : (k : ℝ) ≤ 8 := by exact_mod_cast hk
    linarith
  · have hpow : 2 ^ k ≤ x := Nat.pow_log_le_self 2 (by omega)
    have h9 := nine_sq_le_four_two_pow k hk
    have h9R : 9 * (k : ℝ) ^ 2 ≤ 4 * x := by exact_mod_cast h9.trans (by omega)
    have hsq : √(x : ℝ) ^ 2 = x := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (x : ℝ)]

/-- A `Λ`-sum over `n < x` satisfying `P` is at most the sum of the prime-power fibres over `S`,
provided every prime power `n < x` with `P n` has its prime in `S`. -/
lemma sum_vonMangoldt_le_sum_fiber (x : ℕ) (P : ℕ → Prop) [DecidablePred P] (S : Finset ℕ)
    (hS : ∀ n < x, P n → IsPrimePow n → n.minFac ∈ S) :
    ∑ n ∈ (range x).filter P, (Λ n : ℝ) ≤ ∑ p ∈ S, ∑ n ∈ ppFiber x p, (Λ n : ℝ) := by
  classical
  set T := ((range x).filter P).filter IsPrimePow
  have h1 : ∑ n ∈ (range x).filter P, (Λ n : ℝ) = ∑ n ∈ T, (Λ n : ℝ) := by
    simp only [T]
    rw [sum_filter (s := (range x).filter P)]
    refine sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · rw [vonMangoldt_apply, ite_eq_right h]
  rw [h1, ← sum_fiberwise_of_maps_to (g := Nat.minFac) (t := S)]
  · refine sum_le_sum fun p _ => ?_
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
    intro n hn
    simp only [T, mem_filter, mem_range] at hn
    simp only [ppFiber, mem_filter, mem_range]
    exact ⟨hn.1.1.1, hn.1.2, hn.2⟩
  · intro n hn
    simp only [T, mem_filter, mem_range] at hn
    exact hS n hn.1.1 hn.1.2 hn.2

end Ankeny
