import Ankeny.Large
import Erdos985.Numerics

/-!
# The numerical inequality for `q ≥ 2^17`, with `c = 21/5`

Write `L = log q ≥ 17 log 2`, `x = ⌊(21/5) L²⌋`, `s = √x`. Then
* `s ≥ 24.12` and `L ≤ 0.4884 s` (from `(21/5) L² < s² + 1`);
* `ω(q) ≤ 6 + (L − 10)/log 16` (from `16^ω · 30030 ≤ q · 16^6`, and `log 30030 > 10`);
* `log x = 2 log s ≤ 2 (log 32 + s/32 − 1)`.
Substituting these, the claim reduces to a quadratic inequality in `s` on `[24.12, ∞)`.
-/

namespace Ankeny

open Real

/-- The constant achieved by the analytic argument. -/
noncomputable abbrev cBach : ℝ := 21 / 5

/-- The analytic argument covers `q ≥ Q₀ = 2^17`. -/
abbrev Q₀ : ℕ := 2 ^ 17

lemma log_30030_gt : (10 : ℝ) < Real.log 30030 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    _ < 2.7182818286 ^ 10 := by gcongr
    _ < 30030 := by norm_num

/-- `ω(q) log 16 ≤ log q + 6 log 16 − 10`. -/
lemma card_primeFactors_le (q : ℕ) (hq : q ≠ 0) :
    (q.primeFactors.card : ℝ) * Real.log 16 ≤ Real.log q + 6 * Real.log 16 - 10 := by
  have h := Erdos985.pow_card_primeFactors_mul_le 16 q hq
  have e1 : ∏ r ∈ (Finset.range 16).filter Nat.Prime, r = 30030 := by decide
  have e2 : ((Finset.range 16).filter Nat.Prime).card = 6 := by decide
  rw [e1, e2] at h
  have hR : ((16 : ℝ) ^ q.primeFactors.card * 30030) ≤ (q : ℝ) * 16 ^ 6 := by exact_mod_cast h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hl := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul hq0.ne' (by norm_num),
    Real.log_pow, Real.log_pow] at hl
  have := log_30030_gt
  push_cast at hl
  linarith

lemma quadratic_bound (s : ℝ) (hsge : (24.12 : ℝ) ≤ s) :
    (s + 2 + 3 / 581.7744) * ((2 / 3) * (0.4884 * s + 5 / 3))
      + (7 - 2254211 / 625000 + 1803369 / 5000000 * (0.4884 * s))
        * (2 * (5 * 0.6931471808 + s / 32 - 1)) + 1.6
      < s ^ 2 / 2 - s / 20 - 3 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hsge) (sub_nonneg.2 hsge)]

theorem numericOK_of_ge (q : ℕ) (hq : Q₀ ≤ q) : NumericOK cBach q := by
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hq0 : q ≠ 0 := by unfold Q₀ at hq; omega
  set L := Real.log q with hLdef
  have hL : 17 * 0.6931471803 ≤ L := by
    have : Real.log ((2 : ℝ) ^ 17) ≤ L :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hL0 : 0 ≤ L := by linarith
  set x := ⌊cBach * L ^ 2⌋₊ with hxdef
  have hcL : 0 ≤ cBach * L ^ 2 := by positivity
  have hx1 : (x : ℝ) ≤ 21 / 5 * L ^ 2 := Nat.floor_le hcL
  have hx2 : 21 / 5 * L ^ 2 < x + 1 := Nat.lt_floor_add_one _
  have hLsq : 17 * 0.6931471803 * (17 * 0.6931471803) ≤ L ^ 2 := by nlinarith
  have hx143 : (581.7744 : ℝ) ≤ x := by nlinarith
  have hx144 : 144 ≤ x := by
    have : (143 : ℝ) < x := by linarith
    exact_mod_cast this
  set s := √(x : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x := Real.sq_sqrt (by positivity)
  have hsge : (24.12 : ℝ) ≤ s := by nlinarith
  have hLs : L ≤ 0.4884 * s := by nlinarith
  -- ω
  have hω := card_primeFactors_le q hq0
  rw [show Real.log 16 = 4 * Real.log 2 by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num] at hω
  set ω : ℝ := (q.primeFactors.card : ℝ) with hωdef
  have hω0 : 0 ≤ ω := Nat.cast_nonneg _
  have hωb : ω + 1 ≤ 7 - 2254211 / 625000 + 1803369 / 5000000 * L := by
    have hl4 : 0 < 4 * Real.log 2 := by linarith
    have h0 : ω - 6 ≤ (L - 10) / (4 * Real.log 2) := by
      rw [le_div_iff₀ hl4]; linarith
    have h1 : (L - 10) / (4 * Real.log 2) ≤ 1803369 / 5000000 * L - 2254211 / 625000 := by
      rw [div_le_iff₀ hl4]
      nlinarith [mul_le_mul_of_nonneg_left hl2a.le hL0]
    linarith
  -- log x
  set T := Real.log x with hTdef
  have hT0 : 0 ≤ T := Real.log_nonneg (by linarith)
  have hTs : T = 2 * Real.log s := by
    rw [hsdef, Real.log_sqrt (by positivity)]; ring
  have hlogs : Real.log s ≤ 5 * Real.log 2 + s / 32 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s / 32 by positivity)
    rw [Real.log_div (by positivity) (by norm_num),
      show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow] at h
    push_cast at h
    linarith
  have hTb : T ≤ 2 * (5 * 0.6931471808 + s / 32 - 1) := by
    rw [hTs]; linarith
  -- products
  have hUω : 0 ≤ 7 - 2254211 / 625000 + 1803369 / 5000000 * (0.4884 * s) := by positivity
  have hP1 : (ω + 1) * T ≤ (7 - 2254211 / 625000 + 1803369 / 5000000 * (0.4884 * s))
      * (2 * (5 * 0.6931471808 + s / 32 - 1)) := by
    apply mul_le_mul _ hTb hT0 hUω
    nlinarith
  have h3x : 3 / (x : ℝ) ≤ 3 / 581.7744 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx143
  have h3x0 : 0 ≤ 3 / (x : ℝ) := by positivity
  have hP2 : (s + 2 + 3 / x) * ((2 / 3) * (L + 5 / 3))
      ≤ (s + 2 + 3 / 581.7744) * ((2 / 3) * (0.4884 * s + 5 / 3)) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  refine ⟨hx144, ?_⟩
  have hq2 := quadratic_bound s hsge
  change (s + 2 + 3 / x) * ((2 / 3) * (L + 5 / 3)) + (T + 1) + 0.6 < (x : ℝ) / 2 - s / 20 - 3 - ω * T
  have e : (ω + 1) * T = ω * T + T := by ring
  linarith

end Ankeny
