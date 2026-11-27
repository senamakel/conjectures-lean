import Mathlib

/-! A generic Rankin bound for the finite set of smooth numbers up to a cutoff. -/

namespace Implications.SmoothGapRankin

/-- The multiplicative weight `n ↦ n ^ (-s)`. -/
noncomputable def rankinWeight (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]

private theorem rankinWeight_prime_norm_lt_one {s : ℝ} (hs : 0 < s) {p : ℕ}
    (hp : p.Prime) : ‖rankinWeight s p‖ < 1 := by
  rw [rankinWeight, Real.norm_eq_abs, abs_of_pos]
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

/-- Rankin's inequality: the number of `Y`-smooth positive integers up to `X` is bounded by
`X ^ s` times the finite Euler product for the weight `n ^ (-s)`. -/
theorem smoothNumbersUpTo_card_le_rankin (X Y : ℕ) (s : ℝ) (hX : 0 < X)
    (hs : 0 < s) :
    (X.smoothNumbersUpTo Y).card ≤
      X ^ s * ∏ p ∈ Y.primesBelow, (1 - rankinWeight s p)⁻¹ := by
  classical
  let S : Finset ℕ := X.smoothNumbersUpTo Y
  let f := rankinWeight s
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := f) (rankinWeight_prime_norm_lt_one hs) Y
  have hf : Summable (fun m : Y.smoothNumbers => f m) := hEuler.1.of_norm
  have hf_nonneg (m : Y.smoothNumbers) : 0 ≤ f m := by
    dsimp [f, rankinWeight]
    exact Real.rpow_nonneg (by positivity) _
  let e : {n : ℕ // n ∈ X.smoothNumbersUpTo Y} ↪ Y.smoothNumbers :=
    ⟨(fun n : {n : ℕ // n ∈ X.smoothNumbersUpTo Y} =>
      (⟨n.val, (Nat.mem_smoothNumbersUpTo.mp n.property).2⟩ : Y.smoothNumbers)), by
      intro a b h
      apply Subtype.ext
      exact congrArg Subtype.val h⟩
  let T := S.attach.map e
  have hsum_map : (∑ m ∈ T, f m) = ∑ n ∈ S.attach, f (e n) := by
    simp [T, Finset.sum_map]
  have hsum_le : (∑ m ∈ T, f m) ≤ ∏ p ∈ Y.primesBelow, (1 - f p)⁻¹ := by
    calc
      (∑ m ∈ T, f m) ≤ ∑' m : Y.smoothNumbers, f m := hf.sum_le_tsum T (by intro m hm; exact hf_nonneg m)
      _ = ∏ p ∈ Y.primesBelow, (1 - f p)⁻¹ := hEuler.2.tsum_eq
  have hpoint (n : {n : ℕ // n ∈ X.smoothNumbersUpTo Y}) : 1 ≤ (X : ℝ) ^ s * f (e n) := by
    have hn0 : 0 < n.val := Nat.pos_of_ne_zero
      (Nat.mem_smoothNumbersUpTo.mp n.property).2.1
    have hnX : (n.val : ℝ) ≤ X := by
      exact_mod_cast (Nat.mem_smoothNumbersUpTo.mp n.property).1
    have hn0R : 0 < (n.val : ℝ) := by exact_mod_cast hn0
    have hpow : (n.val : ℝ) ^ s ≤ (X : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity) hnX hs.le
    have hden : 0 < (n.val : ℝ) ^ s := Real.rpow_pos_of_pos hn0R s
    have hratio : 1 ≤ (X : ℝ) ^ s / (n.val : ℝ) ^ s := (le_div_iff₀ hden).2 hpow
    calc
      1 ≤ (X : ℝ) ^ s / (n.val : ℝ) ^ s := hratio
      _ = (X : ℝ) ^ s * f (e n) := by
        dsimp [f, rankinWeight, e]
        rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity : 0 ≤ (n.val : ℝ)) s]
  have hcard : (S.card : ℝ) ≤ (X : ℝ) ^ s * ∑ m ∈ T, f m := by
    calc
      (S.card : ℝ) = ∑ n ∈ S.attach, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S.attach, (X : ℝ) ^ s * f (e n) :=
        Finset.sum_le_sum fun n hn => hpoint n
      _ = (X : ℝ) ^ s * ∑ n ∈ S.attach, f (e n) := by rw [Finset.mul_sum]
      _ = (X : ℝ) ^ s * ∑ m ∈ T, f m := by rw [← hsum_map]
  have hfinal := mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ (X : ℝ) ^ s)
  exact_mod_cast (hcard.trans (by simpa [f] using hfinal))

end Implications.SmoothGapRankin
