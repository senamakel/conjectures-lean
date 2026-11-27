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
  let S := X.smoothNumbersUpTo Y
  let f := rankinWeight s
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := f) (rankinWeight_prime_norm_lt_one hs) Y
  have hf : Summable (fun m : Y.smoothNumbers => f m) := hEuler.1.of_norm
  have hf_nonneg (m : Y.smoothNumbers) : 0 ≤ f m := by
    dsimp [f, rankinWeight]
    exact Real.rpow_nonneg (by positivity) _
  let e : S.attach ↪ Y.smoothNumbers :=
    ⟨fun n => ⟨(n : ℕ), (Nat.mem_smoothNumbersUpTo.mp n.property).2⟩,
      fun a b h => Finset.ext_iff.mp (congrArg Subtype.val h) ▸ Subtype.ext (congrArg Subtype.val h)⟩
  let T := S.attach.map e
  have hsum_map : (∑ m ∈ T, f m) =
      ∑ n ∈ S, f ⟨n, (Nat.mem_smoothNumbersUpTo.mp (show n ∈ S from n.2)).2⟩ := by
    simp [T, e, Finset.sum_map, Finset.sum_attach]
  have hsum_le : (∑ m ∈ T, f m) ≤ ∏ p ∈ Y.primesBelow, (1 - f p)⁻¹ := by
    calc
      (∑ m ∈ T, f m) ≤ ∑' m : Y.smoothNumbers, f m := hf.sum_le_tsum T (by intro m hm; exact hf_nonneg m)
      _ = ∏ p ∈ Y.primesBelow, (1 - f p)⁻¹ := hEuler.2.tsum_eq
  have hpoint (n : ℕ) (hn : n ∈ S) :
      1 ≤ (X : ℝ) ^ s * f ⟨n, (Nat.mem_smoothNumbersUpTo.mp hn).2⟩ := by
    have hn0 : 0 < n := Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp hn).2.1
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Nat.mem_smoothNumbersUpTo.mp hn).1
    have hn0R : 0 < (n : ℝ) := by exact_mod_cast hn0
    have hpow : (n : ℝ) ^ s ≤ (X : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity) hnX hs.le
    have hden : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hn0R s
    have hratio : 1 ≤ (X : ℝ) ^ s / (n : ℝ) ^ s := (le_div_iff₀ hden).2 hpow
    calc
      1 ≤ (X : ℝ) ^ s / (n : ℝ) ^ s := hratio
      _ = (X : ℝ) ^ s * f ⟨n, (Nat.mem_smoothNumbersUpTo.mp hn).2⟩ := by
        dsimp [f, rankinWeight]
        rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)) s]
  have hcard : (S.card : ℝ) ≤ (X : ℝ) ^ s * ∑ m ∈ T, f m := by
    rw [← Finset.card_map e, ← Finset.card_attach]
    simp only [Nat.cast_sum, Nat.cast_one]
    rw [hsum_map]
    calc
      ∑ n ∈ S, 1 ≤ ∑ n ∈ S, (X : ℝ) ^ s * f ⟨n, (Nat.mem_smoothNumbersUpTo.mp (show n ∈ S from n.2)).2⟩ :=
        Finset.sum_le_sum fun n hn => hpoint n hn
      _ = (X : ℝ) ^ s * ∑ n ∈ S, f ⟨n, (Nat.mem_smoothNumbersUpTo.mp (show n ∈ S from n.2)).2⟩ := by rw [Finset.mul_sum]
  have hfinal := mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ (X : ℝ) ^ s)
  exact_mod_cast (hcard.trans (by simpa [f] using hfinal))

end Implications.SmoothGapRankin
