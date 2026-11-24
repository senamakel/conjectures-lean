import Mertens.Liouville
import Mertens.SharpMain
import Mertens.Statement4

/-!
# Titchmarsh's bound for the summatory Liouville function under RH

`abs_mertens_nat_le_sharp` bounds `|M(n)| ≤ K_l (n+1)^{β}`, `β = 1/2 + 12/l`, with the same
constant `K_l = 8 l exp(A(l² e^l + 1))` for every `n ≥ 1`. Through `L(N) = ∑_{d² ≤ N} M(N/d²)`
(`liouvilleSum_nat`) this gives

    |L(N)| ≤ K_l 2^β N^β ∑_{d ≤ N} d^{-2β} ≤ K_l 2^β N^β (1 + log N),

and with `l = ½ log log x` the extra factor `1 + log x` is absorbed in `exp(log x / log log x)`.
-/

namespace Mertens

open Filter Finset ArithmeticFunction

/-- `∑_{n ≤ N} 1_{□}(n) n^{-β} ≤ 1 + log N` for `β ≥ 1/2`. -/
lemma sum_sqInd_rpow_le_log {β : ℝ} (hβ : 1 / 2 ≤ β) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (n : ℝ) ^ (-β) ≤ 1 + Real.log N := by
  classical
  have hfilt : ∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (n : ℝ) ^ (-β) =
      ∑ n ∈ (Ioc 0 N).filter IsSquare, (n : ℝ) ^ (-β) := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by simp at hn; omega
    rw [sqInd_apply]
    by_cases hs : IsSquare n <;> simp [hs, hn0]
  rw [hfilt]
  have hsub : (Ioc 0 N).filter IsSquare ⊆ (Ioc 0 N).image fun d : ℕ => d * d := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨h0, hN⟩, r, rfl⟩ := hn
    refine mem_image.2 ⟨r, mem_Ioc.2 ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos r with rfl | h
      · simp at h0
      · exact h
    · exact le_trans (Nat.le_mul_self r) hN
  have hharm : ∑ d ∈ Ioc 0 N, (d : ℝ)⁻¹ = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, ← Icc_one_eq_Ioc_zero]; push_cast; rfl
  calc ∑ n ∈ (Ioc 0 N).filter IsSquare, (n : ℝ) ^ (-β)
      ≤ ∑ n ∈ (Ioc 0 N).image (fun d : ℕ => d * d), (n : ℝ) ^ (-β) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ d ∈ Ioc 0 N, ((d * d : ℕ) : ℝ) ^ (-β) :=
        sum_image_le_of_nonneg fun _ _ => by positivity
    _ ≤ ∑ d ∈ Ioc 0 N, (d : ℝ)⁻¹ := by
        refine sum_le_sum fun d hd => ?_
        simp only [mem_Ioc] at hd
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.1
        have hd0 : (0 : ℝ) < d := by linarith
        push_cast
        rw [Real.mul_rpow hd0.le hd0.le, ← Real.rpow_add hd0, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    _ = (harmonic N : ℝ) := hharm
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- **The Liouville sum from a uniform Mertens bound**: if `|M(n)| ≤ K (n+1)^β` for every
`n ≥ 1`, with `β ≥ 1/2`, then `|L(N)| ≤ K 2^β N^β (1 + log N)`. -/
theorem abs_liouvilleSum_nat_le_of {K β : ℝ} (hK0 : 0 ≤ K) (hβ : 1 / 2 ≤ β)
    (hK : ∀ n : ℕ, 1 ≤ n → |(mertens n : ℝ)| ≤ K * ((n : ℝ) + 1) ^ β) (N : ℕ) :
    |(liouvilleSum N : ℝ)| ≤ K * 2 ^ β * (N : ℝ) ^ β * (1 + Real.log N) := by
  rw [liouvilleSum_nat]
  have hβ0 : 0 ≤ β := by linarith
  have hterm : ∀ n ∈ Ioc 0 N, |(sqInd n : ℝ) * (mertens (N / n : ℕ) : ℝ)| ≤
      K * 2 ^ β * (N : ℝ) ^ β * ((sqInd n : ℝ) * (n : ℝ) ^ (-β)) := by
    classical
    intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn.1 hn.2)
    have hs : (sqInd n : ℝ) = 0 ∨ (sqInd n : ℝ) = 1 := by
      rw [sqInd_apply]; split_ifs <;> simp
    rcases hs with hs | hs
    · rw [hs]; simp
    rw [hs, one_mul, one_mul]
    have hq1 : 1 ≤ N / n := (Nat.one_le_div_iff hn.1).2 hn.2
    have hq : ((N / n : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) / n) := by
      have h1 : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := Nat.cast_div_le
      have h2 : (1 : ℝ) ≤ (N : ℝ) / n := by
        rw [le_div_iff₀ hn0, one_mul]; exact_mod_cast hn.2
      linarith
    calc |(mertens (N / n : ℕ) : ℝ)| ≤ K * (((N / n : ℕ) : ℝ) + 1) ^ β := hK _ hq1
      _ ≤ K * (2 * ((N : ℝ) / n)) ^ β := by gcongr
      _ = K * 2 ^ β * (N : ℝ) ^ β * (n : ℝ) ^ (-β) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.div_rpow hN0.le hn0.le,
            Real.rpow_neg hn0.le]
          ring
  calc |∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (mertens (N / n : ℕ) : ℝ)|
      ≤ ∑ n ∈ Ioc 0 N, |(sqInd n : ℝ) * (mertens (N / n : ℕ) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, K * 2 ^ β * (N : ℝ) ^ β * ((sqInd n : ℝ) * (n : ℝ) ^ (-β)) :=
        sum_le_sum hterm
    _ = K * 2 ^ β * (N : ℝ) ^ β * ∑ n ∈ Ioc 0 N, (sqInd n : ℝ) * (n : ℝ) ^ (-β) := by
        rw [mul_sum]
    _ ≤ K * 2 ^ β * (N : ℝ) ^ β * (1 + Real.log N) := by
        gcongr
        exact sum_sqInd_rpow_le_log hβ N

set_option maxHeartbeats 800000 in
/-- **Titchmarsh's bound for `L` (RH)**: `|L(x)| ≤ √x exp(25 log x / log log x)` for large `x`. -/
theorem liouvilleSharp_of_RH (hRH : RiemannHypothesis) : LiouvilleSharpBound := by
  obtain ⟨A, hA0, hA⟩ := abs_mertens_nat_le_sharp hRH
  obtain ⟨U, hU⟩ := eventually_atTop.1 (eventually_le_div_log (A + 2) 5)
  set U' := max U (Real.exp 16) with hU'
  refine ⟨25, Real.exp U', fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set u := Real.log x with hudef
  have hu : U' ≤ u := by rw [hudef, Real.le_log_iff_exp_le hx0]; exact hx
  have hu16 : Real.exp 16 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 16) hu16
  have hu1 : 1 ≤ u := le_trans (by linarith [Real.add_one_le_exp (16 : ℝ)]) hu16
  set v := Real.log u with hvdef
  have hv16 : 16 ≤ v := by rw [hvdef, Real.le_log_iff_exp_le hu0]; exact hu16
  have hv0 : 0 < v := by linarith
  have hkey := hU u (le_trans (le_max_left _ _) hu)
  have hx1 : 1 ≤ x := by
    have : 0 ≤ u := hu0.le
    rw [hudef] at this
    by_contra h; push Not at h
    have := Real.log_neg hx0 h; linarith
  set l := v / 2 with hl
  have hl8 : 8 ≤ l := by rw [hl]; linarith
  have hl0 : 0 < l := by linarith
  set X := Real.exp (A * (l ^ 2 * Real.exp l + 1)) with hX
  set β := 1 / 2 + 12 / l with hβ
  have hβ2 : β ≤ 2 := by
    have : 12 / l ≤ 3 / 2 := by rw [div_le_iff₀ hl0]; linarith
    linarith
  have hβ12 : 1 / 2 ≤ β := by have : 0 ≤ 12 / l := by positivity
                              linarith
  have hβ0 : 0 ≤ β := by linarith
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr hx1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : liouvilleSum x = liouvilleSum (N : ℝ) := by
    simp only [liouvilleSum, hNdef, Nat.floor_natCast]
  rw [hL]
  have hb := abs_liouvilleSum_nat_le_of (K := 8 * l * X) (by positivity) hβ12
    (fun n hn => hA l hl8 n hn) N
  refine hb.trans ?_
  have hP : (N : ℝ) ^ β ≤ Real.sqrt x * Real.exp (24 * u / v) := by
    have h1 : (N : ℝ) ^ β ≤ x ^ β := Real.rpow_le_rpow hN0.le hNx hβ0
    have h4 : x ^ β = Real.sqrt x * Real.exp (24 * u / v) := by
      rw [hβ, Real.rpow_add hx0, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0 (12 / l), hl]
      congr 2; rw [← hudef]; field_simp; ring
    rw [h4] at h1; exact h1
  have h2β : (2 : ℝ) ^ β ≤ 4 := by
    calc (2 : ℝ) ^ β ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ2
      _ = 4 := by norm_num
  have hlogN : 1 + Real.log N ≤ Real.exp (1 + v) := by
    have h1 : Real.log N ≤ u := Real.log_le_log hN0 hNx
    have h2 : Real.exp (1 + v) = Real.exp 1 * u := by
      rw [Real.exp_add, hvdef, Real.exp_log hu0]
    have h3 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [h2]; nlinarith
  have hlogN0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN); linarith
  have hEl : Real.exp l = u ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hu0, hl, hvdef]; ring_nf
  have hl2v : l ^ 2 ≤ v ^ 2 := by rw [hl]; nlinarith
  have hsq1 : 1 ≤ u ^ (1 / 2 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
  have h32 : 32 * l ≤ Real.exp (4 + l) := by
    rw [Real.exp_add]
    have e4 : (32 : ℝ) ≤ Real.exp 4 := by
      have := Real.exp_one_gt_d9
      have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]
      have h27 : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      norm_num at h27 ⊢; linarith
    have el : l ≤ Real.exp l := by linarith [Real.add_one_le_exp l]
    nlinarith [Real.exp_pos l]
  have hlle : l ≤ l ^ 2 * Real.exp l := by
    have := Real.one_le_exp hl0.le
    nlinarith
  have hexpo : 4 + l + A * (l ^ 2 * Real.exp l + 1) + (1 + v) ≤ u / v := by
    have e1 : 4 + l + A * (l ^ 2 * Real.exp l + 1) ≤
        (A + 1) * (l ^ 2 * Real.exp l + 1) + 4 := by
      have : (A + 1) * (l ^ 2 * Real.exp l + 1) =
          A * (l ^ 2 * Real.exp l + 1) + (l ^ 2 * Real.exp l + 1) := by ring
      linarith
    have e2 : (A + 1) * (l ^ 2 * Real.exp l + 1) ≤ (A + 1) * (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) := by
      rw [hEl]; gcongr
    have e3 : v ≤ v ^ 2 * u ^ (1 / 2 : ℝ) := by
      have h1 : v ≤ v ^ 2 := by nlinarith
      have h2 : v ^ 2 ≤ v ^ 2 * u ^ (1 / 2 : ℝ) := le_mul_of_one_le_right (by positivity) hsq1
      linarith
    have e4 : (A + 2) * (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) =
        (A + 1) * (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) + (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) := by ring
    linarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc 8 * l * X * 2 ^ β * (N : ℝ) ^ β * (1 + Real.log N)
      ≤ 8 * l * X * 4 * (Real.sqrt x * Real.exp (24 * u / v)) * Real.exp (1 + v) := by
        have hX0 : 0 ≤ 8 * l * X := by positivity
        have a1 : 8 * l * X * 2 ^ β ≤ 8 * l * X * 4 := mul_le_mul_of_nonneg_left h2β hX0
        have a2 := mul_le_mul a1 hP (Real.rpow_nonneg hN0.le β) (by positivity)
        exact mul_le_mul a2 hlogN hlogN0 (by positivity)
    _ = Real.sqrt x * ((32 * l) * X * Real.exp (1 + v) * Real.exp (24 * u / v)) := by ring
    _ ≤ Real.sqrt x * (Real.exp (4 + l) * X * Real.exp (1 + v) * Real.exp (24 * u / v)) := by
        have hX0 : 0 ≤ X := (Real.exp_pos _).le
        have b1 := mul_le_mul_of_nonneg_right h32 hX0
        have b2 := mul_le_mul_of_nonneg_right b1 (Real.exp_pos (1 + v)).le
        have b3 := mul_le_mul_of_nonneg_right b2 (Real.exp_pos (24 * u / v)).le
        exact mul_le_mul_of_nonneg_left b3 hsx
    _ = Real.sqrt x * Real.exp (4 + l + A * (l ^ 2 * Real.exp l + 1) + (1 + v) + 24 * u / v) := by
        rw [hX, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.sqrt x * Real.exp (25 * u / v) := by
        have h25 : 25 * u / v = u / v + 24 * u / v := by ring
        have hle : 4 + l + A * (l ^ 2 * Real.exp l + 1) + (1 + v) + 24 * u / v ≤ 25 * u / v := by
          linarith only [h25, hexpo]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hsx

end Mertens
