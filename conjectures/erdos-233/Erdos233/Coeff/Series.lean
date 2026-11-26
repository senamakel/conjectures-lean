import Mathlib

/-!
# A real series bound for `coef_sums`

`Σ_n min(δ⁴, 16δ²/(n²+1/4)) log(n+4)² ≤ 300 δ³ log(2/δ)²` for `0 < δ ≤ 1/2`.
The tail is handled by telescoping against `T k = (log(k+5)+2)²/k`.
-/

namespace Erdos233.CoeffAux

/-- Telescoping majorant. -/
noncomputable def T (k : ℝ) : ℝ := (Real.log (k + 5) + 2) ^ 2 / k

lemma one_le_log_add_five {k : ℝ} (hk : 0 ≤ k) : 1 ≤ Real.log (k + 5) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma step (k : ℝ) (hk : 1 ≤ k) :
    Real.log (k + 5) ^ 2 / (k + 1) ^ 2 ≤ T k - T (k + 1) := by
  have hL := one_le_log_add_five (by linarith : (0:ℝ) ≤ k)
  have hB : Real.log (k + 6) ≤ Real.log (k + 5) + 1 / (k + 5) := by
    have := Real.log_le_sub_one_of_pos (x := (k + 6) / (k + 5)) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at this
    have h2 : (k + 6) / (k + 5) - 1 = 1 / (k + 5) := by field_simp; ring
    linarith
  have hB0 : Real.log (k + 5) ≤ Real.log (k + 6) := Real.log_le_log (by linarith) (by linarith)
  unfold T
  rw [show k + 1 + 5 = k + 6 by ring]
  set L := Real.log (k + 5)
  set d := Real.log (k + 6) - L with hd
  have hL' : Real.log (k + 6) = L + d := by rw [hd]; ring
  rw [hL']
  have hd0 : 0 ≤ d := by linarith
  have hd1 : (k + 1) * d ≤ 1 := by
    have : d ≤ 1 / (k + 5) := by linarith
    calc (k + 1) * d ≤ (k + 1) * (1 / (k + 5)) := by gcongr
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
  have hdle : d ≤ 1 := by nlinarith
  have hk0 : 0 < k := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have key : L ^ 2 * k + (L + d + 2) ^ 2 * (k * (k + 1)) ≤ (L + 2) ^ 2 * (k + 1) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hk0.le (by linarith : (0:ℝ) ≤ 2 * L + 4 + d))
      (by linarith : (0:ℝ) ≤ 1 - (k + 1) * d), mul_nonneg hk0.le hd0,
      mul_nonneg hk0.le (by linarith : (0:ℝ) ≤ 2 * L - 1 + (1 - d))]
  have hpos : 0 < k * (k + 1) := by positivity
  nlinarith [key, hpos]

lemma telescope (N : ℕ) (hN : 1 ≤ N) (j : ℕ) :
    ∑ i ∈ Finset.range j, Real.log ((N + i : ℕ) + 5 : ℝ) ^ 2 / (((N + i : ℕ) : ℝ) + 1) ^ 2
      ≤ T N - T ((N + j : ℕ) : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have := step ((N + j : ℕ) : ℝ) (by exact_mod_cast le_trans hN (Nat.le_add_right _ _))
    have h2 : ((N + (j + 1) : ℕ) : ℝ) = ((N + j : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]
    linarith

lemma T_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ T k := by unfold T; positivity

/-- The weight. -/
noncomputable def w (δ : ℝ) (n : ℕ) : ℝ := min (δ ^ 4) (16 * δ ^ 2 / ((n : ℝ) ^ 2 + 1 / 4))

lemma w_nonneg (δ : ℝ) (n : ℕ) : 0 ≤ w δ n := by
  unfold w; exact le_min (by positivity) (by positivity)

theorem series_bound (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    Summable (fun n : ℕ => w δ n * Real.log (n + 4) ^ 2) ∧
    ∑' n : ℕ, w δ n * Real.log (n + 4) ^ 2 ≤ 300 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
  set u := 1 / δ with hu
  have hu2 : 2 ≤ u := by rw [hu, le_div_iff₀ hδ0]; linarith
  have hδu : δ = 1 / u := by rw [hu]; field_simp
  set ℓ := Real.log (2 / δ) with hℓ
  have h2δ : 2 / δ = 2 * u := by rw [hu]; ring
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, h2δ, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set N : ℕ := ⌈u⌉₊ with hNdef
  have hNu : u ≤ N := Nat.le_ceil u
  have hNu' : (N : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN1 : 1 ≤ N := by exact_mod_cast (by linarith : (1:ℝ) ≤ N)
  have hlogN : Real.log ((N : ℝ) + 5) ≤ 2 * ℓ := by
    rw [hℓ, h2δ, ← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u - 2) (by linarith : (0:ℝ) ≤ 4 * u + 7)]
  have hlogN4 : Real.log ((N : ℝ) + 4) ≤ 2 * ℓ :=
    le_trans (Real.log_le_log (by positivity) (by linarith)) hlogN
  have hnn : ∀ n : ℕ, 0 ≤ w δ n * Real.log (n + 4) ^ 2 :=
    fun n => mul_nonneg (w_nonneg _ _) (sq_nonneg _)
  -- head
  have head : ∑ n ∈ Finset.range (N + 1), w δ n * Real.log (n + 4) ^ 2 ≤ 8 * δ ^ 3 * ℓ ^ 2 := by
    calc ∑ n ∈ Finset.range (N + 1), w δ n * Real.log (n + 4) ^ 2
        ≤ ∑ n ∈ Finset.range (N + 1), δ ^ 4 * (2 * ℓ) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' : (n : ℝ) ≤ N := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
          gcongr
          · exact min_le_left _ _
          · exact Real.log_nonneg (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
          · exact le_trans (Real.log_le_log (by positivity) (by linarith)) hlogN4
      _ = ((N : ℝ) + 1) * δ ^ 4 * (4 * ℓ ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ (2 * u) * δ ^ 4 * (4 * ℓ ^ 2) := by gcongr; linarith
      _ = 8 * δ ^ 3 * ℓ ^ 2 := by rw [hδu]; field_simp; ring
  -- tail
  have hTN : T N ≤ 16 * δ * ℓ ^ 2 := by
    unfold T
    rw [div_le_iff₀ (by positivity)]
    have h1 : (Real.log ((N : ℝ) + 5) + 2) ^ 2 ≤ (4 * ℓ) ^ 2 := by
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ (N : ℝ) + 5)
      gcongr; linarith
    have h2 : 1 ≤ δ * N := by
      rw [hδu, one_div_mul_eq_div, le_div_iff₀ (by linarith)]; linarith
    nlinarith [sq_nonneg ℓ]
  have tail : ∀ j : ℕ, ∑ i ∈ Finset.range j, w δ (N + 1 + i) * Real.log (((N + 1 + i : ℕ) : ℝ) + 4) ^ 2
      ≤ 256 * δ ^ 3 * ℓ ^ 2 := by
    intro j
    calc _ ≤ ∑ i ∈ Finset.range j, 16 * δ ^ 2 *
          (Real.log ((N + i : ℕ) + 5 : ℝ) ^ 2 / (((N + i : ℕ) : ℝ) + 1) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          have hc : ((N + 1 + i : ℕ) : ℝ) = ((N + i : ℕ) : ℝ) + 1 := by push_cast; ring
          rw [hc, show ((N + i : ℕ) : ℝ) + 1 + 4 = ((N + i : ℕ) : ℝ) + 5 by ring]
          have hw : w δ (N + 1 + i) ≤ 16 * δ ^ 2 / (((N + i : ℕ) : ℝ) + 1) ^ 2 := by
            unfold w
            refine le_trans (min_le_right _ _) ?_
            rw [hc]
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
          calc w δ (N + 1 + i) * Real.log (((N + i : ℕ) : ℝ) + 5) ^ 2
              ≤ 16 * δ ^ 2 / (((N + i : ℕ) : ℝ) + 1) ^ 2 * Real.log (((N + i : ℕ) : ℝ) + 5) ^ 2 := by
                gcongr
            _ = _ := by ring
      _ = 16 * δ ^ 2 * ∑ i ∈ Finset.range j,
          Real.log ((N + i : ℕ) + 5 : ℝ) ^ 2 / (((N + i : ℕ) : ℝ) + 1) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ 16 * δ ^ 2 * T N := by
          gcongr
          exact le_trans (telescope N hN1 j) (by linarith [T_nonneg (Nat.cast_nonneg (N + j) : (0:ℝ) ≤ _)])
      _ ≤ 16 * δ ^ 2 * (16 * δ * ℓ ^ 2) := by gcongr
      _ = 256 * δ ^ 3 * ℓ ^ 2 := by ring
  have hpart : ∀ M : ℕ, ∑ n ∈ Finset.range M, w δ n * Real.log (n + 4) ^ 2
      ≤ 300 * δ ^ 3 * ℓ ^ 2 := by
    intro M
    calc ∑ n ∈ Finset.range M, w δ n * Real.log (n + 4) ^ 2
        ≤ ∑ n ∈ Finset.range (N + 1 + M), w δ n * Real.log (n + 4) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun n _ _ => hnn n)
      _ = ∑ n ∈ Finset.range (N + 1), w δ n * Real.log (n + 4) ^ 2 +
          ∑ i ∈ Finset.range M, w δ (N + 1 + i) * Real.log (((N + 1 + i : ℕ) : ℝ) + 4) ^ 2 :=
          Finset.sum_range_add _ _ _
      _ ≤ 8 * δ ^ 3 * ℓ ^ 2 + 256 * δ ^ 3 * ℓ ^ 2 := add_le_add head (tail M)
      _ ≤ 300 * δ ^ 3 * ℓ ^ 2 := by nlinarith [sq_nonneg ℓ, pow_pos hδ0 3]
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

end Erdos233.CoeffAux
