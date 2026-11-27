import Implications.SmoothGapAnalytic
import Implications.SmoothGapAsymptotic

/-! Converting the analytic cutoff estimate into a stretched-exponential rate. -/

namespace Implications.SmoothGapStretchedRate

open Filter SmoothGapCounting SmoothGapAnalytic SmoothGapAsymptotic

private theorem log_primeAt_tendsto :
    Tendsto (fun n : ℕ => Real.log (primeAt n : ℝ)) atTop atTop := by
  have hnat : Tendsto primeAt atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun n hn => ?_⟩
    have hp := Nat.add_two_le_nth_prime n
    change b ≤ Nat.nth Nat.Prime n
    omega
  exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hnat)

private theorem rounded_parameters (L : ℝ) (hL : 1 < L)
    (hB : 2 ≤ smoothCutoffNat L) :
    0 ≤ rootScale L ∧ rootScale L / 4 ≤ L ∧
      1 / 2 ≤ 1 - rankinDelta L ∧ 1 - rankinDelta L ≤ 1 ∧
      Real.exp (rootScale L / 2) / 2 ≤ (smoothCutoffNat L : ℝ) := by
  have hLpos : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := (Real.log_pos hL).le
  have hR : 0 ≤ rootScale L := Real.sqrt_nonneg _
  have hRle : rootScale L ≤ L := by
    have hp := Real.log_le_sub_one_of_pos hLpos
    have hsq := rootScale_sq hLpos hlog
    by_contra! hc
    have ht := mul_pos (sub_pos.mpr hc) (add_pos_of_pos_of_nonneg hLpos hR)
    have hu := mul_nonneg hLpos.le (show 0 ≤ L - Real.log L by linarith)
    nlinarith only [hsq, ht, hu]
  have hδ := rankinDelta_mul_self hL
  have hδ0 : 0 ≤ rankinDelta L := div_nonneg hlog (by positivity)
  have hδ2 : rankinDelta L ≤ 1 / 2 := by
    by_contra! hc
    have ht := mul_lt_mul_of_pos_right hc hLpos
    linarith
  have hf := Nat.lt_floor_add_one (smoothCutoff L)
  change Real.exp (rootScale L / 2) < (smoothCutoffNat L : ℝ) + 1 at hf
  have hB' : (2 : ℝ) ≤ (smoothCutoffNat L : ℝ) := by exact_mod_cast hB
  exact ⟨hR, by linarith, by linarith, by linarith, by linarith⟩

/-- Combine the two finite cutoff terms after bounding the Euler-product exponent
and rounding the smoothness cutoff. -/
private theorem hitCount_le_of_rankin_parameters
    (D : ℝ)
    (hcut : ∀ (N B j : ℕ) (s : ℝ), 2 ≤ B → 1 / 2 ≤ s → s ≤ 1 →
      (j : ℝ) * hitCount N j / (N + 1 : ℝ) ≤
        ((j : ℝ) * primeAt N / (N + 1 : ℝ)) / B +
          (1 + (primeAt N : ℝ) ^ s *
            Real.exp (4 * (B : ℝ) ^ (1 - s) * D *
              (1 + Real.log (((Nat.log 2 B + 1 : ℕ) : ℝ))))) / (N + 1 : ℝ))
    (N B : ℕ) (s R : ℝ) (hB : 2 ≤ B) (hslo : 1/2 ≤ s) (hshi : s ≤ 1)
    (hR : 0 ≤ R) (hRL : R / 4 ≤ Real.log (primeAt N : ℝ))
    (hround : Real.exp (R / 2) / 2 ≤ (B : ℝ))
    (hbalance : (1 - s) * Real.log (primeAt N : ℝ) = R / 2)
    (hproduct : 4 * (B : ℝ) ^ (1 - s) * D *
        (1 + Real.log (((Nat.log 2 B + 1 : ℕ) : ℝ))) ≤ R / 8)
    (hindex : (primeAt N : ℝ) / (N + 1 : ℝ) ≤ 2 * Real.log (primeAt N : ℝ)) :
    (hitCount N 2 : ℝ) / (N + 1 : ℝ) ≤
      6 * Real.log (primeAt N : ℝ) * Real.exp (-R / 4) := by
  let X : ℝ := primeAt N
  let q : ℝ := N + 1
  let L := Real.log X
  let E := Real.exp (-R / 4)
  let U := 4 * (B : ℝ) ^ (1 - s) * D *
    (1 + Real.log (((Nat.log 2 B + 1 : ℕ) : ℝ)))
  have hq : 0 < q := by dsimp [q]; positivity
  have hX : 0 < X := by
    change (0 : ℝ) < (Nat.nth Nat.Prime N : ℝ)
    exact_mod_cast (Nat.prime_nth_prime N).pos
  have hE : 0 < E := Real.exp_pos _
  have hB' : 0 < (B : ℝ) := by
    exact_mod_cast (by omega : 0 < B)
  have hlarge : 1 / (B : ℝ) ≤ 2 * E := by
    calc
      1 / (B : ℝ) ≤ 1 / (Real.exp (R / 2) / 2) :=
        one_div_le_one_div_of_le (by positivity) hround
      _ = 2 * Real.exp (-(R / 2)) := by rw [Real.exp_neg]; ring
      _ ≤ 2 * E := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by linarith)
  have hXexp : Real.exp L = X := Real.exp_log hX
  have hone : 1 ≤ X * E := by
    rw [← hXexp]
    change 1 ≤ Real.exp L * Real.exp (-R / 4)
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by change R / 4 ≤ L at hRL; linarith)
  have htail : X ^ s * Real.exp U ≤ X * E := by
    rw [Real.rpow_def_of_pos hX]
    change Real.exp (L * s) * Real.exp U ≤ X * Real.exp (-R / 4)
    rw [← hXexp, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change (1 - s) * L = R / 2 at hbalance
    change U ≤ R / 8 at hproduct
    linarith
  have hpos : 0 ≤ 2 * X / q := by positivity
  have hlargeTerm : (2 * X / q) / B ≤ (2 * X / q) * (2 * E) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hlarge hpos
  have htailTerm : (1 + X ^ s * Real.exp U) / q ≤ (2 * X * E) / q := by
    apply div_le_div_of_nonneg_right _ hq.le
    linarith
  have hindex' : X / q ≤ 2 * L := hindex
  have hbnd := (hcut N B 2 s hB hslo hshi)
  change 2 * (hitCount N 2 : ℝ) / q ≤ (2 * X / q) / B +
    (1 + X ^ s * Real.exp U) / q at hbnd
  calc
    (hitCount N 2 : ℝ) / (N + 1 : ℝ) ≤ 3 * (X / q) * E := by
      have hsum := hbnd.trans (add_le_add hlargeTerm htailTerm)
      have hid : (2 * X / q) * (2 * E) + (2 * X * E) / q =
          2 * (3 * (X / q) * E) := by ring
      rw [hid, mul_div_assoc] at hsum
      exact le_of_mul_le_mul_left hsum (by norm_num)
    _ ≤ 6 * Real.log (primeAt N : ℝ) * Real.exp (-R / 4) := by
      have h := mul_le_mul_of_nonneg_right hindex' (show 0 ≤ 3 * E by positivity)
      dsimp [L, E] at h ⊢
      nlinarith only [h]

private theorem eventually_hitCount_le_of_euler_cost
    (hcost : ∀ (D : ℝ), 0 < D → ∀ᶠ L : ℝ in atTop,
      4 * (smoothCutoffNat L : ℝ) ^ rankinDelta L * D *
        (1 + Real.log (((Nat.log 2 (smoothCutoffNat L) + 1 : ℕ) : ℝ))) ≤
          rootScale L / 8) :
    ∀ᶠ N : ℕ in atTop,
      (hitCount N 2 : ℝ) / (N + 1 : ℝ) ≤
        6 * Real.log (primeAt N : ℝ) *
          Real.exp (-(rootScale (Real.log (primeAt N : ℝ))) / 4) := by
  obtain ⟨D, hD, hcut⟩ := hitCount_le_rankin_cutoff
  filter_upwards [log_primeAt_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    log_primeAt_tendsto.eventually eventually_smoothCutoffNat_ge_two,
    log_primeAt_tendsto.eventually (hcost D hD),
    eventually_primeAt_over_index_le] with N hL hB hP hN
  let L := Real.log (primeAt N : ℝ)
  let B := smoothCutoffNat L
  let s := 1 - rankinDelta L
  obtain ⟨hR, hRL, hslo, hshi, hround⟩ := rounded_parameters L hL hB
  have hbalance : (1 - s) * L = rootScale L / 2 := by
    have h := rankinDelta_mul_self hL
    change rankinDelta L * L = rootScale L / 2 at h
    dsimp [s]
    linarith only [h]
  have hP' : 4 * (B : ℝ) ^ (1 - s) * D *
      (1 + Real.log (((Nat.log 2 B + 1 : ℕ) : ℝ))) ≤ rootScale L / 8 := by
    change 4 * (B : ℝ) ^ rankinDelta L * D *
      (1 + Real.log (((Nat.log 2 B + 1 : ℕ) : ℝ))) ≤ rootScale L / 8 at hP
    simpa only [s, sub_sub_cancel] using hP
  exact hitCount_le_of_rankin_parameters D hcut N B s (rootScale L)
    hB hslo hshi hR hRL hround hbalance hP' (by simpa only [Nat.cast_add, Nat.cast_one] using hN)

end Implications.SmoothGapStretchedRate
