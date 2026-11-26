import LLS.Thm14.CellCore

/-!
# The two-variable condition outside the boxes: `u ≥ 10^5`, or `L ≥ 10^30`

With `a = log u`, `b = log L`: `(log L)² ≤ 4L` and `Bf ≤ 12uL`, so `log Bf ≤ a + b + 2.5`. For
`u ≥ 10^5` the term `0.609u` beats everything (`a² ≤ 16√u`); for `L ≥ 10^30` and `u ≤ 10^5`,
`log Bf ≤ b + 14.1` and `2.5b²` beats `0.86b² + 6.26b + 126`.
-/

namespace LLS.Thm14

open Real

lemma log_sq_le_four {L : ℝ} (hL : 0 ≤ L) : Real.log L ^ 2 ≤ 4 * L ∨ Real.log L < 0 := by
  rcases lt_or_ge (Real.log L) 0 with h | h
  · exact Or.inr h
  · left
    have h1 := Real.log_le_rpow_div hL (show (0 : ℝ) < 1 / 2 by norm_num)
    have e : L ^ (1 / 2 : ℝ) / (1 / 2) = 2 * √L := by rw [← Real.sqrt_eq_rpow]; ring
    rw [e] at h1
    have := Real.sq_sqrt hL
    nlinarith

lemma Bf_le {u L : ℝ} (hu : 1 ≤ u) (hL : 9.9 ≤ L) : Bf u L ≤ 12 * (u * L) := by
  unfold Bf
  have hb := log_sq_le_four (show 0 ≤ L by linarith)
  have hb0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hb2 : Real.log L ^ 2 ≤ 4 * L := hb.resolve_right (by linarith)
  nlinarith

lemma log_Bf_le {u L : ℝ} (hu : 1 ≤ u) (hL : 9.9 ≤ L) :
    Real.log (Bf u L) ≤ Real.log u + Real.log L + 2.5 := by
  have hB0 : 0 < Bf u L := by
    unfold Bf; have := sq_nonneg (Real.log L); nlinarith
  have h12 : Real.log 12 ≤ 2.5 := by
    have := LLS.log_le_of_pow 12 3672 1024 (by norm_num) (by norm_num) (by decide +kernel)
    push_cast at this; linarith
  have := Real.log_le_log hB0 (Bf_le hu hL)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by linarith) (by linarith)] at this
  linarith

set_option maxHeartbeats 2000000 in
theorem tail_u (u L : ℝ) (hu : 100000 ≤ u) (hL : 9.9 ≤ L) (hB : 31622 ≤ Bf u L) :
    Phi2 u L (Real.log (Bf u L)) ≤ 0.609 * u + 1.58 + 5 / 2 * Real.log L ^ 2 := by
  set a := Real.log u
  set b := Real.log L
  have hu0 : 0 < u := by linarith
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  have hb0 : 0 ≤ b := Real.log_nonneg (by linarith)
  have hb2 : b ^ 2 ≤ 4 * L := (log_sq_le_four (by linarith)).resolve_right (by linarith)
  have hlam0 : 0 ≤ Real.log (Bf u L) := Real.log_nonneg (by linarith)
  set T := a + b + 2.5 with hTdef
  have hm := Phi2_mono (u := u) (L := L) (u1 := u) (L1 := L) hu0 le_rfl (by linarith) le_rfl hlam0
    (log_Bf_le (by linarith) hL)
  refine hm.trans ?_
  show Phi2 u L T ≤ 0.609 * u + 1.58 + 5 / 2 * b ^ 2
  unfold Phi2
  have hT2 : T ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 18.75 := by
    rw [hTdef]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2.5), sq_nonneg (b - 2.5)]
  have hL3 : (12.9 : ℝ) ≤ L + 3 := by linarith
  -- each fraction
  have hn0 : 0 ≤ 18 * a ^ 2 + 45.86 * a + 248.4 := by positivity
  have f1 : (6 * T ^ 2 + 45.86 * T + 21.25) / (L + 3)
      ≤ (18 * a ^ 2 + 45.86 * a + 248.4) / 12.9 + 72 + 45.86 * b / 12.9 := by
    have hT0 : 0 ≤ T := by positivity
    have s1 : (6 * T ^ 2 + 45.86 * T + 21.25) / (L + 3)
        ≤ ((18 * a ^ 2 + 45.86 * a + 248.4) + 18 * b ^ 2 + 45.86 * b) / (L + 3) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    rw [show ((18 * a ^ 2 + 45.86 * a + 248.4) + 18 * b ^ 2 + 45.86 * b) / (L + 3)
        = (18 * a ^ 2 + 45.86 * a + 248.4) / (L + 3) + 18 * b ^ 2 / (L + 3) + 45.86 * b / (L + 3)
        by ring] at s1
    have s2 : (18 * a ^ 2 + 45.86 * a + 248.4) / (L + 3) ≤ (18 * a ^ 2 + 45.86 * a + 248.4) / 12.9 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) hL3
    have s3 : 18 * b ^ 2 / (L + 3) ≤ 72 := by rw [div_le_iff₀ (by linarith)]; linarith
    have s4 : 45.86 * b / (L + 3) ≤ 45.86 * b / 12.9 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hL3
    linarith
  have f2 : (20 * T ^ 2 + 18.0008 * T + 3) / 31622
      ≤ (60 * a ^ 2 + 60 * b ^ 2 + 375 + 18.0008 * T + 3) / 31622 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have f3 : 0.58824 * T ^ 2 / u ≤ 0.58824 * (3 * a ^ 2 + 3 * b ^ 2 + 18.75) / 100000 :=
    div_le_div₀ (by positivity) (by linarith) (by norm_num) hu
  -- `a` against `u`
  have hq : (u ^ (1 / 4 : ℝ)) ^ 2 = √u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le, Real.sqrt_eq_rpow]; norm_num
  have ha1 : a ≤ 4 * u ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hu0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [div_eq_mul_inv] at this; norm_num at this ⊢; linarith
  have hr0 : 0 ≤ u ^ (1 / 4 : ℝ) := by positivity
  have hsq : √u * √u = u := Real.mul_self_sqrt hu0.le
  have h316 : (316 : ℝ) ≤ √u := by
    rw [show (316 : ℝ) = √(316 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hr1 : u ^ (1 / 4 : ℝ) ≤ √u := by
    have : (1 : ℝ) ≤ u ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  have ha2 : a ^ 2 ≤ 16 * √u := by rw [← hq]; nlinarith
  have hb : 2.4 * b ^ 2 - 9.82 * b ≥ -10.1 := by nlinarith [sq_nonneg (b - 2.05)]
  have h316' : 316 * √u ≤ u := by nlinarith
  have ha3 : a ≤ 4 * √u := by linarith
  have k1 : 1.3973 * a ^ 2 + 9.81 * a ≤ 61.61 * √u := by linarith
  have k2 : 2.498 * b ^ 2 - 9.81 * b ≥ -10.1 := by nlinarith [sq_nonneg b]
  have k3 : 61.61 * √u + 118 ≤ 0.609 * u := by linarith
  have e1 : (18 * a ^ 2 + 45.86 * a + 248.4) / 12.9 = 18 / 12.9 * a ^ 2 + 45.86 / 12.9 * a + 248.4 / 12.9 := by ring
  have e2 : (60 * a ^ 2 + 60 * b ^ 2 + 375 + 18.0008 * T + 3) / 31622
      = 60 / 31622 * a ^ 2 + 60 / 31622 * b ^ 2 + 378 / 31622 + 18.0008 / 31622 * T := by ring
  have e3 : 0.58824 * (3 * a ^ 2 + 3 * b ^ 2 + 18.75) / 100000
      = 0.58824 * 3 / 100000 * a ^ 2 + 0.58824 * 3 / 100000 * b ^ 2 + 0.58824 * 18.75 / 100000 := by ring
  rw [e1] at f1
  rw [e2] at f2
  rw [e3] at f3
  norm_num at f1 f2 f3 k1 k2 k3 ⊢
  linarith

theorem tail_L (u L : ℝ) (hu1 : 1 ≤ u) (hu : u ≤ 100000) (hL : 10 ^ 30 ≤ L) :
    Phi2 u L (Real.log (Bf u L)) ≤ 0.609 * u + 1.58 + 5 / 2 * Real.log L ^ 2 := by
  set b := Real.log L
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < L := by linarith
  have hb69 : 69 ≤ b := by
    have := log_ge_nat (y := L) (X := 10 ^ 30) (k := 102049) (by push_cast; linarith)
      (by decide +kernel) (by norm_num)
    linarith
  have hb2 : b ^ 2 ≤ 4 * L := (log_sq_le_four hL0.le).resolve_right (by linarith)
  have hlogu : Real.log u ≤ 11.6 := by
    have := log_le_nat (y := u) (X := 100000) (k := 17009) hu0 (by push_cast; linarith)
      (by decide +kernel)
    linarith
  have hlam0 : 0 ≤ Real.log (Bf u L) := by
    refine Real.log_nonneg ?_
    unfold Bf; have := sq_nonneg b; nlinarith
  have hlam : Real.log (Bf u L) ≤ b + 14.1 := by
    have := log_Bf_le hu1 (by linarith : (9.9 : ℝ) ≤ L); linarith
  have hm := Phi2_mono (u := u) (L := L) (u1 := 1) (L1 := L) one_pos hu1 hL0 le_rfl hlam0 hlam
  refine hm.trans ?_
  unfold Phi2
  have hT2 : (b + 14.1) ^ 2 ≤ 1.46 * b ^ 2 := by nlinarith
  have hbL : b ≤ 0.06 * L := by nlinarith
  have f1 : (6 * (b + 14.1) ^ 2 + 45.86 * (b + 14.1) + 21.25) / (L + 3) ≤ 37 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hu0' : 0 ≤ u := hu0.le
  nlinarith

end LLS.Thm14
