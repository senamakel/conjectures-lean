import LLS.Thm14.Cells
import LLS.Thm14.Tails

/-!
# The condition `(★)` of `LLS.Thm14.reduce`, in both ranges of `Bf`

* `LLS.Thm14.star_small`: `Bf < 31622`, `s = 31622`. Then `(★)` is
  `31622 − uL > 68.30 + 2.4271u + 0.002L`, which follows from `uL + 3u + 6 + 2.5(log L)² < 31622`
  after splitting at `L = 128, 1000, 4000`.
* `LLS.Thm14.star_large`: `Bf ≥ 31622`, `Bf − 1 < s ≤ Bf`. With `λ = log Bf ≥ ½ log s²`,
  `(★)` follows from `Phi2 u L λ ≤ 0.609u + 1.58 + 2.5(log L)²`, which is
  `LLS.Thm14.Cells.box_all` for `u ≤ 10^5`, `L ≤ 10^30`, and `LLS.Thm14.tail_u`,
  `LLS.Thm14.tail_L` beyond.
-/

namespace LLS.Thm14

open Real

theorem phi2_all (u L : ℝ) (hu : 1 ≤ u) (hL : 9.9 ≤ L) (hB : 31622 ≤ Bf u L) :
    Phi2 u L (Real.log (Bf u L)) ≤ 0.609 * u + 1.58 + 5 / 2 * Real.log L ^ 2 := by
  rcases le_total u 100000 with h | h
  · rcases le_total L (10 ^ 30) with h' | h'
    · exact Cells.box_all u L hu h (by linarith) (by norm_num at h' ⊢; linarith) hB
    · exact tail_L u L hu h h'
  · exact tail_u u L h hL hB

lemma logs31622 : 20.72 ≤ Real.log (((31622 : ℕ) ^ 2 : ℕ) : ℝ) ∧
    Real.log (((31622 : ℕ) ^ 2 : ℕ) : ℝ) ≤ 20.7238 := by
  refine ⟨logX_ge le_rfl, ?_⟩
  have := log_le_nat (y := (((31622 : ℕ) ^ 2 : ℕ) : ℝ)) (X := 999950884) (k := 30615)
    (by norm_num) (by norm_num) (by decide +kernel)
  linarith

theorem star_small (u L : ℝ) (hu : 1 ≤ u) (hL : 9.9 ≤ L) (hB : Bf u L < 31622) :
    ((31622 : ℕ) : ℝ) * 3.42 + 2.391 * u * (31622 : ℕ)
        + 3.127 * Real.log ((((31622 : ℕ) ^ 2 : ℕ)) : ℝ) * (31622 : ℕ)
        + u * (1.5 * Real.log ((((31622 : ℕ) ^ 2 : ℕ)) : ℝ) ^ 2
          + 22.93 * Real.log ((((31622 : ℕ) ^ 2 : ℕ)) : ℝ) + 21.25)
        + 5 * Real.log ((((31622 : ℕ) ^ 2 : ℕ)) : ℝ) ^ 2
        + 9.0004 * Real.log ((((31622 : ℕ) ^ 2 : ℕ)) : ℝ) + 3
        + 0.14706 * Real.log ((((31622 : ℕ) ^ 2 : ℕ)) : ℝ) ^ 2 * L
      < ((31622 : ℕ) : ℝ) * (((31622 : ℕ) : ℝ) - u * L) := by
  obtain ⟨hl1, hl2⟩ := logs31622
  set l := Real.log ((((31622 : ℕ) ^ 2 : ℕ)) : ℝ)
  set b := Real.log L
  have hb0 : 0 ≤ b := Real.log_nonneg (by linarith)
  have hl0 : 0 ≤ l := by linarith
  have hlsq : l ^ 2 ≤ 429.48 := by nlinarith
  have hu0 : 0 ≤ u := by linarith
  have hL0 : 0 ≤ L := by linarith
  have k1 : u * (1.5 * l ^ 2 + 22.93 * l + 21.25) ≤ u * 1140.7 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hu0
  have k2 : 0.14706 * l ^ 2 * L ≤ 63.17 * L := by nlinarith
  have k3 : 3.127 * l ≤ 64.81 := by linarith
  have hBu : u * L + 3 * u + 6 + 2.5 * b ^ 2 < 31622 := by unfold Bf at hB; linarith
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have huL : u * L ≤ 31616 := by linarith
  -- the reduced inequality `31553.7 − uL − 2.4271u − 0.002L > 0`
  have key : u * L + 2.4271 * u + 0.002 * L < 31553.7 := by
    rcases le_total 4000 L with h4 | h4
    · have hb := log_ge_nat (y := L) (X := 4000) (k := 12252) (by push_cast; linarith)
        (by decide +kernel) (by norm_num)
      have : 8.29 ≤ b := by linarith
      have : 171.8 ≤ 2.5 * b ^ 2 := by nlinarith
      have : L ≤ 31616 := by nlinarith
      linarith
    rcases le_total 1000 L with h3 | h3
    · have hb := log_ge_nat (y := L) (X := 1000) (k := 10204) (by push_cast; linarith)
        (by decide +kernel) (by norm_num)
      have : 6.9 ≤ b := by linarith
      have : 119 ≤ 2.5 * b ^ 2 := by nlinarith
      linarith
    rcases le_total 128 L with h2 | h2
    · have hb := log_ge_nat (y := L) (X := 128) (k := 7168) (by push_cast; linarith)
        (by decide +kernel) (by norm_num)
      have : 4.85 ≤ b := by linarith
      have : 58.8 ≤ 2.5 * b ^ 2 := by nlinarith
      rcases le_total u 10 with hu10 | hu10
      · have : u * L ≤ 10 * 1000 := mul_le_mul hu10 h3 hL0 (by norm_num)
        linarith
      · linarith
    · rcases le_total u 110 with hu1 | hu1
      · have : u * L ≤ 110 * 128 := mul_le_mul hu1 h2 hL0 (by norm_num)
        linarith
      · linarith
  push_cast
  nlinarith

theorem star_large (u L : ℝ) (s : ℕ) (hu : 1 ≤ u) (hL : 9.9 ≤ L) (hB : 31622 ≤ Bf u L)
    (hs1 : Bf u L - 1 < s) (hs2 : (s : ℝ) ≤ Bf u L) :
    (s : ℝ) * 3.42 + 2.391 * u * s + 3.127 * Real.log ((s ^ 2 : ℕ) : ℝ) * s
        + u * (1.5 * Real.log ((s ^ 2 : ℕ) : ℝ) ^ 2 + 22.93 * Real.log ((s ^ 2 : ℕ) : ℝ) + 21.25)
        + 5 * Real.log ((s ^ 2 : ℕ) : ℝ) ^ 2 + 9.0004 * Real.log ((s ^ 2 : ℕ) : ℝ) + 3
        + 0.14706 * Real.log ((s ^ 2 : ℕ) : ℝ) ^ 2 * L < (s : ℝ) * ((s : ℝ) - u * L) := by
  have hcell := phi2_all u L hu hL hB
  set lam := Real.log (Bf u L)
  set S : ℝ := (s : ℝ)
  set b := Real.log L
  have hS : 31621 < S := by linarith
  have hS0 : 0 < S := by linarith
  have hSn : 31621 < s := by
    by_contra h
    have : (s : ℝ) ≤ 31621 := by exact_mod_cast (not_lt.1 h)
    linarith
  have hS2 : (31622 : ℝ) ≤ S := by
    have : (31622 : ℕ) ≤ s := hSn
    have h : ((31622 : ℕ) : ℝ) ≤ (s : ℝ) := Nat.cast_le.2 this
    calc (31622 : ℝ) = ((31622 : ℕ) : ℝ) := by norm_num
      _ ≤ S := h
  have hb0 : 0 ≤ b := Real.log_nonneg (by linarith)
  have hu0 : 0 < u := by linarith
  have hL3 : 0 < L + 3 := by linarith
  -- `l = log s² ≤ 2λ`
  have hl : Real.log ((s ^ 2 : ℕ) : ℝ) ≤ 2 * lam := by
    have e : Real.log ((s ^ 2 : ℕ) : ℝ) = 2 * Real.log S := by
      rw [show ((s ^ 2 : ℕ) : ℝ) = S ^ 2 by push_cast; rfl, Real.log_pow]; norm_num
    rw [e]
    have := Real.log_le_log hS0 hs2
    linarith
  have hl0 : 0 ≤ Real.log ((s ^ 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  set l := Real.log ((s ^ 2 : ℕ) : ℝ)
  have hlam0 : 0 ≤ lam := by linarith
  have hl2 : l ^ 2 ≤ 4 * lam ^ 2 := by nlinarith
  -- `D = S − uL > 3u + 5 + 2.5 b²`
  have hD : 3 * u + 5 + 5 / 2 * b ^ 2 < S - u * L := by unfold Bf at hs1; linarith
  have huL3 : u * (L + 3) ≤ S := by nlinarith
  have huL : u * L ≤ S := by nlinarith
  -- the three transfers
  set P := 6 * lam ^ 2 + 45.86 * lam + 21.25 with hPdef
  set Q := 20 * lam ^ 2 + 18.0008 * lam + 3 with hQdef
  have tP : u * (1.5 * l ^ 2 + 22.93 * l + 21.25) ≤ S * (P / (L + 3)) := by
    have h1 : u * (1.5 * l ^ 2 + 22.93 * l + 21.25) ≤ u * P :=
      mul_le_mul_of_nonneg_left (by rw [hPdef]; nlinarith) hu0.le
    have h2 : u * P = u * (L + 3) * (P / (L + 3)) := by field_simp
    have hP0 : 0 ≤ P / (L + 3) := div_nonneg (by positivity) hL3.le
    have h3 := mul_le_mul_of_nonneg_right huL3 hP0
    linarith
  have tQ : 5 * l ^ 2 + 9.0004 * l + 3 ≤ S * (Q / 31622) := by
    have h1 : 5 * l ^ 2 + 9.0004 * l + 3 ≤ Q := by rw [hQdef]; nlinarith
    have hQ0 : 0 ≤ Q / 31622 := div_nonneg (by positivity) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right hS2 hQ0
    have h3 : (31622 : ℝ) * (Q / 31622) = Q := by field_simp
    linarith
  have tR : 0.14706 * l ^ 2 * L ≤ S * (0.58824 * lam ^ 2 / u) := by
    have h1 : 0.14706 * l ^ 2 * L ≤ 0.58824 * lam ^ 2 * L := by nlinarith
    have h2 : 0.58824 * lam ^ 2 * L = u * L * (0.58824 * lam ^ 2 / u) := by field_simp
    have h0 : 0 ≤ 0.58824 * lam ^ 2 / u := div_nonneg (by positivity) hu0.le
    have h3 := mul_le_mul_of_nonneg_right huL h0
    linarith
  have tl : 3.127 * l * S ≤ 6.254 * lam * S := by nlinarith
  have hcS := mul_le_mul_of_nonneg_left hcell hS0.le
  have hsum : S * Phi2 u L lam = S * (6.254 * lam) + S * (P / (L + 3)) + S * (Q / 31622)
      + S * (0.58824 * lam ^ 2 / u) := by unfold Phi2; ring
  have hDS := mul_lt_mul_of_pos_left hD hS0
  nlinarith

end LLS.Thm14
