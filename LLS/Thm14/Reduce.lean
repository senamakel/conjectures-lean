import LLS.Thm14.Assembly

/-!
# From the main inequality to a two-variable condition

With `S = s ≥ 31622`, `l = log s²`, `u = h − 1 ≥ 1`, `uL ≤ S` and `ω(q) ≤ 10 + L/log 30`,
`LLS.Thm14.reduce` shows that the right side of `LLS.Thm14.main_ineq` (with `m ≤ h`, the bound
`Σ_{p ∣ q} llp ≤ ω (l − ½ log 2)²/2` and `LLS.Sharp.P2sum_le_sharp`) is below `X = S²` as soon as

  `S (S − uL) > S (3.42 + 2.391u + 3.127 l) + u (1.5 l² + 22.93 l + 21.25)
      + 5 l² + 9.0004 l + 3 + 0.14706 l² L`.  (★)
-/

namespace LLS.Thm14

open Real

lemma Acoef_bounds {S : ℝ} (hS : 31622 ≤ S) : S ≤ Acoef S ∧ Acoef S ≤ S + 3.0002 := by
  unfold Acoef
  have hS0 : 0 < S := by linarith
  have e : (1 - 1 / S) ^ 2 = (S - 1) ^ 2 / S ^ 2 := by field_simp
  have hS1 : 0 < (S - 1) ^ 2 := by nlinarith
  rw [e, div_div_eq_mul_div]
  constructor
  · rw [le_div_iff₀ hS1]; nlinarith
  · rw [div_le_iff₀ hS1]; nlinarith

lemma sqrt_le_div {S : ℝ} (hS : 31622 ≤ S) : √S ≤ S / 177 := by
  have hS0 : 0 ≤ S := by linarith
  have h177 : (177 : ℝ) ≤ √S := by
    rw [show (177 : ℝ) = √(177 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have := Real.mul_self_sqrt hS0
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

lemma Pc_le (L S l : ℝ) (hSR : 31622 ≤ S) (hL : 9.9 ≤ L) (hl : 20 ≤ l) :
    Pc L S l ≤ (S + 3.0002) * L - 1.0268 * S + 1.5 * l ^ 2 + 5.43 * l
      + 1.127 * L * l + 1.25 := by
  obtain ⟨hA1, hA2⟩ := Acoef_bounds hSR
  obtain ⟨-, -, -, -, l1, l2⟩ := LLS.Sharp.consts
  have hS0 : 0 < S := by linarith
  have hsq0 : 0 ≤ 1 / S ^ 2 := by positivity
  have hsq1 : 1 / S ^ 2 ≤ 1 / 10 ^ 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hlog3 : Real.log 3 ≤ 1.1 := by
    have := LLS.log_le_of_pow 3 1624 1024 (by norm_num) (by norm_num) (by decide +kernel)
    push_cast at this; linarith
  have hlog3nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hL0 : 0 ≤ L := by linarith
  have hA0 : 0 ≤ Acoef S := by linarith
  unfold Pc
  have hsl : 1 / S ^ 2 ≤ 1 := by linarith
  have hin : (1 - 1 / S ^ 2) * L ≤ L := by
    have e : (1 - 1 / S ^ 2) * L = L - (1 / S ^ 2) * L := by ring
    rw [e]; linarith [mul_nonneg hsq0 hL0]
  have hin0 : 0 ≤ (1 - 1 / S ^ 2) * L := mul_nonneg (by linarith) hL0
  have hY : -1.72 + Real.log 2 * (1 + 1 / S ^ 2) + Real.log 3 / S ^ 2 ≤ -1.0268 := by
    have e : -1.72 + Real.log 2 * (1 + 1 / S ^ 2) + Real.log 3 / S ^ 2
        = -1.72 + Real.log 2 + Real.log 2 * (1 / S ^ 2) + Real.log 3 * (1 / S ^ 2) := by ring
    rw [e]
    have a1 := mul_le_mul_of_nonneg_left hsq1 (show 0 ≤ Real.log 2 by linarith)
    have a2 := mul_le_mul_of_nonneg_left hsq1 hlog3nn
    have a3 : Real.log 3 * (1 / 10 ^ 8) ≤ 1.1 * (1 / 10 ^ 8) := by linarith
    have a4 : Real.log 2 * (1 / 10 ^ 8) ≤ 1 * (1 / 10 ^ 8) := by linarith
    linarith
  have e : Acoef S * ((1 - 1 / S ^ 2) * L - 1.72 + Real.log 2 * (1 + 1 / S ^ 2)
      + Real.log 3 / S ^ 2) = Acoef S * ((1 - 1 / S ^ 2) * L)
        + Acoef S * (-1.72 + Real.log 2 * (1 + 1 / S ^ 2) + Real.log 3 / S ^ 2) := by ring
  rw [e]
  have k1 : Acoef S * ((1 - 1 / S ^ 2) * L) ≤ (S + 3.0002) * L :=
    mul_le_mul hA2 hin hin0 (by linarith)
  have k2 : Acoef S * (-1.72 + Real.log 2 * (1 + 1 / S ^ 2) + Real.log 3 / S ^ 2)
      ≤ -1.0268 * S := by
    have := mul_le_mul_of_nonneg_left hY hA0
    linarith
  have k3 : (l - Real.log 2 / 2) ^ 2 / 2 + (l - Real.log 3 / 2) ^ 2 / 2 ≤ l ^ 2 := by
    have b1 : (l - Real.log 2 / 2) ^ 2 ≤ l ^ 2 := by
      have : 0 ≤ (Real.log 2 / 2) * (2 * l - Real.log 2 / 2) := mul_nonneg (by linarith) (by linarith)
      linear_combination this
    have b2 : (l - Real.log 3 / 2) ^ 2 ≤ l ^ 2 := by
      have : 0 ≤ (Real.log 3 / 2) * (2 * l - Real.log 3 / 2) := mul_nonneg (by linarith) (by linarith)
      linear_combination this
    linarith
  have k4 : 1 / 2 * l * max (L - 3) (l + 2) ≤ 1 / 2 * L * l + 1 / 2 * l ^ 2 - 1 / 2 * l := by
    calc 1 / 2 * l * max (L - 3) (l + 2) ≤ 1 / 2 * l * ((L - 3) + (l + 2)) :=
          mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) (by linarith)
      _ = _ := by ring
  linear_combination k1 + k2 + k3 + k4

set_option maxHeartbeats 2000000 in
theorem reduceR (S U L l Nr ω : ℝ) (hSR : 31622 ≤ S) (hU1 : 1 ≤ U) (hL : 9.9 ≤ L)
    (huL : U * L ≤ S) (hl : 20.72 ≤ l) (hlS : Real.log S = l / 2) (hNR : Nr ≤ 0.7072 * S + 1)
    (hN0 : 1 ≤ Nr) (hω : ω ≤ 10 + L / Real.log 30)
    (hstar : S * 3.42 + 2.391 * U * S + 3.127 * l * S + U * (1.5 * l ^ 2 + 22.93 * l + 21.25)
        + 5 * l ^ 2 + 9.0004 * l + 3 + 0.14706 * l ^ 2 * L < S * (S - U * L)) :
    (U + 1) * (2 * psiU S + 2 * psiU Nr) + U * Pc L S l
        + 2 * Acoef S * (l - 1 - eulerMascheroniConstant + 0.25 / S + 12 / S ^ 2)
        + 3 / 20 * S + 3 * l + 3 + ω * (l - Real.log 2 / 2) ^ 2 / 2 < S ^ 2 := by
  have hS0 : 0 < S := by linarith
  obtain ⟨hA1, hA2⟩ := Acoef_bounds hSR
  have hsq := sqrt_le_div hSR
  obtain ⟨g1, g2, p1, p2, l1, l2⟩ := LLS.Sharp.consts
  have hNS : Nr ≤ S := by linarith
  have hsqN : √Nr ≤ √S := Real.sqrt_le_sqrt hNS
  have hlogN : Real.log Nr ≤ l / 2 := by rw [← hlS]; exact Real.log_le_log (by linarith) hNS
  have hT : 2 * psiU S + 2 * psiU Nr ≤ 3.4178 * S + 8 * l + 10 := by
    unfold psiU; rw [hlS]; linarith
  have hT' : (U + 1) * (2 * psiU S + 2 * psiU Nr) ≤ (U + 1) * (3.4178 * S + 8 * l + 10) :=
    mul_le_mul_of_nonneg_left hT (by linarith)
  have hsq0 : 0 ≤ 1 / S ^ 2 := by positivity
  have hsq1 : 1 / S ^ 2 ≤ 1 / 10 ^ 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hPc := Pc_le L S l hSR hL (by linarith)
  have hPc' : U * Pc L S l ≤ U * ((S + 3.0002) * L - 1.0268 * S + 1.5 * l ^ 2 + 5.43 * l
      + 1.127 * L * l + 1.25) := mul_le_mul_of_nonneg_left hPc (by linarith)
  -- `P₂`
  have hP2 : l - 1 - eulerMascheroniConstant + 0.25 / S + 12 / S ^ 2 ≤ l - 1.5767 := by
    have h1 : 0.25 / S ≤ 0.25 / 31622 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hSR
    have h2 : 12 / S ^ 2 = 12 * (1 / S ^ 2) := by ring
    have h3 : 12 * (1 / S ^ 2) ≤ 12 * (1 / 10 ^ 8) := by linarith
    linarith
  have hP2' : 2 * Acoef S * (l - 1 - eulerMascheroniConstant + 0.25 / S + 12 / S ^ 2)
      ≤ 2 * (S + 3.0002) * (l - 1.5767) := by
    have h0 : 0 ≤ l - 1.5767 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hP2 (show 0 ≤ 2 * Acoef S by linarith)
    have h2 := mul_le_mul_of_nonneg_right (show 2 * Acoef S ≤ 2 * (S + 3.0002) by linarith) h0
    linarith
  -- `ω`
  have hlog30 : 3.4 ≤ Real.log 30 := by
    have := LLS.log_ge_of_pow 30 5024 1024 (by norm_num) (by decide +kernel)
    push_cast at this; linarith
  have hω' : ω * (l - Real.log 2 / 2) ^ 2 / 2 ≤ (5 + 0.14706 * L) * l ^ 2 := by
    have hq : (l - Real.log 2 / 2) ^ 2 ≤ l ^ 2 := by
      have : 0 ≤ (Real.log 2 / 2) * (2 * l - Real.log 2 / 2) := mul_nonneg (by linarith) (by linarith)
      linear_combination this
    have hLd : L / Real.log 30 ≤ 0.29412 * L := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hlog30 (show 0 ≤ 0.29412 * L by linarith)
      linarith
    rcases le_total 0 ω with h | h
    · have hω2 : ω ≤ 10 + 0.29412 * L := by linarith
      have a1 := mul_le_mul_of_nonneg_left hq h
      have a2 := mul_le_mul_of_nonneg_right hω2 (sq_nonneg l)
      linarith
    · have : ω * (l - Real.log 2 / 2) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _)
      have : 0 ≤ (5 + 0.14706 * L) * l ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith
  have hst := hstar
  have hUL1 : 3.0002 * (U * L) ≤ 3.0002 * S := by linarith
  have hUL2 : 1.127 * l * (U * L) ≤ 1.127 * l * S := mul_le_mul_of_nonneg_left huL (by linarith)
  have hU8 : (U + 1) * (8 * l + 10) ≤ U * (16 * l + 20) := by
    have : 0 ≤ (U - 1) * (8 * l + 10) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hUl : 0 ≤ U * l := mul_nonneg (by linarith) (by linarith)
  linarith


theorem reduce (s N u : ℕ) (hs : 31622 ≤ s) (hN : 10000 * N ≤ 7072 * s + 10000) (hN1 : 1 ≤ N)
    (hu : 1 ≤ u) (L : ℝ) (hL : 9.9 ≤ L) (huL : (u : ℝ) * L ≤ s) (ω : ℝ) (hω : ω ≤ 10 + L / Real.log 30)
    (hstar : (s : ℝ) * 3.42 + 2.391 * u * s + 3.127 * Real.log ((s ^ 2 : ℕ) : ℝ) * s
        + u * (1.5 * Real.log ((s ^ 2 : ℕ) : ℝ) ^ 2 + 22.93 * Real.log ((s ^ 2 : ℕ) : ℝ) + 21.25)
        + 5 * Real.log ((s ^ 2 : ℕ) : ℝ) ^ 2 + 9.0004 * Real.log ((s ^ 2 : ℕ) : ℝ) + 3
        + 0.14706 * Real.log ((s ^ 2 : ℕ) : ℝ) ^ 2 * L < (s : ℝ) * ((s : ℝ) - u * L)) :
    ((u : ℝ) + 1) * (2 * psiU s + 2 * psiU N) + u * Pc L s (Real.log ((s ^ 2 : ℕ) : ℝ))
        + 2 * Acoef s * (Real.log ((s ^ 2 : ℕ) : ℝ) - 1 - eulerMascheroniConstant
          + 0.25 / √((s ^ 2 : ℕ) : ℝ) + 12 / ((s ^ 2 : ℕ) : ℝ))
        + 3 / 20 * s + 3 * Real.log ((s ^ 2 : ℕ) : ℝ) + 3
        + ω * (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 2 / 2) ^ 2 / 2
      < ((s ^ 2 : ℕ) : ℝ) := by
  have hSR : (31622 : ℝ) ≤ s := by exact_mod_cast hs
  have hXR : ((s ^ 2 : ℕ) : ℝ) = (s : ℝ) ^ 2 := by push_cast; ring
  have hsqX : √((s ^ 2 : ℕ) : ℝ) = s := by rw [hXR, Real.sqrt_sq (by linarith)]
  have hlS : Real.log (s : ℝ) = Real.log ((s : ℝ) ^ 2) / 2 := by
    rw [Real.log_pow]; push_cast; ring
  have hNR : (N : ℝ) ≤ 0.7072 * s + 1 := by
    have : (10000 : ℝ) * N ≤ 7072 * s + 10000 := by exact_mod_cast hN
    linarith
  rw [hsqX]
  rw [hXR] at hstar ⊢
  exact reduceR s u L _ N ω hSR (by exact_mod_cast hu) hL huL (by rw [← hXR]; exact logX_ge hs) hlS hNR
    (by exact_mod_cast hN1) hω hstar

end LLS.Thm14
