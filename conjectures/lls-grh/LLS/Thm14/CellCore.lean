import LLS.Thm14.Reduce

/-!
# The two-variable condition and its cell lemma

`Bf u L = uL + 3(u + 2) + (5/2)(log L)²` is LLS's bound `(h − 1) log q + 3(h + 1)
+ (5/2)(log log q)²` with `u = h − 1`, `L = log q`. When `Bf u L ≥ 31622` we take `s = ⌊Bf⌋`,
and `(★)` follows from

  `Phi2 u L λ ≤ 0.609u + 1.58 + (5/2)(log L)²`,  `λ = log Bf u L`,

with `Phi2 u L λ = 6.254λ + (6λ² + 45.86λ + 21.25)/(L + 3) + (20λ² + 18.0008λ + 3)/31622
+ 0.58824λ²/u`. `LLS.Thm14.cell_of` checks it on a box `[u₁, u₂] × [L₁, L₂]` from rational bounds
at the corners (`log` bounds by integer power comparisons).
-/

namespace LLS.Thm14

open Real

/-- LLS's bound with `u = h − 1`, `L = log q`. -/
noncomputable def Bf (u L : ℝ) : ℝ := u * L + 3 * (u + 2) + 5 / 2 * Real.log L ^ 2

/-- The right side of the two-variable condition. -/
noncomputable def Phi2 (u L lam : ℝ) : ℝ :=
  6.254 * lam + (6 * lam ^ 2 + 45.86 * lam + 21.25) / (L + 3)
    + (20 * lam ^ 2 + 18.0008 * lam + 3) / 31622 + 0.58824 * lam ^ 2 / u

lemma log_ge_nat {y : ℝ} {X k : ℕ} (hX : (X : ℝ) ≤ y) (hk : 2 ^ k ≤ X ^ 1024) (hX0 : 0 < X) :
    (k : ℝ) / 1024 * 0.6931471803 ≤ Real.log y := by
  have h := LLS.log_ge_of_pow X k 1024 (by norm_num) hk
  have : Real.log (X : ℝ) ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hX0) hX
  push_cast at h
  linarith

lemma log_le_nat {y : ℝ} {X k : ℕ} (hy : 0 < y) (hX : y ≤ (X : ℝ)) (hk : X ^ 1024 ≤ 2 ^ k) :
    Real.log y ≤ (k : ℝ) / 1024 * 0.6931471808 := by
  have hX0 : 0 < X := by exact_mod_cast hy.trans_le hX
  have h := LLS.log_le_of_pow X k 1024 (by norm_num) hX0 hk
  have : Real.log y ≤ Real.log (X : ℝ) := Real.log_le_log hy hX
  push_cast at h
  linarith

lemma Phi2_mono {u L lam u1 L1 lam2 : ℝ} (hu1 : 0 < u1) (hu : u1 ≤ u) (hL1 : 0 < L1)
    (hL : L1 ≤ L) (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam2) :
    Phi2 u L lam ≤ Phi2 u1 L1 lam2 := by
  unfold Phi2
  have hlam20 : 0 ≤ lam2 := hlam0.trans hlam
  have hl2 : lam ^ 2 ≤ lam2 ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
  have h1 : (6 * lam ^ 2 + 45.86 * lam + 21.25) / (L + 3)
      ≤ (6 * lam2 ^ 2 + 45.86 * lam2 + 21.25) / (L1 + 3) :=
    div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
  have h2 : (20 * lam ^ 2 + 18.0008 * lam + 3) / 31622
      ≤ (20 * lam2 ^ 2 + 18.0008 * lam2 + 3) / 31622 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have h3 : 0.58824 * lam ^ 2 / u ≤ 0.58824 * lam2 ^ 2 / u1 :=
    div_le_div₀ (by positivity) (by linarith) hu1 hu
  linarith

/-- One box: either `Bf < 31622` on it, or the corner bounds give the condition. -/
lemma cell_of {u L : ℝ} (u1 u2 L1 L2 bl1 bh2 lam2 : ℝ) (hu1 : 0 < u1) (hL1 : 0 < L1)
    (h1 : u1 ≤ u) (h2 : u ≤ u2) (h3 : L1 ≤ L) (h4 : L ≤ L2)
    (hbl : bl1 ≤ Real.log L) (hbl0 : 0 ≤ bl1) (hbh : Real.log L ≤ bh2)
    (hlam : 31622 ≤ Bf u L → Real.log (Bf u L) ≤ lam2)
    (hcheck : u2 * L2 + 3 * (u2 + 2) + 5 / 2 * bh2 ^ 2 < 31622 ∨
      Phi2 u1 L1 lam2 ≤ 0.609 * u1 + 1.58 + 5 / 2 * bl1 ^ 2)
    (hB : 31622 ≤ Bf u L) :
    Phi2 u L (Real.log (Bf u L)) ≤ 0.609 * u + 1.58 + 5 / 2 * Real.log L ^ 2 := by
  have hb0 : 0 ≤ Real.log L := hbl0.trans hbl
  rcases hcheck with hc | hc
  · exfalso
    have hb2 : Real.log L ^ 2 ≤ bh2 ^ 2 := pow_le_pow_left₀ hb0 hbh 2
    have hu0 : 0 ≤ u := by linarith
    have : u * L ≤ u2 * L2 := mul_le_mul h2 h4 (by linarith) (by linarith)
    unfold Bf at hB
    linarith
  · have hlam0 : 0 ≤ Real.log (Bf u L) := Real.log_nonneg (by linarith)
    have hm := Phi2_mono hu1 h1 hL1 h3 hlam0 (hlam hB)
    have hb2 : bl1 ^ 2 ≤ Real.log L ^ 2 := pow_le_pow_left₀ hbl0 hbl 2
    linarith

/-- The `log Bf` bound from a natural upper bound `M` of the corner value. -/
lemma lam_of {u L : ℝ} (u2 L2 bh2 : ℝ) (M k : ℕ) (h2 : u ≤ u2) (h4 : L ≤ L2) (hu0 : 0 ≤ u)
    (hL0 : 0 ≤ L)
    (hb0 : 0 ≤ Real.log L) (hbh : Real.log L ≤ bh2)
    (hM : u2 * L2 + 3 * (u2 + 2) + 5 / 2 * bh2 ^ 2 ≤ M) (hk : M ^ 1024 ≤ 2 ^ k)
    (hB : 31622 ≤ Bf u L) : Real.log (Bf u L) ≤ (k : ℝ) / 1024 * 0.6931471808 := by
  refine log_le_nat (by linarith) ?_ hk
  have hb2 : Real.log L ^ 2 ≤ bh2 ^ 2 := pow_le_pow_left₀ hb0 hbh 2
  have : u * L ≤ u2 * L2 := mul_le_mul h2 h4 hL0 (by linarith)
  unfold Bf
  linarith

end LLS.Thm14
