import LLS.Sharp.Assembly
import LLS.Sharp.Principal
import LLS.Sharp.Lemma51
import LLS.Sharp.NumL
import LLS.L1.Final
import LLS.Statement

/-!
# LLS Theorem 1.5 with the paper's constants, under GRH

For `q ≥ 10¹⁰` take `x = ⌊log² q / 4⌋`, so `x ≥ 132` and `2√x ≤ log q ≤ 2√x + 1/√x`. With
`l = log x`, `u = 1/l`, `y = 1/√x`:

* upper: `log_norm_L1_le_sharp`, `l1Sum1_le_sharp` and `P2sum_le_sharp` give
  `log ‖L(1,χ)‖ ≤ log l + γ + FUu 𝔞 u y` (`upper_alg`), and `FUu_le_log` gives
  `‖L(1,χ)‖ ≤ e^γ (l + 1 + 4/(l + 2 log 2))`;
* lower: `log_norm_L1_ge_sharp` and Lemma 5.1 (`re_Wsum_ge_finset` with the primes up to `11`
  for `x < 22100`, `re_Wsum_ge` beyond) give
  `−log ‖L(1,χ)‖ ≤ log l + γ − log ζ(2) + HLu 𝔞 u y + E` (`lower_alg`), and
  `HLu_le_log_S5` (on ten boxes in `x`) or `HLu_le_log_asym` give
  `1/‖L(1,χ)‖ ≤ (e^γ/ζ(2)) (l + 1 + 4/(l + 2 log 2) + 7 (l + 2 log 2) y/(1 + y²/2))`.

Finally `log log q ≥ l/2 + log 2` and `m ↦ m + 1/m` is increasing for `m ≥ 1`.
-/

namespace LLS.Sharp

open Real Erdos985 Erdos985.Analytic

/-! ### The gamma parts in the variables `u`, `y` -/

lemma ELu_eq (a : ℕ) {X : ℝ} (hX : 0 < X) (hl : Real.log X ≠ 0) :
    ELu a (1 / Real.log X) (1 / √X) = 1 / Real.log X * ELpar a X := by
  have hs : (1 / √X) ^ 2 = 1 / X := by rw [div_pow, Real.sq_sqrt hX.le, one_pow]
  have hX0 : X ≠ 0 := hX.ne'
  unfold ELu ELpar
  rw [hs]
  split_ifs
  · field_simp
    ring
  · ring

lemma EUu_eq (a : ℕ) {X : ℝ} (hX : 0 < X) (hl : Real.log X ≠ 0) :
    EUu a (1 / Real.log X) (1 / √X) = 1 / Real.log X * EUpar a X := by
  have hs : (1 / √X) ^ 2 = 1 / X := by rw [div_pow, Real.sq_sqrt hX.le, one_pow]
  have hX0 : X ≠ 0 := hX.ne'
  unfold EUu EUpar
  rw [hs]
  split_ifs
  · field_simp
    ring
  · ring

/-! ### The algebra of the two bounds -/

/-- The upper bound in the variables `u = 1/l`, `y = 1/s`. -/
lemma upper_alg (a : ℕ) {X l s lq S1 P2 EL logL ll : ℝ} (hs : 4 ≤ s) (hX : s ^ 2 = X)
    (hl : 2 < l) (hEL : ELu a (1 / l) (1 / s) = 1 / l * EL)
    (hL : logL ≤ S1 + (lq / 2 + Gpar a) / l
      - (1 / (2 * l) - 1 / s / l ^ 2) * ((1 - 1 / X) * lq - 2 * P2 + 2 * EL) / (1 + 1 / s) ^ 2
      + 2 / (X * l ^ 2))
    (hS1 : S1 ≤ ll + eulerMascheroniConstant - 1 + eulerMascheroniConstant / l
      + (0.6 / s + 29 / X) / l)
    (hP2 : P2 ≤ l - 1 - eulerMascheroniConstant + 0.25 / s + 12 / X)
    (hlq : lq ≤ 2 * s + 1 / s) :
    logL ≤ ll + eulerMascheroniConstant + FUu a (1 / l) (1 / s) := by
  subst hX
  have hs0 : 0 < s := by linarith
  have hl0 : 0 < l := by linarith
  have hy0 : 0 < 1 / s := by positivity
  have hy4 : 1 / s ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hc0 : 0 ≤ 1 / (2 * l) - 1 / s / l ^ 2 := by
    have : 1 / s / l ^ 2 ≤ 1 / (2 * l) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hD : 1 ≤ (1 + 1 / s) ^ 2 := by nlinarith
  set C := (1 / (2 * l) - 1 / s / l ^ 2) / (1 + 1 / s) ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hC1 : C ≤ 1 / (2 * l) := by
    rw [hC, div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ 1 / (2 * l) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hD h0
    have h2 : 0 ≤ 1 / s / l ^ 2 := by positivity
    linarith
  set K := 1 / (2 * l) - C * (1 - 1 / s ^ 2) with hK
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ 1 / s ^ 2 := by positivity
    have h2 : C * (1 - 1 / s ^ 2) ≤ C := by nlinarith
    rw [hK]; linarith
  have eL : S1 + (lq / 2 + Gpar a) / l
      - (1 / (2 * l) - 1 / s / l ^ 2) * ((1 - 1 / s ^ 2) * lq - 2 * P2 + 2 * EL) / (1 + 1 / s) ^ 2
      + 2 / (s ^ 2 * l ^ 2)
      = S1 + K * lq + Gpar a / l + 2 * C * P2 - 2 * C * EL + 2 / (s ^ 2 * l ^ 2) := by
    rw [hK, hC]; ring
  have b1 : K * lq ≤ K * (2 * s + 1 / s) := mul_le_mul_of_nonneg_left hlq hK0
  have b2 : 2 * C * P2
      ≤ 2 * C * (l - 1 - eulerMascheroniConstant + 0.25 / s + 12 / s ^ 2) :=
    mul_le_mul_of_nonneg_left hP2 (by positivity)
  have eR : ll + eulerMascheroniConstant - 1 + eulerMascheroniConstant / l
        + (0.6 / s + 29 / s ^ 2) / l + K * (2 * s + 1 / s) + Gpar a / l
        + 2 * C * (l - 1 - eulerMascheroniConstant + 0.25 / s + 12 / s ^ 2)
        - 2 * C * EL + 2 / (s ^ 2 * l ^ 2)
      = ll + eulerMascheroniConstant + FUu a (1 / l) (1 / s) := by
    have hELu : EL = l * ELu a (1 / l) (1 / s) := by rw [hEL]; field_simp
    rw [hELu, hK, hC]
    unfold FUu
    field_simp
    ring
  rw [eL] at hL
  linarith

/-- The lower bound in the variables `u = 1/l`, `y = 1/s`. -/
lemma lower_alg (a : ℕ) {X l s lq S1 P2 EU Wre logL ll g e : ℝ} (hs : 4 ≤ s) (hX : s ^ 2 = X)
    (hl : 2 < l) (hEU : EUu a (1 / l) (1 / s) = 1 / l * EU)
    (hL : Wre - ((1 / l + 2 * (1 / s) / l ^ 2) / (1 - 1 / s) ^ 2 - 1 / l) * P2
        + (lq / 2 + Gpar a) / l
        - (1 / (2 * l) + 1 / s / l ^ 2) * ((1 - 1 / X) * lq + 2 * EU) / (1 - 1 / s) ^ 2
        - 2 / (X * l ^ 2) ≤ logL)
    (hW : -(S1 + P2 / l) + g - e ≤ Wre)
    (hS1 : S1 ≤ ll + eulerMascheroniConstant - 1 + eulerMascheroniConstant / l
      + (0.6 / s + 29 / X) / l)
    (hP2 : P2 ≤ l - 1 - eulerMascheroniConstant + 0.25 / s + 12 / X)
    (hlq : lq ≤ 2 * s + 1 / s) :
    -logL ≤ ll + eulerMascheroniConstant - g + e + HLu a (1 / l) (1 / s) := by
  subst hX
  have hs0 : 0 < s := by linarith
  have hl0 : 0 < l := by linarith
  have hy0 : 0 < 1 / s := by positivity
  have hy4 : 1 / s ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hy1 : 0 < 1 - 1 / s := by linarith
  set A := (1 / l + 2 * (1 / s) / l ^ 2) / (1 - 1 / s) ^ 2 with hA
  set d := 1 / (2 * l) + 1 / s / l ^ 2 with hd
  set K := d * (1 - 1 / s ^ 2) / (1 - 1 / s) ^ 2 - 1 / (2 * l) with hK
  have hA0 : 0 ≤ A := by positivity
  have hK0 : 0 ≤ K := by
    have hd1 : 1 / (2 * l) ≤ d := by
      have : 0 ≤ 1 / s / l ^ 2 := by positivity
      rw [hd]; linarith
    have hr : (1 - 1 / s) ^ 2 ≤ 1 - 1 / s ^ 2 := by
      have : 1 / s ^ 2 = (1 / s) ^ 2 := by ring
      rw [this]; nlinarith
    have : d ≤ d * (1 - 1 / s ^ 2) / (1 - 1 / s) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ d := by positivity
      nlinarith
    rw [hK]; linarith
  have eL : Wre - (A - 1 / l) * P2 + (lq / 2 + Gpar a) / l
        - d * ((1 - 1 / s ^ 2) * lq + 2 * EU) / (1 - 1 / s) ^ 2 - 2 / (s ^ 2 * l ^ 2)
      = Wre - (A - 1 / l) * P2 - K * lq + Gpar a / l - 2 * d / (1 - 1 / s) ^ 2 * EU
        - 2 / (s ^ 2 * l ^ 2) := by
    rw [hK]; ring
  rw [eL] at hL
  have b1 : K * lq ≤ K * (2 * s + 1 / s) := mul_le_mul_of_nonneg_left hlq hK0
  have b2 : A * P2 ≤ A * (l - 1 - eulerMascheroniConstant + 0.25 / s + 12 / s ^ 2) :=
    mul_le_mul_of_nonneg_left hP2 hA0
  have eP : (A - 1 / l) * P2 = A * P2 - P2 / l := by ring
  have eR : ll + eulerMascheroniConstant - 1 + eulerMascheroniConstant / l
        + (0.6 / s + 29 / s ^ 2) / l
        + A * (l - 1 - eulerMascheroniConstant + 0.25 / s + 12 / s ^ 2) - g + e
        + K * (2 * s + 1 / s) - Gpar a / l + 2 * d / (1 - 1 / s) ^ 2 * EU + 2 / (s ^ 2 * l ^ 2)
      = ll + eulerMascheroniConstant - g + e + HLu a (1 / l) (1 / s) := by
    have hEUu : EU = l * EUu a (1 / l) (1 / s) := by rw [hEU]; field_simp
    have hs1 : s - 1 ≠ 0 := by intro h; linarith
    have hs1' : 1 - 1 / s ≠ 0 := hy1.ne'
    rw [hEUu, hA, hK, hd]
    unfold HLu
    field_simp
    ring
  linarith

/-! ### From `l` back to `log log q` -/

lemma mplus_mono {m m' : ℝ} (hm : 1 ≤ m) (hmm : m ≤ m') : m + 1 / m ≤ m' + 1 / m' := by
  have hm0 : 0 < m := by linarith
  have hm0' : 0 < m' := by linarith
  have e : m' + 1 / m' - (m + 1 / m) = (m' - m) * (m * m' - 1) / (m * m') := by
    field_simp; ring
  have : 0 ≤ (m' - m) * (m * m' - 1) / (m * m') := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith); nlinarith
  linarith

lemma lVf_eq {l : ℝ} (hl : 0 < l) :
    l * (1 + Vf (1 / l)) = 2 * ((l / 2 + Real.log 2) - Real.log 2 + 1 / 2
      + 1 / (l / 2 + Real.log 2)) := by
  have h2 := consts.2.2.2.2.1
  have : 0 < l / 2 + Real.log 2 := by linarith
  have : 0 < l + 2 * Real.log 2 := by linarith
  unfold Vf
  field_simp
  ring

lemma upper_num {l llq : ℝ} (hl : 2 < l) (hm : l / 2 + Real.log 2 ≤ llq) :
    l * (1 + Vf (1 / l)) ≤ 2 * (llq - Real.log 2 + 1 / 2 + 1 / llq) := by
  have h2 := consts.2.2.2.2.1
  rw [lVf_eq (by linarith)]
  have := mplus_mono (m := l / 2 + Real.log 2) (by linarith) hm
  linarith

lemma lower_num {l llq lq s : ℝ} (hl : 2 < l) (hm : l / 2 + Real.log 2 ≤ llq) (hs : 0 < s)
    (hlq0 : 0 < lq) (hlq : lq ≤ 2 * s + 1 / s) :
    l * (1 + Vf (1 / l) + Zz (1 / l) (1 / s))
      ≤ 2 * (llq - Real.log 2 + 1 / 2 + 1 / llq + 14 * llq / lq) := by
  have h2 := consts.2.2.2.2.1
  have hl0 : 0 < l := by linarith
  have h1 := upper_num hl hm
  have hm0 : 0 < l / 2 + Real.log 2 := by linarith
  have eZ : l * Zz (1 / l) (1 / s) = 28 * (l / 2 + Real.log 2) / (2 * s + 1 / s) := by
    unfold Zz
    field_simp
    ring
  have hZ : 28 * (l / 2 + Real.log 2) / (2 * s + 1 / s) ≤ 28 * llq / lq := by
    calc 28 * (l / 2 + Real.log 2) / (2 * s + 1 / s) ≤ 28 * (l / 2 + Real.log 2) / lq :=
          div_le_div_of_nonneg_left (by positivity) hlq0 hlq
      _ ≤ 28 * llq / lq := div_le_div_of_nonneg_right (by linarith) hlq0.le
  have e : l * (1 + Vf (1 / l) + Zz (1 / l) (1 / s))
      = l * (1 + Vf (1 / l)) + l * Zz (1 / l) (1 / s) := by ring
  have e2 : 2 * (14 * llq / lq) = 28 * llq / lq := by ring
  rw [e, eZ]
  linarith

/-! ### The choice of `x` -/

lemma setup {q : ℕ} (hq : (10 : ℝ) ^ 10 ≤ q) :
    ∃ x : ℕ, 132 ≤ x ∧ 2 * √(x : ℝ) ≤ Real.log q ∧ Real.log q ≤ 2 * √(x : ℝ) + 1 / √(x : ℝ) := by
  have hq0 : (0 : ℝ) < q := by linarith [show (0 : ℝ) < 10 ^ 10 by norm_num]
  set lq := Real.log q with hlqdef
  have hlq : 23 ≤ lq := by
    rw [hlqdef, Real.le_log_iff_exp_le hq0]
    have := Real.exp_one_lt_d9
    calc Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.7182818286 ^ 23 := by gcongr
      _ ≤ 10 ^ 10 := by norm_num
      _ ≤ q := hq
  set x := ⌊lq ^ 2 / 4⌋₊ with hxdef
  have hx1 : (x : ℝ) ≤ lq ^ 2 / 4 := Nat.floor_le (by positivity)
  have hx2 : lq ^ 2 / 4 < x + 1 := Nat.lt_floor_add_one _
  have hx : 132 ≤ x := Nat.le_floor (by push_cast; nlinarith)
  refine ⟨x, hx, ?_, ?_⟩
  · have : √(x : ℝ) ≤ lq / 2 := by
      rw [show lq / 2 = √((lq / 2) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  · have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hs0 : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
    have hss : √(x : ℝ) ^ 2 = x := Real.sq_sqrt hx0.le
    have h1 : √(x : ℝ) * (1 / √(x : ℝ)) = 1 := by field_simp
    have h3 : 0 ≤ (1 / √(x : ℝ)) ^ 2 := sq_nonneg _
    by_contra h
    push Not at h
    have h4 : 0 ≤ 2 * √(x : ℝ) + 1 / √(x : ℝ) := by positivity
    nlinarith

/-! ### Numerical facts -/

lemma log_nat_ge {x X k : ℕ} (hX : X ≤ x) (hk : 2 ^ k ≤ X ^ 1024) (hX0 : 0 < X) :
    (k : ℝ) / 1024 * 0.6931471803 ≤ Real.log x := by
  have h := log_ge_of_pow X k 1024 (by norm_num) hk
  have : Real.log (X : ℝ) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hX0) (by exact_mod_cast hX)
  push_cast at h
  linarith

lemma log_nat_le {x X k : ℕ} (hX : x ≤ X) (hk : X ^ 1024 ≤ 2 ^ k) (hx0 : 0 < x) :
    Real.log x ≤ (k : ℝ) / 1024 * 0.6931471808 := by
  have h := log_le_of_pow X k 1024 (by norm_num) (by omega) hk
  have : Real.log (x : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hx0) (by exact_mod_cast hX)
  push_cast at h
  linarith

/-- `log ζ(2) + Σ_{p ≤ 11} log(1 − p^{−2}) ≤ 0.0229`. -/
lemma zeta2_S5 :
    Real.log (π ^ 2 / 6) - 0.0229
      ≤ ∑ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ), -Real.log (1 - 1 / (p : ℝ) ^ 2) := by
  have e : ∑ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ), -Real.log (1 - 1 / (p : ℝ) ^ 2)
      = -(Real.log (3 / 4) + Real.log (8 / 9) + Real.log (24 / 25) + Real.log (48 / 49)
          + Real.log (120 / 121)) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
    ring
  have eP : Real.log (3 / 4) + Real.log (8 / 9) + Real.log (24 / 25) + Real.log (48 / 49)
      + Real.log (120 / 121) = Real.log (3317760 / 5336100) := by
    rw [← Real.log_mul, ← Real.log_mul, ← Real.log_mul, ← Real.log_mul] <;> norm_num
  rw [e, eP]
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have h := Real.log_le_sub_one_of_pos (x := π ^ 2 / 6 * (3317760 / 5336100)) (by positivity)
  rw [Real.log_mul (by positivity) (by norm_num)] at h
  have : π ^ 2 < 3.1416 ^ 2 := by nlinarith
  linarith

/-- One box of the regime `x ≤ 22100`. -/
lemma S5_iv (a : ℕ) (ha : a ≤ 1) (x X1 X2 k1 k2 : ℕ) (u1 u2 y1 y2 s : ℝ) (hx1 : X1 ≤ x)
    (hx2 : x ≤ X2) (hX1 : 0 < X1) (hk1 : 2 ^ k1 ≤ X1 ^ 1024) (hk2 : X2 ^ 1024 ≤ 2 ^ k2)
    (hu2 : 1 ≤ u2 * ((k1 : ℝ) / 1024 * 0.6931471803))
    (hu1 : u1 * ((k2 : ℝ) / 1024 * 0.6931471808) ≤ 1) (hu10 : 0 < u1) (hk10 : 0 < k1)
    (hy2 : 1 ≤ y2 ^ 2 * X1) (hy1 : y1 ^ 2 * X2 ≤ 1) (hy10 : 0 < y1) (hy20 : 0 < y2)
    (hu2' : u2 ≤ 0.205) (hy2' : y2 ≤ 0.09) (hs : u2 ≤ 0.198 ∧ s = 0 ∨ s = 0.003)
    (hnum : s + y2 * QLhi u1 u2 y2 + 0.0229 + 50 / 3 * y2 ^ 2
      ≤ 2 * (7 * (1 + 1.3862 * u1) * y1 / ((1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2)))))
        / (2 + 7 * (1 + 1.3862 * u1) * y1 / ((1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2)))))) :
    HLu a (1 / Real.log x) (1 / √(x : ℝ)) + (0.0229 + 50 / 3 * (1 / √(x : ℝ)) ^ 2)
      ≤ Real.log (1 + Vf (1 / Real.log x) + Zz (1 / Real.log x) (1 / √(x : ℝ))) := by
  have hx0 : 0 < x := by omega
  have hL1 := log_nat_ge hx1 hk1 hX1
  have hL2 := log_nat_le hx2 hk2 hx0
  have hL10 : 0 < (k1 : ℝ) / 1024 * 0.6931471803 := by
    have : (0 : ℝ) < k1 := by exact_mod_cast hk10
    positivity
  have hl0 : 0 < Real.log x := by linarith
  have hL20 : 0 < (k2 : ℝ) / 1024 * 0.6931471808 := by linarith
  have hu2b : 1 / Real.log x ≤ u2 := by
    rw [div_le_iff₀ hl0]; nlinarith
  have hu1b : u1 ≤ 1 / Real.log x := by
    rw [le_div_iff₀ hl0]; nlinarith
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx0
  have hsx : 0 < √(x : ℝ) := Real.sqrt_pos.2 hxR
  have hss : √(x : ℝ) ^ 2 = x := Real.sq_sqrt hxR.le
  have hX1R : (X1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hX2R : (x : ℝ) ≤ X2 := by exact_mod_cast hx2
  have hy2b : 1 / √(x : ℝ) ≤ y2 := by
    rw [div_le_iff₀ hsx]
    have : 1 ≤ (y2 * √(x : ℝ)) ^ 2 := by
      rw [mul_pow, hss]; nlinarith [sq_nonneg y2]
    nlinarith [mul_pos hy20 hsx]
  have hy1b : y1 ≤ 1 / √(x : ℝ) := by
    rw [le_div_iff₀ hsx]
    have : (y1 * √(x : ℝ)) ^ 2 ≤ 1 := by
      rw [mul_pow, hss]; nlinarith [sq_nonneg y1]
    nlinarith [mul_pos hy10 hsx]
  exact HLu_le_log_S5 a ha hu1b hu2b hu10 hu2' hy1b hy2b hy10 hy2' hs hnum

/-- The lower-bound core for `132 ≤ x ≤ 22100`, on ten boxes. -/
lemma lower_core (a : ℕ) (ha : a ≤ 1) (x : ℕ) (hx1 : 132 ≤ x) (hx2 : x ≤ 22100) :
    HLu a (1 / Real.log x) (1 / √(x : ℝ)) + (0.0229 + 50 / 3 * (1 / √(x : ℝ)) ^ 2)
      ≤ Real.log (1 + Vf (1 / Real.log x) + Zz (1 / Real.log x) (1 / √(x : ℝ))) := by
  rcases le_or_gt x 138 with h0 | h0
  · exact S5_iv a ha x 132 138 7213 7280 (5073 / 25000) (10241 / 50000) (266 / 3125) (272 / 3125) 0.003 hx1 h0
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inr rfl) (by norm_num [QLhi])
  rcases le_or_gt x 150 with h1 | h1
  · exact S5_iv a ha x 138 150 7279 7403 (3991 / 20000) (2537 / 12500) (2041 / 25000) (8513 / 100000) 0.003 h0.le h1
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inr rfl) (by norm_num [QLhi])
  rcases le_or_gt x 177 with h2 | h2
  · exact S5_iv a ha x 150 177 7402 7647 (9659 / 50000) (19959 / 100000) (1879 / 25000) (1633 / 20000) 0.003 h1.le h2
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inr rfl) (by norm_num [QLhi])
  rcases le_or_gt x 247 with h3 | h3
  · exact S5_iv a ha x 177 247 7646 8140 (4537 / 25000) (9661 / 50000) (3181 / 50000) (7517 / 100000) 0 h2.le h3
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inl ⟨by norm_num, rfl⟩) (by norm_num [QLhi])
  rcases le_or_gt x 433 with h4 | h4
  · exact S5_iv a ha x 247 433 8139 8969 (16471 / 100000) (2269 / 12500) (961 / 20000) (6363 / 100000) 0 h3.le h4
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inl ⟨by norm_num, rfl⟩) (by norm_num [QLhi])
  rcases le_or_gt x 965 with h5 | h5
  · exact S5_iv a ha x 433 965 8968 10153 (291 / 2000) (8237 / 50000) (3219 / 100000) (2403 / 50000) 0 h4.le h5
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inl ⟨by norm_num, rfl⟩) (by norm_num [QLhi])
  rcases le_or_gt x 2897 with h6 | h6
  · exact S5_iv a ha x 965 2897 10152 11777 (392 / 3125) (14553 / 100000) (1857 / 100000) (161 / 5000) 0 h5.le h6
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inl ⟨by norm_num, rfl⟩) (by norm_num [QLhi])
  rcases le_or_gt x 8691 with h7 | h7
  · exact S5_iv a ha x 2897 8691 11776 13400 (689 / 6250) (6273 / 50000) (67 / 6250) (929 / 50000) 0 h6.le h7
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inl ⟨by norm_num, rfl⟩) (by norm_num [QLhi])
  rcases le_or_gt x 19367 with h8 | h8
  · exact S5_iv a ha x 8691 19367 13399 14584 (10129 / 100000) (5513 / 50000) (359 / 50000) (1073 / 100000) 0 h7.le h8
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inl ⟨by norm_num, rfl⟩) (by norm_num [QLhi])
  exact S5_iv a ha x 19367 22100 14583 14779 (2499 / 25000) (10131 / 100000) (21 / 3125) (719 / 100000) 0 h8.le hx2
        (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (Or.inl ⟨by norm_num, rfl⟩) (by norm_num [QLhi])

/-! ### Common facts about `x` -/

lemma x_facts {x : ℕ} (hx : 132 ≤ x) :
    0 < (x : ℝ) ∧ 4.8824 ≤ Real.log x ∧ 11.2 ≤ √(x : ℝ) ∧ √(x : ℝ) ^ 2 = x := by
  have hxR : (132 : ℝ) ≤ x := by exact_mod_cast hx
  have hl := log_nat_ge hx (k := 7213) (by decide +kernel) (by norm_num)
  refine ⟨by linarith, by norm_num at hl ⊢; linarith, ?_, Real.sq_sqrt (by linarith)⟩
  rw [show (11.2 : ℝ) = √(11.2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num; linarith)

lemma llq_ge {x : ℕ} {lq : ℝ} (hx : 0 < (x : ℝ)) (h : 2 * √(x : ℝ) ≤ lq) :
    Real.log x / 2 + Real.log 2 ≤ Real.log lq := by
  have hs : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by norm_num) hs.ne', Real.log_sqrt hx.le] at this
  linarith

/-! ### LLS Theorem 1.5 -/

/-- **LLS Theorem 1.5, upper bound, under GRH**: for `q ≥ 10¹⁰` and `χ` primitive mod `q`,
`|L(1, χ)| ≤ 2e^γ (log log q − log 2 + 1/2 + 1/log log q)`. -/
theorem l1UpperBound_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : LLS.L1UpperBound := by
  intro q _ hq χ hprim
  have hχ := LLS.chi_ne_one hq hprim
  obtain ⟨x, hx, hlq1, hlq2⟩ := setup hq
  have hB := LLS.psi1NatBound_of_GRH hGRH
  have hx100 : 100 ≤ x := by omega
  obtain ⟨hxR, hl, hs11, hss⟩ := x_facts hx
  have hs4 : 4 ≤ √(x : ℝ) := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hEL := ELu_eq (parity χ) hxR hl0.ne'
  have key := upper_alg (parity χ) hs4 hss (by linarith) hEL
    (log_norm_L1_le_sharp hGRH hprim hχ x (by omega)) (l1Sum1_le_sharp hB x hx100)
    (P2sum_le_sharp hB x hx100) hlq2
  have hu0 : 0 < 1 / Real.log x := by positivity
  have hu : 1 / Real.log x ≤ 0.205 := by rw [div_le_iff₀ hl0]; linarith
  have hy0 : 0 ≤ 1 / √(x : ℝ) := by positivity
  have hy : 1 / √(x : ℝ) ≤ 0.09 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hy' : 0.198 < 1 / Real.log x → 0.006 ≤ 1 / √(x : ℝ) := by
    intro h
    rcases lt_or_ge x 157 with h1 | h1
    · have : √(x : ℝ) ≤ 13 := by
        rw [show (13 : ℝ) = √(13 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by
          have : (x : ℝ) ≤ 157 := by exact_mod_cast h1.le
          linarith)
      rw [le_div_iff₀ (by linarith)]; linarith
    · exfalso
      have h5 := log_nat_ge h1 (k := 7469) (by decide +kernel) (by norm_num)
      norm_num at h5
      rw [lt_div_iff₀ hl0] at h
      linarith
  have hF := FUu_le_log (parity χ) (Erdos985.Analytic.BoundsAux.parity_le_one χ) hu0 hu hy0 hy hy'
  have hL0 : 0 < ‖DirichletCharacter.LFunction χ 1‖ :=
    norm_pos_iff.2 (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  have hV0 : 0 < 1 + Vf (1 / Real.log x) := by have := Vf_nonneg hu0.le; linarith
  have hm := llq_ge hxR hlq1
  calc ‖DirichletCharacter.LFunction χ 1‖
      = Real.exp (Real.log ‖DirichletCharacter.LFunction χ 1‖) := (Real.exp_log hL0).symm
    _ ≤ Real.exp (Real.log (Real.log x) + eulerMascheroniConstant
          + Real.log (1 + Vf (1 / Real.log x))) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp eulerMascheroniConstant * (Real.log x * (1 + Vf (1 / Real.log x))) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hl0, Real.exp_log hV0]; ring
    _ ≤ Real.exp eulerMascheroniConstant * (2 * (Real.log (Real.log q) - Real.log 2 + 1 / 2
          + 1 / Real.log (Real.log q))) :=
        mul_le_mul_of_nonneg_left (upper_num (by linarith) hm) (Real.exp_pos _).le
    _ = _ := by ring

/-- **LLS Theorem 1.5, lower bound, under GRH**: for `q ≥ 10¹⁰` and `χ` primitive mod `q`,
`1/|L(1, χ)| ≤ (12e^γ/π²)(log log q − log 2 + 1/2 + 1/log log q + 14 log log q/log q)`. -/
theorem l1LowerBound_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : LLS.L1LowerBound := by
  intro q _ hq χ hprim
  have hχ := LLS.chi_ne_one hq hprim
  obtain ⟨x, hx, hlq1, hlq2⟩ := setup hq
  have hB := LLS.psi1NatBound_of_GRH hGRH
  have hx100 : 100 ≤ x := by omega
  obtain ⟨hxR, hl, hs11, hss⟩ := x_facts hx
  have hs4 : 4 ≤ √(x : ℝ) := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hs0 : 0 < √(x : ℝ) := by linarith
  have hEU := EUu_eq (parity χ) hxR hl0.ne'
  have hLg := log_norm_L1_ge_sharp hGRH hprim hχ x (by omega)
  have hS1 := l1Sum1_le_sharp hB x hx100
  have hP2 := P2sum_le_sharp hB x hx100
  have hu0 : 0 < 1 / Real.log x := by positivity
  have hy0 : 0 < 1 / √(x : ℝ) := by positivity
  have hmain : -Real.log ‖DirichletCharacter.LFunction χ 1‖
      ≤ Real.log (Real.log x) + eulerMascheroniConstant - Real.log (π ^ 2 / 6)
        + Real.log (1 + Vf (1 / Real.log x) + Zz (1 / Real.log x) (1 / √(x : ℝ))) := by
    rcases le_or_gt x 22100 with hS | hA
    · have hSp : ∀ p ∈ ({2, 3, 5, 7, 11} : Finset ℕ), p.Prime ∧ p ^ 2 ≤ x := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by omega⟩
      have hW0 := re_Wsum_ge_finset χ x (by omega) _ hSp
      have hcard : ({2, 3, 5, 7, 11} : Finset ℕ).card = 5 := rfl
      rw [hcard] at hW0
      have k := lower_alg (parity χ) hs4 hss (by linarith) hEU hLg hW0 hS1 hP2 hlq2
      have hc := lower_core (parity χ) (Erdos985.Analytic.BoundsAux.parity_le_one χ) x hx hS
      have hz := zeta2_S5
      have he : 10 / 3 * ((5 : ℕ) : ℝ) / x = 50 / 3 * (1 / √(x : ℝ)) ^ 2 := by
        rw [div_pow, hss]; push_cast; ring
      linarith
    · have hW0 := re_Wsum_ge χ x (by omega)
      have hW1 : -(l1Sum1 x + P2sum x / Real.log x) + Real.log (π ^ 2 / 6)
          - (10 / 3 / √(x : ℝ) + 4 / 3 / (√(x : ℝ) - 1)) ≤ (Wsum χ x).re := by linarith
      have k := lower_alg (parity χ) hs4 hss (by linarith) hEU hLg hW1 hS1 hP2 hlq2
      have h10 := log_nat_ge hA.le (k := 14778) (by decide +kernel) (by norm_num)
      norm_num at h10
      have hu : 1 / Real.log x ≤ 0.1 := by rw [div_le_iff₀ hl0]; linarith
      have hs148 : 148.4 ≤ √(x : ℝ) := by
        rw [show (148.4 : ℝ) = √(148.4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by
          have : (22100 : ℝ) ≤ x := by exact_mod_cast hA.le
          norm_num; linarith)
      have hy : 1 / √(x : ℝ) ≤ 0.00674 := by rw [div_le_iff₀ hs0]; linarith
      have hc := HLu_le_log_asym (parity χ) (Erdos985.Analytic.BoundsAux.parity_le_one χ) hu0 hu hy0 hy
      have he : 10 / 3 / √(x : ℝ) + 4 / 3 / (√(x : ℝ) - 1)
          = 10 / 3 * (1 / √(x : ℝ)) + 4 / 3 * (1 / √(x : ℝ)) / (1 - 1 / √(x : ℝ)) := by
        have h1 : √(x : ℝ) - 1 ≠ 0 := by intro h; linarith
        have h2 : 1 - 1 / √(x : ℝ) ≠ 0 := by
          have : 1 / √(x : ℝ) ≤ 1 / 4 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs4
          intro h; linarith
        field_simp
      linarith
  have hL0 : 0 < ‖DirichletCharacter.LFunction χ 1‖ :=
    norm_pos_iff.2 (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  have hZ0 : 0 ≤ Zz (1 / Real.log x) (1 / √(x : ℝ)) := by
    unfold Zz; have := consts.2.2.2.2.1; positivity
  have hV0 : 0 < 1 + Vf (1 / Real.log x) + Zz (1 / Real.log x) (1 / √(x : ℝ)) := by
    have := Vf_nonneg hu0.le; linarith
  have hm := llq_ge hxR hlq1
  have hlq0 : 0 < Real.log q := by linarith
  have hpi : 0 < π ^ 2 / 6 := by positivity
  calc 1 / ‖DirichletCharacter.LFunction χ 1‖
      = Real.exp (-Real.log ‖DirichletCharacter.LFunction χ 1‖) := by
        rw [Real.exp_neg, Real.exp_log hL0, one_div]
    _ ≤ Real.exp (Real.log (Real.log x) + eulerMascheroniConstant - Real.log (π ^ 2 / 6)
        + Real.log (1 + Vf (1 / Real.log x) + Zz (1 / Real.log x) (1 / √(x : ℝ)))) :=
        Real.exp_le_exp.2 hmain
    _ = Real.exp eulerMascheroniConstant / (π ^ 2 / 6) * (Real.log x
          * (1 + Vf (1 / Real.log x) + Zz (1 / Real.log x) (1 / √(x : ℝ)))) := by
        rw [Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log hl0, Real.exp_log hpi,
          Real.exp_log hV0]
        ring
    _ ≤ Real.exp eulerMascheroniConstant / (π ^ 2 / 6) * (2 * (Real.log (Real.log q)
          - Real.log 2 + 1 / 2 + 1 / Real.log (Real.log q)
          + 14 * Real.log (Real.log q) / Real.log q)) :=
        mul_le_mul_of_nonneg_left (lower_num (by linarith) hm hs0 hlq0 hlq2) (by positivity)
    _ = _ := by field_simp; ring

end LLS.Sharp
