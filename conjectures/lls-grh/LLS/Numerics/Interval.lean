import LLS.Numerics.Budget

/-!
# Interval evaluation of the budget `Φ`

`PhiLo` is `Φ(x, L)` with every transcendental quantity replaced by a rational bound in the
direction that makes it smaller: `s₁ ≤ √x ≤ s₂`, `l₁ ≤ log x ≤ l₂`, `L ≤ L₂`, the bounds
`log π > 1.1364`, `γ > 0.57688`, `π < 3.1416`, and bounds `[a_p, b_p]` for `log p`,
`p ∈ {2, 3, 5, 7, 11, 13, 17}`. `Phi_ge_PhiLo` proves `PhiLo ≤ Φ` under sign side-conditions
that are checked numerically together with `PhiLo > 0`.
-/

namespace LLS

open Real Finset

/-- Rational lower and upper bounds for `log p`, `p ∈ {2, 3, 5, 7, 11, 13, 17}`. -/
structure LogBounds where
  lo : ℕ → ℝ
  hi : ℕ → ℝ

/-- `log 2^k ≤ m log a` turns into a lower bound for `log a`. -/
lemma log_ge_of_pow (a k m : ℕ) (hm : 0 < m) (h : 2 ^ k ≤ a ^ m) :
    (k : ℝ) / m * 0.6931471803 ≤ Real.log a := by
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [zero_pow hm.ne'] at h
    · exact ha
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((a : ℝ) ^ m) :=
    Real.log_le_log (by positivity) (by exact_mod_cast h)
  rw [Real.log_pow, Real.log_pow] at h1
  have h2 := Real.log_two_gt_d9
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_mul_eq_mul_div, div_le_iff₀ hmR]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma log_le_of_pow (a k m : ℕ) (hm : 0 < m) (ha : 0 < a) (h : a ^ m ≤ 2 ^ k) :
    Real.log a ≤ (k : ℝ) / m * 0.6931471808 := by
  have h1 : Real.log ((a : ℝ) ^ m) ≤ Real.log ((2 : ℝ) ^ k) :=
    Real.log_le_log (by positivity) (by exact_mod_cast h)
  rw [Real.log_pow, Real.log_pow] at h1
  have h2 := Real.log_two_lt_d9
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_mul_eq_mul_div, le_div_iff₀ hmR]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- Fixed bounds for the logarithms of the small primes (`2^k ≤ p^64 ≤ 2^{k+1}`). -/
noncomputable def lpLo : ℕ → ℝ
  | 2 => 64 / 64 * 0.6931471803
  | 3 => 101 / 64 * 0.6931471803
  | 5 => 148 / 64 * 0.6931471803
  | 7 => 179 / 64 * 0.6931471803
  | 11 => 221 / 64 * 0.6931471803
  | 13 => 236 / 64 * 0.6931471803
  | 17 => 261 / 64 * 0.6931471803
  | _ => 0

noncomputable def lpHi : ℕ → ℝ
  | 2 => 64 / 64 * 0.6931471808
  | 3 => 102 / 64 * 0.6931471808
  | 5 => 149 / 64 * 0.6931471808
  | 7 => 180 / 64 * 0.6931471808
  | 11 => 222 / 64 * 0.6931471808
  | 13 => 237 / 64 * 0.6931471808
  | 17 => 262 / 64 * 0.6931471808
  | _ => 0

lemma lpLo_le (p : ℕ) (hp : p ∈ insert 17 smallP) : lpLo p ≤ Real.log p := by
  simp only [smallP, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact log_ge_of_pow 17 261 64 (by norm_num) (by decide)
  · exact log_ge_of_pow 2 64 64 (by norm_num) (by decide)
  · exact log_ge_of_pow 3 101 64 (by norm_num) (by decide)
  · exact log_ge_of_pow 5 148 64 (by norm_num) (by decide)
  · exact log_ge_of_pow 7 179 64 (by norm_num) (by decide)
  · exact log_ge_of_pow 11 221 64 (by norm_num) (by decide)
  · exact log_ge_of_pow 13 236 64 (by norm_num) (by decide)

lemma le_lpHi (p : ℕ) (hp : p ∈ insert 17 smallP) : Real.log p ≤ lpHi p := by
  simp only [smallP, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact log_le_of_pow 17 262 64 (by norm_num) (by norm_num) (by decide)
  · exact log_le_of_pow 2 64 64 (by norm_num) (by norm_num) (by decide)
  · exact log_le_of_pow 3 102 64 (by norm_num) (by norm_num) (by decide)
  · exact log_le_of_pow 5 149 64 (by norm_num) (by norm_num) (by decide)
  · exact log_le_of_pow 7 180 64 (by norm_num) (by norm_num) (by decide)
  · exact log_le_of_pow 11 222 64 (by norm_num) (by norm_num) (by decide)
  · exact log_le_of_pow 13 237 64 (by norm_num) (by norm_num) (by decide)

/-! ### The lower bound -/

section
variable (x s₁ s₂ l₁ l₂ L₂ : ℝ)

noncomputable def iK₁ : ℝ := (s₁ + 1 + l₁ / 2) / (1 + 1 / x - 2 / s₂)
noncomputable def iK₂ : ℝ := (s₂ + 1 + l₂ / 2) / (1 + 1 / x - 2 / s₁)
noncomputable def ik₁ : ℝ := iK₁ x s₁ s₂ l₁ * (1 - 1 / x) + l₁ / 2
noncomputable def ik₂ : ℝ := iK₂ x s₁ s₂ l₂ * (1 - 1 / x) + l₂ / 2
noncomputable def iEs : ℝ :=
  -(1 / 2) * (1 - 1 / x) * 1.1364 - 0.57688 / 2 * (1 - 1 / x) + (l₂ + 2) / x
noncomputable def iβ₁ : ℝ := l₁ ^ 2 / (2 * lpHi 17) + 2 * iK₁ x s₁ s₂ l₁ / 16
noncomputable def iβ₂ : ℝ := l₂ ^ 2 / (2 * lpLo 17) + 2 * iK₂ x s₁ s₂ l₂ / 16
noncomputable def iA (p : ℕ) : ℝ :=
  (l₂ - lpLo p / 2) ^ 2 / 2 + 2 * iK₂ x s₁ s₂ l₂ * (lpHi p / ((p : ℝ) - 1))
noncomputable def iW (p : ℕ) : ℝ :=
  iA x s₁ s₂ l₂ p + max 0 (iA x s₁ s₂ l₂ p - ik₁ x s₁ s₂ l₁ * lpLo p)

/-- `Φ` with all transcendental inputs replaced by bounds. -/
noncomputable def PhiLo : ℝ :=
  x - 3 / 20 * s₂ - 3 * l₂ - 3 + 2 * iK₁ x s₁ s₂ l₁ * (l₁ - 2) - ik₂ x s₁ s₂ l₂ * L₂
    - 2 * iK₁ x s₁ s₂ l₁ * iEs x l₂ + 1 / 2 * 1.1364 * l₁ - (3.1416 ^ 2 / 6 - 0.57688 / 2 * l₁)
    - iβ₂ x s₁ s₂ l₂ * L₂
    - ∑ p ∈ smallP, max 0 (iW x s₁ s₂ l₁ l₂ p - iβ₁ x s₁ s₂ l₁ * lpLo p)

/-- The side conditions, checked numerically. -/
def SideOK : Prop :=
  64 ≤ x ∧ 0 < s₁ ∧ 0 < 1 + 1 / x - 2 / s₁ ∧ 2 ≤ l₁ ∧ 0 ≤ L₂ ∧ iEs x l₂ ≤ 0 ∧
    iβ₂ x s₁ s₂ l₂ ≤ ik₁ x s₁ s₂ l₁ ∧ (∀ p ∈ smallP, lpHi p / 2 ≤ l₁)

end

set_option maxHeartbeats 2000000 in
theorem Phi_ge_PhiLo (x : ℕ) (L s₁ s₂ l₁ l₂ L₂ : ℝ) (hs₁ : s₁ ≤ √(x : ℝ)) (hs₂ : √(x : ℝ) ≤ s₂)
    (hl₁ : l₁ ≤ Real.log x) (hl₂ : Real.log x ≤ l₂) (hL0 : 0 ≤ L) (hL : L ≤ L₂)
    (hside : SideOK x s₁ s₂ l₁ l₂ L₂) :
    PhiLo x s₁ s₂ l₁ l₂ L₂ ≤ Phi x L ∧ bet x ≤ kap x := by
  obtain ⟨hx64, hs₁0, hden1, hl₁2, hL₂0, hEs, hβκ, hlp⟩ := hside
  set s := √(x : ℝ)
  set l := Real.log (x : ℝ)
  have hx0 : (0 : ℝ) < x := by linarith
  have h1x : 0 ≤ 1 - 1 / (x : ℝ) := by
    have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one hx0]; linarith
    linarith
  have hs0 : 0 < s := lt_of_lt_of_le hs₁0 hs₁
  -- denominators
  set den := 1 + 1 / (x : ℝ) - 2 / s
  have hd1 : 1 + 1 / (x : ℝ) - 2 / s₁ ≤ den := by
    have : 2 / s ≤ 2 / s₁ := div_le_div_of_nonneg_left (by norm_num) hs₁0 hs₁
    simp only [den]; linarith
  have hd2 : den ≤ 1 + 1 / (x : ℝ) - 2 / s₂ := by
    have : 2 / s₂ ≤ 2 / s := div_le_div_of_nonneg_left (by norm_num) hs0 hs₂
    simp only [den]; linarith
  have hden : 0 < den := lt_of_lt_of_le hden1 hd1
  have hKe : Kc x = (s + 1 + l / 2) / den := rfl
  have hK1 : iK₁ x s₁ s₂ l₁ ≤ Kc x := by
    rw [hKe, iK₁]
    exact div_le_div₀ (by linarith) (by linarith) hden hd2
  have hK2 : Kc x ≤ iK₂ x s₁ s₂ l₂ := by
    rw [hKe, iK₂]
    exact div_le_div₀ (by linarith [Real.sqrt_nonneg (x : ℝ)]) (by linarith) hden1 hd1
  have hK10 : 0 ≤ iK₁ x s₁ s₂ l₁ := by
    unfold iK₁
    exact div_nonneg (by linarith) (by linarith)
  have hk1 : ik₁ x s₁ s₂ l₁ ≤ kap x := by
    unfold ik₁ kap
    nlinarith [mul_le_mul_of_nonneg_right hK1 h1x]
  have hk2 : kap x ≤ ik₂ x s₁ s₂ l₂ := by
    unfold ik₂ kap
    nlinarith [mul_le_mul_of_nonneg_right hK2 h1x]
  have hk10 : 0 ≤ ik₁ x s₁ s₂ l₁ := by unfold ik₁; nlinarith
  have hkap0 : 0 ≤ kap x := le_trans hk10 hk1
  -- constants
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have hl17lo := lpLo_le 17 (by simp)
  have hl17hi := le_lpHi 17 (by simp)
  have hl17 : 0 < lpLo 17 := by norm_num [lpLo]
  have hl17lo' : lpLo 17 ≤ Real.log 17 := by have := hl17lo; push_cast at this; exact this
  have hl17hi' : Real.log 17 ≤ lpHi 17 := by have := hl17hi; push_cast at this; exact this
  have hEsle : Eshift x ≤ iEs x l₂ := by
    unfold Eshift iEs
    have h2 : (Real.log x + 2) / x ≤ (l₂ + 2) / x := div_le_div_of_nonneg_right (by linarith) hx0.le
    nlinarith [mul_le_mul_of_nonneg_left hpi.le h1x, mul_le_mul_of_nonneg_left hγ.le h1x]
  -- β
  have hβ1 : iβ₁ x s₁ s₂ l₁ ≤ bet x := by
    unfold iβ₁ bet
    have e1 : l₁ ^ 2 / (2 * lpHi 17) ≤ l ^ 2 / (2 * Real.log 17) := by
      apply div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by linarith [hl17hi'])
    have e2 : 2 * iK₁ x s₁ s₂ l₁ / 16 ≤ 2 * Kc x / 16 := by linarith
    linarith
  have hβ2 : bet x ≤ iβ₂ x s₁ s₂ l₂ := by
    unfold iβ₂ bet
    have e1 : l ^ 2 / (2 * Real.log 17) ≤ l₂ ^ 2 / (2 * lpLo 17) := by
      apply div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by linarith [hl17lo'])
    have e2 : 2 * Kc x / 16 ≤ 2 * iK₂ x s₁ s₂ l₂ / 16 := by linarith
    linarith
  have hβ10 : 0 ≤ iβ₁ x s₁ s₂ l₁ := by
    unfold iβ₁; have : 0 < lpHi 17 := by norm_num [lpHi]
    positivity
  refine ⟨?_, hβ2.trans (hβκ.trans hk1)⟩
  -- the small primes
  have hsmall : ∀ p ∈ smallP, max 0 (Wp x p - bet x * Real.log p)
      ≤ max 0 (iW x s₁ s₂ l₁ l₂ p - iβ₁ x s₁ s₂ l₁ * lpLo p) := by
    intro p hp
    have hpi' : p ∈ insert 17 smallP := mem_insert_of_mem hp
    have hlo := lpLo_le p hpi'
    have hhi := le_lpHi p hpi'
    have hlo0 : 0 ≤ lpLo p := by
      simp only [smallP, mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [lpLo]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      simp only [smallP, mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hlpb := hlp p hp
    have hA : Ap x p ≤ iA x s₁ s₂ l₂ p := by
      unfold Ap iA
      have e1 : (Real.log x - Real.log p / 2) ^ 2 ≤ (l₂ - lpLo p / 2) ^ 2 := by
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      have e2 : Real.log p / ((p : ℝ) - 1) ≤ lpHi p / ((p : ℝ) - 1) :=
        div_le_div_of_nonneg_right hhi (by linarith)
      have e3 : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
      have hK0 : 0 ≤ Kc x := (Kc_pos (by exact_mod_cast hx64)).le
      have := mul_le_mul e2 hK2 hK0 (le_trans e3 e2)
      nlinarith
    have hW : Wp x p ≤ iW x s₁ s₂ l₁ l₂ p := by
      unfold Wp iW
      have : ik₁ x s₁ s₂ l₁ * lpLo p ≤ kap x * Real.log p :=
        mul_le_mul hk1 hlo hlo0 hkap0
      have hm : max 0 (Ap x p - kap x * Real.log p)
          ≤ max 0 (iA x s₁ s₂ l₂ p - ik₁ x s₁ s₂ l₁ * lpLo p) :=
        max_le_max le_rfl (by linarith)
      linarith
    have : iβ₁ x s₁ s₂ l₁ * lpLo p ≤ bet x * Real.log p := mul_le_mul hβ1 hlo hlo0 (by linarith)
    exact max_le_max le_rfl (by linarith)
  have hsum := sum_le_sum hsmall
  -- the rest
  unfold Phi PhiLo
  have t1 : 2 * iK₁ x s₁ s₂ l₁ * (l₁ - 2) ≤ 2 * Kc x * (l - 2) := by
    have := mul_le_mul hK1 (by linarith : l₁ - 2 ≤ l - 2) (by linarith) (by linarith)
    linarith
  have t2 : kap x * L ≤ ik₂ x s₁ s₂ l₂ * L₂ := mul_le_mul hk2 hL hL0 (by linarith)
  have t3 : 2 * Kc x * Eshift x ≤ 2 * iK₁ x s₁ s₂ l₁ * iEs x l₂ := by
    have a1 : Kc x * Eshift x ≤ Kc x * iEs x l₂ :=
      mul_le_mul_of_nonneg_left hEsle (by linarith)
    have a2 : Kc x * iEs x l₂ ≤ iK₁ x s₁ s₂ l₁ * iEs x l₂ :=
      mul_le_mul_of_nonpos_right hK1 hEs
    linarith
  have t4 : bet x * L ≤ iβ₂ x s₁ s₂ l₂ * L₂ :=
    mul_le_mul hβ2 hL hL0 (by linarith [bet_nonneg (by exact_mod_cast hx64 : (64 : ℝ) ≤ x)])
  have t5 : 1 / 2 * 1.1364 * l₁ ≤ 1 / 2 * Real.log Real.pi * l := by nlinarith
  have t6 : Etil x ≤ 3.1416 ^ 2 / 6 - 0.57688 / 2 * l₁ := by
    unfold Etil
    have : Real.pi ^ 2 ≤ 3.1416 ^ 2 := by nlinarith
    nlinarith
  have t7 : -(3 / 20 * s₂) - 3 * l₂ ≤ -(3 / 20 * s) - 3 * l := by linarith
  linarith

end LLS
