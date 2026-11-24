import LLS.Bach2.SoundBasic

/-!
# Soundness of the checker, part 2: interval bounds for the budget

The rational formulas of `LLSCheck` cast to the real formulas of `LLS.Numerics.Interval`
(`iK₁`, `iK₂`, `ik₁`, `ik₂`, `iEs`), and those bound `Kc`, `kap`, `Eshift`, `base2`, `Wp` and
`betP` under the side conditions `Side`. The arguments are those of `LLS.Phi_ge_PhiLo`.
-/

namespace LLS.Check

open Real Finset LLS

/-- The side conditions of a block, over `ℝ`. -/
structure Side (x : ℕ) (s₁ s₂ l₁ l₂ : ℝ) : Prop where
  hs₁ : s₁ ≤ √(x : ℝ)
  hs₂ : √(x : ℝ) ≤ s₂
  hl₁ : l₁ ≤ Real.log x
  hl₂ : Real.log x ≤ l₂
  hx64 : (64 : ℝ) ≤ x
  hs₁0 : 0 < s₁
  hden1 : 0 < 1 + 1 / (x : ℝ) - 2 / s₁
  hl₁0 : 0 ≤ l₁
  hEs : iEs x l₂ ≤ 0

section
variable {x : ℕ} {s₁ s₂ l₁ l₂ : ℝ}

theorem Side.core (h : Side x s₁ s₂ l₁ l₂) :
    iK₁ x s₁ s₂ l₁ ≤ Kc x ∧ Kc x ≤ iK₂ x s₁ s₂ l₂ ∧ ik₁ x s₁ s₂ l₁ ≤ kap x ∧
      kap x ≤ ik₂ x s₁ s₂ l₂ ∧ Eshift x ≤ iEs x l₂ ∧ 0 ≤ iK₁ x s₁ s₂ l₁ ∧
      0 ≤ ik₁ x s₁ s₂ l₁ := by
  obtain ⟨hs₁, hs₂, hl₁, hl₂, hx64, hs₁0, hden1, hl₁0, hEs⟩ := h
  set s := √(x : ℝ)
  set l := Real.log (x : ℝ)
  have hx0 : (0 : ℝ) < x := by linarith
  have h1x : 0 ≤ 1 - 1 / (x : ℝ) := by
    have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one hx0]; linarith
    linarith
  have hs0 : 0 < s := lt_of_lt_of_le hs₁0 hs₁
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
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hEsle : Eshift x ≤ iEs x l₂ := by
    unfold Eshift iEs
    have h2 : (Real.log x + 2) / x ≤ (l₂ + 2) / x := div_le_div_of_nonneg_right (by linarith) hx0.le
    nlinarith [mul_le_mul_of_nonneg_left hpi.le h1x, mul_le_mul_of_nonneg_left hγ.le h1x]
  exact ⟨hK1, hK2, hk1, hk2, hEsle, hK10, hk10⟩

/-- Lower bound for the main terms. -/
noncomputable def baseLoR (x s₁ s₂ l₁ l₂ Pc : ℝ) : ℝ :=
  x - 3 / 20 * s₂ - 3 * l₂ - 3 + 2 * iK₁ x s₁ s₂ l₁ * Pc - 2 * iK₁ x s₁ s₂ l₁ * iEs x l₂
    + 1 / 2 * 1.1364 * l₁ - (3.1416 ^ 2 / 6 - 0.57688 / 2 * l₁)

theorem Side.base (h : Side x s₁ s₂ l₁ l₂) {Pc : ℝ} (hPc : 0 ≤ Pc) :
    baseLoR x s₁ s₂ l₁ l₂ Pc ≤ base2 x Pc := by
  obtain ⟨hK1, -, -, -, hEsle, hK10, -⟩ := h.core
  have hEs := h.hEs
  have hl₁ := h.hl₁
  have hl₂ := h.hl₂
  have hs₂ := h.hs₂
  have hl₁0 := h.hl₁0
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have hK0 : 0 ≤ Kc x := hK10.trans hK1
  unfold baseLoR base2
  have t1 : 2 * iK₁ x s₁ s₂ l₁ * Pc ≤ 2 * Kc x * Pc := by nlinarith
  have t3 : 2 * Kc x * Eshift x ≤ 2 * iK₁ x s₁ s₂ l₁ * iEs x l₂ := by
    have a1 : Kc x * Eshift x ≤ Kc x * iEs x l₂ := mul_le_mul_of_nonneg_left hEsle hK0
    have a2 : Kc x * iEs x l₂ ≤ iK₁ x s₁ s₂ l₁ * iEs x l₂ := mul_le_mul_of_nonpos_right hK1 hEs
    linarith
  have t5 : 1 / 2 * 1.1364 * l₁ ≤ 1 / 2 * Real.log Real.pi * Real.log x := by nlinarith
  have t6 : Etil x ≤ 3.1416 ^ 2 / 6 - 0.57688 / 2 * l₁ := by
    unfold Etil
    have : Real.pi ^ 2 ≤ 3.1416 ^ 2 := by nlinarith
    nlinarith
  have t7 : -(3 / 20 * s₂) - 3 * l₂ ≤ -(3 / 20 * √(x : ℝ)) - 3 * Real.log x := by linarith
  linarith

/-- Upper bound for `A_p`. -/
noncomputable def AupR (x s₁ s₂ l₂ lo hi p : ℝ) : ℝ :=
  (l₂ - lo / 2) ^ 2 / 2 + 2 * iK₂ x s₁ s₂ l₂ * (hi / (p - 1))

/-- Upper bound for `W_p`. -/
noncomputable def WupR (x s₁ s₂ l₁ l₂ lo hi p : ℝ) : ℝ :=
  AupR x s₁ s₂ l₂ lo hi p + max 0 (AupR x s₁ s₂ l₂ lo hi p - ik₁ x s₁ s₂ l₁ * lo)

theorem Side.Wp_le (h : Side x s₁ s₂ l₁ l₂) (p : ℕ) (hp2 : 2 ≤ p) {lo hi : ℝ}
    (hlo : lo ≤ Real.log p) (hhi : Real.log p ≤ hi) (hlo0 : 0 ≤ lo) (hhi2 : hi / 2 ≤ l₁) :
    Wp x p ≤ WupR x s₁ s₂ l₁ l₂ lo hi p := by
  obtain ⟨-, hK2, hk1, -, -, hK10, hk10⟩ := h.core
  have hl₁ := h.hl₁
  have hl₂ := h.hl₂
  have hkap0 : 0 ≤ kap x := hk10.trans hk1
  have hp1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hA : Ap x p ≤ AupR x s₁ s₂ l₂ lo hi p := by
    unfold Ap AupR
    have e1 : (Real.log x - Real.log p / 2) ^ 2 ≤ (l₂ - lo / 2) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    have e2 : Real.log p / ((p : ℝ) - 1) ≤ hi / ((p : ℝ) - 1) :=
      div_le_div_of_nonneg_right hhi (by linarith)
    have e3 : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
    have hK0 : 0 ≤ Kc x := (Kc_pos h.hx64).le
    have := mul_le_mul e2 hK2 hK0 (le_trans e3 e2)
    nlinarith
  unfold Wp WupR
  have : ik₁ x s₁ s₂ l₁ * lo ≤ kap x * Real.log p := mul_le_mul hk1 hlo hlo0 hkap0
  have hm : max 0 (Ap x p - kap x * Real.log p)
      ≤ max 0 (AupR x s₁ s₂ l₂ lo hi p - ik₁ x s₁ s₂ l₁ * lo) :=
    max_le_max le_rfl (by linarith)
  linarith

/-- Bounds for `β(x, P₀)`. -/
noncomputable def betLoR (x s₁ s₂ l₁ hP P0 : ℝ) : ℝ :=
  l₁ ^ 2 / (2 * hP) + 2 * iK₁ x s₁ s₂ l₁ / (P0 - 1)
noncomputable def betHiR (x s₁ s₂ l₂ lP P0 : ℝ) : ℝ :=
  l₂ ^ 2 / (2 * lP) + 2 * iK₂ x s₁ s₂ l₂ / (P0 - 1)

theorem Side.bet (h : Side x s₁ s₂ l₁ l₂) (P0 : ℕ) (hP0 : 2 ≤ P0) {lP hP : ℝ}
    (hlP : lP ≤ Real.log P0) (hhP : Real.log P0 ≤ hP) (hlP0 : 0 < lP) :
    0 ≤ betLoR x s₁ s₂ l₁ hP P0 ∧ betLoR x s₁ s₂ l₁ hP P0 ≤ betP x P0 ∧
      betP x P0 ≤ betHiR x s₁ s₂ l₂ lP P0 := by
  obtain ⟨hK1, hK2, -, -, -, hK10, -⟩ := h.core
  have hl₁ := h.hl₁
  have hl₂ := h.hl₂
  have hl₁0 := h.hl₁0
  have hP1 : (0 : ℝ) < (P0 : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P0 := by exact_mod_cast hP0
    linarith
  have hhP0 : 0 < hP := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold betLoR
    have : 0 ≤ 2 * iK₁ x s₁ s₂ l₁ / ((P0 : ℝ) - 1) := div_nonneg (by linarith) hP1.le
    have : 0 ≤ l₁ ^ 2 / (2 * hP) := by positivity
    linarith
  · unfold betLoR betP
    have e1 : l₁ ^ 2 / (2 * hP) ≤ Real.log x ^ 2 / (2 * Real.log P0) :=
      div_le_div₀ (by positivity) (by nlinarith) (by linarith) (by linarith)
    have e2 : 2 * iK₁ x s₁ s₂ l₁ / ((P0 : ℝ) - 1) ≤ 2 * Kc x / ((P0 : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by linarith) hP1.le
    linarith
  · unfold betHiR betP
    have e1 : Real.log x ^ 2 / (2 * Real.log P0) ≤ l₂ ^ 2 / (2 * lP) :=
      div_le_div₀ (by positivity) (by nlinarith) (by positivity) (by linarith)
    have e2 : 2 * Kc x / ((P0 : ℝ) - 1) ≤ 2 * iK₂ x s₁ s₂ l₂ / ((P0 : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by linarith) hP1.le
    linarith

end

/-! ### Casts from the rational formulas -/

section
variable (x : ℕ) (s1 s2 l1 l2 : ℚ)

lemma cast_K1 : ((K1 (x : ℚ) s1 s2 l1 : ℚ) : ℝ) = iK₁ x s1 s2 l1 := by
  simp only [K1, iK₁]; push_cast; ring
lemma cast_K2 : ((K2 (x : ℚ) s1 s2 l2 : ℚ) : ℝ) = iK₂ x s1 s2 l2 := by
  simp only [K2, iK₂]; push_cast; ring
lemma cast_k1 : ((k1 (x : ℚ) s1 s2 l1 : ℚ) : ℝ) = ik₁ x s1 s2 l1 := by
  simp only [k1, ik₁]; push_cast; rw [cast_K1]
lemma cast_k2 : ((k2 (x : ℚ) s1 s2 l2 : ℚ) : ℝ) = ik₂ x s1 s2 l2 := by
  simp only [k2, ik₂]; push_cast; rw [cast_K2]
lemma cast_Es : ((Es (x : ℚ) l2 : ℚ) : ℝ) = iEs x l2 := by
  simp only [Es, iEs]; push_cast; ring
lemma cast_baseLo (Pc : ℚ) :
    ((baseLo (x : ℚ) s1 s2 l1 l2 Pc : ℚ) : ℝ) = baseLoR x s1 s2 l1 l2 Pc := by
  simp only [baseLo, baseLoR]; push_cast; rw [cast_K1, cast_Es]; ring
lemma cast_pos (t : ℚ) : ((pos t : ℚ) : ℝ) = max 0 (t : ℝ) := by
  unfold pos
  split_ifs with h
  · rw [max_eq_right (by exact_mod_cast h)]
  · push Not at h
    push_cast; rw [max_eq_left (by exact_mod_cast h.le)]
lemma cast_Aup (lo hi p : ℚ) :
    ((Aup (x : ℚ) s1 s2 l2 lo hi p : ℚ) : ℝ) = AupR x s1 s2 l2 lo hi p := by
  simp only [Aup, AupR]; push_cast; rw [cast_K2]
lemma cast_Wup (lo hi p : ℚ) :
    ((Wup (x : ℚ) s1 s2 l1 l2 lo hi p : ℚ) : ℝ) = WupR x s1 s2 l1 l2 lo hi p := by
  simp only [Wup, WupR]; push_cast; rw [cast_pos]; push_cast; simp only [cast_Aup, cast_k1]
lemma cast_betLo (hP P0 : ℚ) :
    ((betLo (x : ℚ) s1 s2 l1 hP P0 : ℚ) : ℝ) = betLoR x s1 s2 l1 hP P0 := by
  simp only [betLo, betLoR]; push_cast; rw [cast_K1]
lemma cast_betHi (lP P0 : ℚ) :
    ((betHi (x : ℚ) s1 s2 l2 lP P0 : ℚ) : ℝ) = betHiR x s1 s2 l2 lP P0 := by
  simp only [betHi, betHiR]; push_cast; rw [cast_K2]

end

end LLS.Check
