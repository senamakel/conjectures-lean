import LLS.Numerics.Good

/-!
# The budget for a prime modulus `q > x`

When `q` is prime and `q > x`, no prime power `≤ x` divides `q`, so all losses vanish and the
key inequality gives `Φ₁(x, log q) ≤ 0` for the loss-free budget `Φ₁` below
(`Φ = Φ₁ − β L − Σ_{p<17} …`). This is what makes the constant `1` of LLS Corollary 1.2
reachable for the least quadratic non-residue.
-/

namespace LLS

open Real Finset

/-- The loss-free budget. -/
noncomputable def Phi1 (x L : ℝ) : ℝ :=
  x - 3 / 20 * √x - 3 * Real.log x - 3 + 2 * Kc x * (Real.log x - 2) - kap x * L
    - 2 * Kc x * Eshift x + 1 / 2 * Real.log Real.pi * Real.log x - Etil x

theorem Phi1_nonpos (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (hqp : q.Prime) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hxq : x < q) (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) :
    Phi1 x (Real.log q) ≤ 0 := by
  classical
  obtain ⟨lf, Z, hlf, hZ0, R, hRq, hlog, h1, h2⟩ := key hGRH χ hχ x hx hval
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hpf : q.primeFactors = {q} := Nat.Prime.primeFactors hqp
  have hzero : ∀ p ∈ q.primeFactors, llp x p = 0 ∧ lcp x p = 0 := by
    intro p hp
    rw [hpf, mem_singleton] at hp
    subst hp
    exact ⟨llp_eq_zero hqp hxq, lcp_eq_zero hqp hxq⟩
  have hS0 : ∀ S ⊆ q.primeFactors, ∑ p ∈ S, llp x p = 0 ∧ ∑ p ∈ S, lcp x p = 0 :=
    fun S hS => ⟨sum_eq_zero fun p hp => (hzero p (hS hp)).1,
      sum_eq_zero fun p hp => (hzero p (hS hp)).2⟩
  obtain ⟨a1, a2⟩ := hS0 _ subset_rfl
  obtain ⟨b1, b2⟩ := hS0 R hRq
  rw [a1, b1] at h2
  rw [a2, b2] at h1
  have hRlog : 0 ≤ ∑ p ∈ R, Real.log p := sum_nonneg fun p hp => by
    have := Nat.prime_of_mem_primeFactors (hRq hp)
    exact Real.log_nonneg (by exact_mod_cast this.one_lt.le)
  have hlfL : lf ≤ Real.log q := by linarith
  set s := √(x : ℝ)
  set l := Real.log x
  set den := 1 + 1 / (x : ℝ) - 2 / s
  have hden : 3 / 4 ≤ den := den_pos hxR
  set K := Kc x
  have hKdef : K * den = s + 1 + l / 2 := by
    show Kc x * den = _
    unfold Kc
    exact div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hK0 : 0 < K := Kc_pos hxR
  have hN : (s + 1 + l / 2) * Z ≤ K * (lf * (1 - 1 / x) - 2 * (l - 2 - 0 - 0) + 2 * Eshift x) := by
    rw [← hKdef]
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    nlinarith
  have hS : (x : ℝ) - 3 / 20 * s - 3 * l - 3 - 0 - 0
      ≤ K * (lf * (1 - 1 / x) - 2 * (l - 2 - 0 - 0) + 2 * Eshift x) + lf / 2 * l
        - 1 / 2 * Real.log Real.pi * l + Etil x := by
    have : (√(x : ℝ) + 1) * Z + (lf + Z) / 2 * l = (s + 1 + l / 2) * Z + lf / 2 * l := by ring
    linarith
  have hkap0 : 0 ≤ kap x := by
    have h1x : 0 ≤ 1 - 1 / (x : ℝ) := by
      have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    unfold kap; positivity
  have hlf' : K * (lf * (1 - 1 / x)) + lf / 2 * l ≤ kap x * Real.log q := by
    have : K * (lf * (1 - 1 / x)) + lf / 2 * l = kap x * lf := by simp only [kap, K, l]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hlfL hkap0
  unfold Phi1
  change (x : ℝ) - 3 / 20 * s - 3 * l - 3 + 2 * K * (l - 2) - kap x * Real.log q
    - 2 * K * Eshift x + 1 / 2 * Real.log Real.pi * l - Etil x ≤ 0
  have hexp : K * (lf * (1 - 1 / x) - 2 * (l - 2 - 0 - 0) + 2 * Eshift x)
      = K * (lf * (1 - 1 / x)) - 2 * K * (l - 2) + 2 * K * Eshift x := by ring
  linarith

/-- `Φ₁` with bounds substituted (the first part of `PhiLo`). -/
noncomputable def Phi1Lo (x s₁ s₂ l₁ l₂ L₂ : ℝ) : ℝ :=
  x - 3 / 20 * s₂ - 3 * l₂ - 3 + 2 * iK₁ x s₁ s₂ l₁ * (l₁ - 2) - ik₂ x s₁ s₂ l₂ * L₂
    - 2 * iK₁ x s₁ s₂ l₁ * iEs x l₂ + 1 / 2 * 1.1364 * l₁ - (3.1416 ^ 2 / 6 - 0.57688 / 2 * l₁)

/-- The side conditions for `Φ₁`. -/
def Side1OK (x s₁ l₁ l₂ L₂ : ℝ) : Prop :=
  64 ≤ x ∧ 0 < s₁ ∧ 0 < 1 + 1 / x - 2 / s₁ ∧ 2 ≤ l₁ ∧ 0 ≤ L₂ ∧ iEs x l₂ ≤ 0

theorem Phi1_ge (x : ℕ) (L s₁ s₂ l₁ l₂ L₂ : ℝ) (hs₁ : s₁ ≤ √(x : ℝ)) (hs₂ : √(x : ℝ) ≤ s₂)
    (hl₁ : l₁ ≤ Real.log x) (hl₂ : Real.log x ≤ l₂) (hL0 : 0 ≤ L) (hL : L ≤ L₂)
    (hside : Side1OK x s₁ l₁ l₂ L₂) :
    Phi1Lo x s₁ s₂ l₁ l₂ L₂ ≤ Phi1 x L := by
  obtain ⟨hx64, hs₁0, hden1, hl₁2, hL₂0, hEs⟩ := hside
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
  have hk2 : kap x ≤ ik₂ x s₁ s₂ l₂ := by
    unfold ik₂ kap
    nlinarith [mul_le_mul_of_nonneg_right hK2 h1x]
  have hkap0 : 0 ≤ kap x := by
    have := (Kc_pos (by exact_mod_cast hx64 : (64 : ℝ) ≤ x)).le
    unfold kap; nlinarith
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have hEsle : Eshift x ≤ iEs x l₂ := by
    unfold Eshift iEs
    have h2 : (Real.log x + 2) / x ≤ (l₂ + 2) / x := div_le_div_of_nonneg_right (by linarith) hx0.le
    nlinarith [mul_le_mul_of_nonneg_left hpi.le h1x, mul_le_mul_of_nonneg_left hγ.le h1x]
  have hKc0 : 0 ≤ Kc x := (Kc_pos (by exact_mod_cast hx64 : (64 : ℝ) ≤ x)).le
  unfold Phi1 Phi1Lo
  have t1 : 2 * iK₁ x s₁ s₂ l₁ * (l₁ - 2) ≤ 2 * Kc x * (l - 2) := by
    have := mul_le_mul hK1 (by linarith : l₁ - 2 ≤ l - 2) (by linarith) (by linarith)
    linarith
  have t2 : kap x * L ≤ ik₂ x s₁ s₂ l₂ * L₂ := mul_le_mul hk2 hL hL0 (by linarith)
  have t3 : 2 * Kc x * Eshift x ≤ 2 * iK₁ x s₁ s₂ l₁ * iEs x l₂ := by
    have a2 : Kc x * iEs x l₂ ≤ iK₁ x s₁ s₂ l₁ * iEs x l₂ :=
      mul_le_mul_of_nonpos_right hK1 hEs
    have : 0 ≤ Kc x := (Kc_pos (by exact_mod_cast hx64 : (64 : ℝ) ≤ x)).le
    have a1' : Kc x * Eshift x ≤ Kc x * iEs x l₂ := mul_le_mul_of_nonneg_left hEsle this
    linarith
  have t5 : 1 / 2 * 1.1364 * l₁ ≤ 1 / 2 * Real.log Real.pi * l := by nlinarith
  have t6 : Etil x ≤ 3.1416 ^ 2 / 6 - 0.57688 / 2 * l₁ := by
    unfold Etil
    have : Real.pi ^ 2 ≤ 3.1416 ^ 2 := by nlinarith
    nlinarith
  have t7 : -(3 / 20 * s₂) - 3 * l₂ ≤ -(3 / 20 * s) - 3 * l := by linarith
  linarith

/-- A prime modulus for which the loss-free argument works with constant `c`. -/
def GoodP (c : ℝ) (q : ℕ) : Prop :=
  ∃ x : ℕ, 64 ≤ x ∧ (x : ℝ) ≤ c * Real.log q ^ 2 ∧ 0 < Phi1 x (Real.log q)

theorem goodP_of_data {c : ℝ} (q Qa Qb ka kb x : ℕ) (s₁ s₂ : ℝ) (k₁ k₂ : ℕ)
    (h1 : Qa ≤ q) (h2 : q < Qb)
    (hka : 2 ^ ka ≤ Qa ^ 64) (hkb : Qb ^ 64 ≤ 2 ^ kb) (hk₁ : 2 ^ k₁ ≤ x ^ 64) (hk₂ : x ^ 64 ≤ 2 ^ k₂)
    (hs₁0 : 0 ≤ s₁) (hs₁ : s₁ ^ 2 ≤ x) (hs₂0 : 0 ≤ s₂) (hs₂ : (x : ℝ) ≤ s₂ ^ 2)
    (hx : (x : ℝ) ≤ c * ((ka : ℝ) / 64 * 0.6931471803) ^ 2)
    (hside : Side1OK x s₁ ((k₁ : ℝ) / 64 * 0.6931471803) ((k₂ : ℝ) / 64 * 0.6931471808)
      ((kb : ℝ) / 64 * 0.6931471808))
    (hpos : 0 < Phi1Lo x s₁ s₂ ((k₁ : ℝ) / 64 * 0.6931471803) ((k₂ : ℝ) / 64 * 0.6931471808)
      ((kb : ℝ) / 64 * 0.6931471808)) :
    GoodP c q := by
  have hx64 : (64 : ℝ) ≤ x := hside.1
  have hxpos : 0 < x := by exact_mod_cast (show (0 : ℝ) < x by linarith)
  have hQa : 0 < Qa := by
    rcases Nat.eq_zero_or_pos Qa with h | h
    · subst h; simp at hka
    · exact h
  have hq0 : 0 < q := lt_of_lt_of_le hQa h1
  have hLa : (ka : ℝ) / 64 * 0.6931471803 ≤ Real.log q :=
    (log_ge_of_pow Qa ka 64 (by norm_num) hka).trans
      (Real.log_le_log (by exact_mod_cast hQa) (by exact_mod_cast h1))
  have hLb : Real.log q ≤ (kb : ℝ) / 64 * 0.6931471808 :=
    (Real.log_le_log (by exact_mod_cast hq0) (by exact_mod_cast h2.le)).trans
      (log_le_of_pow Qb kb 64 (by norm_num) (by omega) hkb)
  have hs₁' : s₁ ≤ √(x : ℝ) := Real.le_sqrt_of_sq_le hs₁
  have hs₂' : √(x : ℝ) ≤ s₂ := by
    rw [show s₂ = √(s₂ ^ 2) from (Real.sqrt_sq hs₂0).symm]
    exact Real.sqrt_le_sqrt hs₂
  have hl₁ := log_ge_of_pow x k₁ 64 (by norm_num) hk₁
  have hl₂ := log_le_of_pow x k₂ 64 (by norm_num) hxpos hk₂
  have hL0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq0)
  have hP := Phi1_ge x (Real.log q) s₁ s₂ _ _ _ hs₁' hs₂' hl₁ hl₂ hL0 hLb hside
  have hka0 : (0 : ℝ) ≤ (ka : ℝ) / 64 * 0.6931471803 := by positivity
  refine ⟨x, by exact_mod_cast hx64, ?_, lt_of_lt_of_le hpos hP⟩
  have hc : 0 ≤ c := by
    by_contra h
    push Not at h
    have : c * ((ka : ℝ) / 64 * 0.6931471803) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg _)
    linarith
  calc (x : ℝ) ≤ c * ((ka : ℝ) / 64 * 0.6931471803) ^ 2 := hx
    _ ≤ c * Real.log q ^ 2 := by gcongr

end LLS
