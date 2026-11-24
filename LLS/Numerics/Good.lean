import LLS.Numerics.Interval

/-!
# Certified intervals of moduli

`GoodQ c q`: some `x ≤ c log² q` with `x ≥ 64` makes the budget positive, `Φ(x, log q) > 0`, and
satisfies `β(x) ≤ κ(x)`. By `Phi_nonpos` this contradicts GRH unless the character takes a
value `≠ 1` at some `n ≤ x` prime to `q`. `goodQ_of_data` turns a finite certificate (integer
power comparisons for the logarithms, rational square-root bounds, and a rational inequality
`PhiLo > 0`) into `GoodQ c q` for every `q` in a range `[Q_a, Q_b)`.
-/

namespace LLS

/-- A modulus for which the analytic argument works with constant `c`. -/
def GoodQ (c : ℝ) (q : ℕ) : Prop :=
  ∃ x : ℕ, 64 ≤ x ∧ (x : ℝ) ≤ c * Real.log q ^ 2 ∧ 0 < Phi x (Real.log q) ∧ bet x ≤ kap x

theorem goodQ_of_data {c : ℝ} (q Qa Qb ka kb x : ℕ) (s₁ s₂ : ℝ) (k₁ k₂ : ℕ)
    (h1 : Qa ≤ q) (h2 : q < Qb)
    (hka : 2 ^ ka ≤ Qa ^ 64) (hkb : Qb ^ 64 ≤ 2 ^ kb) (hk₁ : 2 ^ k₁ ≤ x ^ 64) (hk₂ : x ^ 64 ≤ 2 ^ k₂)
    (hs₁0 : 0 ≤ s₁) (hs₁ : s₁ ^ 2 ≤ x) (hs₂0 : 0 ≤ s₂) (hs₂ : (x : ℝ) ≤ s₂ ^ 2)
    (hx : (x : ℝ) ≤ c * ((ka : ℝ) / 64 * 0.6931471803) ^ 2)
    (hside : SideOK x s₁ s₂ ((k₁ : ℝ) / 64 * 0.6931471803) ((k₂ : ℝ) / 64 * 0.6931471808)
      ((kb : ℝ) / 64 * 0.6931471808))
    (hpos : 0 < PhiLo x s₁ s₂ ((k₁ : ℝ) / 64 * 0.6931471803) ((k₂ : ℝ) / 64 * 0.6931471808)
      ((kb : ℝ) / 64 * 0.6931471808)) :
    GoodQ c q := by
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
  obtain ⟨hP, hβ⟩ := Phi_ge_PhiLo x (Real.log q) s₁ s₂ _ _ _ hs₁' hs₂' hl₁ hl₂ hL0 hLb hside
  have hka0 : (0 : ℝ) ≤ (ka : ℝ) / 64 * 0.6931471803 := by positivity
  refine ⟨x, by exact_mod_cast hx64, ?_, lt_of_lt_of_le hpos hP, hβ⟩
  have hc : 0 ≤ c := by
    by_contra h
    push Not at h
    have : c * ((ka : ℝ) / 64 * 0.6931471803) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg _)
    linarith
  calc (x : ℝ) ≤ c * ((ka : ℝ) / 64 * 0.6931471803) ^ 2 := hx
    _ ≤ c * Real.log q ^ 2 := by gcongr

end LLS
