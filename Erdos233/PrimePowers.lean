import Mathlib

/-!
# Step 7. Proper prime powers in a short window

`(ψ − θ)(B) − (ψ − θ)(A) = Σ_{2 ≤ k ≤ log₂ B} (θ(B^{1/k}) − θ(A^{1/k}))`, each term is at most
`log B · (B^{1/k} − A^{1/k} + 1) ≤ log B · ((B − A)/√A + 1)`.
-/

namespace Erdos233

open Real Chebyshev Finset

lemma theta_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    θ b - θ a ≤ Real.log b * (b - a + 1) := by
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hsplit : θ b = θ a + ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, Real.log p := by
    simp only [theta, sum_filter]
    rw [sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  rw [hsplit, add_sub_cancel_left]
  have hb1 : 1 ≤ b := ha.trans hab
  calc ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, Real.log p
      ≤ ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, Real.log b := by
        rw [sum_filter]
        refine sum_le_sum fun p hp => ?_
        split_ifs with h
        · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast h.one_lt.le
          have hpb : (p : ℝ) ≤ b := by
            have := (mem_Ioc.1 hp).2
            exact (Nat.cast_le.2 this).trans (Nat.floor_le (by linarith))
          exact Real.log_le_log (by linarith) hpb
        · exact Real.log_nonneg hb1
    _ = ((⌊b⌋₊ - ⌊a⌋₊ : ℕ) : ℝ) * Real.log b := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (b - a + 1) * Real.log b := by
        gcongr
        · exact Real.log_nonneg hb1
        · rw [Nat.cast_sub hfl]
          have h1 := Nat.floor_le (show 0 ≤ b by linarith)
          have h2 := Nat.lt_floor_add_one a
          linarith
    _ = Real.log b * (b - a + 1) := by ring

lemma rpow_sub_rpow_le_sqrt {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) {k : ℕ} (hk : 2 ≤ k) :
    B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) ≤ (B - A) / Real.sqrt A := by
  have hA0 : 0 < A := by linarith
  have hk' : (1 : ℝ) / k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    exact_mod_cast (by omega : 1 * 2 ≤ 1 * k)
  have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
  have hq : 1 ≤ B / A := by rw [le_div_iff₀ hA0]; linarith
  have e1 : B ^ ((1 : ℝ) / k) = A ^ ((1 : ℝ) / k) * (B / A) ^ ((1 : ℝ) / k) := by
    rw [Real.div_rpow (by linarith) hA0.le, mul_div_cancel₀]
    exact (Real.rpow_pos_of_pos hA0 _).ne'
  have h1 : A ^ ((1 : ℝ) / k) ≤ A ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hA hk'
  have h2 : (B / A) ^ ((1 : ℝ) / k) ≤ (B / A) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hq hk'
  have h3 : 1 ≤ (B / A) ^ ((1 : ℝ) / k) := Real.one_le_rpow hq hk0
  have hsA : A ^ ((1 : ℝ) / 2) = Real.sqrt A := (Real.sqrt_eq_rpow A).symm
  have hsq : (B / A) ^ ((1 : ℝ) / 2) = Real.sqrt B / Real.sqrt A := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hA0.le]
  have hsA0 : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0
  have key : B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) ≤ Real.sqrt B - Real.sqrt A := by
    rw [e1]
    have : A ^ ((1 : ℝ) / k) * ((B / A) ^ ((1 : ℝ) / k) - 1)
        ≤ A ^ ((1 : ℝ) / 2) * ((B / A) ^ ((1 : ℝ) / 2) - 1) :=
      mul_le_mul h1 (by linarith) (by linarith) (Real.rpow_nonneg hA0.le _)
    rw [hsA, hsq, mul_sub, mul_sub, mul_div_cancel₀ _ hsA0.ne', mul_one, mul_one] at this
    linarith
  have hsB : Real.sqrt A ≤ Real.sqrt B := Real.sqrt_le_sqrt hAB
  have : Real.sqrt B - Real.sqrt A ≤ (B - A) / Real.sqrt A := by
    rw [le_div_iff₀ hsA0]
    have hA' := Real.mul_self_sqrt hA0.le
    have hB' := Real.mul_self_sqrt (show 0 ≤ B by linarith)
    nlinarith
  linarith

/-- The proper prime powers in `(A, B]` carry `Λ`-mass at most
`(log B / log 2) · log B · ((B − A)/√A + 1)`. -/
theorem psi_sub_theta_window {A B : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    (ψ B - θ B) - (ψ A - θ A)
      ≤ (Real.log B / Real.log 2) * Real.log B * ((B - A) / Real.sqrt A + 1) := by
  set N := ⌊Real.log B / Real.log 2⌋₊ with hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNA : ⌊Real.log A / Real.log 2⌋₊ ≤ N :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith) hAB) hl2.le)
  rw [psi_eq_theta_add_sum_theta' (hA.trans hAB) le_rfl,
    psi_eq_theta_add_sum_theta' hA hNA, ← hN]
  simp only [add_sub_cancel_left]
  rw [← sum_sub_distrib]
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hterm : ∀ k ∈ Icc 2 N, θ (B ^ ((1 : ℝ) / k)) - θ (A ^ ((1 : ℝ) / k))
      ≤ Real.log B * ((B - A) / Real.sqrt A + 1) := by
    intro k hk
    have hk2 : 2 ≤ k := (mem_Icc.1 hk).1
    have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
    have ha1 : 1 ≤ A ^ ((1 : ℝ) / k) := Real.one_le_rpow (by linarith) hk0
    have hab : A ^ ((1 : ℝ) / k) ≤ B ^ ((1 : ℝ) / k) :=
      Real.rpow_le_rpow (by linarith) hAB hk0
    refine (theta_sub_le ha1 hab).trans ?_
    have hlog : Real.log (B ^ ((1 : ℝ) / k)) ≤ Real.log B := by
      rw [Real.log_rpow (by linarith)]
      have : (1 : ℝ) / k ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    have hd := rpow_sub_rpow_le_sqrt (by linarith) hAB hk2
    have hpos : 0 ≤ B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) + 1 := by linarith
    calc Real.log (B ^ ((1 : ℝ) / k)) * (B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) + 1)
        ≤ Real.log B * (B ^ ((1 : ℝ) / k) - A ^ ((1 : ℝ) / k) + 1) :=
          mul_le_mul_of_nonneg_right hlog hpos
      _ ≤ Real.log B * ((B - A) / Real.sqrt A + 1) := by gcongr
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
  have hcard : ((N + 1 - 2 : ℕ) : ℝ) ≤ Real.log B / Real.log 2 := by
    have : ((N + 1 - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    exact this.trans (Nat.floor_le (div_nonneg hlB hl2.le))
  have hnn : 0 ≤ Real.log B * ((B - A) / Real.sqrt A + 1) := by
    have : 0 ≤ (B - A) / Real.sqrt A := div_nonneg (by linarith) (Real.sqrt_nonneg _)
    positivity
  calc ((N + 1 - 2 : ℕ) : ℝ) * (Real.log B * ((B - A) / Real.sqrt A + 1))
      ≤ Real.log B / Real.log 2 * (Real.log B * ((B - A) / Real.sqrt A + 1)) :=
        mul_le_mul_of_nonneg_right hcard hnn
    _ = _ := by ring

end Erdos233
