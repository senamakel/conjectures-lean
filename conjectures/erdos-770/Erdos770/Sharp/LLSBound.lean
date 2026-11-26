import Erdos770.Core
import LLS.Statement

/-!
# The bad prime under LLS Theorem 1.1

`lt_of_lls`: if a prime `r ≥ 3000` divides `iⁿ - 1` for every `2 ≤ i ≤ M`, with `M ≥ P n`, then
`M < (log r + 13/4)²`. `LLS.LeastPrimeOutsideSubgroup` (LLS 2015, Theorem 1.1 (1)) gives a prime
`ℓ ∉ H = ker (x ↦ xⁿ)` with `ℓ ≤ (log r + B(r))²`, and `ℓ ∉ H` forces `ℓ > M`.

`B_le`: for a prime `r ≥ 3000`, `B(r) ≤ 13/4` (the maximum is about `3.126`, at `r = 3001`): with
`L = log r > 8` and `λ = log L ≥ log 8`, `A(r) ≥ 2λ - 8/5 - L/(r - 1)`, so
`B(r) ≤ max(0, 6.2 - 2λ + 2λ²/L + 2L/(r - 1))`, and `λ/L ≤ log 8 / 8 < 0.26`, `L/(r - 1) ≤ 0.012`.
-/

namespace Erdos770.Sharp

open Real

lemma log_3000_gt : (8 : ℝ) < Real.log 3000 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 8 < 2.7182818286 ^ 8 := by gcongr
    _ < 3000 := by norm_num

lemma log_100_lt : Real.log 100 < 4.86 := by
  have h : Real.log 100 < Real.log ((2 : ℝ) ^ 7) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_lt_d9]

theorem B_le {r : ℕ} (hr : r.Prime) (h3000 : 3000 ≤ r) : LLS.B r ≤ 13 / 4 := by
  have hr' : (3000 : ℝ) ≤ r := by exact_mod_cast h3000
  set L := Real.log (r : ℝ) with hL_def
  have hL8 : 8 < L :=
    lt_of_lt_of_le log_3000_gt (Real.log_le_log (by norm_num) hr')
  set LL := Real.log L with hLL_def
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hLL : 2.0794 ≤ LL := by
    have : Real.log 8 ≤ LL := Real.log_le_log (by norm_num) hL8.le
    have := Real.log_two_gt_d9
    linarith
  have he8 : Real.exp 1 ≤ 8 := by
    have := Real.exp_one_lt_d9; linarith
  have hratio : LL / L ≤ Real.log 8 / 8 :=
    Real.log_div_self_antitoneOn he8 (le_trans he8 hL8.le) hL8.le
  have hlog8' : Real.log 8 / 8 ≤ 0.26 := by
    have := Real.log_two_lt_d9
    rw [hlog8, div_le_iff₀ (by norm_num)]; linarith
  have hLLL : LL ≤ 0.26 * L := by
    have := hratio.trans hlog8'
    rwa [div_le_iff₀ (by linarith)] at this
  have hfrac : LL ^ 2 / L ≤ 0.26 * LL := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hLr : L / ((r : ℝ) - 1) ≤ 0.012 := by
    have h := Real.log_le_sub_one_of_pos (x := (r : ℝ) / 100) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    have := log_100_lt
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hA : 2 * LL - 8 / 5 - L / ((r : ℝ) - 1) ≤ LLS.A r := by
    unfold LLS.A
    rw [hr.primeFactors, Finset.sum_singleton]
    exact le_max_right _ _
  unfold LLS.B
  rw [hr.primeFactors, Finset.card_singleton]
  apply max_le (by norm_num)
  have : 2 * ((1 : ℕ) : ℝ) * LL ^ 2 / L = 2 * (LL ^ 2 / L) := by push_cast; ring
  rw [this]
  linarith

theorem lt_of_lls (hL : LLS.LeastPrimeOutsideSubgroup) {n M r : ℕ} (hn : 1 ≤ n)
    (hr : r.Prime) (h3000 : 3000 ≤ r) (hMr : M < r) (hPM : P n ≤ M)
    (hdvd : ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1) :
    (M : ℝ) < (Real.log r + 13 / 4) ^ 2 := by
  have := Fact.mk hr
  have : NeZero r := ⟨hr.ne_zero⟩
  let H : Subgroup (ZMod r)ˣ := (powMonoidHom n : (ZMod r)ˣ →* (ZMod r)ˣ).ker
  have hmem : ∀ x : (ZMod r)ˣ, x ∈ H ↔ x ^ n = 1 := fun x => by
    simp [H, MonoidHom.mem_ker]
  have hH : H ≠ ⊤ := by
    intro htop
    have hall : ∀ x : (ZMod r)ˣ, x ^ n = 1 := fun x => (hmem x).1 (htop ▸ Subgroup.mem_top x)
    have hexp : Monoid.exponent (ZMod r)ˣ ∣ n := Monoid.exponent_dvd_of_forall_pow_eq_one hall
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units] at hexp
    have := le_P hn hr hexp
    omega
  obtain ⟨ℓ, hℓp, hℓc, hℓH, hℓle⟩ := hL r h3000 H hH
  have hMℓ : M < ℓ := by
    by_contra hle
    push Not at hle
    apply hℓH
    rw [hmem]
    ext
    push_cast
    rw [ZMod.coe_unitOfCoprime]
    exact (dvd_pow_sub_one_iff hℓp.one_lt.le).1 (hdvd ℓ hℓp.two_le hle)
  have hB := B_le hr h3000
  have hB0 : 0 ≤ LLS.B r := le_max_left _ _
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr.one_lt.le)
  calc (M : ℝ) < ℓ := by exact_mod_cast hMℓ
    _ ≤ (Real.log r + LLS.B r) ^ 2 := hℓle
    _ ≤ (Real.log r + 13 / 4) ^ 2 := by gcongr

end Erdos770.Sharp
