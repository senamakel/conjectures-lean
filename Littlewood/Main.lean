import Littlewood.Statement
import Littlewood.Bound
import Lindelof.Transfer
import Littlewood.Asymptotic

/-!
# Step 10: assembly of RH ⇒ Littlewood's bound

* `log_norm_zeta_le` (RH): with `σ₀ = 1/2 + 1/log x` in `key_bound`, and Lindelöf's transfer
  `‖ζ(1/2+it)‖ ≤ C₁ t^{δ/2} ‖ζ(1/2+δ+it)‖` (`Lindelof.norm_zeta_half_le`, from the monotonicity
  of `|ξ|` under RH) with `δ = 1/log x`:

      log |ζ(1/2+it)| ≤ A + log t / (2 log x)
                         + (2((x+1)(log x)² + x + 1 + S) + B + log (3 + t)) / log x.

* `littlewood_of_RH`: take `x = √(log t)`, so `log x = ½ log log t`; the right side is
  `3 log t / log log t + O(√(log t) log log t)`, hence `≤ 4 log t / log log t` for large `t`.
-/

open Complex Filter Asymptotics ArithmeticFunction

namespace Littlewood

open Erdos985.Analytic

/-- `ζ'/ζ` is bounded on `Re s = 2`. -/
theorem norm_logDeriv_zeta_two_le : ∃ B : ℝ, ∀ t : ℝ,
    ‖deriv riemannZeta ((2 : ℂ) + t * I) / riemannZeta ((2 : ℂ) + t * I)‖ ≤ B := by
  refine ⟨∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖, fun t => ?_⟩
  have hre : 1 < ((2 : ℂ) + t * I).re := by simp
  have h1 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
  have hs2 := (LSeriesSummable_vonMangoldt (s := 2) (by norm_num)).norm
  have heq : (fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) ((2 : ℂ) + t * I) n‖)
      = fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖ := by
    funext n; rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp
  have : ‖deriv riemannZeta ((2 : ℂ) + t * I) / riemannZeta ((2 : ℂ) + t * I)‖
      = ‖LSeries (fun n => (Λ n : ℂ)) ((2 : ℂ) + t * I)‖ := by
    rw [h1, neg_div, norm_neg]
  rw [this]
  calc ‖LSeries (fun n => (Λ n : ℂ)) ((2 : ℂ) + t * I)‖
      ≤ ∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) ((2 : ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm (by rw [heq]; exact hs2)
    _ = _ := by rw [heq]

/-- `Re ξ'/ξ(2 + it) ≤ B + log (3 + t) + 5`. -/
theorem re_logDeriv_xi_two_le {B : ℝ}
    (hB : ∀ t : ℝ, ‖deriv riemannZeta ((2 : ℂ) + t * I) / riemannZeta ((2 : ℂ) + t * I)‖ ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re ≤ B + Real.log (3 + t) + 5 := by
  have hs : 0 < ((2 : ℂ) + t * I).re := by simp
  have hs1 : (2 : ℂ) + t * I ≠ 1 := fun h => by have := congrArg re h; simp at this
  have hζ : riemannZeta ((2 : ℂ) + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have h := logDeriv_riemannZeta_eq_archR hs hs1 hζ
  have hxi : deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I) =
      deriv riemannZeta ((2 : ℂ) + t * I) / riemannZeta ((2 : ℂ) + t * I) + archR ((2 : ℂ) + t * I) := by
    rw [h]; ring
  rw [hxi]
  have h1 := (re_le_norm _).trans (hB t)
  have h2 := (re_le_norm _).trans (norm_archR_two_le t)
  rw [abs_of_nonneg ht] at h2
  rw [add_re]
  linarith

/-- **Littlewood's bound with an explicit parameter `x`** (RH). -/
theorem log_norm_zeta_le (hRH : RiemannHypothesis) :
    ∃ A B : ℝ, ∀ t x : ℝ, 1 ≤ t → Real.exp 2 ≤ x →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (A + Real.log t / (2 * Real.log x) +
        (2 * ((x + 1) * Real.log x ^ 2 + (x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) + B +
          Real.log (3 + t)) / Real.log x) := by
  obtain ⟨C₁, hC₁⟩ := Lindelof.norm_zeta_half_le hRH
  obtain ⟨B, hB⟩ := norm_logDeriv_zeta_two_le
  set S := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS
  refine ⟨Real.log (max C₁ 1) + S, B + 5, fun t x ht hx => ?_⟩
  have hx1 : 1 < x := lt_of_lt_of_le (by have := Real.add_one_le_exp (2 : ℝ); linarith) hx
  have hL2 : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  set δ : ℝ := 1 / L with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by rw [hδ, div_le_div_iff₀ hL0 (by norm_num)]; linarith
  set σ₀ : ℝ := 1 / 2 + δ with hσ₀
  have h0 : 1 / 2 < σ₀ := by linarith
  have h2 : σ₀ ≤ 2 := by linarith
  have hηL : 1 ≤ (σ₀ - 1 / 2) * L := by
    rw [hσ₀, show 1 / 2 + δ - 1 / 2 = δ by ring, hδ, one_div_mul_cancel hL0.ne']
  have hK := key_bound hRH ht hx1 h0 h2 hηL
  have hxi := re_logDeriv_xi_two_le hB (by linarith : (0 : ℝ) ≤ t)
  -- `log |ζ(2 + it)| ≤ S`
  have hζ2 : riemannZeta (2 + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have hS1 : 0 < ‖riemannZeta (2 + t * I)‖ := norm_pos_iff.2 hζ2
  have hf2 : Real.log ‖riemannZeta (2 + t * I)‖ ≤ S := by
    have := Lindelof.norm_zeta_le_of_two_le (s := 2 + t * I) (by simp)
    have hl := Real.log_le_sub_one_of_pos hS1
    linarith
  -- `log |ζ(σ₀ + it)|`
  have hne1 : (σ₀ : ℂ) + t * I ≠ 1 := fun h => by have := congrArg im h; simp at this; linarith
  have hζ0 : riemannZeta (σ₀ + t * I) ≠ 0 :=
    Lindelof.riemannZeta_ne_zero_of_RH hRH (by simp; linarith) hne1
  have hf0 : Real.log ‖riemannZeta (σ₀ + t * I)‖ ≤ S +
      (2 * ((x + 1) * L ^ 2 + (x + 1 + S)) + (B + 5) + Real.log (3 + t)) / L := by
    have h : (Real.log ‖riemannZeta (σ₀ + t * I)‖ - Real.log ‖riemannZeta (2 + t * I)‖) * L ≤
        2 * ((x + 1) * L ^ 2 + (x + 1 + S)) + (B + 5) + Real.log (3 + t) := by
      rw [mul_comm]; linarith
    have h' := (le_div_iff₀ hL0).2 h
    linarith
  -- the transfer to the half line
  have hT := hC₁ δ hδ0 hδ2 t ht
  have hσ₀c : ((1 / 2 + δ : ℝ) : ℂ) + t * I = (σ₀ : ℂ) + t * I := by rw [hσ₀]
  rw [hσ₀c] at hT
  have ht0 : 0 < t := by linarith
  have hpow : t ^ (δ / 2) = Real.exp (Real.log t / (2 * L)) := by
    rw [Real.rpow_def_of_pos ht0]; congr 1; rw [hδ]; field_simp
  have hnorm0 : ‖riemannZeta (σ₀ + t * I)‖ = Real.exp (Real.log ‖riemannZeta (σ₀ + t * I)‖) :=
    (Real.exp_log (norm_pos_iff.2 hζ0)).symm
  have hCmax : C₁ ≤ Real.exp (Real.log (max C₁ 1)) := by
    rw [Real.exp_log (by positivity)]; exact le_max_left _ _
  calc ‖riemannZeta (1 / 2 + t * I)‖
      ≤ C₁ * t ^ (δ / 2) * ‖riemannZeta (σ₀ + t * I)‖ := hT
    _ ≤ Real.exp (Real.log (max C₁ 1)) * Real.exp (Real.log t / (2 * L)) *
          Real.exp (S + (2 * ((x + 1) * L ^ 2 + (x + 1 + S)) + (B + 5) + Real.log (3 + t)) / L) := by
        rw [hpow, hnorm0]
        gcongr
    _ = Real.exp (Real.log (max C₁ 1) + S + Real.log t / (2 * L) +
          (2 * ((x + 1) * L ^ 2 + (x + 1 + S)) + (B + 5) + Real.log (3 + t)) / L) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf

/-- **Littlewood's theorem** (1924): RH implies `|ζ(1/2 + it)| ≤ exp (C log t / log log t)`
for large `t`, here with `C = 4`. -/
theorem littlewood_of_RH (hRH : RiemannHypothesis) : LittlewoodBound := by
  obtain ⟨A, B, h⟩ := log_norm_zeta_le hRH
  obtain ⟨U, hU4, hU⟩ := exists_threshold A B (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)
  refine ⟨4, Real.exp U, fun t ht => ?_⟩
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos 4) hU4
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos U) ht
  have ht1 : 1 ≤ t := le_trans (Real.one_le_exp hU0.le) ht
  set u := Real.log t with hu
  have huU : U ≤ u := by rw [hu, Real.le_log_iff_exp_le ht0]; exact ht
  have hu4 : Real.exp 4 ≤ u := hU4.trans huU
  have hx : Real.exp 2 ≤ Real.sqrt u := by
    rw [show Real.exp 2 = Real.sqrt (Real.exp 2 ^ 2) from (Real.sqrt_sq (Real.exp_pos 2).le).symm,
      ← Real.exp_nat_mul]
    exact Real.sqrt_le_sqrt (by norm_num at hu4 ⊢; exact hu4)
  have hw : Real.log (3 + t) ≤ u + 2 := by
    have h4 : Real.log (3 + t) ≤ Real.log (4 * t) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) ht0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h4
    have := Real.log_two_lt_d9
    push_cast at h4
    linarith
  calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ _ := h t (Real.sqrt u) ht1 hx
    _ ≤ Real.exp (4 * Real.log t / Real.log (Real.log t)) :=
        Real.exp_le_exp.2 (hU u huU _ hw)

end Littlewood
