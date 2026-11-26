import Cramer.Identity

/-!
# Piecewise-linear weights with integer knots, and their explicit formula

Knots `n_j = B + j s` (`j = 0, …, J`), values `s · c_j` at the knots (`c : ℕ → ℤ`,
`c 0 = 0`, `c j = 0` for `j ≥ J`), linear in between. With the second differences
`a_j = c_{j+1} − 2c_j + c_{j−1}` the weight is `w(n) = Σ_j a_j (n_j − n)₊`, so
`Σ_n Λ(n) w(n) = Σ_j a_j Ψ₁(n_j)` (`sum_vonMangoldt_wt`).

Under RH, erdos-985's explicit formula for each `Ψ₁(n_j)` gives (`sum_psi1N_ge_of_zeroSum`)

`Σ_j a_j Ψ₁(n_j) ≥ s² Σ_j c_j − Z − (3/2) Σ_j |a_j|`

for any bound `Z` on `Σ_ρ m_ρ ‖Σ_j a_j g_ρ(n_j)‖`, `g_ρ(t) = t^{ρ+1}/(ρ(ρ+1))`: the affine
terms of the formula cancel because `Σ a_j = Σ a_j n_j = 0`, and `n²/2` gives
`Σ a_j n_j²/2 = s² Σ c_j`.
-/

namespace Cramer.CMS

open Finset Complex Erdos985.Analytic ArithmeticFunction Cramer

/-- Second differences, with `c_{−1} = 0`. -/
def aco (c : ℕ → ℤ) (j : ℕ) : ℤ := c (j + 1) - 2 * c j + (if j = 0 then 0 else c (j - 1))

/-- The knots. -/
def kn (B s j : ℕ) : ℕ := B + j * s

/-- The weight `w(n) = Σ_j a_j (n_j − n)₊`. -/
noncomputable def wt (c : ℕ → ℤ) (J B s : ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ range (J + 1), (aco c j : ℝ) * max ((kn B s j : ℝ) - n) 0

/-- **Summation by parts** for the second differences. -/
lemma sum_aco_mul {R : Type*} [CommRing R] (c : ℕ → ℤ) {J : ℕ} (hc0 : c 0 = 0)
    (hcJ : ∀ j, J ≤ j → c j = 0) (G : ℕ → R) :
    ∑ j ∈ range (J + 1), (aco c j : R) * G j =
      ∑ j ∈ range (J + 1), (c j : R) * (G (j + 1) - 2 * G j + (if j = 0 then G 0 else G (j - 1))) := by
  have e1 : ∑ j ∈ range (J + 1), (c (j + 1) : R) * G j =
      ∑ j ∈ range (J + 1), (c j : R) * (if j = 0 then G 0 else G (j - 1)) := by
    conv_rhs => rw [sum_range_succ']
    rw [sum_range_succ, hcJ (J + 1) (by omega)]
    simp [hc0]
  have e2 : ∑ j ∈ range (J + 1), (if j = 0 then (0 : R) else (c (j - 1) : R)) * G j =
      ∑ j ∈ range (J + 1), (c j : R) * G (j + 1) := by
    conv_rhs => rw [sum_range_succ]
    rw [sum_range_succ', hcJ J le_rfl]
    simp
  have h3 : ∑ j ∈ range (J + 1), (aco c j : R) * G j =
      ∑ j ∈ range (J + 1), (c (j + 1) : R) * G j - 2 * ∑ j ∈ range (J + 1), (c j : R) * G j +
        ∑ j ∈ range (J + 1), (if j = 0 then (0 : R) else (c (j - 1) : R)) * G j := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [aco]; push_cast; split_ifs <;> ring
  rw [h3, e1, e2, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => by ring

/-- `Σ a_j = 0`. -/
lemma sum_aco (c : ℕ → ℤ) {J : ℕ} (hc0 : c 0 = 0) (hcJ : ∀ j, J ≤ j → c j = 0) :
    ∑ j ∈ range (J + 1), (aco c j : ℝ) = 0 := by
  have := sum_aco_mul (R := ℝ) c hc0 hcJ (fun _ => 1)
  simp only [mul_one, ite_self] at this
  rw [this]; refine sum_eq_zero fun j _ => ?_; ring

/-- `Σ a_j n_j = 0` and `Σ a_j n_j² = 2 s² Σ c_j`. -/
lemma sum_aco_kn (c : ℕ → ℤ) {J : ℕ} (hc0 : c 0 = 0) (hcJ : ∀ j, J ≤ j → c j = 0) (B s : ℕ) :
    ∑ j ∈ range (J + 1), (aco c j : ℝ) * (kn B s j : ℝ) = 0 ∧
    ∑ j ∈ range (J + 1), (aco c j : ℝ) * (kn B s j : ℝ) ^ 2 =
      2 * (s : ℝ) ^ 2 * ∑ j ∈ range (J + 1), (c j : ℝ) := by
  constructor
  · rw [sum_aco_mul (R := ℝ) c hc0 hcJ]
    refine sum_eq_zero fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hc0]
    · simp only [kn, Nat.pos_iff_ne_zero.1 hj, if_false]
      push_cast
      rw [Nat.cast_sub (by omega)]; push_cast; ring
  · rw [sum_aco_mul (R := ℝ) c hc0 hcJ, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hc0]
    · simp only [kn, Nat.pos_iff_ne_zero.1 hj, if_false]
      push_cast
      rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- `Σ_{n < N} Λ(n) w(n) = Σ_j a_j Ψ₁(n_j)` once `N ≥` every knot. -/
lemma sum_vonMangoldt_wt (c : ℕ → ℤ) (J B s N : ℕ) (hN : ∀ j ∈ range (J + 1), kn B s j ≤ N) :
    ∑ n ∈ range N, (Λ n : ℝ) * wt c J B s n = ∑ j ∈ range (J + 1), (aco c j : ℝ) * psi1N (kn B s j) := by
  simp only [wt, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [psi1N_eq_sum_max (hN j hj), mul_sum]
  refine sum_congr rfl fun n _ => ?_
  push_cast; ring

/-- Summability of `ρ ↦ m_ρ V(n, ρ)` under RH. -/
lemma summable_mV (hRH : RiemannHypothesis) (n : ℕ) (hn : 1 ≤ n) :
    Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => (analyticOrderNatAt xiZeta ρ : ℂ) * V n ρ := by
  have hcrit : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => xiZeta_zero_re_RH hRH ρ.2
  have hsq : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
      (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ := by
    have hs := (hadamard_logDeriv differentiable_xiZeta (by rw [xiZeta_zero]; exact one_ne_zero)
      xiZeta_growth).1 1 one_pos
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ρ => ?_) hs
    have hq := PrincipalAux.inv_norm_mul_le_re (hcrit ρ)
    have hn2 : ‖(ρ : ℂ)‖ ^ (1 + 1 : ℝ) = 1 / 4 + (ρ : ℂ).im ^ 2 := by
      rw [show (1 + 1 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, ← normSq_eq_norm_sq,
        normSq_apply, hcrit ρ]; ring
    have hre1 : (1 / (1 - (ρ : ℂ)) + 1 / (ρ : ℂ)).re = 1 / (1 / 4 + (ρ : ℂ).im ^ 2) := by
      have key : ∀ z : ℂ, z.re = 1 / 2 → (1 / (1 - z) + 1 / z).re = 1 / (1 / 4 + z.im ^ 2) := by
        rintro ⟨x, γ⟩ hx
        simp only at hx
        subst hx
        simp [normSq_apply]
        field_simp
        ring
      exact key _ (hcrit ρ)
    rw [hre1] at hq
    rw [hn2, div_eq_mul_one_div, div_eq_mul_one_div (analyticOrderNatAt xiZeta ρ : ℝ)]
    exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
  refine Summable.of_norm_bounded ((hsq.mul_left ((n : ℝ) * (√(n : ℝ) + 2 + 3 / n)))) fun ρ => ?_
  rw [norm_mul, V, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have := norm_zeroTerm_le n hn (hcrit ρ)
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  calc (analyticOrderNatAt xiZeta ρ : ℝ) * ((n : ℝ) * ‖zeroTerm n ρ‖)
      ≤ (analyticOrderNatAt xiZeta ρ : ℝ) *
          ((n : ℝ) * ((√(n : ℝ) + 2 + 3 / n) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖)) := by gcongr
    _ = _ := by ring

/-- **The explicit formula for the weight.** Under RH, with `B ≥ 1`, if
`Σ_ρ m_ρ ‖Σ_j a_j g_ρ(n_j)‖ ≤ Z` then `Σ_j a_j Ψ₁(n_j) ≥ s² Σ c_j − Z − (3/2) Σ |a_j|`. -/
theorem sum_psi1N_ge_of_zeroSum (hRH : RiemannHypothesis) (c : ℕ → ℤ) {J : ℕ} (hc0 : c 0 = 0)
    (hcJ : ∀ j, J ≤ j → c j = 0) {B s : ℕ} (hB : 1 ≤ B) {Z : ℝ}
    (hsumD : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => (analyticOrderNatAt xiZeta ρ : ℝ) *
      ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (kn B s j)‖)
    (hD : ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
      ‖∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (kn B s j)‖ ≤ Z) :
    (s : ℝ) ^ 2 * ∑ j ∈ range (J + 1), (c j : ℝ) - Z - 3 / 2 * ∑ j ∈ range (J + 1), |(aco c j : ℝ)|
      ≤ ∑ j ∈ range (J + 1), (aco c j : ℝ) * psi1N (kn B s j) := by
  set m : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt xiZeta ρ : ℂ)
  set D : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ => ∑ j ∈ range (J + 1), (aco c j : ℂ) * gρ ρ (kn B s j)
  have hcrit : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => xiZeta_zero_re_RH hRH ρ.2
  have hρ0 : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ) ≠ 0 := fun ρ h => by
    have := hcrit ρ; rw [h] at this; norm_num at this
  have hρ1 : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (ρ : ℂ) + 1 ≠ 0 := fun ρ h => by
    have := hcrit ρ
    have h2 : ((ρ : ℂ) + 1).re = 0 := by rw [h]; simp
    simp [this] at h2; norm_num at h2
  have hkn1 : ∀ j, 1 ≤ kn B s j := fun j => by unfold kn; omega
  have hsumD' : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => ‖m ρ * D ρ‖ := by
    refine hsumD.congr fun ρ => ?_
    simp [m, D]
  -- the zero part
  have hcomb : ∑ j ∈ range (J + 1), (aco c j : ℂ) * ∑' ρ, m ρ * V (kn B s j) ρ = -∑' ρ, m ρ * D ρ := by
    have hs : ∀ j ∈ range (J + 1), Summable fun ρ => (aco c j : ℂ) * (m ρ * V (kn B s j) ρ) :=
      fun j _ => (summable_mV hRH _ (hkn1 j)).mul_left _
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hs, ← tsum_neg]
    refine tsum_congr fun ρ => ?_
    simp only [D, mul_sum, ← sum_neg_distrib]
    -- `Σ a_j V(n_j) = −Σ a_j g(n_j)`: the affine part of `V` cancels
    have hV : ∀ j, V (kn B s j) ρ = (((kn B s j : ℕ) : ℂ) - 1) / (2 - ρ) - gρ ρ (kn B s j : ℕ)
        + ((kn B s j : ℕ) : ℂ) / ρ - 1 / (1 + ρ) := fun j => V_eq (hkn1 j) (hρ0 ρ) (hρ1 ρ)
    have h0 : ∑ j ∈ range (J + 1), (aco c j : ℂ) = 0 := by
      have := sum_aco (c := c) hc0 hcJ; exact_mod_cast this
    have h1 : ∑ j ∈ range (J + 1), (aco c j : ℂ) * ((kn B s j : ℕ) : ℂ) = 0 := by
      have := (sum_aco_kn c hc0 hcJ B s).1; exact_mod_cast this
    have e : ∀ j ∈ range (J + 1), (aco c j : ℂ) * (m ρ * V (kn B s j) ρ) =
        -(m ρ * ((aco c j : ℂ) * gρ ρ (kn B s j))) + m ρ * ((aco c j : ℂ) * ((kn B s j : ℕ) : ℂ)) *
          (1 / (2 - ρ) + 1 / ρ) - m ρ * (aco c j : ℂ) * (1 / (2 - ρ) + 1 / (1 + ρ)) := by
      intro j _; rw [hV j]; ring
    calc ∑ j ∈ range (J + 1), (aco c j : ℂ) * (m ρ * V (kn B s j) ρ)
        = ∑ j ∈ range (J + 1), -(m ρ * ((aco c j : ℂ) * gρ ρ (kn B s j)))
          + (m ρ * (1 / (2 - ρ) + 1 / ρ)) * ∑ j ∈ range (J + 1), (aco c j : ℂ) * ((kn B s j : ℕ) : ℂ)
          - (m ρ * (1 / (2 - ρ) + 1 / (1 + ρ))) * ∑ j ∈ range (J + 1), (aco c j : ℂ) := by
          rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
          exact sum_congr rfl fun j hj => by rw [e j hj]; ring
      _ = _ := by rw [h1, h0]; ring
  have hZ : -(∑' ρ, m ρ * D ρ).re ≥ -Z := by
    have h1 : (∑' ρ, m ρ * D ρ).re ≤ ‖∑' ρ, m ρ * D ρ‖ := re_le_norm _
    have h2 : ‖∑' ρ, m ρ * D ρ‖ ≤ ∑' ρ, ‖m ρ * D ρ‖ := norm_tsum_le_tsum_norm hsumD'
    have h3 : ∑' ρ, ‖m ρ * D ρ‖
        = ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) * ‖D ρ‖ :=
      tsum_congr fun ρ => by simp [m]
    linarith
  -- each `Ψ₁(n_j)`
  set Yf : ℕ → ℝ := fun n => (n : ℝ) * ((gammaPart (1 : DirichletCharacter ℂ 1) n).re
    + Real.log n) - n with hYf
  have hpsi : ∀ j ∈ range (J + 1), psi1N (kn B s j) =
      (∑' ρ, m ρ * V (kn B s j) ρ).re
      + Yf (kn B s j)
      + ((kn B s j : ℕ) : ℝ) ^ 2 / 2 - 5 * (kn B s j : ℕ) / 2 + 3
      - (((kn B s j : ℕ) : ℝ) - 1) * (deriv riemannZeta 2 / riemannZeta 2).re := by
    intro j _
    rw [psi1N_formula _ (hkn1 j), hYf]
    ring
  have hsum : ∑ j ∈ range (J + 1), (aco c j : ℝ) * psi1N (kn B s j) =
      ∑ j ∈ range (J + 1), (aco c j : ℝ) * ((∑' ρ, m ρ * V (kn B s j) ρ).re
      + Yf (kn B s j)
      + ((kn B s j : ℕ) : ℝ) ^ 2 / 2 - 5 * (kn B s j : ℕ) / 2 + 3
      - (((kn B s j : ℕ) : ℝ) - 1) * (deriv riemannZeta 2 / riemannZeta 2).re) :=
    sum_congr rfl fun j hj => by rw [hpsi j hj]
  rw [hsum]
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  -- the pieces
  have hre : ∑ j ∈ range (J + 1), (aco c j : ℝ) * (∑' ρ, m ρ * V (kn B s j) ρ).re =
      -(∑' ρ, m ρ * D ρ).re := by
    have := congrArg Complex.re hcomb
    rw [Complex.re_sum] at this
    simp only [Complex.re_ofReal_mul, neg_re] at this
    rw [← this]
    refine sum_congr rfl fun j _ => ?_
    rw [show ((aco c j : ℂ)) = ((aco c j : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  have hF : -(3 / 2 * ∑ j ∈ range (J + 1), |(aco c j : ℝ)|) ≤
      ∑ j ∈ range (J + 1), (aco c j : ℝ) * Yf (kn B s j) := by
    rw [← neg_mul, mul_sum]
    refine sum_le_sum fun j _ => ?_
    simp only [hYf]
    obtain ⟨-, g1, g2⟩ := gammaPart_one_bound (kn B s j) (hkn1 j)
    have hb1 : (1 : ℝ) ≤ ((kn B s j : ℕ) : ℝ) := by exact_mod_cast hkn1 j
    set u := ((kn B s j : ℕ) : ℝ)
    set G := (gammaPart (1 : DirichletCharacter ℂ 1) (kn B s j)).re + Real.log (kn B s j)
    have hu1 : -(3 / 2) ≤ u * G - u := by
      have := mul_le_mul_of_nonneg_left g1 (by linarith : (0 : ℝ) ≤ u)
      have e : u * (3 / (2 * u)) = 3 / 2 := by field_simp
      nlinarith
    have hu2 : u * G - u ≤ 0 := by
      have := mul_le_mul_of_nonneg_left g2 (by linarith : (0 : ℝ) ≤ u); linarith
    have habs : |u * G - u| ≤ 3 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have := neg_abs_le ((aco c j : ℝ) * (u * G - u))
    rw [abs_mul] at this
    nlinarith [abs_nonneg (aco c j : ℝ)]
  have h0 := sum_aco (c := c) hc0 hcJ
  obtain ⟨h1, h2⟩ := sum_aco_kn c hc0 hcJ B s
  have e3 : ∑ j ∈ range (J + 1), (aco c j : ℝ) * (((kn B s j : ℕ) : ℝ) ^ 2 / 2) =
      (s : ℝ) ^ 2 * ∑ j ∈ range (J + 1), (c j : ℝ) := by
    rw [show ∑ j ∈ range (J + 1), (aco c j : ℝ) * (((kn B s j : ℕ) : ℝ) ^ 2 / 2) =
      (∑ j ∈ range (J + 1), (aco c j : ℝ) * ((kn B s j : ℕ) : ℝ) ^ 2) / 2 by
      rw [sum_div]; refine sum_congr rfl fun j _ => by ring, h2]; ring
  have e4 : ∑ j ∈ range (J + 1), (aco c j : ℝ) * (5 * ((kn B s j : ℕ) : ℝ) / 2) = 0 := by
    rw [show ∑ j ∈ range (J + 1), (aco c j : ℝ) * (5 * ((kn B s j : ℕ) : ℝ) / 2) =
      5 / 2 * ∑ j ∈ range (J + 1), (aco c j : ℝ) * ((kn B s j : ℕ) : ℝ) by
      rw [mul_sum]; refine sum_congr rfl fun j _ => by ring, h1]; ring
  have e5 : ∑ j ∈ range (J + 1), (aco c j : ℝ) * 3 = 0 := by rw [← sum_mul, h0]; ring
  have e6 : ∑ j ∈ range (J + 1), (aco c j : ℝ) * ((((kn B s j : ℕ) : ℝ) - 1) *
      (deriv riemannZeta 2 / riemannZeta 2).re) = 0 := by
    simp only [sub_mul, one_mul, mul_sub, sum_sub_distrib, ← mul_assoc]
    rw [← sum_mul, ← sum_mul, h1, h0]; ring
  rw [hre, e3, e4, e5, e6]
  linarith

end Cramer.CMS
