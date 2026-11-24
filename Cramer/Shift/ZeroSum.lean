import Cramer.ZeroSum
import Cramer.Vendor.Digamma
import Erdos985.Analytic.Constants

/-!
# Zero sums for shifted Lorentzians

For `S > 3/2`, real `T` and `s = 1/2 + S + iT`, Hadamard's product gives
`Σ_ρ m_ρ Re(1/(s−ρ) + 1/ρ) = Re ξ'/ξ(s) − Re ξ'/ξ(0)`. Under RH, `Re 1/(s−ρ) = S/(S² + (γ−T)²)`
and `Re 1/ρ > 0`, so

`Σ_ρ m_ρ S²/(S² + (γ − T)²) ≤ S (Lc(S, T) + 1/40)`,

`Lc(S,T) = 1/(1/2+S) + 1/(S−1/2) − ½ log π + ½ (log((1/2+S)/2) + ½ log(1 + T²/(S−3/2)²))
  + 1.52 · 2^{1−S}`.

The digamma term uses the complex bound `Re ψ(σ + it) ≤ log σ + ½ log(1 + t²/(σ−1)²)`
(`Cramer.Vendor.Digamma.re_digamma_le`), and `Re ζ'/ζ(s) ≤ Σ Λ(n) n^{−Re s} ≤ 1.52 · 2^{3/2 − Re s}`.
-/

namespace Cramer

open Complex Erdos985.Analytic ArithmeticFunction

/-- The upper bound for `Re ξ'/ξ(1/2 + S + iT)`. -/
noncomputable def Lc (S T : ℝ) : ℝ :=
  1 / (1 / 2 + S) + 1 / (S - 1 / 2) - (1 / 2) * Real.log Real.pi
    + (1 / 2) * (Real.log ((1 / 2 + S) / 2) + 1 / 2 * Real.log (1 + T ^ 2 / (S - 3 / 2) ^ 2))
    + 1.52 * (2 : ℝ) ^ (1 - S)

/-- `Re ζ'/ζ(s) ≤ 1.52 · 2^{3/2 − Re s}` for `Re s ≥ 3/2`. -/
lemma re_logDeriv_zeta_le_complex {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    (deriv riemannZeta s / riemannZeta s).re ≤ 1.52 * (2 : ℝ) ^ (3 / 2 - s.re) := by
  have hs1 : 1 < s.re := by linarith
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs1
  have hsumm : LSeriesSummable (fun n => ((Λ n : ℝ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
  have e : deriv riemannZeta s / riemannZeta s = -LSeries (fun n => ((Λ n : ℝ) : ℂ)) s := by
    rw [key]; ring
  rw [e, neg_re]
  have h1 : -(LSeries (fun n => ((Λ n : ℝ) : ℂ)) s).re ≤ ‖LSeries (fun n => ((Λ n : ℝ) : ℂ)) s‖ := by
    have := Complex.abs_re_le_norm (LSeries (fun n => ((Λ n : ℝ) : ℂ)) s)
    linarith [neg_abs_le (LSeries (fun n => ((Λ n : ℝ) : ℂ)) s).re]
  refine h1.trans ?_
  have hn : ∀ n : ℕ, ‖LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) s n‖
      ≤ (2 : ℝ) ^ (3 / 2 - s.re) * ((Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · positivity
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have : n = 1 := by omega
        subst this; simp
      · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
        have hnpos : (0 : ℝ) < n := by linarith
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        have hsplit : (n : ℝ) ^ s.re = (n : ℝ) ^ (s.re - 3 / 2) * (n : ℝ) ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_add hnpos]; ring_nf
        have hp : (2 : ℝ) ^ (s.re - 3 / 2) ≤ (n : ℝ) ^ (s.re - 3 / 2) :=
          Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
        have h22 : (2 : ℝ) ^ (3 / 2 - s.re) * (2 : ℝ) ^ (s.re - 3 / 2) = 1 := by
          rw [← Real.rpow_add (by norm_num)]; norm_num
        have hΛ := (vonMangoldt_nonneg : (0 : ℝ) ≤ Λ n)
        rw [hsplit]
        have h3 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
        calc (Λ n : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ)
            = (Λ n : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (3 / 2 - s.re) * (2 : ℝ) ^ (s.re - 3 / 2)) := by
              rw [h22, mul_one]
          _ ≤ (Λ n : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (3 / 2 - s.re) * (n : ℝ) ^ (s.re - 3 / 2)) := by
              gcongr
          _ = _ := by ring
  have hS : Summable fun n : ℕ => (2 : ℝ) ^ (3 / 2 - s.re) * ((Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    summable_vonMangoldt_rpow.mul_left _
  calc ‖LSeries (fun n => ((Λ n : ℝ) : ℂ)) s‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsumm.norm
    _ ≤ ∑' n : ℕ, (2 : ℝ) ^ (3 / 2 - s.re) * ((Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) :=
        hsumm.norm.tsum_le_tsum hn hS
    _ = (2 : ℝ) ^ (3 / 2 - s.re) * ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ (2 : ℝ) ^ (3 / 2 - s.re) * 1.52 := by
        gcongr; exact tsum_vonMangoldt_rpow_le
    _ = _ := by ring

/-- `Re ξ'/ξ(1/2 + S + iT) ≤ Lc(S, T)` for `S > 3/2`. -/
lemma re_logDeriv_xi_le_shift {S T : ℝ} (hS : 3 / 2 < S) :
    (deriv xiZeta (((1 / 2 + S : ℝ) : ℂ) + T * I) / xiZeta (((1 / 2 + S : ℝ) : ℂ) + T * I)).re
      ≤ Lc S T := by
  set s : ℂ := ((1 / 2 + S : ℝ) : ℂ) + T * I with hsdef
  have hsre : s.re = 1 / 2 + S := by simp [hsdef]
  have hsim : s.im = T := by simp [hsdef]
  have hs' : 1 < s.re := by rw [hsre]; linarith
  have h := PrincipalAux.logDeriv_riemannZeta_eq hs'
  have hξ : deriv xiZeta s / xiZeta s = deriv riemannZeta s / riemannZeta s
      + 1 / s + 1 / (s - 1) + gammaLogDeriv (1 : DirichletCharacter ℂ 1) s := by
    rw [h]; ring
  rw [hξ, PrincipalAux.gammaLogDeriv_one]
  have hz := re_logDeriv_zeta_le_complex (s := s) (by rw [hsre]; linarith)
  rw [hsre] at hz
  have hdig : (digamma (s / 2)).re ≤
      Real.log ((1 / 2 + S) / 2) + 1 / 2 * Real.log (1 + (T / 2) ^ 2 / ((1 / 2 + S) / 2 - 1) ^ 2) := by
    have e : s / 2 = (((1 / 2 + S) / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by
      rw [hsdef]; push_cast; ring
    rw [e]
    exact Vendor.Digamma.re_digamma_le (by linarith)
  have hq : (T / 2) ^ 2 / ((1 / 2 + S) / 2 - 1) ^ 2 = T ^ 2 / (S - 3 / 2) ^ 2 := by
    have : S - 3 / 2 ≠ 0 := by linarith
    field_simp; ring
  rw [hq] at hdig
  have hσ0 : 0 < 1 / 2 + S := by linarith
  have hr1 : (1 / s).re ≤ 1 / (1 / 2 + S) := by
    rw [one_div, inv_re, normSq_apply, hsre]
    rw [div_le_div_iff₀ (by nlinarith [sq_nonneg s.im]) hσ0]
    nlinarith [sq_nonneg s.im]
  have hr2 : (1 / (s - 1)).re ≤ 1 / (S - 1 / 2) := by
    have hre : (s - 1).re = S - 1 / 2 := by rw [sub_re, hsre]; simp; ring
    have hS0 : 0 < S - 1 / 2 := by linarith
    rw [one_div, inv_re, normSq_apply, hre]
    have : (S - 1 / 2) * (S - 1 / 2) ≤ (S - 1 / 2) * (S - 1 / 2) + (s - 1).im * (s - 1).im := by
      nlinarith [sq_nonneg (s - 1).im]
    rw [div_le_div_iff₀ (by nlinarith) hS0]
    nlinarith
  have hpow : (2 : ℝ) ^ (3 / 2 - (1 / 2 + S)) = (2 : ℝ) ^ (1 - S) := by ring_nf
  rw [hpow] at hz
  simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at *
  have e3 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have e4 : ((1 : ℂ) / 2).im = 0 := by norm_num
  rw [e3, e4] at *
  unfold Lc
  nlinarith

/-- **The zero sum of one shifted Lorentzian.** Under RH, for `S > 3/2` and real `T`,
`Σ_ρ m_ρ S²/(S² + (Im ρ − T)²) ≤ S (Lc(S,T) + 1/40)`, and the series converges. -/
theorem shift_zeroSum_le (hRH : RiemannHypothesis) {S T : ℝ} (hS : 3 / 2 < S) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} => (analyticOrderNatAt xiZeta ρ : ℝ) *
      (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2))) ∧
    ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
      (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2)) ≤ S * (Lc S T + 1 / 40) := by
  set s : ℂ := ((1 / 2 + S : ℝ) : ℂ) + T * I with hsdef
  have hsre : s.re = 1 / 2 + S := by simp [hsdef]
  have hx0 : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; norm_num
  have hxs : xiZeta s ≠ 0 := fun h => by
    have := (xiZeta_zero_re_mem h).2; rw [hsre] at this; linarith
  obtain ⟨-, b, H⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨hsum, es⟩ := H s hxs
  have hz : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero] at e0
  have hre := Complex.reCLM.hasSum hsum.hasSum
  simp only [Complex.reCLM_apply] at hre
  set r : {ρ : ℂ // xiZeta ρ = 0} → ℝ := fun ρ =>
    ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re
  have hrtsum : ∑' ρ, r ρ ≤ Lc S T + 1 / 40 := by
    show ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re ≤ _
    rw [hre.tsum_eq]
    have e : (∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
        (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))
        = deriv xiZeta s / xiZeta s - deriv xiZeta 0 / xiZeta 0 := by
      rw [es, e0]; ring
    rw [e, sub_re]
    linarith [re_logDeriv_xi_le_shift (T := T) hS, neg_re_logDeriv_xi_zero_lt]
  have hr : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, r ρ = (analyticOrderNatAt xiZeta ρ : ℝ) *
      (1 / (s - ρ) + 1 / ρ).re := by
    intro ρ; simp [r, mul_re]
  have hpt : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2) ≤ S * (1 / (s - ρ) + 1 / ρ).re := by
    intro ρ
    have hρ := xiZeta_zero_re_RH hRH ρ.2
    obtain ⟨⟨x, γ⟩, hzr⟩ := ρ
    simp only at hρ ⊢
    subst hρ
    have hre2 : (1 / (s - ⟨1 / 2, γ⟩) + 1 / ⟨1 / 2, γ⟩).re
        = S / (S ^ 2 + (γ - T) ^ 2) + (1 / 2) / (1 / 4 + γ ^ 2) := by
      rw [hsdef]
      simp [normSq_apply]
      field_simp
      ring
    rw [hre2]
    have : 0 ≤ S * ((1 / 2) / (1 / 4 + γ ^ 2)) := by
      apply mul_nonneg (by linarith); positivity
    have e : S ^ 2 / (S ^ 2 + (γ - T) ^ 2) = S * (S / (S ^ 2 + (γ - T) ^ 2)) := by ring
    rw [e, mul_add]
    linarith
  have hcmp : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
      (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2)) ≤ S * r ρ := by
    intro ρ
    rw [hr]
    have hm : (0 : ℝ) ≤ analyticOrderNatAt xiZeta ρ := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (hpt ρ) hm
    linarith
  have hnn : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, 0 ≤ (analyticOrderNatAt xiZeta ρ : ℝ) *
      (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2)) := fun ρ => by positivity
  have hS' : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => S * r ρ := hre.summable.mul_left _
  have hsum2 := Summable.of_nonneg_of_le hnn hcmp hS'
  refine ⟨hsum2, ?_⟩
  calc _ ≤ ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, S * r ρ := hsum2.tsum_le_tsum hcmp hS'
    _ = S * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, r ρ := tsum_mul_left
    _ ≤ S * (Lc S T + 1 / 40) := by
        apply mul_le_mul_of_nonneg_left hrtsum; linarith

end Cramer
