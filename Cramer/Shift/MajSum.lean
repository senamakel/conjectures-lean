import Cramer.Shift.ZeroSum
import Cramer.Shift.Check

/-!
# The zero sum of the majorant

Under RH, with `x_ρ = γh/(2m)`, each pair `lor(σ, x − τ) + lor(σ, x + τ)` is a pair of shifted
Lorentzians in `γ` of width `S = 2mσ/h` centred at `±T`, `T = 2mτ/h`, so
`Σ_ρ m_ρ M(x_ρ) ≤ Σ_c (C/KC) · 2S (Lc(S, T) + 1/40)` (`Cramer.Shift.shift_zeroSum_le`).
-/

namespace Cramer.Shift

open Complex Erdos985.Analytic

/-- The bound on the zero sum of the majorant. -/
noncomputable def majZ (maj : List (ℕ × ℕ × ℕ)) (m h : ℝ) : ℝ :=
  (maj.map (fun c => ((c.1 : ℝ) / KC) * (2 * (2 * m * ((c.2.1 : ℝ) / NN) / h)
    * (Lc (2 * m * ((c.2.1 : ℝ) / NN) / h) (2 * m * ((c.2.2 : ℝ) / NN) / h) + 1 / 40)))).sum

lemma Lc_neg (S T : ℝ) : Lc S (-T) = Lc S T := by unfold Lc; ring_nf

lemma lor_eq_shift {σ τ m h γ : ℝ} (hm : 0 < m) (hh : 0 < h) :
    lor σ (γ * h / (2 * m) - τ) = (2 * m * σ / h) ^ 2 / ((2 * m * σ / h) ^ 2 + (γ - 2 * m * τ / h) ^ 2) := by
  unfold lor
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp
  · field_simp

/-- **The zero sum of the majorant.** -/
theorem majF_zeroSum (hRH : RiemannHypothesis) (maj : List (ℕ × ℕ × ℕ))
    (hσ : ∀ c ∈ maj, 1000 ≤ c.2.1) {m h : ℝ} (hm : 0 < m) (hh : 0 < h) (hε : h / m ≤ 1 / 800) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} => (analyticOrderNatAt xiZeta ρ : ℝ) *
      majF maj ((ρ : ℂ).im * h / (2 * m))) ∧
    ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
      majF maj ((ρ : ℂ).im * h / (2 * m)) ≤ majZ maj m h := by
  induction maj with
  | nil => simp [majF, majZ]
  | cons c cs ih =>
    obtain ⟨ihS, ihle⟩ := ih (fun d hd => hσ d (List.mem_cons_of_mem _ hd))
    obtain ⟨C, Sg, Tu⟩ := c
    have hSg : (1000 : ℝ) ≤ Sg := by exact_mod_cast hσ _ (List.mem_cons_self ..)
    set σ : ℝ := (Sg : ℝ) / NN
    set τ : ℝ := (Tu : ℝ) / NN
    set S := 2 * m * σ / h with hSdef
    set T := 2 * m * τ / h
    have hS : 3 / 2 < S := by
      have hmh : 800 ≤ m / h := by
        rw [le_div_iff₀ hh]; rw [div_le_iff₀ hm] at hε; linarith
      have hσ0 : (1 / 1000 : ℝ) ≤ σ := by
        simp only [σ]; rw [le_div_iff₀ hNN]; norm_num [NN] at hSg ⊢; linarith
      have : S = 2 * σ * (m / h) := by rw [hSdef]; ring
      rw [this]; nlinarith
    obtain ⟨s1, l1⟩ := shift_zeroSum_le hRH (T := T) hS
    obtain ⟨s2, l2⟩ := shift_zeroSum_le hRH (T := -T) hS
    rw [Lc_neg] at l2
    have hcoef : (0 : ℝ) ≤ (C : ℝ) / KC := by positivity
    have e : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) *
        majF ((C, Sg, Tu) :: cs) ((ρ : ℂ).im * h / (2 * m))
        = (C : ℝ) / KC * ((analyticOrderNatAt xiZeta ρ : ℝ) * (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2))
            + (analyticOrderNatAt xiZeta ρ : ℝ) * (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - -T) ^ 2)))
          + (analyticOrderNatAt xiZeta ρ : ℝ) * majF cs ((ρ : ℂ).im * h / (2 * m)) := by
      intro ρ
      simp only [majF, List.map_cons, List.sum_cons]
      rw [lor_eq_shift hm hh, show (ρ : ℂ).im * h / (2 * m) + τ = (ρ : ℂ).im * h / (2 * m) - (-τ) by ring,
        lor_eq_shift hm hh]
      have : 2 * m * -τ / h = -T := by simp only [T]; ring
      rw [this]
      ring
    have hsum : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
        (C : ℝ) / KC * ((analyticOrderNatAt xiZeta ρ : ℝ) * (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2))
            + (analyticOrderNatAt xiZeta ρ : ℝ) * (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - -T) ^ 2))) :=
      (s1.add s2).mul_left _
    refine ⟨?_, ?_⟩
    · simp_rw [e]; exact hsum.add ihS
    · simp_rw [e]
      rw [hsum.tsum_add ihS, tsum_mul_left, s1.tsum_add s2]
      simp only [majZ, List.map_cons, List.sum_cons] at ihle ⊢
      have : (C : ℝ) / KC * (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ)
            * (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - T) ^ 2))
          + ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ)
            * (S ^ 2 / (S ^ 2 + ((ρ : ℂ).im - -T) ^ 2)))
          ≤ (C : ℝ) / KC * (2 * S * (Lc S T + 1 / 40)) := by
        apply mul_le_mul_of_nonneg_left _ hcoef; linarith
      linarith

end Cramer.Shift
