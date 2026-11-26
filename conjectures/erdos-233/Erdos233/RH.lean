import Erdos233.Basic

/-!
# Step 1. RH places every zero of `ξ` on the critical line
-/

namespace Erdos233

open Complex Erdos985.Analytic

theorem zero_re_of_RH (hRH : RiemannHypothesis) (ρ : Zeros) : (ρ : ℂ).re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := xiZeta_zero_re_mem ρ.2
  have hs0 : (ρ : ℂ) ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hs1 : (ρ : ℂ) ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hξ := ρ.2
  rw [xiZeta_eq hs0 hs1] at hξ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rcases mul_eq_zero.mp hξ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd (sub_eq_zero.mp h) hs1
    · exact h
  have hζ : riemannZeta ρ = 0 := by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  refine hRH ρ hζ ?_ hs1
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  simp at this
  rw [this] at h0
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

end Erdos233
