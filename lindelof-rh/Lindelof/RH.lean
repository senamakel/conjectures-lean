import Lindelof.Statement
import Erdos985.Analytic.Principal.Bounds.Xi

/-!
# Step 1: RH in usable forms

* `riemannZeta_ne_zero_of_RH`, `riemannZeta₁_ne_zero_of_RH`: no zeros right of the critical line.
* `xiZeta_zero_re_of_RH`: every zero of `ξ` lies on the critical line.
-/

namespace Lindelof

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux

/-- RH: `ζ` has no zeros with `Re s > 1/2` (other than the junk value at the pole). -/
theorem riemannZeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro h
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    simp at hs
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have := hRH s h htriv hs1
  linarith

/-- RH: the entire function `ζ₁(s) = (s - 1) ζ(s)` has no zeros with `Re s > 1/2`. -/
theorem riemannZeta₁_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; simp [riemannZeta₁_one]
  · intro h
    apply riemannZeta_ne_zero_of_RH hRH hs hs1
    rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero]

/-- RH: `ξ` has no zeros with `Re s > 1/2`. -/
theorem xiZeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    xiZeta s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; rw [xiZeta_one] at h; norm_num at h
  rw [xiZeta_eq hs0 hs1] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd h hs1'
    · exact h
  exact riemannZeta_ne_zero_of_RH hRH hs hs1
    (by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div])

/-- RH: every zero of `ξ` has real part `1/2`. -/
theorem xiZeta_zero_re_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  have h1 : ¬ 1 / 2 < ρ.re := fun h => xiZeta_ne_zero_of_RH hRH h hρ
  have h2 : ¬ 1 / 2 < (1 - ρ).re := fun h =>
    xiZeta_ne_zero_of_RH hRH h (by rw [xiZeta_one_sub]; exact hρ)
  simp only [sub_re, one_re] at h2
  linarith

end Lindelof
