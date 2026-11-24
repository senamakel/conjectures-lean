import Speiser.Statement
import Speiser.Xi
import Speiser.Gamma

/-!
# RH ⇒ `ζ'(s) ≠ 0` for `0 < Re s < 1/2`, `|Im s| ≥ 8`

Suppose `ζ'(s) = 0` there. RH gives `ζ(s) ≠ 0` (`Re s ≠ 1/2`), hence `ξ(s) ≠ 0`, and
`ξ'/ξ(s) = 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2)` (`Speiser.Xi`). The left side has real
part `≤ 0` (Hadamard, under RH); the right side has real part `> 0` (`Speiser.Gamma`).
-/

open Complex Erdos985.Analytic

namespace Speiser

/-- **Speiser's theorem above height 8, under RH.** -/
theorem speiserAbove_of_RH (hRH : RiemannHypothesis) : SpeiserAbove 8 := by
  intro s h0 h1 ht hd
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hζ : riemannZeta s ≠ 0 := by
    intro h
    have := hRH s h (by
      rintro ⟨n, rfl⟩
      have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [this] at h0
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith) hs1
    linarith
  have hξ : xiZeta s ≠ 0 := by
    rw [xiZeta_eq hs0 hs1]
    refine mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) ?_
    intro hΛ
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have hle := re_logDeriv_xiZeta_nonpos hRH hξ h1.le
  rw [logDeriv_xiZeta_of_deriv_eq_zero h0 hs1 hζ hd] at hle
  have := re_archimedean_pos h0 h1.le ht
  linarith

/-- The full target, given the bounded region `|Im s| < 8` (tier H: the input that the
literature settles numerically). -/
theorem speiser_of_RH_of_below (hRH : RiemannHypothesis) (hB : SpeiserBelow 8) :
    SpeiserStatement :=
  speiserStatement_of_above_of_below (speiserAbove_of_RH hRH) hB

end Speiser
