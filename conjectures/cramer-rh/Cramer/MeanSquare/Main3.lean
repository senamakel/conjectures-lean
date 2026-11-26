import Cramer.MeanSquare.Asymptotic
import Cramer.MeanSquare.Zeros

/-!
# Cramér's mean-square asymptotic under RH (Round 6 headline theorem)

`logMeanSquare_tendsto` proves `(∫_1^X ((ψ(x) − x)/x)² dx)/log X → Σ_ρ ‖m_ρ/ρ‖²` over the
zeros of erdos-985's `xiZeta`; `zerosEquiv` and `cramerTerm_eq` move the constant to the
Mathlib-only `cramerConstant` of `Cramer/Statement3.lean`.
-/

namespace Cramer

open Cramer.MeanSq

/-- **Cramér (1922)**; Montgomery–Vaughan Theorem 13.6 / Exercise 13.1.1.3: under RH,
`∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X` with `c₁ = Σ_ρ m_ρ/|ρ|²` (zeros counted with
multiplicity), and the series for `c₁` converges. -/
theorem logMeanSquareAsymptotic_of_RH (hRH : RiemannHypothesis) :
    CramerLogMeanSquareAsymptotic := by
  have hfun : cramerTerm = (fun ρ => ‖binv ρ‖ ^ 2) ∘ zerosEquiv := funext cramerTerm_eq
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (zerosEquiv.summable_iff).2 (binv_summable hRH)
  · have hc : cramerConstant = ∑' ρ, ‖binv ρ‖ ^ 2 := by
      rw [cramerConstant, hfun]
      exact zerosEquiv.tsum_eq (fun ρ => ‖binv ρ‖ ^ 2)
    rw [hc]
    exact logMeanSquare_tendsto hRH

end Cramer
