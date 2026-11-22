import Robin.Defs

/-!
# Mertens' constant is `γ`

If `Σ_{p ≤ x} −log(1 − 1/p) − log log x` converges, its limit is `γ`. Proof: for `s > 1`,
`(s−1)∫₁^∞ P(t) t^{−s} dt = Σ_p c_p p^{1−s} = log ζ(s) + o(1)`, `log((s−1)ζ(s)) → 0`, and
Mathlib's `eulerMascheroniConstant_eq_neg_integral_log_log` gives
`(s−1)∫₁^∞ log log t · t^{−s} dt = −γ − log(s−1)`; an Abelian argument finishes.
-/

namespace Robin

open Filter Topology Real

theorem mertens_const_eq_gamma {C : ℝ}
    (h : Tendsto (fun x : ℝ => primeSum cp x - Real.log (Real.log x)) atTop (𝓝 C)) :
    C = Real.eulerMascheroniConstant := by
  sorry

end Robin
