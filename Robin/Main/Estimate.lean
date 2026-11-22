import Robin.RH.Psi1
import Robin.Mertens.Identity

/-!
# The analytic estimate for `x ≥ e^{30}`

`ε(x − θ(x)) + Σ_{p≤x} c_p − Σ_{p≤x} min(1/p², ε log p) < γ + log log x`, from
Mertens with remainder, the bound for `Ψ₁` (integration by parts against `w` and `−(d/dt) 1/(t² log t)`),
and `ψ − θ ≤ ψ(√t) + ψ(t^{1/3}) + ψ(t^{1/5})`.
-/

namespace Robin

open Filter Topology Real Chebyshev

theorem main_estimate (hB : Psi1NatBound) {x : ℝ} (hx : Real.exp 30 ≤ x) :
    epsR x * (x - θ x) + primeSum cp x - gainSum x
      < Real.eulerMascheroniConstant + Real.log (Real.log x) := by
  sorry

end Robin
