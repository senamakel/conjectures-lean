import Ramanujan.Analytic
import Schoenfeld.Rosser

/-!
# Main theorems (conditional on RH)

* `ramanujan_of_RH`: under RH, Ramanujan's inequality `π(x)² < (e x/log x) π(x/e)` holds for every
  real `x ≥ e⁴⁰ ≈ 2.354·10¹⁷`. RH enters through Schoenfeld's bound
  `|π(x) − li(x)| < √x log x/(8π)` (`Schoenfeld.schoenfeldPi_of_RH`, schoenfeld-rh).
* `ramanujan_of_RH_of_verified`: under RH, and given the finite range
  `[38,358,837,683, e⁴⁰]` as a cited hypothesis (`RamanujanVerifiedRange`), Dudek–Platt's
  Theorem 1.3 in the form `RamanujanStatement` (every real `x ≥ 38,358,837,683`).
-/

namespace Ramanujan

/-- **Ramanujan's inequality under RH for `x ≥ e⁴⁰`.** -/
theorem ramanujan_of_RH (hRH : RiemannHypothesis) : RamanujanInequalityFrom (Real.exp 40) :=
  ramanujan_of_schoenfeldPi (Schoenfeld.schoenfeldPi_of_RH hRH)

/-- `RamanujanVerifiedRange` and Ramanujan's inequality for `x ≥ X₀` give the full statement,
for any `X₀ ≤ e⁴⁰`. -/
theorem ramanujanStatement_of_verified_of_from {X₀ : ℝ} (hX₀ : X₀ ≤ Real.exp 40)
    (hV : RamanujanVerifiedRange) (h : RamanujanInequalityFrom X₀) : RamanujanStatement := by
  intro x hx
  rcases le_or_gt x (Real.exp 40) with h' | h'
  · exact hV x hx h'
  · exact h x (by linarith)

/-- **Dudek–Platt's Theorem 1.3 under RH, given the finite range.** Ramanujan's inequality for
every real `x ≥ 38,358,837,683`, from RH and the cited computation `RamanujanVerifiedRange`
for `38,358,837,683 ≤ x ≤ e⁴⁰`. -/
theorem ramanujan_of_RH_of_verified (hRH : RiemannHypothesis) (hV : RamanujanVerifiedRange) :
    RamanujanStatement :=
  ramanujanStatement_of_verified_of_from le_rfl hV (ramanujan_of_RH hRH)

end Ramanujan
