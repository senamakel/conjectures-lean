import Robin.Defs

/-!
# The integrated Chebyshev function `Ψ₁` and pointwise bounds for `ψ`

From `|Ψ₁(m) − m²/2| ≤ m^{3/2}/20 + 3m` at natural `m` (which is `BachBound` multiplied by `m`)
we get the bound for real `t`, and pointwise bounds for `ψ` by monotone differencing:
`(Ψ₁(s) − Ψ₁(s−h))/h ≤ ψ(s) ≤ (Ψ₁(s+h) − Ψ₁(s))/h`.
-/

namespace Robin

open ArithmeticFunction Real Chebyshev

/-- The hypothesis in the form "Ψ₁ at integers". (`BachBound` multiplied by `m`.) -/
def Psi1NatBound : Prop :=
  ∀ m : ℕ, 1 ≤ m → |psi1 m - (m : ℝ) ^ 2 / 2| ≤ (m : ℝ) ^ ((3 : ℝ) / 2) / 20 + 3 * m

theorem psi1_continuous : Continuous psi1 := by
  sorry

/-- `Ψ₁` has right derivative `ψ(t)` everywhere. -/
theorem psi1_hasDerivWithinAt (t : ℝ) : HasDerivWithinAt psi1 (ψ t) (Set.Ioi t) t := by
  sorry

theorem psi1_bound (hB : Psi1NatBound) {t : ℝ} (ht : 16 ≤ t) :
    |psi1 t - t ^ 2 / 2| ≤ t ^ ((3 : ℝ) / 2) / 20 + 4 * t := by
  sorry

theorem psi_upper (hB : Psi1NatBound) {s : ℝ} (hs : 1000 ≤ s) : ψ s ≤ s + s ^ ((3 : ℝ) / 4) := by
  sorry

theorem psi_lower (hB : Psi1NatBound) {s : ℝ} (hs : 1000 ≤ s) : s - s ^ ((3 : ℝ) / 4) ≤ ψ s := by
  sorry

/-- `θ(t) − t = O(t^{3/4})`, the input for Mertens' theorem. -/
theorem theta_sub_bound (hB : Psi1NatBound) :
    ∃ C, ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4) := by
  sorry

end Robin
