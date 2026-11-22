import Robin.Mertens.Abelian

/-!
# Mertens' third theorem with an explicit remainder

If `θ(t) − t = O(t^{3/4})`, then for `x ≥ 2`
`Σ_{p≤x} c_p = γ + log log x + (θ(x) − x)/(x log x) − ∫_x^∞ (θ(t) − t) w(t) dt − Σ_{p>x}(c_p − 1/p)`
(Abel summation for `Σ 1/p`; the constant is identified by `mertens_const_eq_gamma`).
We keep the inequality obtained by dropping the last (nonnegative) sum.
-/

namespace Robin

open Filter Topology Real Chebyshev

theorem mertens_RH (hθ : ∃ C, ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4))
    {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun t => (θ t - t) * wM t) (Set.Ioi x) ∧
    primeSum cp x ≤ Real.eulerMascheroniConstant + Real.log (Real.log x)
      + (θ x - x) / (x * Real.log x) - ∫ t in Set.Ioi x, (θ t - t) * wM t := by
  sorry

end Robin
