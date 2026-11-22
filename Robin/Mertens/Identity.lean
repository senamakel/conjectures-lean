import Robin.Mertens.Abelian
import Robin.Mertens.Identity.Abel

/-!
# Mertens' third theorem with an explicit remainder

If `θ(t) − t = O(t^{3/4})`, then for `x ≥ 2`
`Σ_{p≤x} c_p = γ + log log x + (θ(x) − x)/(x log x) − ∫_x^∞ (θ(t) − t) w(t) dt − Σ_{p>x}(c_p − 1/p)`
(Abel summation for `Σ 1/p`; the constant is identified by `mertens_const_eq_gamma`).
We keep the inequality obtained by dropping the last (nonnegative) sum.
-/

namespace Robin

open Filter Topology Real Chebyshev MeasureTheory Set

theorem mertens_RH (hθ : ∃ C, ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4))
    {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun t => (θ t - t) * wM t) (Set.Ioi x) ∧
    primeSum cp x ≤ Real.eulerMascheroniConstant + Real.log (Real.log x)
      + (θ x - x) / (x * Real.log x) - ∫ t in Set.Ioi x, (θ t - t) * wM t := by
  obtain ⟨C, hC⟩ := hθ
  refine ⟨integrableOn_err hC hx, ?_⟩
  -- `primeSum cp X − log log X = D₁(x) + Σ_{p≤X}(c_p − 1/p) + o(1)` for `X ≥ x`
  have hlim : Tendsto (fun X => primeSum cp X - Real.log (Real.log X)) atTop
      (𝓝 (D1 x + ∑' n, aK n)) := by
    have h1 := ((tendsto_const_nhds (x := D1 x)).add tendsto_primeSum_aK).add
      (tendsto_err_div hC) |>.sub (tendsto_integral_err hC)
    rw [add_zero, sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop x] with X hX
    rw [← D1_eq hC hx hX]
    unfold D1; rw [primeSum_cp_split]; ring
  have hγ := mertens_const_eq_gamma hlim
  have hle := primeSum_aK_le x
  have hx' : primeSum cp x = D1 x + Real.log (Real.log x) + (θ x - x) / (x * Real.log x)
      - (∫ t in Ioi x, (θ t - t) * wM t) + primeSum (fun p => cp p - 1 / (p : ℝ)) x := by
    unfold D1; rw [primeSum_cp_split]; ring
  linarith

end Robin
