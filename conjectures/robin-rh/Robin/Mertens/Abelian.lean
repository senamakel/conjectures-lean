import Robin.Defs
import Robin.Mertens.Abelian.Limit
import Robin.Mertens.Abelian.Zeta

/-!
# Mertens' constant is `γ`

If `Σ_{p ≤ x} −log(1 − 1/p) − log log x` converges, its limit is `γ`. Proof: for `s > 1`,
`(s−1)∫₁^∞ P(t) t^{−s} dt = Σ_p c_p p^{1−s} = log ζ(s) + o(1)`, `log((s−1)ζ(s)) → 0`, and
Mathlib's `eulerMascheroniConstant_eq_neg_integral_log_log` gives
`(s−1)∫₁^∞ log log t · t^{−s} dt = −γ − log(s−1)`; an Abelian argument finishes.
-/

namespace Robin

open Filter Topology Real MeasureTheory Set

theorem mertens_const_eq_gamma {C : ℝ}
    (h : Tendsto (fun x : ℝ => primeSum cp x - Real.log (Real.log x)) atTop (𝓝 C)) :
    C = Real.eulerMascheroniConstant := by
  set F : ℝ → ℝ := fun x => primeSum cp x - Real.log (Real.log x) with hFdef
  have hint : ∀ s : ℝ, 1 < s → IntegrableOn (fun t => F t * t ^ (-s)) (Ioi 1) := by
    intro s hs
    refine ((mellin_primeSum hs).1.sub (integrableOn_log_log_mul_rpow hs)).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    simp [F, sub_mul]
  have hA := abelian_limit h hint
  have hB : Tendsto (fun s => (s - 1) * ∫ t in Ioi 1, F t * t ^ (-s)) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
    have hlim := (tendsto_tsum_aP_sub_bZ.add tendsto_log_zeta_add_log).add_const
      Real.eulerMascheroniConstant
    rw [add_zero, zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : (1:ℝ) < s := hs
    have hP := mellin_primeSum hs
    have hLL := integrableOn_log_log_mul_rpow hs
    have e1 : ∫ t in Ioi 1, F t * t ^ (-s)
        = (∫ t in Ioi 1, primeSum cp t * t ^ (-s))
          - ∫ t in Ioi 1, Real.log (Real.log t) * t ^ (-s) := by
      rw [← integral_sub hP.1 hLL]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp [F, sub_mul]
    have hγ := Real.eulerMascheroniConstant_eq_neg_integral_log_log hs
    have hdiff : Summable fun k : ℕ => aP k * (k : ℝ) ^ (1 - s) - bZ s k :=
      Summable.of_norm_bounded ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2)
        (fun k => term_bound hs.le k)
    have hb : Summable fun k : ℕ => bZ s k := by
      refine ((summable_aP_mul_rpow hs).sub hdiff).congr fun k => ?_
      ring
    have e2 := (summable_aP_mul_rpow hs).tsum_sub hb
    have e3 := log_riemannZeta_re_eq_tsum hs
    rw [e2, ← e3, e1, mul_sub, hP.2]
    linarith
  exact tendsto_nhds_unique hA hB

end Robin
