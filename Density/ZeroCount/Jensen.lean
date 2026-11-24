import Density.Statement

/-!
# Counting zeros with Jensen's inequality

`Density.zeroCountOn_le_of_jensen`: if `f` is analytic on `closedBall c R`, `f c ≠ 0` and
`‖f‖ ≤ M` on the circle `sphere c R`, then for `0 < r < R` the multiplicity-weighted number of
zeros of `f` in any `S ⊆ closedBall c r` is at most `log (M / ‖f c‖) / log (R / r)`.

This is Mathlib's `AnalyticOnNhd.sum_divisor_le` (Jensen's inequality), restated for
`Complex.zeroCountOn`.
-/

open Complex Metric Set

namespace Density

/-- The divisor of an analytic function at a point of its domain is the natural-number order
`analyticOrderNatAt` (both are `0` where the order is infinite). -/
lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {z : ℂ} (hz : z ∈ U) : MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, analyticOrderNatAt]
  cases analyticOrderAt f z with
  | top => simp
  | coe n => simp

/-- **Jensen's inequality for `zeroCountOn`.** -/
theorem zeroCountOn_le_of_jensen {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hM : 1 ≤ M) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) {S : Set ℂ} (hS : S ⊆ closedBall c r) :
    (zeroCountOn f S : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [abs_of_pos hR]
  have J := AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M) (by rwa [abs_of_pos hr])
    (by rwa [abs_of_pos hr, abs_of_pos hR]) hM hf' hfc (by rwa [abs_of_pos hR])
  rw [abs_of_pos hr] at J
  set D := MeromorphicOn.divisor f (closedBall c r)
  have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR.le)
  have hDfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall c r)
  set F := hDfin.toFinset
  set g : ℂ → ℕ := fun s => analyticOrderNatAt f s
  -- every point of `S` with a nonzero order lies in `F`
  have hsub : S ∩ Function.support g ⊆ (F : Set ℂ) := by
    intro s ⟨hsS, hs⟩
    simp only [Set.Finite.coe_toFinset, Function.mem_support, F]
    rw [divisor_eq_analyticOrderNatAt hfr (hS hsS)]
    exact_mod_cast hs
  have hfin : (S ∩ Function.support g).Finite := F.finite_toSet.subset hsub
  have h1 : zeroCountOn f S ≤ ∑ s ∈ F, g s := by
    unfold zeroCountOn
    rw [finsum_mem_eq_sum g hfin]
    exact Finset.sum_le_sum_of_subset (fun x hx => hsub (by simpa using hx))
  have h2 : (∑ᶠ u, D u) = ∑ u ∈ F, (g u : ℤ) := by
    rw [finsum_eq_sum_of_support_subset D (s := F) (by simp [F])]
    refine Finset.sum_congr rfl fun u hu => ?_
    have huD : u ∈ Function.support D := by simpa [F] using hu
    exact divisor_eq_analyticOrderNatAt hfr (D.supportWithinDomain huD)
  have h3 : ((∑ᶠ u, D u : ℤ) : ℝ) = ((∑ s ∈ F, g s : ℕ) : ℝ) := by
    rw [h2]; push_cast; rfl
  calc (zeroCountOn f S : ℝ) ≤ ((∑ s ∈ F, g s : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ((∑ᶠ u, D u : ℤ) : ℝ) := h3.symm
    _ ≤ _ := J

end Density
