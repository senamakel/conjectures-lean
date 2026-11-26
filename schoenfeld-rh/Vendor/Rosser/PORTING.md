# Porting log: Lean v4.35.0 / Mathlib v4.35.0 to Lean v4.36.0 / Mathlib fc4f59e5

The 216 vendored files were copied unchanged from their sources (see `README.md`), apart from
the two-line provenance comment added at the top of every file. 188 files compile at this
repository's pin with no other change. The 28 files below needed edits. Every edit is a proof
repair after Mathlib API drift; no statement (`theorem`/`lemma`/`def` signature) was changed,
no hypothesis was added, and no `sorry`, `axiom`, `opaque` or `native_decide` was introduced.

The recurring causes:

* **Set-valued filter relations.** Mathlib (2026-08-14) split `=ᶠ`/`≤ᶠ` on sets into
  `Filter.EventuallyEqSet` and `Filter.EventuallySubset`, so `ae_eq_refl` and
  `LE.le.eventuallyLE` no longer apply to sets, and set-builder membership such as
  `s ∈ {b | 0 < b.re}` or `s ∈ A ∩ B` is no longer unfolded during unification.
* **Higher-order unification through real numerals.** `Continuous.div (by fun_prop) …` and
  similar calls now sometimes solve the numerator or denominator metavariable by unfolding
  `ℝ` to its Cauchy-sequence structure, which `fun_prop` and `positivity` cannot handle, or
  time out in `whnf`. The fix is to name the function, `(f := …)` / `(g := …)`.
* **API changes.** `AnalyticOnNhd.circleAverage_log_norm` dropped its radius argument;
  `Filter.diff_mem` is now `Filter.sdiff_mem`.
* **Heartbeats.** One declaration needed `set_option maxHeartbeats 1000000 in`.

| File | Change |
|---|---|
| `RSBounds/BacklundJensen.lean` | Mathlib's `AnalyticOnNhd.circleAverage_log_norm` no longer takes the radius-nonzero argument: dropped `hR.ne'` |
| `RSBounds/BacklundPairedJensen.lean` | same Jensen API change, twice |
| `RSBounds/BacklundReflection.lean` | three `DifferentiableAt` / `logDeriv` steps re-elaborated: `hf.const_cpow`, explicit `DifferentiableAt.comp (g := Complex.Gamma)`, `simp only [Pi.div_def, Pi.mul_def]` in place of two `change` |
| `TernaryGoldbach/Explicit/RectResidue.lean` | `logDeriv g = fun s => deriv g s / g s` by `funext … logDeriv_apply` in place of `rfl`; two `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` calls given the integrand explicitly |
| `TernaryGoldbach/Explicit/MellinRotate.lean` | binder type annotation `(ht : t ∈ Ioo (-(π / 4)) (π / 4))` |
| `TernaryGoldbach/Explicit/Digamma.lean` | two `ContinuousAt.div` calls given the numerator `(f := …)` explicitly |
| `RSBounds/IEANTNGamma/Recurrence.lean` | `simpa using h` replaced by `rw [Complex.norm_natCast] at h; exact (by linarith : …)` (simp now rewrites `‖·‖` on `ℂ` to `√normSq`) |
| `RSBounds/BacklundHalfStrip.lean` | binder type annotation in a `DiffContOnCl.mono` argument |
| `RSBounds/BacklundStripNormalizer.lean` | continuity of `u ↦ 1/(1+u²)` by explicit `Continuous.div` (the unifier had unfolded the real numerals) |
| `TernaryGoldbach/Prelim/PNTMertens.lean` | `ae_eq_refl _` on sets → `Filter.EventuallyEqSet.rfl` (Mathlib split set-valued `=ᶠ` into `EventuallyEqSet`); a `mem_nhds` membership stated as `1 ∈ {b : ℂ \| 0 < b.re}`; one trailing `· simp` removed (`convert!` now closes that goal) |
| `TernaryGoldbach/CircleMethod.lean` | `(Set.sdiff_subset …).eventuallyLE` → `.eventuallySubset` (same Mathlib split) |
| `Zeta23/Analytic/RectangleLogDeriv.lean` | `apply Filter.inter_mem` on a set difference → `exact Filter.sdiff_mem …` |
| `Zeta23/FromPNTPlus/ZetaBounds.lean` | `isOpen_aux`: the set is rewritten (by `rfl`) as an intersection before `IsOpen.inter` |
| `RSBounds/BacklundAnchor.lean` | `set_option maxHeartbeats 1000000 in` on `hasDerivAt_log_anchor` (`whnf` timeout at the default 200000) |
| `RSBounds/BacklundRightArc.lean` | in `convexOn_arcFunction`, two `simpa only [smul_eq_mul, …] using h` replaced by `exact h` (simp now unfolds the real numerals to Cauchy sequences; the terms are definitionally equal) |
| `RSBounds/BacklundDigammaSeriesAdapter.lean` | `GammaSolution.ne_neg_natCast_of_mem (s := z + 1) hz'`: the point is given explicitly |
| `RSBounds/BacklundGammaPhaseArctan.lean` | two `Continuous(On).div` calls given the denominator `(g := …)` explicitly (same numeral unfolding) |
| `TernaryGoldbach/Explicit/Xi.lean` | `isOpen_lt` / `isOpen_ne` given their constants and the membership stated with `show` (set-builder membership is no longer unfolded by unification) |
| `RSBounds/BacklundZetaBoundary.lean` | in `zeta_second_order_remainder`, the closing `convert hh using 1; congr 1; ring` (a `whnf` timeout in `congr 1`) replaced by `refine Eq.trans_le ?_ hh; refine congrArg (fun z : ℂ => ‖z‖) ?_; ring` |
| `RSBounds/BacklundGammaPhasePrimitive.lean` | `by positivity` for `0 < N + a` replaced by `add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) ha` |
| `RSBounds/BacklundDigammaStirling.lean` | two `ContinuousOn.div (by fun_prop) (by fun_prop)` given `(f := …) (g := …)` explicitly (`whnf` timeouts) |
| `TernaryGoldbach/Explicit/XiPartial.lean` | continuity of `v ↦ (1 − v − s)⁻¹` by `ContinuousAt.inv₀ (f := fun v => 1 - v - s) (by fun_prop)`, and the now-unneeded `simp only … at h` dropped (`whnf` timeout) |
| `RSBounds/BacklundGammaPhaseEstimate.lean` | `Continuous.div` given `(f := …) (g := …)` explicitly (numeral unfolding) |
| `RSBounds/BacklundCountPole.lean` | four `continuous_const.div` calls given the denominator `(g := …)` explicitly (numeral unfolding, one `whnf` timeout) |
| `RSBounds/BacklundGammaModulusHorizontal.lean` | `GammaSolution.ne_neg_natCast_of_mem (s := …)`: the point is given explicitly |
| `RSBounds/BacklundCountMultiplicity.lean` | `isOpen_lt` / `isOpen_ne` given their constants and the membership stated with `show` |
| `RSBounds/BacklundZetaPhase.lean` | in `hasDerivAt_zeta_horiz`, `HasDerivAt.scomp` given `(g₁ := riemannZeta) (h := …)` and the `smul` removed with `rw [one_smul] at h` (`whnf` timeout) |
| `RSBounds/BacklundCountIdentity.lean` | four `continuous_const.div` calls given the denominator `(g := …)` explicitly (`whnf` timeouts); one `Ioi` membership stated with `show (0 : ℝ) < σ` |
