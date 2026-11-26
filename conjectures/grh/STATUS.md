# Port status: grh-compact to Lean v4.36.0 / Mathlib fc4f59e5 (paused 2026-11-26)

Source: lsernau/grh-lean, `grh-compact/`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`
(Apache-2.0, Copyright 2026 Anthropic, PBC). Its pin is Lean v4.35.0 / Mathlib 56a00585.
The port was paused on the owner's instruction before it finished. **The package does not build yet.**

## Where it stands

- 106 of 794 modules compile at our pin (`.lake/build` at the time of the pause). The dependency
  graph is narrow at the bottom, so each build pass only exposes the next layer of failures.
- No full cold build has completed, so there is no build time or peak memory, and no
  `#print axioms` output yet. The largest single `lean` process seen used 7.3 GB RSS.
- Grep of `src/` (unchanged by the port): no `sorry`, `axiom`, `opaque`, `native_decide`,
  `implemented_by`, `extern` or `unsafe`.
- Statements: `src/Statements.lean` is word for word riemann-hypothesis `src/Statements.lean`
  (minus the module-system header); `src/Main.lean` proves `riemannHypothesis : RiemannHypothesis`,
  `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`,
  `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`,
  `LFunction_eq_zero_re : DirichletLZerosOnLine`,
  `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`, the same names and
  types as riemann-hypothesis. Switching an `Unconditional/` file is a change of import only.
  Neither file was modified.
- Bridge `GRH/Bridge.lean` and the demo `prime-powers-rh/Unconditional/PrimePowersViaGRHLean.lean`
  (+ `scripts/check-via-grh-lean.sh`) are written but not built (they need `Main`).

## Modified vendored files (34)

All changes are inside proofs except one statement re-spelling:

- STATEMENT RE-SPELLED: `src/Lib/General/Geometry/OpenSubfunctors.lean:104`
  `fieldLocus V ≤ V` -> `fieldLocus (fun K x ↦ x ∈ V K) ≤ V` (same name, same meaning; `Set` is
  now a structure, so a subfunctor's sets are no longer predicates). Needs the owner's sign-off.

The `-- Modified for Lean v4.36.0 / Mathlib fc4f59e5: ...` header lines and the NOTICE list are
not added yet (adding a line shifts the error line numbers the fix-up loop relies on).

```
src/Lib/Adelic/Adeles/AdeleIdempotent.lean
src/Lib/Adelic/Adeles/AdeleTopology.lean
src/Lib/Adelic/QuotientMeasure/Packing.lean
src/Lib/Adelic/Witt/FrameAction.lean
src/Lib/Analytic/PolyaVinogradov/PolyaVinogradov.lean
src/Lib/ClassField/Places/ProfiniteGalois.lean
src/Lib/DiscreteSeries/Bruhat/FloorGroups.lean
src/Lib/DiscreteSeries/CuspKernel/CircleMean.lean
src/Lib/DiscreteSeries/Haar/SkewCoordinates.lean
src/Lib/GLn/SchurModule/Interlacing.lean
src/Lib/GaloisRep/Pseudocharacter/FibreSum.lean
src/Lib/General/Algebra/AdicRingHomExt.lean
src/Lib/General/Analysis/HolomorphicIntegral.lean
src/Lib/General/Combinatorics/Average.lean
src/Lib/General/Geometry/EtaleCharts.lean
src/Lib/General/Geometry/OpenSubfunctors.lean
src/Lib/General/Geometry/ReducedClosure.lean
src/Lib/General/Groups/ValuationPair.lean
src/Lib/General/Groups/VirtualCharacters.lean
src/Lib/General/LinearAlgebra/Base.lean
src/Lib/General/LinearAlgebra/CommonEigenvectors.lean
src/Lib/General/LinearAlgebra/HuaIntegral.lean
src/Lib/General/LinearAlgebra/ValuedMatrix.lean
src/Lib/General/Measure/HaarModulus.lean
src/Lib/General/Measure/SubgroupIntegral.lean
src/Lib/General/NumberTheory/ClassNumberBound.lean
src/Lib/General/NumberTheory/Embeddings.lean
src/Lib/General/NumberTheory/QuadField.lean
src/Lib/General/Topology/LocalDefs.lean
src/Lib/PadicHodge/PeriodRings/Ainf.lean
src/New/Core/ModuleIndex.lean
src/New/Selmer/RibetCramer.lean
src/New/TwistedHecke/FrobeniusFactors.lean
src/New/TwistedHecke/InterlacingCone.lean
```

`CircleMean.lean` and `FibreSum.lean` are edited but not yet confirmed by a whole-file check.

## Remaining errors (last build pass, plus fix-up reports)

| File | Error |
|---|---|
| `Lib/ClassField/GaloisCohomology/DiscreteUnits.lean:171` | `fun_prop` cannot prove continuity of `Prod.map (fun x ↦ ⇑u ∘ x) …` |
| `Lib/ClassField/Places/Places.lean:124-145` | mismatches on `le_nhds_of_unique_clusterPt` / `IsPlaceOver.centrePrime_liesOver`; ambiguous `ext`; missing `TopologicalSpace (Ideal _)`, `ContinuousSMul Γ (𝓞 Ω)` |
| `Lib/Cyclotomic/Voronoi/StickelbergerInteger.lean:21` | whnf heartbeat timeout in `smul_bernoulli_mem_lifts` (`monomial _` degree no longer inferred); the kernel "unknown constant" at line 70 follows. Candidate fix in the pattern list, unverified |
| `Lib/General/Measure/Place.lean:231` | unknown constant `Membership.mem.intro` / `Set.Mem.intro`; simp max recursion at 232 |
| `Lib/Analytic/DirichletTheta/MellinTheta.lean:37,163,172` | set-membership vs predicate (`x ∈ {z | 0 < z.re}`); a `rw` under an image of `fun i ↦ (q*i)⁻¹` |
| `Lib/General/NumberTheory/QuadFieldSplitting.lean:33` | `w.q` (absNorm) no longer defeq to `Nat.card`: rewrite with `absNorm_eq_natCard` |

Everything downstream of these (about 680 modules) has not been elaborated yet. No kernel
non-termination was seen: every timeout so far was an elaboration heartbeat limit and went
away with a local fix.

## Recurring fix patterns

Known breakage patterns (Lean v4.35/Mathlib 56a00585 -> v4.36/fc4f59e5), append yours:
- Root-level FunLike lemmas now shadow namespaced ones under `open`: one_apply, mul_apply, ext_iff -> qualify (Matrix.one_apply, Matrix.mul_apply, Polynomial.ext_iff).
- `Set` is a structure (Set.ofPred / Mem); code treating a set as a predicate breaks; `Subtype.finite` -> `Set.toFinite _`.
- `R[X]` is AddMonoidAlgebra: `Polynomial.coeff` constant gone (`AddMonoidAlgebra.coeff`).
- `Ideal.jacobson ⊥` vs `Ring.jacobson R`: `Ideal.jacobson_bot`.
- `absNorm` no longer defeq to Nat.card of quotient: `absNorm_eq_natCard`.
- bare `@[simps!]` may generate nothing: `@[simps! apply]`.
- `integrableOn_const` not simp; `Set.univ_inter` sometimes needed.
- grind may need extra splits or lemma hints (map_add, dotProduct_zero ...).
- Tactic continuation lines inside `by` need deeper indentation than before.
Policy: proofs only; statement re-spelling only when it no longer typechecks for a representational reason (same meaning, same name), reported as STATEMENT RE-SPELLED. Never touch src/Main.lean, src/Statements.lean.
- `natDegree_X_pow_sub_C` now takes `a` explicitly: `natDegree_X_pow_sub_C _`.
- `↥s` for a Set is no longer defeq to a plain Subtype: `mk_set_le` on a Subtype (e.g. CauSeq) -> `mk_subtype_le`.
- `⊆` / `MapsTo` no longer compose by `.trans` as raw functions: write `fun x hx ↦ hs (h hx)`.
- Ambiguity with new root lemmas under `open Nat`/`open ArithmeticFunction`: `le_div_iff_mul_le` -> `Nat.le_div_iff_mul_le`, `one_apply` -> `ArithmeticFunction.one_apply`.
- `FinPlace.q` (= absNorm) no longer unfolds to Nat.card: `rw [FinPlace.q, FinPlace.q, absNorm_eq_natCard, absNorm_eq_natCard]` first.
- Elaboration order: auto-param defaults (`:= by bound`) no longer see metavariables solved by a sibling `by` block; pass the implicit args explicitly (`(K := ...) (d := ...)`). `by tauto` no longer finds `Pairwise -> Set.Pairwise`: use `hf.set_pairwise _`.
- Anonymous-constructor carriers given as a predicate (`⟨⟨IsChar, ...⟩⟩`) or as `_` inferred by higher-order unification now fail ("expected type `?m.1 a` is not an inductive type"): write the carrier as `{x | P x}`, spelled out explicitly when it was inferred (FibreSum). Annotate binder types inside it.
- `V.1` of a Subfunctor is `∀ U, Set (X U)`, no longer a predicate: `fieldLocus V.1` -> `fieldLocus fun K x ↦ x ∈ V K`; `V.rec (by tauto)` -> `fun _ _ e _ φ _ ↦ V.map φ e` (EtaleCharts).
- `mapsTo_span` with `(·.comp p)`: give `(s := {f | P f}) (t := ...)` and go through `Set.mem_setOf` (VirtualCharacters).
- Simp-normal-form of `IsChar`-style `@[simps!]`: see InterlacingCone (`@[simps! apply]`; then proofs that relied on the old ite-smul shape need rewriting).
- `RCLike.exists_norm_eq_mul_self _`: unifying `_` unfolds real subtraction into `Real.cauchy`; give the argument explicitly (FrobeniusFactors).
- Polynomial `lifts` witness `⟨monomial _ c, funext ...⟩`: degree no longer inferred and funext no longer applies; use `monomial n`, then prove the equation by folding into `C` (StickelbergerInteger, unfinished).
- `ζ.mono` composed with `∘` no longer unifies: `fun _ hg ↦ ... (measure_mono hg)` (HaarModulus).

## Next steps

1. Fix the six files above with `bin/chk`-style single-file elaboration
   (`lake env lean --tstack=400000 -DmaxHeartbeats=4000000 -DmaxSynthPendingDepth=3 -DautoImplicit=false -DrelaxedAutoImplicit=false <file>`).
2. Re-run `nice -n 10 lake build Lib New Main GRH` (LEAN_NUM_THREADS=16 on the shared box),
   fix the next frontier, repeat until it builds. Work in batches of 4 to 5 files per agent.
3. Then: add the `-- Modified for ...` header to each changed file and list them in NOTICE;
   do a cold build (`rm -rf .lake/build`) and record wall time and peak memory; run
   `lake env lean scripts/PrintAxioms.lean`; build `GRH.Bridge`; run
   `conjectures/prime-powers-rh/scripts/check-via-grh-lean.sh` and paste its axioms.
4. Write `README.md` in the house shape (vendored copy at the commit above, five statements,
   axioms, build cost, modified files, credits per NOTICE/ATTRIBUTION, and the source's review
   status: "The proof has passed machine checks only ... No mathematician has read it through").
5. Get the owner's sign-off on the one re-spelled statement.
