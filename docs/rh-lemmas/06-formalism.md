# 06 · `src/Formalism`: what is actually proved there

Repo: `riemann-hypothesis` @ `507a75d91d`. All paths below are relative to
`riemann-hypothesis/src/Formalism/` unless they start with another top-level directory.
I read sources only. Nothing was built.

## 1. Scope and method

**Coverage.** About 15,300 `.lean` files and 2.5M lines, split into 96 sub-libraries plus 7
top-level files (`Statement*.lean`, `DefsOC.lean`, `ZetaRealNonvanish.lean`). The four giants
make up 83% of the files: LocalToGlobal (4,895 files, 791k lines), PeriodIntegrals (3,369 /
369k), SharpRestriction (2,757 / 565k) and HermitianCurvature (1,796 / 408k). The rest of the
code imports Formalism about 25,000 times. Most of those imports go to LocalToGlobal and
SharpRestriction.

`LandauZeroFreeBounds`, `ZeroFreeRegion` and `PeriodIntegrals/ExplicitFormulaCounts` belong to
another agent. They appear here only as dependencies.

**House style, and how I used it.** Almost every sub-library follows one pattern. A
`Statement*.lean` file defines a named `def Foo : Prop := ∀ …`, and a `Final*`, `*Proofs/` or
`*Holds` file then proves `theorem foo : Foo := …`. That makes the statements cheap to survey
without reading proofs. I did four things:

1. **Indexed** every `def X : Prop :=` in Formalism (10,569 of them). For each one I searched the
   whole `src/` tree (149k files) for a theorem of the form `theorem t : X :=`, resolving
   names through the enclosing namespace and the `open` lines. 7,290 of the Props have such a
   closing theorem. The regex misses universe-polymorphic forms (`Foo.{u}`) and signatures
   that span several lines, so treat the count of unproved Props as an over-count. I checked
   those cases by hand for every headline item (for example `ModelUnit.{u}`, `ThmAGen.{u}` and
   `FormalGroupPointsTorsionFree.{u}`).
2. **Filtered** for statements that mention only Mathlib vocabulary. This removes any Prop
   whose body uses an identifier defined anywhere in the repo, apart from a whitelist of names
   that collide with Mathlib. 417 closed Props survive with no internal identifier and about
   90 more with exactly one harmless one. **I read all of those statements.** That pass is
   the basis of the inventory below.
3. **Read fully**: the top-level Formalism files, ZetaNonvanishing (5 files), the Statement
   and Final files of MahlerMeasure, EllipticTorsion, PadicSubsetSums/CentralIdempotents,
   GaloisIrreducibility, LogVandermondeBounds, GaussJetBounds (`Statement.lean`) and
   GL3MeanSquares' top-level and `JacobiCharacterSums/*St.lean`, plus the proof heads of the
   PNT-in-progressions, zero-density and Deuring–Heilbronn chains.
4. **Sampled**: AdmissibleDesigns (`TheoremFromNormalizedOpen.lean`,
   `KernelLengthHigherColumns.lean`), the `D7` and `Ranks` data structures, the GaloisCohomology
   statements and the `Fact`-hypothesis plumbing.

**Not done**: no proof bodies were checked beyond the head of the term. I did not try to
confirm that the theorems actually typecheck. `rg` finds no `sorry`, `axiom`, `opaque` or
`native_decide` anywhere under Formalism.

**Brief anomaly.** `UnitaryGroupMassFormula` and `SiegelLatticeTheory` are not top-level
sub-libraries. They live at `PeriodIntegrals/UnitaryGroupMassFormula` (2,831 files) and
`LocalToGlobal/SiegelLatticeTheory` (1,972 files). I treat them as such below.

## 2. What this subtree actually is

Formalism is the repo's **library of supporting lemmas for an automorphic/arithmetic-geometry
approach to RH**: unitary groups over CM fields, Hermitian lattices and their mass formulas,
theta lifts, p-adic Galois representations with Wach/crystalline lattices, Selmer-type length
bounds and adelic Haar-measure bookkeeping. Most of its weight sits in statements about one
enormous bundled datum, `D7` (`LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:80`).
`D7` holds a CM field `E/F`, rank parameters `Ranks` with about 15 numeric side conditions,
period maps, Hecke-twisted columns and so on, with dozens of compatibility axioms as fields.
Theorems about `D7` are only meaningful if a `D7` exists. The repo has constructors
(`nonempty_D7_of_localGap`, `LocalRingCardinality/SpanPowerMembership.lean:42`, and
`Development/.../AssembleLattice.lean:18`), but I did not check whether their inputs can be
inhabited. Part of the tree also carries hypotheses as instance arguments
(`[Fact ReciprocityTheory.ChartRestriction.T2.Core]`, `[Fact …H0.FinCore]`, in 83
AdmissibleDesigns files and some WachLatticeTwists files). Those are discharged elsewhere from
Artin reciprocity, local Tate duality and the local Euler characteristic
(`Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerLengthBoundAtPoint.lean:29`).

Directory names are a poor guide to content. `MahlerMeasure` contains no Mahler measure:
it covers Mahler's *binomial-coefficient* basis, Gauss norms and Smith form over ℤ_p.
`HermitianCurvature` is mostly Fourier-decay and Markov-type inequalities (namespace
`FourierDecayAlt`). `GL3MeanSquares` is where a genuine unconditional **prime number theorem
in arithmetic progressions with an exceptional-zero term, a Deuring–Heilbronn bound and a
zero-density estimate** live (namespace `HermitianLattices.Ext.PrimesInProgressions`).
`PadicSubsetSums` holds counting of polynomials over finite fields, permutation cycle
statistics and Brauer–Nesbitt (namespace `IrreducibleCountingLemmas`). `EllipticTorsion` is
honest: Weierstrass models, formal groups and integrality of torsion.

The **reusable core** is a layer of roughly 400–500 lemmas stated purely in Mathlib vocabulary.
They are scattered through every sub-library as "helper" Props: classical analytic number
theory (Chebyshev and Mertens bounds, π(x) < 1.26x/log x, PNT in APs, a log-type zero-density
estimate, Deuring–Heilbronn), geometry of numbers (Minkowski's first and second theorems,
Hadamard, Packing, class-number bound), adelic and local-field facts (strong approximation for
𝔾_a, density of F in the finite adeles, local trace duality), representation theory
(Brauer–Nesbitt, central idempotents, Burnside density), p-adic valuations (LTE variants,
Legendre-type bounds) and finite-field counting. Mathlib lacks many of these.

## 3. Inventory (most reusable first)

"Mathlib" means the statement uses only Mathlib objects. Each "proof" location is the theorem
that closes the Prop. All are closed with no visible hypotheses unless noted.

### 3a. Analytic number theory

| Declaration (Prop → proof) | path:line | Statement (paraphrased) | Objects | Classical name | Reuse |
|---|---|---|---|---|---|
| `HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW` → `…PrimesInProgressions.pnt_progressions_relative_weak_holds` | `GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean:30` → `…/PNTFinal.lean:26` | There are constants c₃>0, A₀, C₀ such that for every modulus M with 8∣M: either no exceptional real zero β₁ > 1−1/(8 log M) of a quadratic χ₁ mod M exists, or one is given. For X ≥ 2 with log X ≥ C₀ log M·log log M and gcd(b,M)=1, π(X;M,b) equals (li X − χ₁(b) li(X^β₁))/φ(M) up to a relative error A₀(e^{−c₃ log X/log M} + e^{−√(c₃ log X)}). | Mathlib (`li`, `piAP`, `mainAP` are local but transparent: integral of 1/log, a prime-count filter, an explicit formula) | Page / Gallagher-type uniform PNT in APs with Siegel-zero term (Davenport ch. 20) | **High**. The strongest analytic result in the subtree. 8∣M is harmless (lift q to 8q). |
| `…PrimesInProgressions.LogDensityM` → `logDensityM_proof'` | `…/DeuringHeilbronnM.lean:81` → `…/PNTFinal.lean:22` | Zero-density bound: any set of zeros (χ mod M, ρ) with Re ρ ≥ σ ≥ 1/2, \|Im ρ\| ≤ T, 1-separated in height for each χ, has at most C·(MT)^{A(1−σ)}·log(MT)^B elements. | Mathlib (`IsLZero` = `LFunction χ s = 0`, excluding the pole) | Linnik/Montgomery-type zero density with a log factor | **High** |
| `…PrimesInProgressions.DeuringHeilbronnMB` → `deuring_heilbronn_lossy` | `…/PNTDHBSt.lean:15` → `…/PNTDHB.lean:17` | Given an exceptional zero β₁ of a real χ₁ mod M, every other zero ρ (any χ mod M) with 1−c₀ ≤ Re ρ and \|Im ρ\| ≤ T satisfies 1−Re ρ ≥ c₂·log(c₁/((1−β₁) log(MT)^B))/log(MT). | Mathlib | Deuring–Heilbronn phenomenon (repulsion, "lossy" form) | **High** |
| `…PrimitiveCharacterCasts.ZeroDensityBox` → `ZD.zero_density_box` | `…/CountSt.lean:11` → `…/CountZAll.lean:17` | For Q ≥ 3, the number of primitive characters of conductor ≤ Q with an L-zero in Re s > 1−1/400, \|Im s\| ≤ Q is ≤ C·Q^{1/4}. | Mathlib | Large-sieve zero-density, character-aspect | **High** |
| `…PrimesInProgressions.ExplicitS` → `smoothed_explicit_formula` | `…/DeuringHeilbronnM.lean:57` → `…/PNTExplMain.lean:19` | A smoothed explicit formula for ψ(y,χ), with a finite zero set Z near Re=1, multiplicities, and a local zero-count ≤ C log(M(\|t\|+2)) in unit windows. | Mathlib | Explicit formula (truncated, smoothed) | Med–high. Overlaps the ExplicitFormulaCounts agent. |
| `GL2a2.LogDerivSeries` → `log_deriv_series` | `GL3MeanSquares/PrimeCountAsymptoticInProgressions.lean:17` → `GL3MeanSquares/HookFormulaTorsion/PsiZeroIntegral.lean:525` | For χ ≠ 1, the partial sums ∑_{n≤N} Λ(n)χ(n)/n converge to −L′(1,χ)/L(1,χ). | Mathlib | Convergence of ∑Λχ/n (needs PNT-in-AP strength at s=1) | **High** |
| `GL2a2.PsiZeroConst` → `psi_zero_integral_constant` | same file `:22` → `…PsiZeroIntegral.lean:528` | ∫₁^U (ψ(u)−u)/u² du → −1−γ. | Mathlib | Classical PNT corollary | High |
| `…Ext.PrimesInProgressions.DHHyper` → `deuring_heilbronn_hypergeometric` | `…/DHFinish2Of.lean:42` → `…/PNTDHHyper.lean:118` | For quadratic χ₁ ≠ 1 mod M ≥ 3: ∑_{y<n≤x} (1∗χ₁)(n)/n ≤ \|L(1,χ₁)\| log(x/y) + C·M(log y+1)/√y. | Mathlib | Divisor-sum asymptotics for 1∗χ | Med |
| `…Ext.PrimesInProgressions.DHTuran2` → `turan_power_sum_bound` | `…/DHFinish2Of.lean:16` → `…/TuranPowerSumBound.lean:16` | Turán's second main theorem: for \|zᵢ\| ≤ 1 with one \|zᵢ\| = 1, some k ∈ [m+1, m+An] has \|∑ zᵢ^k\| ≥ (n/(C(m+n)))^{An}. | Mathlib | Turán power-sum method | **High** (Mathlib lacks it) |
| `…DHCauchy` → `deuring_heilbronn_cauchy` | `…/PNTDHSt.lean:27` → `…/PNTDHCauchy.lean:88` | Jensen-type: if f is holomorphic on a closed disc, f(z₀) ≠ 0 and \|f\| ≤ B\|f(z₀)\|, then the zeros in radius r/3 have total multiplicity ≤ log B/log 2, and higher derivatives of −f′/f are controlled near z₀. | Mathlib | Jensen / Landau local lemma | High |
| `PI.DiscFactor`, `PI.DiscLog` → `chk_discFactor`, `chk_discLog` | `PeriodIntegrals/DiscIn.lean:9,19` → `PeriodIntegrals/ExplicitFormulaCounts/AnalyticInputs.lean:12,13` | Weierstrass factorisation on a disc (f = ∏(z−ρ)^m · h with h zero-free); holomorphic logarithm of a zero-free function on a disc. | Mathlib | Standard complex analysis | High |
| `PI.PrimeCountBound` → `prime_count_bound` | `PeriodIntegrals/PrimeCount.lean:13` → `PeriodIntegrals/OrbitalBoundsConclusion/PrimeCount.lean:11` | π(y) < 1.26·y/log y for every real y > 1 (`pr y` = primes ≤ ⌊y⌋). | Mathlib | Rosser–Schoenfeld (1.25506) | **High** |
| `PI.PC.LfUpper`/`LfLower` | `PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PrimeCountBoundOf.lean:20,22` → `…/LogFactorialLe.lean:127` | y log y − y − ½ log y + 9/10 ≤ log⌊y⌋! ≤ y log y − y + ½ log y + 1. | Mathlib | Explicit Stirling | High |
| `PI.PrimeLogOverP`, `QuotientMetricDivisors…PrimeLogSum`, `PieriBlockIdeals…MertensReciprocalElementary`, `ThetaLog4` (several copies) | `PeriodIntegrals/PrimeSums.lean:9`; `MirabolicMackeyTheory/StatementC.lean:24`; `PieriBlockIdeals/MertensReciprocalElementary.lean:298` | Explicit Chebyshev and Mertens bounds: ∑_{p≤Y} log p ≤ Y log 4; ∑_{p≤Y} log p/p ≤ log Y (+ log 4 in some copies); ∑_{p≤y} 1/p ≤ log y; ∑_{p>X} log p/p² ≤ 2.04/X. | Mathlib | Chebyshev, Mertens 1st/2nd (explicit, one-sided) | High |
| `ZetaNonvanishing.mertens_upper`/`mertens_lower` (lemmas) | `ZetaNonvanishing/GzLipschitz.lean:59,90` | log k − 1 ≤ ∑_{n≤k} Λ(n)/n ≤ log k + log 4 + 4. | Mathlib | Mertens' first theorem (explicit) | High |
| `Formalism.MellinSgen` → `mellinSgen` | `DefsOC.lean:16` → `ZetaNonvanishing/MellinSgen.lean:105` | For any a(n) with \|a(n)\| ≤ KΛ(n), the Cesàro sum S_a(x)=∑_{n≤x} a(n)(x/n−1) is measurable, its weighted absolute value is integrable for σ>1, and its Mellin transform is L(a,s)/(s(s−1)) for Re s>1. | Mathlib | Perron/Mellin for Cesàro means | High |
| `Formalism.GzLipschitz` → `zetaPrimeSumErrorLipschitz` | `StatementU.lean:15` → `ZetaNonvanishing/GzLipschitz.lean:224` | The error term G(x)=S(x)−x log x+(1+γ)x (Cesàro-weighted ψ) satisfies \|G(t)\| ≤ Kt and is K-Lipschitz on [1/2,∞). | Mathlib | n/a | Med |
| `FX.LPartialSum` → `l_function_partial_sum` | `LFunctionBounds/PositivityBound.lean:23` → `LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean:140` | For χ ≠ 1 with \|partial character sums\| ≤ B and Re s > 0: \|L(s,χ) − ∑_{n≤N} χ(n)n^{−s}\| ≤ 2B(1+\|s\|/σ)N^{−σ}. | Mathlib | Partial summation for L(s,χ) | High |
| `PI.LBoundRight`, `PI.ZetaBoundRight`, `PI.LInvRight` | `PeriodIntegrals/ZerosWindowIn.lean:9,13,16` → `ExplicitFormulaCounts/AnalyticInputs.lean` | \|L(s,χ)\| ≤ 1+2(q+1)(1+\|s\|/σ) for χ ≠ 1, σ>0; \|ζ(s)\| ≤ 1+1/\|s−1\|+\|s\|(1+1/σ); \|L(s,χ)\|⁻¹ ≤ σ/(σ−1) for σ>1. | Mathlib | Convexity-free trivial bounds | High (other agent's area) |
| `…Dens.EtaPartial` → `eta_partial_sums` | `…/PNTDensSt.lean:71` → `…/PNTDensLs.lean:137` | Explicit error for the alternating (η) Dirichlet series approximating (1−2^{1−s})ζ(s), for Re s>0. | Mathlib | Dirichlet eta | Med |
| `FX.DivisorBound`, `…Dens.DivSq` | `LFunctionBounds/PositivityBound.lean:20`; `…/PNTDensSt.lean:27` | d(n) ≪_ε n^ε; ∑_{n≤x} d(n)² ≤ x(1+log x)³. | Mathlib | Divisor bound / Ramanujan | High |
| `…Dens.PairCross`/`PairSame`/`Spacing`/`Offdiag`, `…ZD.DualIneq` | `…/PNTDensSt.lean:35–53`; `…/CountZDefs.lean:28` | Short character-sum bounds over (U,2U]; well-spaced point counting; large-sieve duality inequality. | Mathlib | Large-sieve ingredients | Med |
| `GaloisIrreducibility.PrimeRecipSum` → `prime_reciprocal_sum_bound` | `PadicSubsetSums/CentralIdempotents/GaloisIrreducibility.lean:124` → `PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean:337` | For N ≥ 100: ∑ 1/p over primes N/2 < p ≤ N−3 is ≥ 1/(5 log N). | Mathlib | Bertrand-type reciprocal sum | Med |

### 3b. Geometry of numbers, lattices and number fields

| Declaration | path:line | Statement | Objects | Classical name | Reuse |
|---|---|---|---|---|---|
| `FN.MinkowskiIIUpper` → `minkowskiIIUpper` | `SuccessiveMinima/StatementMink.lean:18` → `SuccessiveMinima/MinkowskiIIUpper.lean:16` | For a ℤ-lattice L and a compact convex symmetric K with 0 in its interior: vol(K)·∏λᵢ(L,K) ≤ 2ⁿ covol(L). | Mathlib + `succMin` (successive minima) | **Minkowski's second theorem** (upper half) | **High**. Not in Mathlib. |
| `FN.AdaptedBasis` | `SuccessiveMinima/DefsMink.lean:54` → `…/AdaptedBasis.lean:72` | Linearly independent lattice vectors v can be completed to a ℤ-basis b with the same flag of ℝ-spans. | Mathlib | Basis adapted to a flag | High |
| `L2.SG.Pf.Tau.MinkowskiFirstTheorem` → `t8m` | `LocalToGlobal/SiegelLatticeTheory/…/LatticeVectorsBoundedBelow.lean:56` → `…/BlockGramReduction/T8m.lean:18` | In dimension d there is C with ‖u‖² ≤ C·covol(L)^{2/d} for some nonzero u ∈ L. | Mathlib | Minkowski's first theorem | High (Mathlib has the convex-body version) |
| `F.ShortVector`, `F.MuMaxLeMin` | `LatticeSlopes/CovolAntiSameRank.lean:35`, `LatticeSlopes/Statement.lean:99` | For any discrete subgroup of rank r: ‖v‖ ≤ √r·covol^{1/r}; bound on the max slope from the minimum norm. | Mathlib + `covol`/`rk`/`muMax` (local, faithful) | Hermite-type | High |
| `HarderNarasimhan.HNStep`/`HNSlopes`/`HNExtreme`/`SlopeIneq` → `hnStep_spec`, `hnSlopes` | `HarderNarasimhan/Statement.lean:68,78,88,95` → `HarderNarasimhan/ShiftInvariance.lean:48,50` | Harder–Narasimhan (Stuhler–Grayson) filtration for lattices L ⊂ V with a map to a Euclidean space: the slope-θ step is saturated and maximal, slopes are antitone and sum to deg L, the HN polygon dominates, and slopes behave under maps with norm ≤ C. | internal defs (`IsLat`, `muMin`, `deg`, `slopeList`) on Mathlib objects | Stuhler / Grayson HN for Euclidean lattices | **High** if the defs are accepted. They look faithful (log covolume degree). |
| `HermitianLatticeCounting.LatticeSumBounds.ClassNumberBound` → `classNumberBound` | `FlagUnipotentLattices/CardSubmodulesAndLinearEquivBounds.lean:158` → `FlagUnipotentLattices/CardSubgroupsOfIndexLe.lean:23` | For every number field E: h_E ≤ \|d_E\|^{(1+log₂[E:ℚ])/2}. | Mathlib (`NumberField.classNumber`, `discr`) | Explicit Minkowski-type class-number bound | **High** |
| `…IdealNormLeCount` → `ideal_norm_le_count` | same file `:152` → `…/IdealsOfNormEqIndexSet.lean:372` | #{nonzero ideals with N𝔞 ≤ x} ≤ x^{1+log₂ n}. | Mathlib | Crude ideal count | High |
| `…CardSubmodulesOfIndexLePow`, `S6.SublatticeCount`, `SLP.SubmoduleIndexCountO`, `SLP.SubmoduleCountDed`, `SLP.AutCount` | `FlagUnipotentLattices/CardSubmodulesAndLinearEquivBounds.lean:163`; `HyperbolicPlaceProducts/Statement.lean:59,64` | Counts of O_E-submodules of index j in a projective module of rank ≤ k (≤ j^{k+log₂ n}); counts of submodules and automorphisms of finite modules. | Mathlib | Sublattice counting | High |
| `…ProjQuotCard` | `…CardSubmodulesAndLinearEquivBounds.lean:260` | #(P/IP) = N(I)^{rank P} for projective P over O_E. | Mathlib | n/a | Med–high |
| `…Packing`, `…BoxCount`, `…BoxCountO`, `…LatticeSum`, `MainNotions…LatSum` | same file `:136,239,383,390`; `SharpRestriction/CuspSpanNormBounds/KTwoMinorIntegrality.lean:18` | Packing bound #{x ∈ Λ, ‖x‖ ≤ R} ≤ (1+2R/ℓ₀)^n; box counts for lattices in ∏ℂ with a product-norm lower bound; convergence and size of ∑∏max(1,‖x_v‖/H)^{−3}. | Mathlib | Lattice-point counting | High |
| `HermitianLatticesTheory.ShortVectors` | `HermitianLattices/DefsCS.lean:43` → `HermitianLattices/FinalNeighbourConstruct.lean:41` | A lattice with minimum ≥ c and covolume ≤ C has n independent vectors of norm ≤ B(N,c,C). | Mathlib | Mahler compactness flavour | Med–high |
| `PIW.AdelClassFin.PartMink` | `PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean:79` | For G positive definite over ℝ there is a nonzero c ∈ ℤᴺ with cᵀGc ≤ K·det(G)^{1/N}. | Mathlib | Hermite constant | High |
| `PI.TransferenceCoverDiv` → `coverDiv` | `PeriodIntegrals/TransferenceCoverRad.lean:13` | If the dual lattice has minimum ≥ κ, the covering radius is ≤ n/(2κ). | Mathlib | Banaszczyk-type transference (weak) | Med–high |
| `LatticeBaseChangeAlt.NearestPlane`, `…ComplexHadamard`/`GHadamard`, `HadamardInequality.Hadamard`/`HadamardMax`, `L2.LamCM.HadamardPD`, `…GramHadamard`/`WedgeHadamard`, `F.GramDetLe`, `E.CovolGram` | `FilteredPoleLength/ReducedBasisBounds/*.lean`; `GelfandTransference/Statement.lean:16,19`; `LocalToGlobal/CMDeterminantIdeals/StatementA.lean:23`; `FockGram/StatementLat.lean:29` | Babai nearest-plane rounding; Hadamard's inequality (real, complex, positive definite, Gram and sesquilinear forms); covolume = √det Gram. | Mathlib | Hadamard, Babai | Med (some partly in Mathlib) |
| `LatticeIndexTer.LogProductFormula` | `LogFactorialIndices/StatementNorm.lean:13` → `…/LogProductFormula.lean:14` | ∑_σ log\|σx\| = ∑_𝔭 v_𝔭(x) log N𝔭 for x ∈ L^×. | Mathlib | Product formula (log form) | High |
| `…ExpansionTerms.AlgebraicIntegerNormGeOne`, `HermitianLattices.IntegralLatticeDensity.IntegerMeanLog`, `…LocalIntegralStructure.CMRoot` | `FlagUnipotentLattices/UnipotentStabiliserCharacterisation.lean:30`; `GL3MeanSquares/InvariantSeriesBidegreeOneOne.lean:68` | \|N(x)\| ≥ 1 for nonzero algebraic integers, in Archimedean-place form; AM–GM for CM places. | Mathlib | n/a | Med |
| `DirichletDensity…QuadDiscr` → `quadDiscr` | `DirichletDensity/Statement.lean:20` → `DirichletDensity/HostDensityArith.lean:14` | K = ℚ(√a), a squarefree, a ≡ 1 mod 4 ⇒ disc K = a. | Mathlib | Quadratic discriminant | Med–high |
| `PI.InertPrime` (+ SharpRestriction copy), `PI.ClassNumImQ.IntBasis`, `PI.QD.*`, `PI.IdealLatticeWork.OKArea`/`OKBasis`, `PI.GoodTwo.NormPow` | `PeriodIntegrals/InertPrime.lean:11`; `PeriodIntegrals/ClassNumImQ.lean:14`; `…/QuadraticDifference/QuadDiffOf.lean`; `…/IdealLatticeBasis/IdealBasisAlt.lean:13,24`; `PeriodIntegrals/GoodTwo.lean:45` | Imaginary quadratic arithmetic: (−d/p) = −1 ⇒ p inert; integral basis of ℚ(√−d), d ≡ 3 mod 4; the covolume of O_K in ℂ is √\|d\|/2; for d ≡ 7 mod 8 squarefree, x²+xy+((d+1)/4)y² = 2^h has a solution with y odd. | Mathlib | n/a | Med |
| `IrreducibleCountingLemmas.Z.DegreeOneSplit`, `L2.SG.Pf.SatGramLoc.SplitPrimeLoc`, `…SplitDiff`, `…DdTraceCore`, `PI.UnitaryGroupMassFormula.UJClassMass.WPlace`, `MainNotions.BridgeLemma.ExistsPrimeAbove` | various | Splitting of degree-one primes in quadratic extensions; totally split p; the different ideal and the trace dual; every prime lies above some prime. | Mathlib | Dedekind basics | Med |
| `PI.EmbTraceSum` (+ `MainNotions.Ext.TraceSum`) | `PeriodIntegrals/EmbTraceSum.lean:9` | The sum over embeddings extending φ₀\|_K equals φ₀(Tr_{E/K}). | Mathlib | n/a | Med |
| `PI.PowBddInt`, `PI.UnitKron`, `PI.PowBddIntWork.StepA/B`, `PI.Mk.TraceStep`/`PowerSumStep`, `LogVandermondeBounds…PrimeOrderFinrank`, `GL3MeanSquares…RationalMatrixPrimeOrderBound`, `HermitianLatticeCounting…FiniteOrderCongruence` | `PeriodIntegrals/PowBddInt.lean:11`, `UnitKron.lean:11`; `LogVandermondeBounds/LogVandermondeVariationUnbounded.lean:31`; `GL3MeanSquares/RationalMatrixPrimeOrderBound.lean:12`; `FlagUnipotentLattices/CardSubmodulesAndLinearEquivBounds.lean:396` | Power-bounded matrices over a number field have integral characteristic polynomial; a unitary γ (for a definite form) with integral charpoly has finite order (Kronecker); A^p = 1, A ≠ 1 over ℚ ⇒ p ≤ n+1, over K ⇒ p−1 ≤ [K:ℚ]·n; Minkowski: A ≡ 1 mod g ≥ 3 of finite order ⇒ A = 1; \|P\| divides ∑ tr(g)^k for finite P ⊂ GL_N(ℤ). | Mathlib | Kronecker, Minkowski's congruence lemma | **High** |

### 3c. Adelic, local-field and measure statements

| Declaration | path:line | Statement | Objects | Classical name | Reuse |
|---|---|---|---|---|---|
| `PI.UnipApproxD.AddDense` → `additive_dense_integers` | `PeriodIntegrals/UnitaryGroupMassFormula/UnipotentApproximation/MemZeroLocusGLIff.lean:12` → `…/AddDense.lean:287` | F is dense in the finite adele ring 𝔸_{F,f}. | Mathlib | Strong approximation for 𝔾_a | **High** |
| `PI.VolStabS.SAf` (+ `VolStabSW` copy) | `…/StabilizerVolume/LocDensSA.lean:15` | Every open subgroup U of 𝔸_{F,f} meets every coset x+F: there is a ∈ F with x − a ∈ U. | Mathlib | Same | High |
| `PI.StrongApproxE.DedSA`, `PI.UnitaryApproxFinWork.WeakApproxF`, `PI.LocLatEq.W.AvoidP`, `L2.Ker.ApproxP` | `…/StrongApproximation/LocSmall.lean:20`; `…/UnitaryApproximation/WeakApproxF.lean:26` | Approximation at finitely many places with integrality elsewhere; weak approximation in completions modulo D; prime avoidance. | Mathlib | Strong/weak approximation (Dedekind form) | High |
| `L2.Props.IntAdelesCompactOpen` | `LocalToGlobal/AdelicCompactOpens/IntAdelesCompactOpen.lean:11` → `PeriodIntegrals/…/IsCompactAdicCompletionIntegers.lean:158` | ∏_v O_v is compact and open in 𝔸_{F,f}. | Mathlib | n/a | High (Mathlib may have part of it) |
| `PI.AdCpctDen` | `PeriodIntegrals/AdCpctDen.lean:11` | Elements of F landing in a compact subset of 𝔸_{F,f} have a bounded common denominator. | Mathlib | n/a | Med–high |
| `PI.VolStabS.ChLift`, `HeckeCharacterZeroLocus.StdAdditiveCharExists` | `…/LocDensSAChar.lean:19`; `UnipotentAdelicQuotients/StdAdditiveCharExists.lean:11` → `PeriodIntegrals/ExplicitFormulaCounts/BridgeStdAddChar.lean:12` | Continuous characters of the infinite adeles are exp(ℓ(x)); for totally real F a standard additive character of 𝔸_F/F exists with the usual Archimedean component. | Mathlib | Tate's thesis setup | High |
| `D.Classical.GlobalNormIndexTwo` | `UnipotentAdelicQuotients/GlobalNormIndexTwo.lean:14` → `Development/…/MemNormGroupIffEverywhereNorm.lean:195` | For a quadratic extension E/F there is a unique nontrivial continuous idele-class character killing norms. | Mathlib | Global class field theory, quadratic case | **High**, but the proof sits outside Formalism and I have not checked what it depends on. |
| `GaloisCohomology.LocalTateDualityK`, `LocalEulerCharK`, `LocalFinitenessK` | `GaloisCohomology/LocalTateDualityK.lean:41,51,35` → claimed `CompanionTheory/AutomorphicTheory/PadicCyclotomicFields/GcohTop.lean:15` | Local Tate duality (H²(μ) ≅ ℤ/l^r and cup-product pairings perfect), Euler characteristic formula, and finiteness, for finite ℤ/l^r[G_K]-modules, K/ℚ_l finite. | Repo-defined H⁰/H¹/H² via continuous cochains, on Mathlib objects | Tate local duality, Tate's Euler characteristic formula | **High if real.** The proofs are outside my subtree and not verified. |
| `PI.LocDualGen.W.FpDual`/`FpDualUnram`/`EpSelfDual`, `PI.ProdFormulaE.St.TrInt`/`CardStep` | `…/LocalDualGenerator/FpDualUnram.lean:17,24,31`; `…/ProductFormulaHaar/ResCharIff.lean:30`, `NormMod.lean:72` | The inverse different of a p-adic field is principal (trace dual); unramified ⇒ O is self-dual; integral ⇒ \|Tr\| ≤ 1; #(O_K/(t)) = N(𝔭-part). | Mathlib (`IsNonarchimedeanLocalField`) | Local different | High |
| `PI.LocalEndW.ValContinuous`/`ValSurjective`/`HenselRoot`, `IndefR.LocBrg.HenselSqrt`/`FinNormSurj`, `L2.Th1.D.KurComplete`/`KurRoots`, `L2.LamCM.BigResExt`, `…ComplMax` | `…/LocalEndomorphisms/ValSurjective.lean:12–35`; `LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/FinNormSurj.lean:9,13`; `LocalToGlobal/TorsionIntegrality/GaussSumParity/StatementK.lean:31,34`; `LocalToGlobal/CMDeterminantIdeals/StatementG.lean:33` | Valuation-preserving ring endomorphisms of F_v are continuous and surjective; Hensel ℓ-th roots of 1-units; finite-field norm surjectivity; the maximal unramified extension of ℚ_l is complete and contains μ_n for l∤n; complete DVRs have extensions with residue field as large as wanted. | Mathlib | n/a | Med–high |
| Haar/quotient-measure package: `PI.WeilQuotMeas.WqUnique`, `…StepBruhat`, `PI.QuotMeasUniqW.QmuWeight`, `…GenWeil`, `MassDataIdxSteps.HaarIdx`, `PIW.MassDataColumns.HaarRatio`, `PI.UnimodIdx`, `IndefR.Leaf.HaarRightInvPi/Transfer`, `L2.SG.Pf.QuotIndep`, `PI.VolStabS.RPAbs`, `PI.FoldMult`, `D.haarProductClosedCompact` | `PeriodIntegrals/WeilQuotMeas.lean:26`; `…/WeilQuotientMeasure/StepBruhat.lean:15`; `…/MeasureDecomposition/InstDecomp.lean:51`; `…/LatticeIndices/MeasBAll.lean:16`; `…/StabilizerVolume/RestrProdSt.lean:17`; `UnipotentAdelicQuotients/HaarProductClosedCompact.lean:14` | Uniqueness of G-invariant measures on G/H up to scalars; Bruhat functions; Weil disintegration ∫_G = ∫_{G/S}∫_S; μ(K) = [K:A]μ(A) for open A; unimodularity criteria; restricted-product measures with ∏ ∫ fᵥ = ∫ ∏ fᵥ; Iwasawa-type G = PK volume formula. | Mathlib | Weil's formula, Bruhat functions | **High**: Mathlib has only fragments |
| `PI.VolStabS.ChangeVar`, `…SubmLB`, `…HenselCount`, `PI.RhsWLim.W.ChartLim`/`ChartJac`, `PI.LowSplitHaarW.TriShear` (+ `MainNotions.LocalOrbitGerms.TriangularShearMeasurePreserving`) | `…/StabilizerVolume/DensInfLoc.lean:19`, `LBSubm.lean:14`, `HenselCount.lean:13`; `…/WeightedLimitGauge/VolumeLieE.lean:88,96`; `…/LowerShearHaar/TriShear.lean:11` | Submersion change of variables; measure of the preimage of a small set under a submersion; Hensel counting of p-adic solutions; density limits of measures under C¹ charts; triangular shears preserve Haar measure. | Mathlib | Local densities | Med–high |
| `PI.PrimeZeta2`, `PI.LevelKSplit…PlacesCountable` | `…/CountingFormula/DensMultOf.lean:17` | ∑_𝔭 N𝔭^{−2} converges; the set of places is countable. | Mathlib | n/a | Med |

### 3d. Algebra, representation theory, groups and finite fields

| Declaration | path:line | Statement | Objects | Classical name | Reuse |
|---|---|---|---|---|---|
| `IrreducibleCountingLemmas.Z.BrauerNesbitt`/`BrauerNesbittAlg` → `brauer_nesbitt`, `brauer_nesbitt_algebra` | `PadicSubsetSums/CentralIdempotents/PrimitiveRootFifteenSubOneUnit.lean:25,34` → `PadicSubsetSums/StableGradedCounts/ZBrauerNesbitt.lean:456`, `ZBrauerNesbittAlg.lean:129` | Two finite-dimensional semisimple modules (over any field k and any k-algebra) whose elements all have equal characteristic polynomials are isomorphic. The group version gives an intertwiner. | Mathlib | **Brauer–Nesbitt** (char-poly form, any characteristic) | **High**. Not in Mathlib. |
| `NG.StatBurnside` → `NG.burnside` | `CharacterColumnKernels/StatOntoLattice.lean:15` → `…/IdempotentNormalForms/IdemNormalForm.lean:13` | A simple A-module with scalar endomorphisms is acted on surjectively: A ↠ End_k(V). | Mathlib | Burnside / Jacobson density | High |
| `GaloisIrreducibility.CentralIdempotent`/`CentralIdemOrthogonal`/`CentralIdemSumOne`, `TW.CentralIdempotentIntegral` | `PadicSubsetSums/CentralIdempotents/GaloisIrreducibility.lean:146,153`; `…/EigenbasisOfDistinctRoots.lean:71`; `…/CentralIdempotentIntegral.lean:14` | e_ρ = (dim/\|G\|)∑χ(g⁻¹)g is a central idempotent for irreducible ρ, e_ρe_σ = 0 for ρ ≇ σ, ∑e = 1; \|G\|·coeff of a central idempotent is integral. | Mathlib | Character idempotents | High |
| `GaloisIrreducibility.JordanPrime`, `PrimitiveOfPCycle`, `PowerPCycle`, `NoSolvableTransitive`, `AltNotSolvable` | `GaloisIrreducibility/Statement.lean:62–83` → `GaloisIrreducibility/NoSolvableTransitive.lean:26–29` | A transitive group containing a p-cycle with n < 2p is primitive; primitive + p-cycle with p+3 ≤ n ⇒ A_n ≤ G (Jordan); hence such G is not solvable. | Mathlib | **Jordan's theorem** (prime-cycle case) | **High** |
| `…GaloisIrreducibility.SquarefreeCount`, `IrredCountUpper`, `TypeCountExact`, `FrobOrbitIrred`, `DivisorDegreeSubSum` | `PadicSubsetSums/CentralIdempotents/GaloisIrreducibility.lean:55–135` | Over 𝔽_q: #squarefree monic degree-N with nonzero constant term ≥ q^N − 2q^{N−1}; d·#irreducible monic degree d ≤ q^d; exact count of polynomials with given factorisation type as ∏ binom(I_d, n_d); roots of an irreducible form one Frobenius orbit of size deg. | Mathlib | Gauss counting, factorisation types | High |
| `…CycleTypeProb`, `CycleProbPrime`, `CycleProbSum`, `LemmaP` | same file `:62–117` | #perms of cycle type (n_d) = N!/∏d^{n_d} n_d!; p-cycle frequency 1/p for N < 2p; #perms fixing an a-set ≤ (7/8)N!. | Mathlib | Cauchy's cycle-type formula | High |
| `…PrimeToPartSpec`/`PrimeToPartEqIff` | same file `:26,31` | Prime-to-l part of a finite-order element: its order and characterisation. | Mathlib + local `primeToPart` (transparent) | n/a | Med |
| `IrreducibleCountingLemmas.WindowSums.GLCardVal`, `LogVandermondeBounds.StandardLattice.CardGeneralLinear`/`CardUnitriangular`/`CardStabilizerVector`/`EulerProductBounds`, `PI.DensSplitW.FiberCard`, `PI.GGMirBoundW.RowExists`/`CharOrth` | `PadicSubsetSums/CentralIdempotents/WindowSums.lean:56`; `LogVandermondeBounds/LogVandermondeVariationUnbounded.lean:11–26`; `PeriodIntegrals/…/SplitDensity/FiberCard.lean:10` | #GL_n(𝔽_q) formula; v_g(#GL_r(𝔽_{g'})); unitriangular count; stabiliser of a vector; ½ ≤ ∏(1−q^{−i}) ≤ 1 for q ≥ 3; number of independent lifts; additive-character orthogonality. | Mathlib | n/a | High |
| `PI.Witt.OneVector`/`Anisotropic`, `PI.WittExtension` → `witt_extension_theorem` | `PeriodIntegrals/UnitaryGroupMassFormula/WittDecomposition/Anisotropic.lean:10,17`; `PeriodIntegrals/WittExtension.lean:9` | For nondegenerate Hermitian (sesquilinear, star-ring, char 0) forms, an isometric embedding of a subspace extends to an isometry of V. | Mathlib | **Witt's extension theorem** (Hermitian) | **High** |
| `HermitianLatticesTheory.UnimodUnramUnique` | `HermitianLattices/StatementJac.lean:11` → `HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean:426` | Over an unramified quadratic extension of a Henselian local ring with finite residue field, every unimodular Hermitian matrix is congruent to 1. | Mathlib | Jacobowitz (unramified) | High |
| `PI.UD.SVDStep`/`GramStep`, `L2.Props.HermDefON`, `MainNotions…WhitenStatement`, `PI.AprimeInfW.CayIdU`, `PI.UnitaryDense`/`FramesDense`, `L2.SG.Pf.ColDictValCPf.Dens` | `PeriodIntegrals/…/UnitaryDensity/GramStep.lean:13,18`; `LocalToGlobal/AdelicCompactOpens/HermDefONFamily.lean:12`; `PeriodIntegrals/UnitaryDense.lean:12,17` | SVD, Cholesky-type factorisations; the Cayley transform identity; U(n) is Zariski-dense (a polynomial vanishing on the unitary group is 0). | Mathlib | n/a | Med–high |
| `PI.WwMainW.CBSorted`, `FX/…DetMulEqSumAdjugate`, `GM.DetBlockLead`, `CountingSumsFrames.DetLeadDiag`, `…GramDetGen`, `…CofactorVec`, `…MinorBound`, `LatticeBaseChangeAlt.CauchyBinetMax`/`DetPerturbation` | `PeriodIntegrals/…/LFunctionMinors/FintypeColChoice.lean:26`; `MahlerMeasure/Statement.lean:11`; `PolynomialDimension/DigitSumValuationBound.lean:22` | Cauchy–Binet over ordered embeddings; leading coefficient of det of polynomial matrices with weighted degrees; minor bounds; perturbation of determinants. | Mathlib | Cauchy–Binet | Med (Mathlib has unordered Cauchy–Binet) |
| `PI.SSAscent…TraceNilStep`, `FourierDecayAlt…NilOfCharpoly`, `Z.BCCyclicVector`, `Z.UnipotentTwistCharpoly`, `Z.GeneralizedEigenSplit`, `L2.FormalSeriesBounds.RowTiePKey.JointEigSt`, `InvariantFactorPaths.L4.Sl2Injective` | `PeriodIntegrals/…/SemisimpleTraceForm/TraceNilStep.lean:19`; `PadicSubsetSums/CentralIdempotents/SchurOrthogonalityCompact.lean:28–42` | tr(M^m)=0 for all m ⇒ M nilpotent (char 0); separable char poly ⇒ cyclic vector; commuting periodic matrices diagonalise simultaneously; sl₂ highest-weight injectivity. | Mathlib | n/a | Med |
| `KernelCokernelLengths.KerCokerEq`/`DetLen`, `FilteredPoleLength…LengthBaseChangeLocal`, `TruncatedSeriesCounting…LenPi0`/`SubGen`/`LengthQuotientLeOfPowSMul`/`ColChain`, `PoleLengthBounds.FiltLenGr`/`LenPiU`, `PI.PoleLengthCount.PiLen`, `IrreducibleCountingLemmas.WindowSums.ColengthTwoStep` | `JumpKernelCokernel/KerCokerEq.lean:9`, `Statement.lean:46`; `FilteredPoleLength/ReducedBasisBounds/LengthBaseChangeLocal.lean:22`; `TruncatedSeriesCounting/RamifiedValuationInequality.lean:79,86,93` | Module-length calculus: for finite length M, length ker f = length coker f; over a DVR, length(M/dM) = v(det d); length multiplies by e under base change of DVRs; lengths of products and filtrations. | Mathlib (`Module.length`) | Fitting/Herbrand-quotient-type facts | **High**: Mathlib's `Module.length` API is thin |
| `PI.FGTFG.ProjStep` | `PeriodIntegrals/…/TorsionFreeGenerators/RankOneStep.lean:9` | f.g. torsion-free modules over a Dedekind domain are projective. | Mathlib | n/a | Med (check Mathlib first) |
| `CohomologicalDescent.HeightDescentMinors.LinPrime`/`LinDivision`/`RootsProduct`, `LevelStatements.Lv.CycloDistStatement`/`PsCycloStatement`/`RhoUniqueStatement`, `WindowSums.DistinctTerms`, `TruncatedSeriesCounting.R9.CancelQ`/`CancelC`, `CMCount…PowerSeriesDVRFactorisation` | `PieriBlockIdeals/CapelliCentralEnveloping.lean:171–186`; `SharpRestriction/LevelLetterCocycles/CyclotomicPowerSeries/ConstSectionStatement.lean:13–52`; `WindowSums/Statement.lean:16` | Over an I-adically complete domain, X−c (c ∈ I) is prime in O⟦X⟧ with division; Φ_{l^{s+1}}(1+X) is distinguished; iterates of (1+X)^l−1 produce cyclotomic factors up to units; ideal membership in O⟦X⟧. | Mathlib | Iwasawa-algebra basics | Med–high for Iwasawa-theory work |
| `GM.SmithZp`, `GM.GaussMulRad`, `GM.MahlerK`/`MahlerDisc`, `ELL.IntValuedZp` | `MahlerMeasure/StatementD.lean:14,21,25`; `MahlerMeasure/StatementB.lean:11`; `EllipticTorsion/Statement.lean:52` | Smith normal form over ℤ_p; the Gauss norm sup‖a_k‖ρ^k is multiplicative over ultrametric fields; binomial polynomials C(p^k X + t, i) have integral coefficients for i ≤ p^k; integer-valued polynomials are ℤ_p-valued. | Mathlib | Smith form, Gauss's lemma (ultrametric), Mahler | High |
| `G.LogExistsUnique`/`SubstInjective`/`HomComp`/`LogIffHomGa` | `FormalGroupLog/Statement.lean:40,92` → `FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean:337` | Formal group laws in char 0 have a unique normalised logarithm, which is a homomorphism to 𝔾_a; substitution is injective. | repo `FormalGroupLaw`-style defs on Mathlib `MvPowerSeries` (not inspected in depth) | Formal logarithm | Med |
| `FG.WittCharZero`/`WittTeichRoot` | `FormalGroupWitt/Statement.lean:54,57` | W(𝔽̄_l) has char 0 and contains primitive (l^d−1)-th roots of unity. | Mathlib | n/a | Med |

### 3e. p-adic valuation arithmetic and elementary inequalities

| Declaration | path:line | Statement | Reuse |
|---|---|---|---|
| `ResultantValuation.LTEUnit`, `WindowSums.ZpowVal`/`ValProd`, `NG.characterColumnKernelLengthBound`, `TwoAdicCyclotomicDecomposition.TwistVal`/`TwoAdicOrder`/`InvLength`/`CoinvLength` | `ResultantValuation/WindowValuation.lean:11`; `WindowSums/Statement.lean:24,31`; `CharacterColumnKernels/CharacterColumnKernelLengthBound.lean:11`; `TameInertiaTowers/StatementGroup.lean:55–124` | Lifting-the-exponent in ℤ_l: v(u^j−1) = s + v_l(j); v(∏(1−u^i)) = Ms + v(M!); v₂(5^{2^s e}−1) = s+2+v₂(e); the order of an odd a in (ℤ/2^N)^×. High: Mathlib's LTE is only for ℤ/ℕ. |
| `IncomingBounds.FactValBounds`, `WindowSums.WindowSum`, `RepresentationBoundsCohomology.N2.StatSumValEnd/Gen`, `IrreducibleCountingLemmas.WindowSums.LiftExp`/`DigitLemma`/`LagrangeBoundT` | `IncomingBounds/LemmaMNumerics.lean:12`; `WindowSums/Statement.lean:61`; `WachLatticeTwists/LagrangeExtensionCocycles/Statement.lean:34,40` | Legendre bounds N/(l−1) − log_l N − 1 ≤ v_l(N!) ≤ (N−1)/(l−1); ∑_{i∈window} v_l(i) ≤ L/(l−1) + log_l D. Med–high. |
| `GrowthSums.HarmonicVal`/`LogCoefVal`/`PowerSumPoly` | `GrowthSums/StatementA.lean:22,26`; `GrowthSums/StatementC.lean:15` | p-adic valuation of p^{(t+1)s}·∑_{y<p^{t+1}} y^{−s}; Faulhaber polynomial existence. Med. |
| `CyclotomicNorms.RootsOfUnityCount` | `CyclotomicNorms/StatementI.lean:23` → `Development/…/CardPowEqOneLeOfIsCyclicUnits.lean:82` | #{x ∈ ℤ/l^w : x^d = 1} ≤ d·l^{v_l(d)} (l odd), ≤ 2d always. Med. |
| `HyperbolicPlaceProducts.OmegaPow`, `S6.CfBound`, `…PiPowFactorial`, `…StirlingInv`, `…CompositionBlockProdBound`, `PI.IndexUBound`, `FourierDecayAlt.Sz.ZetaTail`, `…ProdOneAddTwoDivLeSqrt`, many `Num*` | various | Scalar numerical inequalities (n^{Ω(j)} ≤ j^{log₂ n}, π^{k−1}/(k−2)! < 17, Stirling lower bound, product of composition blocks ≤ e^{n/e}, …). Low–med: trivial to restate, useful as ready-made lemmas. |

### 3f. Real and complex analysis

| Declaration | path:line | Statement | Reuse |
|---|---|---|---|
| `FourierDecayAlt.E.AMarkov` → `markov_inequality`; `…MarkovVector` | `HermitianCurvature/StatementE.lean:22,26` → `HermitianCurvature/HermitianCurvatureProofs/Markov.lean:292,435` | **Markov brothers' inequality**: deg p ≤ d and \|p\| ≤ M on [−1,1] ⇒ \|p′\| ≤ d²M there. A vector-valued, interval-rescaled, iterated version follows. High. |
| `FourierDecayAlt.Qr.Trotter`/`TrotterMx` → `trotter_product_formula` | `HermitianCurvature/FrameExists2.lean:18,23` → `…/GroupGeneratedByExp.lean:169,173` | **Lie–Trotter product formula** (e^{X/n}e^{Y/n})^n → e^{X+Y} in any complete normed ℝ-algebra. High. |
| `FourierDecayAlt.Qr.OneParamDiff`, `REAL.OneParam`, `REAL.GrowthIter`/`TaylorRadius` | `HermitianCurvature/StatementQr.lean:220`; `RealPlaceAnalysis/Complexify.lean:114` | A continuous one-parameter group in finite dimensions is e^{tA}; exp additivity. Med. |
| `FourierDecayAlt.E.HerglotzLSC` | `HermitianCurvature/StatementE.lean:46` | Herglotz/Bochner-type bound for positive-definite sequences against lower-semicontinuous densities on the torus. Med. |
| `FourierDecayAlt.B.RegIBP`, `PI.SSU.Complete`/`ShiftInv`, `FourierDecayAlt.A6.ParsevalGroup`, `PI.SSE.ThetaDerivNe`/`ThetaA`, `L2.Th1.F.PInjective`/`PDerivZero`/`ZetaSummable`, `L2.Th1.H.ExpSeriesEntire`, `DimensionVariation.GaussCoord`, `ExpansionTerms.InversePowerIntegralPi` | `HermitianCurvature/StatementB.lean:62`; `PeriodIntegrals/…/ThetaSeriesUniqueness/Complete.lean:19,23`; `LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/ThetaLine.lean:41,45` | Fourier transform of h−h″; an entire 1-periodic function with zero Fourier coefficients is 0; Parseval on finite abelian groups; jacobiTheta₂′(1/2+τ/2,τ) ≠ 0 for Im τ ≥ √3/2; ℘(z)=℘(w) ⟺ z ≡ ±w; ℘′(z)=0 ⟺ 2z ∈ Λ; Gaussian integrals over ℂⁿ. Med–high, especially the Weierstrass-℘ facts. |

### 3g. Elliptic curves and formal groups (EllipticTorsion)

| Declaration | path:line | Statement | Objects | Reuse |
|---|---|---|---|---|
| `ELL.ModelUnit` → `modelUnit` | `EllipticTorsion/Statement.lean:47` → `EllipticTorsion/FormalGroupPointsNoTorsion.lean:50` | Over an algebraically closed ultrametric field, every j with \|j\| ≤ 1 is the j-invariant of an elliptic Weierstrass curve with integral coefficients and unit discriminant. | Mathlib `WeierstrassCurve` | Potential good reduction ⟺ integral j (one direction) | High |
| `ELL.ModelLegendre`/`ModelDeuring`, `LegendreInv`/`DeuringInv` | `EllipticTorsion/Statement.lean:27–41` → `…/Legendre.lean:31`, `…/Deuring.lean:34` | Legendre (residue char ≠ 2) and Deuring (char ≠ 3) normal forms realise any integral j with good reduction; Δ and c₄ of these families. | Mathlib | Med–high |
| `ELL.FormalGroupPointsTorsionFree` → `formal_group_points_no_torsion`; `ELL.TorsionIntegral` (via `torsionIntegral_of`); `L2.Th1.E.TorsionIntegral` → `torsion_integral` | `EllipticTorsion/FormalGroupPointsTorsionFree.lean:31,38` → `EllipticTorsion/FormalGroupPointsNoTorsion.lean:58`, `EllipticTorsion/EllipticTorsionProofs/TorInt.lean:74`; `LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/StatementA.lean:53` → `…/NonsingularJetNorms/Taylor0ConstMul.lean:17` | For an integral model with unit Δ over an ultrametric field: points with \|x\| > 1 ("formal group" points) have no n-torsion for \|n\| = 1, and every prime-to-p torsion point has integral coordinates. | Mathlib `WeierstrassCurve.Affine.Point` + transparent predicate (`1 < ‖x‖`) | Nagell–Lutz / reduction injective on prime-to-p torsion | **High** |
| `ELL.VeluIntegralModel`, `NAddSubgroup`/`NZpSmul`/`NPderiv`, `FrobExpand` | `EllipticTorsion/VeluIntegralModel.lean:47`; `EllipticTorsion/Statement.lean:70–81` | Vélu isogeny models stay integral; log(1+f) series with integral f form a ℤ_p-submodule closed under ∂. | Mathlib + transparent defs | Med |

### 3h. Selected internal-but-faithful statements

| Declaration | path:line | Statement | Reuse |
|---|---|---|---|
| `HermitianLatticeCounting…` mass and class-set finiteness (`HermitianLattices.ClassSetFinite`, `SiegelMassRatio`, `GL3MeanSquares…SiegelMassRatioThm`) | `HermitianLattices/*`, `GL3MeanSquares/MassLowerBoundClosed.lean:14` | Finiteness of genus class sets and Siegel-type mass ratios for Hermitian lattices over CM fields. They use local `IsLat`/genus defs that look faithful, but I have not checked their side conditions. | Med, if someone needs unitary mass formulas |
| `PI.HermLatFin` | `PeriodIntegrals/HermLatFin.lean` | Finiteness of the admitted O_E-lattices that are integral for a Hermitian form, up to the unitary group. | Med |

## 4. Internal definitions worth knowing

| Def | Where | Verdict |
|---|---|---|
| `D7` (master datum) | `LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:80` | A huge structure: `Ranks` (k, m, t even/odd, m+3 ≤ k, k+m+4 ≤ t, …), `Host R` (CM field E/F, q, d, QS ≤ n², `o^64 ≤ 2^e`, …), period maps and many coherence fields. **Not degenerate by construction**, but every theorem quantified over `D7` is only as meaningful as its constructors (`LocalRingCardinality/SpanPowerMembership.lean:39–44`, `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AssembleLattice.lean:18`). Several proofs branch on `Nonempty D7` (`SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean:1058`). Most of LocalToGlobal, SharpRestriction, AdmissibleDesigns, WachLatticeTwists, LocalRingCardinality and SizeWindowBrackets sits behind it. Not reusable. |
| `ReciprocityTheory.ChartRestriction.T2.Core` | `ReciprocityTheory/ReductiveGroups/TraceFormulas/LatDefs.lean:323` | A bundle of 13 local Galois-cohomology facts (decomposition-group equivalences, H² ≅ K/O, finiteness, …), carried as `[Fact Core]` in 70 files. It is built from `GlobalArtinReciprocity`, `LocalTateDualityK` and `LocalEulerCharK` (`Development/…/LocalDualityClassFieldFactsOfArtinTateEulerStatement.lean:12`). It is a faithful hypothesis bundle, so the theorems that use it are conditional at the file level. |
| `Formalism.MainNotions.N.K.H0.FinCore` | `AdmissibleDesigns/KernelLengthHigherColumns.lean:70` | Finiteness of invariants for `D7` twists. Discharged in `Development/…/SelmerLengthBoundAtPoint.lean:20`. |
| `GaloisCohomology.H0/H1/H2`, `GK`, `cycK`, `cupH1H1TwistedDual` | `GaloisCohomology/*`, `ReciprocityTheory/NeutralLocalFields/Duality.lean` | Continuous-cochain cohomology of G_K for K ⊂ ℚ̄_l finite over ℚ_l. Faithful as far as I read. |
| `IsLZero χ s` | `LandauZeroFreeBounds/Statement.lean:16` | `(χ ≠ 1 ∨ s ≠ 1) ∧ LFunction χ s = 0`. Faithful (it excludes the pole of ζ-type L). |
| `liX`, `piAP`, `mainAP`, `IsExcPair` | `GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MeanSquareHypWIff.lean:9–24` | li(X) = ∫₂^X dt/log t; π(X;M,b); main term with optional exceptional zero β₁ > 1−1/(8 log M). Faithful. |
| `PI.pr y`, `PI.PC.lf` | `PeriodIntegrals/PrimeCount.lean`, `…/ChebyshevPrimeBounds/PrimeCountBoundOf.lean:16` | Primes ≤ ⌊y⌋; log ⌊x⌋!. Faithful. |
| `succMin`, `covol`, `rk`, `muMax`, `muMin`, `slopeList`, `hnStep`, `IsLat`, `IsSat` | `SuccessiveMinima/DefsMink.lean`, `LatticeSlopes/Statement.lean`, `HarderNarasimhan/Statement.lean` | Standard lattice invariants. As far as I read, these are the textbook definitions (log-covolume degree, saturated sublattices). I did not check edge conventions (rank 0, empty inf). |
| `gaussR`, `binK`, `vmin` | `MahlerMeasure/StatementD.lean`, `Statement.lean` | Gauss norm at radius ρ, binomial polynomial C(X,k) = descPochhammer/k!, truncated valuation. Faithful. |
| `InFormalGroupPoints`, `IntegralModel`, `IntCurve`, `legendre`, `deuring` | `EllipticTorsion/*`, `LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/IsTransSys.lean:27` | `1 < ‖x‖`; integral aᵢ; aᵢ integral with ‖Δ‖ = 1; the standard Legendre and Deuring families. Faithful. |
| `primeToPart`, `centralIdem`, `monicOf`, `IsOrbit`, `IsSubSum` | `PadicSubsetSums/CentralIdempotents/GaloisIrreducibility.lean`, `GaloisIrreducibility/Statement.lean:13–16` | Transparent one-liners. Faithful. |
| `PeriodPair` (with `weierstrassP`, `lattice`) | used in `LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/*` | Mathlib's `PeriodPair`. Fine. |
| `Letters`, `TieData`, `fock`, `IsTypeProj`, `WeylLat`, `grLat` | `MahlerMeasure/StatementT*.lean` | Fock-space and GL_r weight-space machinery for Weyl modules over ℚ_p. Faithful-looking but special-purpose. |
| `DworkPowerSeriesWeights.*` (`WtGe`, `letterLog`, `BHyp`, `torus`) | `GaussJetBounds/Statement.lean` | Weighted coefficient bounds for Dwork-type power series in variables indexed by ZMod d. Special-purpose; `BHyp` is a substantive hypothesis bundle. |

## 5. Mechanical families

- **`*Holds` / `*Of` / `*_of` adapter files**: LocalToGlobal 136 `…Holds` + 110 `…Of` file names,
  PeriodIntegrals 87 + 121, SharpRestriction 35 + 71, HermitianCurvature 31 + 21. Each one turns a
  sub-Prop into a theorem or wires hypotheses together.
- **Duplicate Props**: the same statement is often defined again under another namespace. Examples:
  `InertPrime` (PeriodIntegrals and SharpRestriction), `TriShear` (two in PeriodIntegrals, one in
  SharpRestriction), `HenselCount`/`SAf`/`ChLift`/`AddIntF`/`CosDens` (identical copies in
  `StabilizerVolume` and `StabilizerOrbitVolume`), five copies of the Chebyshev θ ≤ Y log 4 or
  Mertens bounds, `MonoCount`/`SumAntidiagonalTuple`, and `LocalEndHomeo` (PeriodIntegrals and
  LocalToGlobal). I estimate dozens of such pairs.
- **Numeric-constant lemmas** (`Num*`, `*Numeric`, `HCoef`, `NumC`, `ParConsts`, `ElevenLe`, …):
  closed real inequalities with specific constants. There are a few hundred across HermitianCurvature
  (`StatementPB`, `StatementTC`), TruncatedSeriesCounting and SharpRestriction.
- **`D7`-indexed case analysis**: most of LocalToGlobal/{GroupLattices, Columns, ProjectiveLattices,
  CharacterGerms, KernelLattices, InertKernelTheory, PairingIndexBounds}, SharpRestriction/{GrowthBounds
  (1,183 files), LevelLetterCocycles (735)}, LocalRingCardinality (`Data*`, `Fact*`, 104 Props), and
  SizeWindowBrackets. These are statements about row, column, tie and window data of `D7`.
- **Counterexample files** (`RankGapBounds/RandomSubsetCounterexample.lean`, `CloudMinFalse.lean`,
  `SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean`, `PieriBlockIdeals/ExponentBoundCounterexample.lean`,
  `FlagUnipotentLattices/…/BlockMinorSumCounterexample.lean`): these refute candidate intermediate
  statements. Despite its name, the last one also proves useful positive lemmas
  (`InversePowerIntegralPi`, `CompositionBlockProdBound`).

## 6. Per-sub-library characterisation (file count)

The four giants:
- **LocalToGlobal (4,895)**: unitary or Hermitian local–global theory for `D7`.
  SiegelLatticeTheory (1,972) holds Siegel-domain reduction, Gram distortion, Minkowski I and Haar
  transversals. TorsionIntegrality (426) holds the Weierstrass ℘ facts, torsion integrality and
  ℚ_l^{ur} facts. IndefiniteReal (360) holds local norm surjectivity, Hensel square roots and Haar
  transfer. Then GlobalTheory, ProjectiveLattices, Columns, GroupLattices, CharacterGerms and others.
  It has about 40 Mathlib-level lemmas (§3). The rest is `D7`-bound.
- **PeriodIntegrals (3,369)**: mostly `UnitaryGroupMassFormula` (2,831), the richest Mathlib-level
  layer: adelic approximation, Haar and quotient measures, Witt extension, local differents,
  Chebyshev π(x) < 1.26x/log x, unitary density, theta-series facts. Also `OrbitalBoundsConclusion`
  (291) and `ExplicitFormulaCounts` (7, other agent). About 110 pure statements.
- **SharpRestriction (2,757)**: GrowthBounds (1,183) and LevelLetterCocycles (735) are `D7`-bound
  growth and cocycle bookkeeping. CyclotomicPowerSeries holds Iwasawa-algebra lemmas, plus some
  lattice-sum and PD-matrix lemmas. About 20 pure.
- **HermitianCurvature (1,796)**: namespace `FourierDecayAlt`, covering Fourier decay, Bessel and
  oscillatory integrals, Capelli identities and RTT relations. Pure gems: Markov's inequality, Trotter,
  the Herglotz bound, one-parameter groups, the p-adic change of variables (`ChangeVar` →
  `padic_change_of_variables`, `HermitianCurvatureProofs/PadicChangeOfVariables.lean:641`). About 32 pure.

Deep-dive candidates:
- **GL3MeanSquares (355)**: misnamed. **Unconditional PNT in APs with an exceptional zero, Linnik-type
  zero density, Deuring–Heilbronn, Turán's power-sum theorem, ∑Λχ/n → −L′/L(1)**, plus Hermitian-lattice
  mass and `UnimodularClassRepresentatives`. The most valuable library for analytic NT (§3a).
  `PrimeCountAsymptoticInProgressions C₀ Cr cr cb` (all moduli, `InvNormSqConjRatioPowIdentities.lean:38`)
  is **not** proved here. It is only a hypothesis of `ShortIntervalImpliesProgressions`.
- **PadicSubsetSums (60)**: namespace `IrreducibleCountingLemmas`. Counting polynomials over 𝔽_q,
  permutation cycle statistics, Brauer–Nesbitt, central idempotents, valuation-of-#GL facts. 64/73 Props
  closed. High reuse.
- **MahlerMeasure (48)**: misnamed (no Mahler measure). Smith form over ℤ_p, Gauss-norm
  multiplicativity, integrality of Mahler binomials, a p-adic "valuation window" lower bound for
  determinants of binomial matrices, GL_r Weyl and Fock weight spaces. 28/29 closed.
- **EllipticTorsion (44)**: honest. Weierstrass models, formal group, prime-to-p torsion integrality,
  Vélu integrality (§3g).
- **GaussJetBounds (60)**: Dwork-style weighted p-adic power-series bounds for specific "letter"
  substitutions (`ThmAGen`, `LemmaS`). Mostly closed (the regex under-counts `.{u}` Props). Special-purpose,
  low reuse except `JCount`.
- **LogVandermondeBounds (17)**: log bounds for Vandermonde products and Weyl dimensions of interlacing
  data (`VandPlace`, `UpperPlace`, `LogRatioLowerBound` → `vandermonde_place_lower_bound`,
  `HookGammaAmgmMultinomialBounds.lean`), plus #GL_n(𝔽_q) lemmas. The GL counts are reusable; the
  rest is low reuse.
- **TruncatedSeriesCounting (35)**: ideal membership in O⟦X⟧ and lengths over DVRs and PIDs (§3d).
  Med reuse.
- **AdmissibleDesigns (91, 859 theorems)**: Selmer-type length inequalities for `D7`, all under
  `[Fact T2.Core]` and `[Fact FinCore]`. None of its 36 named Props is closed by a bare theorem. They
  are inputs and outputs of `selmer_inequality_two` and similar. Not reusable.
- **UnitaryGroupMassFormula / SiegelLatticeTheory**: see PeriodIntegrals and LocalToGlobal above.

The rest (Props closed/defined in parentheses where useful):
- ThetaLogCoordinates (205): Fock and theta coordinates for `D7`; a few pure (sl₂ injectivity, residue-class lower bound). Low.
- WachLatticeTwists (115): Wach-module and Hodge–Tate twist lattices; some `[Fact T2.Core]`; pure: valuation sums, the adic-completeness bijection `StatOnePlus`, DVR root integrality `StatRootsInt`. Low–med.
- LocalRingCardinality (109): hosts `D7`/`Ranks`/`Host`, plus `Data*`/`Fact*` interface Props (77/104). Low.
- GradedWeylDivisibility (102): bideterminants, dual-Weyl lattices, Fock pairings (73/75). Low–med for GL_n rep theory.
- AdmissibleDesigns (91): see above.
- PieriBlockIdeals (86): Pieri rules, Capelli and content linkage; pure: power-series primality, ℤ_l theta congruences, Mertens/Chebyshev copies, `Linkage`. Med.
- SatakeDualWeyl (83): Satake/Hecke algebra for unitary groups, adelic Iwasawa (62/70). Low–med.
- PadicSubsetSums (60), GaussJetBounds (60): see above.
- QuotientMetricDivisors (60): metric divisors and Hermitian twist gluing; `PrimeLogSum`. Low.
- LandauZeroFreeBounds (57), ZeroFreeRegion (34): other agent.
- RealPlaceAnalysis (51): Casimir operators, smooth vectors, Taylor-radius lemmas. Low–med.
- MahlerMeasure (48), EllipticTorsion (44): see above.
- CharacterColumnKernels (43): Burnside density, l-adic valuation of x^b − x^a. Med for the two pure lemmas.
- DistinguishedUnitIdeals (42): Eisenstein/distinguished-polynomial arcs (79/79 closed); `KillerShift`. Low.
- UnipotentAdelicQuotients (39): Siegel sets, elliptic regularity (bump functions, weighted Sobolev limits), `GlobalNormIndexTwo`, standard additive character. Med.
- HarderNarasimhan (38): HN filtration for Euclidean lattices (31/31). High (§3b).
- HermitianLattices (38): genus, mass, short vectors, Jacobowitz unramified uniqueness. Med–high.
- FlagUnipotentLattices (38): class-number bound, ideal and submodule counts, packing, Minkowski congruence (140/153). High.
- SizeWindowBrackets (33): `D7` window bookkeeping; pure prime-sum copies. Low.
- PolynomialDimension (32): det-adjugate identities, multinomial and digit counts. Low–med.
- FrobeniusOrbits (29): "Host" CM-field facts, the real subfield of 2-power cyclotomic fields, discriminants. Med (not inspected in depth).
- FormalDegreeBessel (28): formal degrees and Bessel models (36/36). Low.
- FilteredPoleLength (27): Hadamard, nearest-plane, Cauchy–Binet max, DVR length base change. Med.
- JumpKernelCokernel (27): ker/coker length equality, det-length formula. Med–high.
- MirabolicMackeyTheory (22): Mackey theory for mirabolic subgroups; `ThetaLog4`. Low–med.
- LatticeSlopes (18): slopes, μ_max, short vectors. High.
- IncomingBounds (17): Legendre v_l(N!) bounds, Cayley identity. Med.
- LogVandermondeBounds (17): see above.
- LatticeTheta (14): lattice theta inversion and summable decay. Med (not inspected).
- BranchSandwichDivisors (14): branching and Weyl-dimension bounds for `D7`. Low.
- TameInertiaTowers (14): 2-adic orders, coinvariant lengths, abelian genus decompositions. Med.
- DoubleCosetMeasures (14): double-coset volumes. Low–med.
- MeanHeightDescent (14): average-degree and Minkowski μ_max lemmas. Low–med.
- GaloisIrreducibility (14): Jordan's theorem chain. High.
- SubspaceCounting (13): walk and subspace counts. Low.
- FormalGroupWitt (13): Witt vectors of 𝔽̄_l, Frobenius lifts (3/11 closed by bare theorems). Low–med.
- GrowthSums (12): harmonic-sum valuations, Faulhaber. Med.
- EisensteinCokernelLengths (12): Eisenstein ideal relations, numeric constants. Low.
- WeaklyAdmissibleFiltrations (11): Fontaine weakly-admissible and crystalline definitions (8/12). Low.
- TorsionNormIteration (11): Lubin–Tate example and formal-group inverse integrality (0/7 bare closures). Low.
- CoboundaryTransfers, RankGapBounds, LogFactorialIndices, GaussValuationBounds, ThetaSupremumBounds, HyperbolicPlaceProducts (10 each): respectively cocycle diagram chases; rank-gap plus counterexamples; the product formula and lattice indices; truncated-ideal relations and the existence of `c_j` with v(c_j−c_j′) = v_l(j−j′); Gaussian integrals and Fock jets; torsion-index and submodule counts. Each has 1–4 pure lemmas (§3).
- YangianSpanCharacter (9): Yangian RTT relations. Low.
- SuccessiveMinima (9): Minkowski II, adapted basis. High.
- WindowSums (8): LTE in ℤ_l, window valuation sums, a Lagrange-interpolation annihilator. Med–high.
- FockGram (8): covolume = √det Gram, PSD Gram. Med.
- CyclotomicNorms (8): roots-of-unity counts, irreducibility criteria. Med.
- LFunctionBounds (7): divisor bound, partial sums of L(s,χ). High.
- PairingDivisors (7), LagrangeIdealLifts (7): Lagrange ideal lifts in ℤ_l[X]. Med for `LagrangeIdeal`.
- SelfDualUnimodular (6), FormalGroupLog (5), ZetaNonvanishing (5), DivisorInequality (5), DegreeFormula (5), DirichletDensity (5), ThetaLiftIndependence (5), FrobeniusContraction (5): small. ZetaNonvanishing (Mellin, Mertens, G Lipschitz) and FormalGroupLog are reusable; `FrobeniusContraction.ContractBij` (an I-adically contracting f gives a bijective f − id) is reusable.
- LatticeRigidity, ResultantValuation, CMTypeGalois, GaloisCohomology, SmithDeterminants, GelfandTransference (4 each): GaloisCohomology holds the *statements* of local Tate duality and Euler characteristic (§3c), whose proofs live outside the subtree. ResultantValuation has `LTEUnit`. GelfandTransference has Hadamard.
- TowerValuationBounds (4), MonomialMeanResidues (3), CorankShare (3), ThickAverageLoss (3), AdicCompletionExports (3), DropLevelBounds (3): small special-purpose pieces. AdicCompletionExports and DropLevelBounds have 0 closed Props of their own (they are interfaces).
- Singletons and pairs: ConjugateSelfDual (3), GaussIdealIdentity, NormUnitaryBounds, AlgebraicWeights, FrobeniusBaseCase (2 each), PrimeAboveExistence, WachModuleLifts, JacquetSubsetSums (`NoFixedSum`, `SignEven`), TranslateCocycles, WeightedDeltaMeans, MoebiusJetDuality, JacobiWeightFamilies, LogSumExpBounds, SobolevGaussianKernels, ArtinHasse, LogFactorialBounds (1 each). These are mostly statement-only stubs or interfaces. ArtinHasse (139 lines, 7 theorems) and LogFactorialBounds (4 theorems) hold real but small proofs.

## 7. Standalone value

**Named theorems effectively proved here, in usable Mathlib-level form** (as far as reading statements goes):
- PNT in arithmetic progressions, uniform in the modulus, with the exceptional-zero term (moduli
  divisible by 8); a log-type zero-density estimate for Dirichlet L; Deuring–Heilbronn; a large-sieve
  zero-density count; Turán's second main theorem; ∑Λχ/n = −L′/L(1,χ) (GL3MeanSquares).
- π(x) < 1.26x/log x for all x > 1; explicit Chebyshev, Mertens and Stirling (PeriodIntegrals, ZetaNonvanishing).
- Minkowski's second theorem (upper bound); Minkowski I with an unspecified constant; Harder–Narasimhan
  for Euclidean lattices; a class-number bound h ≤ \|d\|^{(1+log₂ n)/2}; ideal and sublattice counts;
  Minkowski's congruence lemma; Kronecker's theorem for unitary integral matrices.
- Brauer–Nesbitt; the Burnside density theorem; character central idempotents; Jordan's prime-cycle
  theorem plus non-solvability; Cauchy's cycle-type count; counts of irreducible and squarefree
  polynomials over 𝔽_q.
- Witt's extension theorem (Hermitian, char 0); Jacobowitz uniqueness for unimodular unramified Hermitian lattices.
- Density of F in 𝔸_{F,f}, strong approximation for 𝔾_a, compact-open integral adeles, uniqueness
  of invariant measures on G/H, Weil disintegration, Bruhat functions.
- Markov brothers' inequality; the Lie–Trotter product formula.
- Smith normal form over ℤ_p; multiplicativity of the ultrametric Gauss norm; integrality of Mahler binomials.
- Integrality of prime-to-p torsion on good-reduction elliptic curves; integral models for integral j
  (alg. closed ultrametric fields).

**Special cases only**:
- PNT in APs: only 8∣M, and in the regime log X ≫ log M·log log M. The all-moduli asymptotic
  `PrimeCountAsymptoticInProgressions` and the short-interval statement `PrimesAPInterval` are
  hypotheses, not theorems.
- Minkowski II: only the upper bound. Minkowski I: existential constant only.
- Global class field theory: only the quadratic norm-index statement (`GlobalNormIndexTwo`), proved
  outside Formalism.
- Jordan: only the p-cycle with n < 2p, p+3 ≤ n case.
- Witt extension: Hermitian forms over a field with star, char 0.

**Misleading names**: `MahlerMeasure` (no Mahler measure), `HermitianCurvature` (Fourier/Markov
analysis, no curvature), `GL3MeanSquares` (PNT-in-AP and Hermitian mass, no GL₃ mean squares),
`PadicSubsetSums` (finite-field counting and Brauer–Nesbitt), `ZetaNonvanishing` (Mellin and Mertens
lemmas, not a non-vanishing theorem: its `key_identity` is conditional on `MellinS`, `LSeriesLamF`
and `MellinElem`), `GaussJetBounds` (Dwork weights), `LogVandermondeBounds` (Weyl-dimension log
bounds), `SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` (finite-group character sums, no RH).

## 8. Open questions / not verified

- **Typechecking**: I verified none of it. "Closed" means "a theorem with that type exists in the
  source".
- **The closure index is heuristic.** It resolves names via namespaces and `open`s. It can miss
  universe-polymorphic and multi-line forms, and a short name can collide (I caught one: `LemmaP`
  exists in two namespaces). I checked every headline item in §3 by hand at the proof-head level,
  but not their transitive dependencies.
- **Hidden hypotheses**: theorems inside files with `variable [h : Fact X]` take X as an argument.
  I checked this for AdmissibleDesigns and WachLatticeTwists (affected) and for the headline files
  in §3 (not affected, as far as I saw). I did not check every file a headline transitively uses.
  Any `Fact` such a lemma needs would have to be found by instance search, which constrains it but
  does not exclude a global `instance` proved conditionally.
- **Outside-subtree proofs**: `LocalTateDualityK`, `LocalEulerCharK`, `GlobalNormIndexTwo`,
  `RootsOfUnityCount`, `StdAdditiveCharExists` and `GlobalArtinReciprocity` are proved in
  CompanionTheory, Development or ExplicitFormulaCounts. I did not inspect those proofs.
- **`D7` non-vacuity**: I did not check whether the inputs of `exampleRecord`/`AssembleLattice` can be inhabited.
- **Faithfulness of HN, genus and mass defs** (`IsLat`, `deg`, `ClassSetFinite`, `SiegelMassRatio`):
  they look standard, but I have not checked edge cases.
- **Overlaps**: GL3MeanSquares' zero-density and Deuring–Heilbronn chain imports `LandauZeroFreeBounds`
  (`IsLZero`, `ZeroFreeDirichlet`). Its ultimate dependence on that agent's results is not traced here.
- **Not opened at all**: LatticeTheta, FrobeniusOrbits, SatakeDualWeyl, FormalDegreeBessel,
  DoubleCosetMeasures, YangianSpanCharacter and WeaklyAdmissibleFiltrations beyond their Prop names.
  Their one-line characterisations come from names and statement heads.
