# riemann-hypothesis: the proof spine and its Mathlib-level waypoints

Source: `~/work/personal/riemann-hypothesis` at `507a75d91d131d627b380df4e32f6e9fb21dd067`. All paths
below are relative to its `src/`. Read-only survey, nothing was built. Declaration names and
locations come from the sources. Statements are paraphrased, not copied (the repo has no licence).

## 1. Scope and method

- **Spine.** I started at `Main.lean` and read every file on the main term chain down to the
  point where the argument goes into internal structures: `Main.lean`,
  `CharacterBoxes/{HalfPlane,EveryCharacter,ClaimStrip,MainConclusion,Imprimitive,ZeroFreeAllOfTopG,SupplyChi,ExistsPageN,DivinNOfHypV}`,
  `Supplements/Kernels/MainTheorems.lean`,
  `ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/{TopPlug,SiegelEisensteinSecondTermHypotheses}` and the
  tail of `EveryCharacterOfLiteratureOfVWin.lean` (5950 lines; I read only the last theorem and the
  `OpenLiteratureStatements` assembly). I also read
  `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/{ExplicitFormulaErrorOfHostConditions,PrimePairSizeCondition,Analytic,TopWin,TopDefs,Window}`,
  `Formalism/StatementOC.lean`, `Development/AutomorphicArithmetic/PrimitiveCosets/{Imports,LevelGmLeOnFamilyScales,WindowInequalityOfArtinInputs,CoreGm,CoreAtH}`,
  the `DedekindLFunctions` headers, `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean`, and the statement of
  `each_unit_bound_statement`. That is about 8 levels below `Main`.
- **Import graph.** I parsed the `import` headers of all 149,396 `.lean` files in a scratch
  script. 149,395 of them are in the transitive import closure of `Main` (only `Challenge.lean`
  is not), so imports do not tell you what the proof uses. The spine below follows actual term
  dependencies instead. I used the same graph to measure how many repo files each candidate
  lemma needs, which is what it would cost to vendor it.
- **Assigned directories.**

  | Directory | Files | Lines | How read |
  |---|---|---|---|
  | `Formalism/LandauZeroFreeBounds` | 57 | 6,674 | every `def`/`theorem` header, every top-level file in full |
  | `Formalism/ZeroFreeRegion` | 34 | 3,312 | every header, `Statement`/`SmallHeightLogDeriv`/`FinalZFR`/`LogDerivRegion` in full |
  | `Formalism/PeriodIntegrals/ExplicitFormulaCounts` | 7 | 127 | all of it, plus the `PI.*` statement files it closes |
  | `Development/AutomorphicArithmetic/DedekindLFunctions` | 35 | 3,625 | every header, `CharFamily`/`LandauZeroFreeCriterion`/`ZeroFreeOfRpowWindow`/`lemmaL` in full |
  | `Development/AutomorphicArithmetic/MeanSquareBounds` | 35 | 4,462 | headers of every theorem that mentions a Mathlib analytic object, plus the key defs |
  | `Development/AutomorphicArithmetic/ResidueCharacters` | 36 | 3,789 | headers only |
  | `Development/AutomorphicArithmetic/CyclotomicBounds` | 197 | 15,766 | headers of the 108 files that do not use `D7`/`Host`/`Frame`; the other 89 only counted |

  Also read: `Formalism/ZetaNonvanishing` (5 files) and `Formalism/LFunctionBounds` (7 files).
- **The analytic core from the earlier audit.** It is in
  `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/` (a directory of 1,217 files). I
  read the headers of all 21 files involved.
- **Skipped.** The rest of `GlobalInterpolation` (Linnik-type and zero-density files, listed in
  §7 for whoever covers it), the "literature" layer (`AbelianVarietyTheory/PublishedTheorems`,
  `Proofs/DivisorProofs`, ...), and the constructions that instantiate `FamP`, `HostExW` and `Row0b`.
- **Hygiene.** `rg` finds no `sorry` in `LandauZeroFreeBounds`, `ZeroFreeRegion`,
  `LFunctionBounds`, `ZetaNonvanishing`, `DedekindLFunctions`, `GlobalInterpolation` or
  `CharacterBoxes`, no `native_decide` in the first three, and no top-level `axiom` declaration
  anywhere in `src/`. Proof bodies were not checked beyond spot reads.

## 2. What the spine actually is

**Final reductions (Mathlib only, about 100 lines).** `Main.lean` gets RH and the other forms
from one proposition, `UpperTheory.EveryCharacter`. It says: for every Dirichlet character χ
mod N and every s with Re s > 1/2 (excluding χ = 1, s = 1), `LFunction χ s ≠ 0`. It is
definitionally the same as `DirichletLNonvanishingRightOfHalf` and `Claim.HalfPlane`.
`Claim.strip` and `Claim.zeta` turn this into "all zeros in the strip lie on Re = 1/2" by three
steps: pass to the primitive character (the finite Euler factors don't vanish for Re s > 0),
apply the functional equation for primitive characters (Mathlib's `completedLFunction_one_sub`),
and use Gamma-factor nonvanishing. `UpperTheory.Top.imprimitive` likewise reduces
`EveryCharacter` to `Formalism.HC.ZeroFreeAll`: every *primitive* character (bundled as
`PChar`) has no zeros in Re s > 1/2.

**The real mechanism: a one-sided Landau theorem on windows.** Define the Riesz-weighted
explicit-formula remainder

  G_χ(y) = Σ_{n≤y} Λ(n) χ(n) (y/n − 1) + y·L′/L(1,χ)                          (χ ≠ 1)
  G_1(y) = Σ_{n≤y} Λ(n) (y/n − 1) − y log y + (1+γ) y                        (trivial χ)

(`Deduction.Gchi`, `Formalism.HC.An.gChi`, `Formalism.Gz`). Its Mellin transform is
−(L′/L(s) − s·L′/L(1))/(s(s−1)), proved in `mellin_Gchi_of_ne_one` and `mellin_Gchi_modOne`.
So each zero ρ produces a simple pole with residue −m/(ρ(ρ−1)), which is positive when ρ is
real and lies in (0,1). The key analytic theorem, `Deduction.zeroFree_of_rpow_window`, is
Mathlib-only and about 30 files. Take any finite family of characters χ_i (not principal unless
the modulus is 1) and any positive weights a_i. Suppose Σ a_i Re G_{χ_i}(y) ≤ C·y^θ for all y in
[Y, Y^{1+δ}], for some arbitrarily large Y. Then no L(s,χ_i) vanishes for Re s > θ. Only a
**one-sided** bound on **windows** is needed. The proof (`lemmaL`, `landau_window`,
`landau_dichotomy`, `landau_nearest`, `iteratedDeriv_laplace`) is Landau/Pringsheim in style: it
works with high derivatives of the Laplace transform at a real point, which concentrate on one
window. Non-real nearest singularities make those derivatives oscillate. A real one has positive
residue, which contradicts the one-sided bound. `UpperTheory.Comparison₂.formB` applies this to the
family `Level.cyc ψ`: the primitive characters inducing the powers of ψ, with weight 1 on the
trivial one and 1/(3·ord ψ + 1) on the others. So `ZeroFreeAll` follows once, for every
primitive ψ and every ε > 0,

  Gm_ψ(x) := G_1(x) + Σ_{ψ′ ∈ ⟨ψ⟩, ψ′≠1} (3o+1)^{-1} Re G_{ψ′}(x) ≤ x^{1/2 + C·ε}     on windows [Y, Y^λ].   (★)

This is `ChebyshevInequalityOnWindows` (`TopWin.lean:24`), reached via
`zeroFreeOn_of_tiedWin_cyc` and `zeroFreeAll_of_topG`.

**Where (★) comes from (RH-strength input; traced, not verified).** `core_gm` (`CoreGm.lean:16`)
bounds Gm by two terms.

- *Term 1: ASK − MAIN, plus x^{1/2+O(ε)}.* `ch_core` and `GmA_eq` are character-orthogonality
  bookkeeping over an abelian "host" group E0 × A, i.e. a Galois group of an auxiliary abelian
  field cut out by ψ and Jacobi symbols mod two primes q, d. ASK is a nonnegative weighted sum
  over primes that are **inert** in the host, of log p · max(a/p^i − w, 0). MAIN is its main term.
- *Term 2: SigA.* This sums ‖G‖ over the auxiliary twisted characters ψ·J_q·J_d. For good pairs
  (q, d) they are small: the `MeanSquareBounds` large-sieve, Box and zero-density machinery shows
  that most quadratic twists satisfy ‖G‖ ≤ y^{1/2+τ} on the window.

The bound on ASK − MAIN is `ch_top` → `each_unit_bound_statement`
(`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:171`). That is pure
real-number bookkeeping over an abstract `Data` record. All the strength sits in hypotheses
(`SizeData₂`, `ErrWindows`, `ChainTied`) supplied by the family `FamP` and the hypothesis
`HostExW (3/2)`, which comes from `UpperTheory.Top.VWin` (`ExistsPageN.lean:48-53`). `VWin`
bounds a Galois-cohomology quantity: Σ_l log l · Σ_{e<t} length_{ℤ_l} Ш¹(G_{E,S}, ℚ_l/ℤ_l(e)) ≤
√exp(x^ε) for the number fields E ⊂ ℚ(ζ_N) fixed by ψ and the Jacobi symbols. In words, the
repo derives an RH-quality upper bound for inert-prime sums from a bound on Tate–Shafarevich
lengths of Tate twists. That bound is a Bloch–Kato/Tamagawa-type statement about special
values. `VWin` in turn comes from `Row0b` (`Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:73`):
Galois representations attached to regular algebraic polarized cuspidal representations of GL_a
over CM fields, with local-global compatibility. The repo "proves" it through theta lifts
(`galoisLocalGlobalStrong_recParameter`, `RowSrc.lean:10`) and the `OpenLiteratureStatements`
layer. I did not check whether the definitions on that branch (`FamP`, `HostExW`, `Row0b`,
`LData`/`Sha`) are faithful, so §7 lists it as the main unverified point.

**Distance from the directory names.** `DedekindLFunctions` holds no Dedekind zeta functions.
It holds the Landau-window theorem for families of Dirichlet characters plus the host
bookkeeping (`ChCore`, `ChTop`, `ChBalance`). `CharacterBoxes` is the final reduction layer.
`MeanSquareBounds` is a large-sieve and zero-density argument over quadratic twists.
`LandauZeroFreeBounds` and `ZeroFreeRegion` are what their names say: classical analytic number
theory, complete and Mathlib-level. They are **not on the RH spine through `ZeroFreeAll`**,
except through `MeanSquareBounds` (`psi_thin` uses `NoZeroComplex` and `PI.ExplicitFormula`).
`ResidueCharacters` and `CyclotomicBounds` are p-adic Hodge, Galois-cohomology and lattice
bookkeeping on the internal `D7` structures, with a few stand-alone algebraic lemmas.

## 3. Inventory (most reusable first)

"Files" = number of repo files in the transitive import closure (vendoring cost). "M" = the
statement mentions only Mathlib objects. "I" = it mentions repo-internal definitions.

| Declaration | path:line | Statement (paraphrased) | M / I | Classical name | Reusability |
|---|---|---|---|---|---|
| `Formalism.ZeroFreeDirichlet.zFRDirichlet` | `Formalism/LandauZeroFreeBounds/NoZeroComplex.lean:36` | There is c > 0 such that, for all q and χ mod q, any zero of L(s,χ) with Re s ≥ 1 − c/log(q(\|Im s\|+2)) (excluding χ = 1, s = 1) has χ real non-principal, s real and simple. At most one such (χ, s) exists per modulus q. | M (`InRegion`, `IsLZero` are 2-line Mathlib defs) | de la Vallée Poussin–Landau zero-free region with Landau–Page exceptional zero | **High.** Exact classical statement, 66 files, uniform in q |
| `Formalism.ZeroFreeDirichlet.siegelLower` | `Formalism/LandauZeroFreeBounds/FinalSiegel.lean:21` | For every ε > 0 there is c > 0 with ‖L(1,χ)‖ ≥ c·q^{−ε} for every real non-principal χ mod q | M | Siegel's theorem (ineffective) | **High.** 39 files |
| `Formalism.ZeroFreeDirichlet.excBound` | `Formalism/LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:36` | For every ε there is c > 0 such that every real zero β of a real non-principal L(s,χ) mod q satisfies β ≤ 1 − c·q^{−ε} | M | Siegel's bound on exceptional zeros | High |
| `Formalism.ZeroFreeDirichlet.siegelWalfisz` | `…/SiegelWalfiszAPOfSiegelLower.lean:38` | For every A there are c, C with \|ψ(x,χ) − δ_χ x\| ≤ C·x·exp(−c√log x) whenever q ≤ (log x)^A | M (`psiChi` = Σ_{n≤x} Λ(n)χ(n)) | Siegel–Walfisz (character form) | **High.** About 107 files. The AP form follows from the orthogonality lemma `chebyshev_progression_orthogonality` (`ExceptionalZeroBounds/SiegelWalfiszAPOf.lean:13`) |
| `Formalism.ZeroFreeDirichlet.psiChiBound` | `…/SiegelWalfiszAPOfSiegelLower.lean:27` | PNT for ψ(x,χ) with explicit exceptional-zero term −x^β/β and error x·exp(−c√log x), for q ≤ exp(c√log x) | M + `ExcZeros` (faithful) | PNT in APs, Page–Landau form | High |
| `Formalism.ZeroFreeDirichlet.{noZeroComplex, realLargeT, realSmallT, twoReal, localZeros}` | `…/NoZeroComplex.lean:21-33` | The pieces of the ZFR: complex χ have no zeros in the region; real χ have no zeros at height ≥ δ/log; near the real axis there is at most one simple real zero; two distinct real characters can't both have zeros in the region (Landau); and a local zero-sum bound for −Re L′/L near 1+it | M | Landau's lemma, Page's theorem | High as stepping stones |
| `Formalism.ZeroFreeDirichlet.negLogDerivPositivity` | `…/ExceptionalZeroBounds/Positivity.lean:134` | For σ > 1: 3·Re(−L′/L(σ,χ₀)) + 4·Re(−L′/L(σ+it,χ)) + Re(−L′/L(σ+2it,χ²)) ≥ 0, plus the 2-term and 4-term real-character analogues | M | Mertens' 3-4-1 inequality, character form | High |
| `Formalism.ZF.zeroFreeRegion`, `logDerivRegion`, `gzPNT` | `Formalism/ZeroFreeRegion/FinalZFR.lean:21`, `LogDerivRegion.lean:18,24` | ζ(s) ≠ 0 for Re s ≥ 1 − c/log(\|t\|+2). In that region \|ζ′/ζ(s) + 1/(s−1)\| ≤ C log²(\|t\|+2). \|Σ_{n≤y} Λ(n)(y/n−1) − y log y + (1+γ)y\| ≤ K·y·exp(−c√log y) | M | Classical ZFR for ζ, and PNT with dVP error (Riesz-weighted form) | **High.** 21 files |
| `Formalism.ZF.{mertensInequality, perron_formula, rectangle_double_pole, laurentExpansionAtOne, zeroFactorization, logDerivBoundOnBall, landauLocal, growthBound, zetaInvBound_statement}` | `Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/*.lean` (e.g. `ThreeFourOne.lean:50`, `Perron.lean:253`) | 3-4-1 for ζ. Perron: Σ Λ(n)(y/n−1) = (1/2π)∫ −ζ′/ζ(w)·y^w/(w(w−1)) on Re w = σ₀ > 1, integrable. Rectangle residue theorem for a double pole. Laurent expansion at 1. Local factorization of a holomorphic function on a disc as ∏(z−ρ)^m · h. Borel–Carathéodory-type bound \|f′/f\| ≤ 24 log M / R. Landau's local zero lemma (zero count ≤ log M/log 2, \|f′/f − Σ m/(z−ρ)\| ≤ 72 log M/r). \|ζ(s)\| growth and 1/\|ζ\| ≤ σ/(σ−1) | M (`LandauLocal`, `ZeroFactor`, `LogDerivBound` are about an arbitrary f : ℂ → ℂ) | Landau's lemma, Perron's formula | **High.** The disc lemmas are generic complex analysis that Mathlib lacks |
| `Deduction.zeroFree_of_rpow_window` | `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:15` | For any finite family of Dirichlet characters with positive weights (each non-principal or of modulus 1), and 0 < θ < 1: if Σ a_i Re G_{χ_i}(y) ≤ C y^θ on [Y, Y^{1+δ}] for some arbitrarily large Y, then every L(s,χ_i) ≠ 0 for Re s > θ | M (`CharFamily`, `Gm`, `ZeroFree` are transparent Mathlib-level defs) | Landau's theorem (one-sided, windowed). Gives the "ψ(x,χ) = O(x^{θ+ε}) ⇒ GRH_θ" direction | **High.** 30 files. The criterion side of any "RH ⇔ prime-sum bound" project |
| `Deduction.lemmaL`, `Deduction.landau_window` | `…/LandauTheorems/lemmaL.lean:17`, `landauWindow.lean:87` | The integral-window form: g ≤ R on [U,(1+δ)U] with ∫ R e^{−θu} ≤ e^{ηU} (all η, some arbitrarily large U), together with `PoleData` (Laplace transform meromorphic, simple poles, positive real residues), implies every pole has Re ≤ θ | M + `PoleData` (faithful structure) | Landau/Ingham oscillation | High. Abstract and reusable for other Dirichlet series |
| `Deduction.poleData_char`, `Deduction.poleData` | `…/LandauTheorems/poleData.lean:141,252` | The Laplace transform of u ↦ G_χ(e^u) extends meromorphically to Re s > 0. Its only poles are simple, at zeros ρ ≠ 0, with residue −m_ρ/(ρ(ρ−1)), m_ρ the multiplicity | M | Explicit formula, Mellin form | High |
| `Deduction.mellin_Gchi_of_ne_one`, `mellin_Gchi_modOne` | `…/mellinGchiOfNeOne.lean:118`, `mellinGchiModOne.lean:119` | ∫_1^∞ G_χ(y) y^{−s−1} dy = −(L′/L(s) − s·L′/L(1))/(s(s−1)) for Re s > 1. The ζ version has −(ζ′/ζ + 1/(s−1) + 1 − (1+γ)s)/(s(s−1)) | M | Mellin transform of a Riesz mean | High |
| `Deduction.LFunction_conj` | `…/LandauTheorems/LFunctionConj.lean:92` | L(s̄, χ⁻¹) is the complex conjugate of L(s, χ), for all s (through the Hurwitz continuation) | M | Reflection under conjugation | **High.** Small and missing from Mathlib |
| `Deduction.mertens_upper`, `Deduction.Gchi_growth` | `…/mertensUpper.lean:107`, `GchiGrowth.lean:41` | Σ_{n≤y} Λ(n)/n ≤ log y + 2. ‖G_χ(y)‖ ≤ C y² | M | Mertens' first theorem (upper half) | Medium |
| `GlobalTheory.T.perron_integral_shift_primitive_LFunction` (also `GlobalTheory.PerronShift.perron_shift`) | `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PerronIntegralShiftPrimitiveLFunctionStatement.lean:10` (`PerronIntegralShiftPrimitiveLFunction.lean:232`) | For primitive χ mod N and 2 ≤ T ≤ u there is T′ ∈ [T, T+1] such that the truncated Perron integral of −L′/L at c = 1 + 1/log u, minus δ_χ u, plus Σ_{\|Im ρ\|<T′} m_ρ u^ρ/ρ, is ≤ C(u log²(NuT)/T + log(Nu) + Σ_{\|Im ρ\|<1} m_ρ/\|ρ\|) | M | Contour shift in the truncated explicit formula | **High.** 14 files, Mathlib only |
| `GlobalTheory.PerronPsi.truncated_perron_psi` | `…/GlobalInterpolation/TruncatedPerronPsi.lean:441` | For all χ mod q and 2 ≤ T ≤ 2u, u ≥ 2: \|ψ(u,χ) − (1/2π)∫_{−T}^{T} −L′/L(c+it) u^{c+it}/(c+it) dt\| ≤ C(u log²u/T + log u), where c = 1 + 1/log u | M | Truncated Perron formula for ψ(x,χ) | **High.** 2 files |
| `GlobalTheory.PerronKernel.truncated_perron_kernel` | `…/GlobalInterpolation/TruncatedPerronKernel.lean:351` | \|(1/2π)∫_{−T}^{T} y^{c+it}/(c+it) dt − 1_{y>1}\| ≤ C y^c min(1, 1/(T\|log y\|)) | M | Perron's kernel lemma | **High.** 1 file |
| `GlobalTheory.ExplicitRect.residue_identity` | `…/GlobalInterpolation/AnalyticAtDslope.lean:193` | For primitive χ: the boundary integral of −L′/L(s)u^s/s around [−1/2, c] × [−T, T] (with no zeros on the horizontal edges or the left edge, and a given Laurent datum at 0) equals 2πi(δ_χ u − Σ_{0<Re ρ<1, \|Im ρ\|<T} m_ρ u^ρ/ρ − (m log u + h(0))) | M | Residue computation for the explicit formula | High |
| `GlobalTheory.ResRect.residue_rectangle` | `…/GlobalInterpolation/BdIntEqZeroOfPrimitive.lean:147` | Rectangle residue theorem: f is holomorphic on a closed rectangle except at finitely many interior points p with expansions a/(s−p)² + r_p/(s−p) + analytic. Then the boundary integral equals 2πi Σ r_p | M | Residue theorem (rectangles, poles of order ≤ 2) | **High.** Mathlib-only, 1 file |
| `GlobalTheory.LWide.logDeriv_LFunction_strip` | `…/GlobalInterpolation/LogDerivLFunctionStrip.lean:78` | Uniformly in non-principal χ mod q and −1 ≤ Re s ≤ 2 with L(s) ≠ 0: the zeros within 7/2 of 2 + i·Im s are finite, number ≪ log(q(\|t\|+2)), and \|L′/L(s) − Σ m_w/(s−w)\| ≪ log(q(\|t\|+2)) | M | Local zero-sum approximation of L′/L | High |
| `GlobalTheory.GoodHeight.{exists_bound_right, local_formula, exists_height}` | `…/GlobalInterpolation/ExistsBoundRight.lean:79,98,155` | ‖L′/L(s)‖ ≤ B for Re s ≥ 2. The primitive local formula. For each T ≥ 2 there is a height T′ ∈ [T, T+1] where L ≠ 0 and \|L′/L\| ≪ log²(NT) on −1/2 ≤ σ ≤ 3 | M | Good heights (classical) | High |
| `GlobalTheory.ZeroWindow.count_zeros_window` | `…/GlobalInterpolation/FinsumMemLeOfSubset.lean:31` | For primitive χ mod N: zeros with 0 < Re ρ < 1 and \|Im ρ − t\| ≤ 1 number ≪ log(N(\|t\|+2)), counted with multiplicity | M | Unit-window zero count (N(T+1) − N(T) ≪ log qT) | **High** |
| `GlobalTheory.ExplicitRect.finite_zeros`, `order_ne_top`, `logDeriv_one`, `exists_entire` | `AnalyticAtDslope.lean:115,143,155,103` | Finitely many zeros in 0 < Re < 1, \|Im\| < T. Zeros have finite order away from 1. Laurent form of L′/L at 1. An entire F with F(1) ≠ 0 vanishing at the zeros of L | M | — | Medium-high |
| `GlobalTheory.LFunction_zero_of_re_nonpos`, `completedLFunction_ne_zero_of_re_nonpos`, `rootNumber_ne_zero_of_isPrimitive` | `…/GlobalInterpolation/CompletedLFunctionNeZeroOfReNonpos.lean:90,70,53` | For primitive χ, zeros with Re s ≤ 0 are trivial: s = −n, simple, s = 0 only for even non-principal χ, s = −1 only for odd χ. The completed L-function doesn't vanish for Re s ≤ 0 (excluding s = 0, χ = 1). The root number is nonzero | M | Trivial zeros of Dirichlet L-functions | **High.** 1 file |
| `GlobalTheory.LogDerivZeros.main`, `GlobalTheory.LWide.disc`, `GlobalTheory.ZetaWide.scaled` (the same file also has `GlobalTheory.ZetaWide.main`, the ζ analogue of `logDeriv_LFunction_strip`) | `NormOneSubConjMul.lean:130`, `LogDerivLFunctionStrip.lean:14`, `ImportsMore.lean:14` | For r < R < 1 there is C such that, for f analytic on the closed unit disc with f(0) ≠ 0 and \|f\| ≤ M: the zeros in \|w\| ≤ R are finite and number ≤ C(1 + log(M/\|f(0)\|)), and \|f′/f(z) − Σ m_w/(z−w)\| ≤ C(1 + log(M/\|f(0)\|)) for \|z\| ≤ r. `disc` and `scaled` are the versions for any disc | M (arbitrary f) | Jensen and Borel–Carathéodory local lemma | **High.** Generic complex analysis |
| `GlobalTheory.logDeriv_eq_order_div_add_analytic`, `FactorOrderExistence.exists_factor_order` | `LogDerivEqOrderDivAddAnalytic.lean:11`, `ExistsFactorOrder.lean:11` | f′/f = ord_p f/(s−p) + analytic near p. g = (z−w)^ord · h with h(w) ≠ 0 on the domain | M (arbitrary f) | — | Medium-high (small Mathlib gaps) |
| `GlobalTheory.LLeft.norm_LFunction_le_poly_left`, `LLower.norm_LFunction_ge`, `ZetaLeft.norm_sub_one_mul_riemannZeta_le` | `SummableNinePowMulInvSqSucc.lean:275`, `TsumOneDivRpowLe.lean:67`, `NormSubOneMulRiemannZetaLe.lean:193` | \|L(s,χ)\| ≤ C q⁴(\|s\|+2)⁴ for Re s ≥ −7/4 and χ ≠ 1. \|L(s,χ)\| ≥ (σ−1)/σ for σ > 1. \|(s−1)ζ(s)\| ≤ C(\|s\|+2)⁵ for Re s ≥ −7/4 | M | Polynomial growth (convexity-free) | Medium-high |
| `GlobalTheory.ZeroBand.zeros_band` | `FiniteBox.lean:100` | Changing T to any T′ ∈ [T, T+1] changes Σ m_ρ u^ρ/ρ by ≪ u log²(NuT)/T | M | — | Medium |
| `GlobalTheory.ExplicitFormula.truncated_explicit_formula`, `PI.ExplicitFormula` (`explicitFormula_closed`), `GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed` | `…/GlobalInterpolation/TruncatedExplicitFormula.lean:16`, `Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean` (def `Formalism/PeriodIntegrals/ExplicitFormula.lean:33`), `ExplicitFormulaClosed.lean:49` | For primitive χ mod N and 2 ≤ T ≤ u: \|ψ₀(u,χ) + Σ_{0<Re ρ<1, \|Im ρ\|<T} m_ρ u^ρ/ρ\| ≤ C(u log²(NuT)/T + log(Nu) + Σ_{\|Im ρ\|<1} m_ρ/\|ρ\|), where ψ₀ = ψ − δ_χ u | M (`psi0` is a 2-line Mathlib def, defined 3 times) | Truncated explicit formula (Davenport ch. 19) | **High statement, expensive import.** 203 files through GI, 80 through PI. The Mathlib-only path is `perron_shift` + `truncated_perron_psi` |
| `PI.zerosWindow_closed` | `Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean` | Same unit-window zero count as `count_zeros_window`, proved independently | M | — | Duplicate |
| `Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox` (proof `zero_density_box`) | def `Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountSt.lean:11`, proof `CountZAll.lean:17` | For Q ≥ 3, the number of primitive characters of conductor ≤ Q that have a zero with Re s > 1 − 1/400 and \|Im s\| ≤ Q is ≤ C·Q^{1/4} | M | Log-free zero density near σ = 1 (Linnik/Gallagher type, crude constant) | **High.** 24 files. Not a scheduled directory; found while tracing `MeanSquareBounds.count_bad` |
| `QH.psi_thin` | `Development/AutomorphicArithmetic/MeanSquareBounds/PsiThin.lean:389` | For primitive χ mod N, λ ≥ max(1, log N), with no Siegel zero within c₀ of 1 when χ is real: ‖ψ₀(u,χ)‖ ≤ C u (log u + λ)² exp(−c log u/(λ + √log u)) | M + `NoExc` (faithful: L(β) ≠ 0 for β ∈ (1−c₀, 1)) | PNT for a single character, uniform in the conductor | High |
| `QH.g_integral` | `…/MeanSquareBounds/GIntegral.lean:225` | For primitive χ and y ≥ 1: G_χ(y) = −y ∫_y^∞ ψ₀(u,χ)/u² du | M | Integral representation of the Riesz remainder | Medium |
| `QH.count_bad`, `QH.small_zeros`, `QH.twist_prim`, `QH.real_decomp`, `QH.ind_unique` | `MeanSquareBounds/{CountBad:13, SmallZeros:36, TwistPrim:13, realDecomp:88, IndUnique:11}` | Few primes q > F make some primitive twist of conductor f·q ≤ Q fail the zero-free box (≤ CQ^{1/4}). For fixed N₀ there is a uniform zero-free interval near 1 for χ ≠ 1 mod N ≤ N₀. ξ·(·/q) is primitive mod fq (q odd, q ∤ f). Every real χ with modulus dividing N₀qd factors as ξ·J_q^a·J_d^b. A primitive character is determined by its values on n coprime to M | M (J q n = Jacobi symbol (n/q)) | Twisting quadratic characters | Medium |
| `Claim.strip`, `Claim.zeta`, `Claim.prim_zero`, `Claim.prim_reflect`, `Claim.factor_ne_zero`, `Claim.gamma_ne_zero` | `Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:63,79,27,46,11,39` | Half-plane nonvanishing ⇒ zeros on the line (χ and ζ). A zero of L(χ) in the strip is a zero of the primitive L. A zero ρ of primitive L gives a zero 1−ρ of L(χ⁻¹). Euler factors 1 − ψ(p)p^{−s} ≠ 0 for Re s > 0. The Gamma factor ≠ 0 for Re > 0 | M | — | **High.** Exactly what `conjectures` needs to move between RH forms (2 files) |
| `UpperTheory.Top.imprimitive` | `…/CharacterBoxes/Imprimitive.lean:9` | Primitive-only half-plane nonvanishing implies it for all characters | M + `PChar` (faithful) | — | High |
| `Formalism.ZeroFreeDirichlet.lfunction_one_same_character`, `lfunction_one_upper_bound`, `lfunction_deriv_near_one`, `real_lfunction_real_on_reals`, `zeta_negative_real_axis`, `l_function_partial_sum`, `divisor_weight_bound` | `ExceptionalZeroBounds/{SameCharacterLFunctionOne:102, LFunctionOneUpperBound:14, LDerivNearOne:127, LRealPos:31, ZetaNegReal:33}`, `Formalism/LFunctionBounds/LFunctionBoundsProofs/{LPartialSum:140, DivisorBound:60}` | \|L(1,χ₁)\| ≤ (ω(q₁q)+1)²\|L(1,χ)\| when χ₁ and χ induce the same character. \|L(1,χ)\| ≪ log 3q. \|L′(σ,χ)\| ≪ log²(3q) near 1. A real χ has L(σ) real and positive right of its last real zero. ζ(σ) < 0 on (0,1). Partial-sum approximation of L(s,χ) for Re s > 0 with error 2B(1+\|s\|/σ)N^{−σ}. d(n) ≪_ε n^ε | M | Standard lemmas | High (small and self-contained) |
| `Formalism.FX.rectangle_residue` | `Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean:127` | Rectangle residue theorem for finitely many simple poles | M | Residue theorem | Medium (overlaps `residue_rectangle`) |
| `UpperTheory.Comparison₂.formB` | `Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:12` | For each `Level` Λ (finite inverse-closed set of primitive characters containing 1, with weights): a windowed bound Λ.Gm(x) ≤ x^θ implies every ψ ∈ Λ is zero-free for Re > θ | I (`Level`, but transparent) | Landau window, applied | Medium (just `zeroFree_of_rpow_window` repackaged) |
| `UpperTheory.Comparison₂.core_gm`, `Deduction.ch_core`, `Deduction.ch_top`, `…each_unit_bound_statement` | `PrimitiveCosets/CoreGm.lean:16`, `DedekindLFunctions/LandauTheorems/ChCore.lean:347`, `ChTop.lean:41`, `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:171` | Bound Gm by x^{1/2+O(ε)} + Σ_{twists}‖G‖, given abstract host, size and window data (`HostFactsS`, `SizesA`, `CharsA`, `IdentU`, `SizeData₂`, `ErrWindows`, …) | I | — | **Low.** Bookkeeping over internal records. The mathematics is in the hypotheses |

## 4. Internal definitions worth knowing

| Definition | Where | Verdict |
|---|---|---|
| `UpperTheory.EveryCharacter`, `Claim.HalfPlane`, `Claim.Strip`, `Claim.Zeta` | `CharacterBoxes/EveryCharacter.lean:7`, `HalfPlane.lean` | Faithful. Same terms as `Statements.lean` |
| `Formalism.HC.PChar` (N, a character mod N, primitivity), `PChar.of` (primitive character inducing χ), `ZeroFreeAll` | `TotientGaloisClasses/PrimePairSizeCondition.lean:11`, `ExplicitFormulaErrorOfHostConditions.lean:20` | Faithful. `ZeroFreeAll` = every primitive L has no zeros in Re > 1/2. At PChar.one it reads Mathlib's junk value ζ(1) = (γ − log 4π)/2 ≠ 0, which is harmless |
| `Deduction.Gchi`, `Formalism.HC.An.gChi`, `Formalism.Gz`, `Formalism.Gchi` | `DedekindLFunctions/CharFamily.lean:19`, `TotientGaloisClasses/Analytic.lean:27`, `Formalism/StatementOC.lean:17` | Faithful. The Riesz-weighted remainder; `gChi_eq` identifies them |
| `Deduction.CharFamily`, `Gm`, `ZeroFree`, `WindowHyp`, `PoleData`, `WindowHypU` | `CharFamily.lean:28-45`, `LandauZeroFreeCriterion.lean:19-29` | Faithful and non-degenerate. `PoleData` is the usual meromorphic Laplace-transform datum with positive real residues |
| `Level`, `Level.cyc ψ`, `Level.Gm`, `FormB`, `HasWindows` | `ExplicitFormulaErrorOfHostConditions.lean`, `Window.lean:11-28` | Faithful. Weights 1 on the trivial character, 1/(3o+1) on the others |
| `ChebyshevInequalityOnWindows` | `TopWin.lean:24` | Faithful statement of (★), but it quantifies over *families* `Fam`, `core`, `Tied`, so its content depends on what `FamP` and `ChainTied` are. Not checked |
| `Deduction.CH.HostFactsS`, `ArithData`, `primVal`, `GPsi`, `ASK`, `MAIN`, `AskMainBalance` | `DedekindLFunctions/SplitInertia.lean:18`, `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:42-110` | An abstract finite abelian "Galois group" E0 × H with inertia subgroups and Frobenius elements per prime. Nothing ties it to an actual number field (`HostFacts` lists only splitting and ramification shape), so these defs are faithful only up to how a `HostRaw`/`D7` instantiates them (not checked). `ASK` (inert-prime sum) and `MAIN` are honest formulas |
| `UpperTheory.Top.VWin` / `VWinAt` / `VAt` / `VVle` / `IsChiField` / `WinPair` | `CharacterBoxes/ExistsPageN.lean:16-53` | `VVle E t B`: for every algebraic closure and every choice of `LData` (S = places above l, plus a cyclotomic character), Ш¹ of ℚ_l/ℤ_l(e) has finite length for 0 < e < t, and Σ_l log l · Σ_e length ≤ B. `IsChiField` cuts E out of ℚ(ζ_N) by ψ and two Jacobi symbols. **Not judged.** It depends on `Sha1`, `H1` and `locFam` in `Formalism/GaloisCohomology/Statement.lean` (173 lines, not read in full). This is the crux of the RH claim |
| `UpperTheory.GalStar.Row0b` | `Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:73` | Existence of l-adic Galois representations for RACP cuspidal automorphic representations of GL_a over CM fields, with properties `PropsB`. Not checked. If faithful, this is a major theorem (Harris–Taylor–Shin–Chenevier–Harris–Caraiani) |
| `QH.ZeroFreeBox Q χ` (no zeros with Re > 1 − 1/400, \|Im\| ≤ Q), `GoodC`, `Box`, `NoExc`, `J q n` = Jacobi symbol (n/q) | `Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean:46`, `MeanSquareBounds/PrimeSetTwoBounds.lean:17-76` | Faithful, Mathlib-level |
| `Formalism.ZeroFreeDirichlet.InRegion`, `IsLZero`, `ExcZeros`, `negLD`, `psiChi`, `psiAP`; `PI.psi0`, `ZerosBelow`, `ZerosNear` | `Formalism/LandauZeroFreeBounds/Statement.lean`, `SiegelWalfiszAP.lean`, `Formalism/PeriodIntegrals/{ExplicitFormula,ZerosWindow}.lean` | Faithful, 1–3 lines each |

## 5. Mechanical families

- `LandauZeroFreeBounds/ExceptionalZeroBounds/*Of.lean` and `ZeroFreeRegion/ZetaLogDerivativeBounds/*Of.lean`
  (about 15 files). Each is a "Prop implication" combinator `XOf : A → B → … → X`, proved once
  and closed in the top files. Not mechanical case splits, but the reusable content is the closed
  props, not the combinators.
- `*Statement.lean` twins in `GlobalInterpolation` (about 25 one-theorem, 11–13-line files). Each
  re-exports a theorem under a `GlobalTheory.T.*` name.
- `DedekindLFunctions/LandauTheorems/{ChCore, ChBalance, ChTop}` and `PrimitiveCosets/*`
  (19 files, 1,436 lines). Orthogonality and inequality bookkeeping over the abstract host
  group. One pattern, no stand-alone mathematics.
- `ResidueCharacters` (36 files): numeric bounds on lattice exponents (`NumBounds`, `NumCost`,
  `NumRow`, `LocNum`) and p-adic Hodge or crystalline-lattice lemmas on `D7`. Almost entirely
  internal. Exceptions: `SumLogDivSqModPmOneLe.lean` (elementary Σ log l / l² bounds, prime-power
  valuation sum ≤ log n, orders mod 2^K) and `FiniteRoots.lean` (roots of unity in an algebraic
  closure of ℚ_l).
- `CyclotomicBounds` (197 files): 89 files on internal `D7`/`Host`/`Frame`. The rest is
  stand-alone algebra: DVR, lattice and de Rham-period lemmas (`DeRhamLattices/*`, 15 files),
  unitary-Gram diagonalisation over local rings, Skolem–Noether for matrix algebras over local
  rings (`CyclotomicTotient/SkolemNoether.lean:9`, `exists_conj_of_algHom`; `det_algHom` at :131),
  `Monomial.lean` (`torsionOrder_le`: #μ(K) ≤ 2[K:ℚ]²; a finite count of integral unitary
  matrices ≤ #μ(K)^n·n!), `TorsionReduceInjective.tame_ext`, and elementary log-sum bounds.
  No analytic number theory.

## 6. Standalone value

**Effectively proved in usable form (Mathlib objects, small closure, no `sorry`):**

1. The de la Vallée Poussin zero-free region for ζ, ζ′/ζ bounds in it, and PNT with error
   x·exp(−c√log x) (Riesz-weighted). In `ZeroFreeRegion`, 21 files.
2. The Dirichlet zero-free region with at most one simple real exceptional zero (Landau–Page).
   `zFRDirichlet`, 66 files.
3. **Siegel's theorem** L(1,χ) ≫_ε q^{−ε}, the Siegel bound on exceptional zeros, and the
   **Siegel–Walfisz theorem**. About 107 files, all inside `LandauZeroFreeBounds`,
   `ZeroFreeRegion`, `LFunctionBounds`, `ZetaNonvanishing`.
4. The **truncated Perron formula** for ψ(x,χ) and Perron's kernel lemma (Mathlib only, 1–2 files).
   The **contour shift** for primitive L (14 files). The **truncated explicit formula**
   (statement is Mathlib-level, but the proof pulls in 203 or 80 files).
5. Unit-window zero counting, ≪ log(q(\|t\|+2)), and the local zero-sum formula for L′/L. Trivial
   zeros of primitive L-functions are exactly the expected ones and are simple.
6. Generic complex analysis missing from Mathlib: a rectangle residue theorem (poles of order ≤ 2),
   Landau's local lemma and the Jensen/Borel–Carathéodory zero-count bound for f′/f on discs,
   local factorisation by zero order.
7. **Landau's one-sided windowed criterion** (`zeroFree_of_rpow_window`): a one-sided bound
   x^θ on windows for a positive combination of Riesz-weighted character prime sums forces a
   zero-free half-plane Re > θ. This is the converse direction of the usual "GRH ⇒ ψ(x,χ) =
   O(x^{1/2+ε})". It is a correct and useful theorem on its own, for example for "X ⇔ RH"
   statements.
8. A log-free-type zero-density bound near Re = 1 for primitive characters (`ZeroDensityBox`,
   ≪ Q^{1/4} exceptions, 24 files).
9. The final reductions (half-plane ⇒ critical line, imprimitive ⇒ primitive, functional-equation
   reflection) in `ClaimStrip.lean`, 2 files.

**Only special cases or crude constants:** the zero density is fixed at σ = 1 − 1/400, height Q,
and exponent 1/4. It is not a general N(σ,Q,T) bound. The ψ estimates are of de la
Vallée-Poussin strength, not Vinogradov–Korobov. Polynomial growth uses q⁴(\|s\|+2)⁴, with no
convexity bound.

**Misleading names:** `DedekindLFunctions` has no Dedekind zeta functions. It is the Landau
window machinery plus host bookkeeping. In `ChebyshevInequalityOnWindows` and `windowInequality_of_artinInputs`,
"Artin inputs" means the abstract host data, not Artin L-functions. `GlobalInterpolation` is the
home of the explicit-formula core, despite the name. `MeanSquareBounds` is about mean squares of
Jacobi-symbol polynomials over primes q and zero-free boxes for twists. `PeriodIntegrals/ExplicitFormulaCounts`
is a 7-file closing layer: 2 analytic files (explicit formula, zero windows) and 5 representation-theory files
(Weyl dimension, adelic unimodularity, β-independence, additive characters).
The `LiteratureTheorems.*_of_literature` names (Kawamata–Viehweg, Grothendieck–Messing, …) are
fields projected out of a structure `OpenLiteratureStatements`, not proofs of those theorems.

## 7. Open questions / not verified

- **The crux is unread.** I did not check whether `FamP`, `ChainTied`, `HostExW`, `VWin`/`VVle`
  (through `Formalism/GaloisCohomology/Statement.lean`'s `Sha1`/`H1`) and `Row0b` are faithful
  definitions or degenerate ones, i.e. definitions under which the size data are cheap to supply.
  Each analytic step on the spine is classical and plausible. The RH-strength content enters only
  through the bound on ASK − MAIN, which `core_gm` takes from those hypotheses. Any judgment of
  the RH proof has to start there.
- I did not re-derive the windowed Landau theorem's proof. Its statement is mathematically sound
  in my reading: positive real residues plus Pringsheim/derivative oscillation. It typechecks in
  the upstream build, but this box has not rebuilt it.
- Namespaces in §3 come from the `namespace` lines, not from elaboration. Run `#check` before
  you import.
- Adjacent and not inventoried: `GlobalInterpolation` has more Linnik-type results on Mathlib
  objects: `ChebyshevPsiProgressionRelativeError` (`psiAP_relative`: ψ(u;M,b) with relative
  error and an explicit exceptional term for u ≥ M^{c₂}), `LogFreeZeroDensityDirichletOneModulus`,
  `Repulsion` (Deuring–Heilbronn), `RayClassLFunctionZeroFreeRegion`,
  `ExceptionalDirichletZeroUniqueZeroFreeRegion`, `InRegionMono.main : ZFRDirichlet` (a second
  proof). These are likely the strongest classical results in the repo after Siegel–Walfisz.
  Whoever covers `GlobalInterpolation` should read them.
- `Formalism/ZetaNonvanishing` and `Formalism/ZetaRealNonvanish.lean` set up an older ζ·L Landau
  argument (`key_identity`, `Pfun`, Mellin of LamF). I found no closed headline theorem there,
  and its role on the spine is unclear.
