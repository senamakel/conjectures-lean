# riemann-hypothesis inventory 05: `WeilBound`, `EtaleCohomology`, `ResolutionOfSingularities`

Source: [riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) at `507a75d91d`. All paths below are relative to
`src/Development/` unless they start with another top-level directory of `src/`. Nothing was built.
Every claim comes from reading source text. The repo has no licence, so statements are paraphrased, not copied.

## 1. Scope and method

| Subtree | `.lean` files | lines | theorem/lemma decls |
|---|---|---|---|
| `WeilBound/` | 6,798 | 844,308 | 39,765 |
| `EtaleCohomology/` | 1,307 | 103,048 | 6,505 |
| `ResolutionOfSingularities/` | 499 | 142,101 | 6,344 |

Biggest sub-directories: `WeilBound/CoreStatements` (3,581 files; `AutomorphicKernels` 852,
`PadicHodgeComparison` 521, `PublishedTheorems` 519, `HodgeTatePoints` 299, `TorusUniformisation` 194),
`WeilBound/RepresentationTheoryGL` (2,422; `ArchimedeanBaseChange` 762, `SiegelWeilProof` 635,
`UnitaryDualProof` 300), `WeilBound/ThetaLifts` (780), `EtaleCohomology/EtaleSheaves` (625),
`EtaleCohomology/TateTwists` (224), `EtaleCohomology/CohomologicalPurity` (202),
`ResolutionOfSingularities/EmbeddedResolution` (477).

How I worked:
- `rg` for `sorry`, `axiom`, `opaque`, `native_decide`, `implemented_by` and `extern` across all three
  subtrees found **none**.
- I extracted every theorem signature with a script and flagged the ones that mention no repo-defined
  identifier, i.e. statements purely about Mathlib objects. That gave 7,068 in WeilBound, 1,457 in
  EtaleCohomology and 1,717 in ResolutionOfSingularities. Almost all are small helpers. I skimmed
  random samples and keyword-filtered lists (NumberField, adic completions, Schwartz/Fourier, Haar,
  `dedekindZeta`, Gamma, charpoly, Scheme).
- I listed every `theorem X : SomeProp` whose target is a named proposition. This is how the repo
  states its big results: a `def Foo : Prop` holds the statement and a separate theorem proves it. For
  the important ones I opened the `Prop` definition and the structures it uses.
- Read in full: `ResolutionOfSingularities/Statements.lean`, `HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean`,
  `EmbeddedResolution/HironakaTheorem.lean`, `Foundations/BlowupUniversalProperty.lean` and the statement
  lines of `Foundations/Blowup/*`; the étale-cohomology base definitions
  (`AbelianVarietyTheory/Definitions/Divisors/GalMapMul.lean`, `.../DivisorSupportCondition.lean`), and
  `CohomologicalPurity/LeafIndExc.lean`, `InrFold.lean`, `EtaleTrace/LadicH0LocallyConstant.lean`,
  `FrobTraceOf.lean`, `WeilConjectures/FermatCount.lean`; the JS/Landau files under
  `WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/`; the Deligne–Ribet files;
  `NonsplitUniqueness/Places.lean`; `SimpleEigenvalues/.../SimEig.lean`.
- Not read: the bodies of most of the 6,798 WeilBound files, `ArchimedeanBaseChange`, `SiegelWeilProof`,
  `UnitaryDualProof`, `HodgeTatePoints` and `TorusUniformisation`, apart from statement sampling.
  Many headline `Prop`s proved in WeilBound are *defined* in other subtrees
  (`AbelianVarietyTheory/PublishedTheorems`, `ReciprocityTheory`, `AutomorphicSpectrum`). I read
  those statements but audited their internal structures (cuspidal representations `CG`, Hecke characters
  `HChar`, coherent cohomology `coh`) only lightly. Other inventory passes probably own those.

## 2. What these subtrees actually are

**None of the three is what its name promises, except ResolutionOfSingularities.**

- **`WeilBound` contains no Weil bound.** Nothing in it mentions Kloosterman sums, character sums
  over finite fields, curves over finite fields or point counts: `rg Kloosterman` returns 0 hits, and the
  `FiniteField`/`GaussSum` hits are Frobenius identities in helpers and a *local p-adic* Gauss sum. The tree is a
  very large body of automorphic and arithmetic machinery: GL_n over **totally complex** number
  fields (cuspidal spectrum, Satake parameters, the Jacquet–Shalika bound |α| < q^{1/2}, strong
  multiplicity one), Weil-representation / theta / Siegel–Weil, p-adic Hodge–Tate comparison, Galois
  cohomology of G_{F,S} (finiteness, Euler characteristic, Poitou–Tate), nef line bundles and Nadel
  vanishing, and wrapper files that re-export "published theorem" `Prop`s proved elsewhere
  (`CoreStatements/StandardPublishedResults`, `AbelianHeightsDuality/PublishedTheoremStatements/ProvedMore.lean`).
  "Weil" seems to refer to the Weil representation and to the "Ramanujan-type" bound on Satake
  parameters, not to Weil's theorem. Most of it is internal scaffolding, but several pieces of analysis
  are self-contained and stated purely in Mathlib terms (Landau's theorem, an abstract
  Rankin–Selberg rigidity theorem, Euler-product lemmas for `dedekindZeta`).
- **`EtaleCohomology` is a real, if idiosyncratic, foundation of étale cohomology.** Its sheaves
  are Mathlib sheaves of modules on `Scheme.etaleTopology` (the big étale site), and cohomology is
  computed as homotopy classes from the sheafified free chain complex of a simplicial presheaf into a
  chosen injective resolution. The theory is organised as a long list of `Prop` axioms `A1…E8` (quasi-iso
  invariance, Čech descent, Mayer–Vietoris, filtered colimits, homotopy invariance, affine proper base
  change, purity, Poincaré duality, …). Each is proved separately, mostly in
  `AbelianVarietyTheory/Proofs/DivisorProofs` and `AutomorphicArithmetic/CommutativeAlgebra/EtaleCohomology`.
  The subtree's own headline is **cohomological purity (Gysin sequence) for smooth pairs**, which is
  discharged unconditionally downstream. The sub-directory `WeilConjectures` contains **no Weil conjecture
  proof**: the weight statement `EWeil.Model` is only defined and never proved. `EtaleTrace` reduces
  the Lefschetz and Grothendieck–Lefschetz trace formulas to a list of hypotheses (`goal_of`), but most of
  those hypotheses (`LFin`, `LKunneth`, `LPd`, `LTr`, `LFix`, `LCycle`, `LFrobId`, …) have no proof anywhere in
  the repo. Poincaré duality `GlobalTheory.EtC.E8` is never proved either; it is only taken as a
  hypothesis (e.g. `WeilBound/.../BocksteinBaseChange/CstSmoothOfP.lean:44`). `DivisorCycles` is matrix and representation
  theory, and `CyclotomicDiscriminants` is chain-level group homology of cyclic groups. Neither name fits.
- **`ResolutionOfSingularities` really states and proves Hironaka in characteristic zero**, in
  its functorial (Włodarczyk / Bierstone–Milman) form, for Mathlib `Scheme`s, together with functorial
  principalization of ideal sheaves and general existence of blowups. All objects are Mathlib's
  (`Scheme`, `IdealSheafData`, `Smooth`, `IsProper`, `smoothLocus`, `IsRegularLocalRing`). The repo-defined
  predicates are short and faithful (see §4). This is by some distance the most reusable result in the three
  subtrees. In the RH proof it enters through `WeilBound/CoreStatements/ResolutionCharZero` (resolution and
  principalization for projective varieties, feeding Nadel vanishing and nef/bigness), and its
  certificate inductive is the reason `con-leche` / `con-ron` cannot check the export
  (`verification/NOTES.md`).

## 3. Inventory (most reusable first)

| Declaration | path:line | Statement (paraphrased) | Objects | Classical name / reference | Reusability |
|---|---|---|---|---|---|
| `FunctorialResolution.functorialResolutionCharZero` | `ResolutionOfSingularities/HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean:19` | There is a rule assigning to every reduced, quasi-compact, locally finite type scheme X over a char-0 field k a finite sequence of blowups X_r → … → X_0 ≅ X such that: X_r is smooth over k, X_r → X is proper and an isomorphism over the smooth locus, the preimage of the smooth locus is dense, every center lies over the non-smooth locus, and the reduced preimage of the non-smooth locus is a strict normal crossings divisor. The rule is compatible with smooth morphisms (of any relative dimension) and with field extensions, in the sense of `IsPullbackSequence` (empty blowups dropped). Universe-polymorphic. | Mathlib schemes + short faithful defs (`Statements.lean`) | Hironaka 1964; functorial form Bierstone–Milman 1997, Włodarczyk 2005, Kollár's book | **High.** A genuine, general statement. Separatedness is not even required. |
| `FunctorialResolution.functorialPrincipalizationCharZero` | `…/HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean:106` | For X smooth and quasi-compact over a char-0 field, an ideal sheaf I that is nonzero on every irreducible component, and a list E of smooth divisors with SNC: there is a sequence of blowups with smooth centers having SNC with the accumulated boundary, such that the pullback of I becomes the product of exceptional divisors and all levels stay smooth with SNC boundary. Functorial for smooth morphisms and field extensions. | Mathlib schemes + faithful defs | Embedded principalization (Hironaka; Włodarczyk) | **High** |
| `FunctorialResolution.EmbeddedResolution.strongResolutionOfSingularitiesCharZero` | `ResolutionOfSingularities/EmbeddedResolution/HironakaTheorem.lean:74` | The same theorem in the internal `ResolutionRule` / `IsStrongResolution` vocabulary (the form the two above repackage). | same | Hironaka | High (use the repackaged form) |
| `FunctorialResolution.Blowup.exists_isBlowupAlongIdealSheaf` | `ResolutionOfSingularities/Foundations/Blowup/BlowupExistence.lean:712` | Every scheme X and every quasi-coherent ideal sheaf I have a blowup: a morphism π: Y → X such that the pullback of I is locally generated by a nonzerodivisor and π is universal for that property. Also `blowup I` / `blowup.proj I` (:718, :721). | Mathlib schemes; `IsBlowupAlongIdealSheaf` = universal property | Blowup existence (Hartshorne II.7.13–14, Stacks 0806) | **High.** Mathlib has no general blowup. |
| `FunctorialResolution.Blowup.blowupIsProper` / `isProper_of_isBlowupAlongIdealSheaf` | `…/Foundations/Blowup/BlowupProper.lean:93, :105` | A blowup of a locally Noetherian scheme is proper. | Mathlib | Standard | High |
| `FunctorialResolution.Blowup.blowupIsIsoOffCenter` | `…/Foundations/Blowup/BlowupIsoOffCenter.lean:23` | A blowup restricts to an isomorphism over the complement of the support of the center. | Mathlib | Standard | High |
| `…StrictTransform.*`, `IsBlowupAlongIdealSheaf.{existsUnique_lift, exists_iso, pullback_snd_of_isOpenImmersion}` | `…/Foundations/Blowup/StrictTransform.lean`, `BlowupBasic.lean:108-146`, `BlowupExistence.lean:71` | Strict transform, uniqueness of blowups up to isomorphism, compatibility with open immersions. | Mathlib | Standard | Med–high (blowup API) |
| `GlobalTheory.Published.Principalisation` via `principalisation_closed` | `WeilBound/CoreStatements/ResolutionCharZero/PrincipalisationClosed.lean:18` (statement in `AbelianVarietyTheory/PublishedTheorems/Divisors₂/GeometricallyConnectedOfIsIsoRestrict.lean:110`) | Y integral, smooth of relative dimension d and projective over a char-0 field k, I ≠ 0. Then a smooth-centered blowup sequence s: Y′ → Y exists with Y′ integral, smooth and projective, s an isomorphism off V(I), I·O_{Y′} effective Cartier, and its support SNC. | Mathlib schemes + `IsProjOver`, `IsSmoothBlowupSeq` (internal) | Log resolution / principalization, projective case | High (projective corollary) |
| `resolutionCharZero` | `WeilBound/CoreStatements/ResolutionCharZero/ResolutionCharZero.lean:10` (stmt `AutomorphicSpectrum/PublishedTheorems/Geometry₂/ConclusionOfSmooth.lean:51`) | Non-functorial resolution at universe 0 for separated schemes; `.projective` keeps projectivity. | Mathlib + internal `IsBlowupSeq` | Hironaka | Med (weaker than the first row) |
| `UpperTheory.Et.purGysin` (purity, Gysin sequence) | proved `AutomorphicArithmetic/CommutativeAlgebra/EtaleCohomology/PurTop.lean:133` from the leaves in `EtaleCohomology/CohomologicalPurity/*`; hypotheses discharged at `AutomorphicArithmetic/Foundations/GaloisRepresentations/KunnethLefschetz/EtSideGood.lean:47`; statement `Gysin` at `EtaleCohomology/CohomologicalPurity/LeafIndExc.lean:14` | Take a smooth pair Z ⊂ X over S (X smooth of relative dimension e+d, Z closed and smooth of relative dimension e, U = X∖Z) and q invertible on S. Then Gysin and residue maps exist that give a long exact sequence … → H^{n+2d−1}(U, μ_q^{⊗(i+d)}) → H^n(Z, μ_q^{⊗i}) → H^{n+2d}(X, μ_q^{⊗(i+d)}) → H^{n+2d}(U, …) → …, natural under cartesian maps of pairs, compatible with cup product and with reduction mod r ∣ q. | Mathlib schemes; internal cohomology `Ht` (faithful, §4) | Absolute cohomological purity for smooth pairs (SGA 4 XVI, SGA 4½ "Cycle") | Med–high. Real theorem, but tied to the repo's cohomology API. |
| `GlobalTheory.EtC.{A1…A11,B1…B7,C1…C5,D1…D3,E1…E4,E6}` | statements `AbelianVarietyTheory/Definitions/Divisors/DivisorSupportCondition.lean`; most proofs in `AbelianVarietyTheory/Proofs/DivisorProofs/*`, `E1` at `AutomorphicArithmetic/CommutativeAlgebra/EtaleCohomology/AffineProperBaseChange.lean:30` | Axioms of the étale theory, each proved: e.g. A1 quasi-iso invariance, A2 Čech descent along smooth surjections, A9 H^0 = sections and H^{<0} = 0, B1 continuity along filtered colimits of rings, C4 𝔸¹-homotopy invariance, C5 cohomology of 𝔾_m over strictly henselian rings, D1 projective bundle formula, E1 affine proper base change for henselian pairs (Gabber), E6 the purity corollary. | Mathlib schemes + internal `Ht` | SGA 4, Gabber's affine analogue | Medium (a usable étale library, not Mathlib-compatible). Mostly outside my subtree. |
| `GlobalTheory.EtC.E8` (Poincaré duality) | `AbelianVarietyTheory/Definitions/Divisors/DivisorSupportCondition.lean:158` | Statement only, **no proof found**. Used as a hypothesis in `WeilBound/.../BocksteinBaseChange/CstSmoothOfP.lean:44` (a path the main proof does not take). | | Poincaré duality | None (unproved) |
| `LateralTheory.EtaleTrace.lefschetz_of`, `frobTrace_of`, `goal_of` | `EtaleCohomology/EtaleTrace/FrobTraceOf.lean:12, :55, :72` (stmts `LadicH0LocallyConstant.lean:102,112,130`) | Lefschetz fixed-point formula for correspondences (c, a) with a finite étale, and Grothendieck–Lefschetz Frobenius trace formula, **conditional** on about 15 leaf hypotheses, most of which are never proved. | internal | Grothendieck–Lefschetz | Low (skeleton only) |
| `LateralTheory.DivDb.etale_open_coset_condition_holds_assembled` | `EtaleCohomology/DivisorCycles/FinFinDense.lean:15` (stmt `OpenCoset.lean:138`) | For a compact topological group Γ, any homomorphism r: Γ → GL_n(C) and a polynomial f in matrix entries vanishing on r(O) for some nonempty open O: f vanishes on r(gU) for some finite-index normal subgroup U and some g. No continuity of r is assumed. | Mathlib only (`MvPolynomial`, `GL`) | Zariski-closure / identity-component argument | Medium |
| `LateralTheory.DivDb.goal_holds` (`DivWCoreLac`) | `EtaleCohomology/DivisorCycles/GoalHolds.lean:23` (stmt `WeilBound/CoreStatements/PadicHodgeComparison/CocharacterLieDivisors/DivWCoreLacUseType.lean:27`) | For a continuous semisimple representation ρ of a compact group over an algebraically closed char-0 topological field, with degree-n monic polynomials P_s annihilating ρ(s) on a dense set, plus a Lie/Zariski condition: there is an n-dimensional continuous semisimple representation r with related characteristic polynomials and a prescribed determinant. | Mathlib + small internal defs (`IsSSMat`, `InLieZar`) | "Subrepresentation from char-poly factors" (Chenevier/Rajan-type) | Low–med (specialised) |
| `PositivityTheory.RgJS.landauL` (stmt `LandauL`) | `WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean:252` (def `…/AbsoluteRigidity/NewtonLow.lean:37`) | Let c_i, l_i ≥ 0 and suppose F(σ) = exp(Σ_i c_i e^{−l_i σ}) for real σ > σ₁, with the series converging there. If F is complex-analytic at every real σ > σ₀, then the series converges for every σ > σ₀. | **Mathlib only** | Landau's theorem (nonnegative Dirichlet series), exponential form | **High.** Usable directly for nonvanishing arguments. |
| `…AbsoluteRigidity.LandauIteratedDerivatives.hasSum_iteratedDeriv`, `summable_pow`, `propagate` | same file :37, :14, :81 | Termwise differentiation of generalized Dirichlet series with nonnegative data; analytic continuation along the real axis. | Mathlib only | | Medium |
| `PositivityTheory.RgJS.newton_identities_low_degree` (`NewtonLow`) | `…/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean:88` (def `NewtonLow.lean:42`) | For each N ≥ 1 there is c > 0 such that any N complex numbers with ∏|a_i| = 1 satisfy Σ_{k=1}^{N} |Σ_i a_i^k|² ≥ c. | Mathlib only | Newton identities | Medium |
| `PositivityTheory.RgJS.euler_product_log_bound` (`EulerLog`) | `…/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean:107` | For "prime-like" weights q_w ≥ 2 (Σ q^{−σ} < ∞ for σ > 1) and parameters with |α|, |β| ≤ √q_w: for Re s > 2 the Rankin–Selberg Euler product ∏_w ∏_{a,b}(1 − α ᾱ′ q^{−s})^{−1} converges and equals exp of the absolutely convergent log series. | Mathlib only (abstract) | Rankin–Selberg log expansion | Medium |
| `PositivityTheory.RgJS.removable_singularity_holds` (`Remov`) | `…/AbsoluteRigidity/RemovableSingularities/RemovableSingularityHolds.lean:57` | If G is analytic on the real points σ > 0 and |G(σ)| ≤ M(σ−1)^r on (1,2], then G = (σ−1)^r G′ on σ > 1 with G′ analytic at the real points σ > 0. | Mathlib only | | Low–med |
| `PositivityTheory.RgJS.absRig_closed` (`AbsRig`) | `…/AbsoluteRigidity/AbsRigClosed.lean:23` (defs `NewtonLow.lean:21-71`) | Abstract linear independence of Satake systems. Take weights q (≥ 2, Σq^{−σ} < ∞ for σ > 1, Σ1/q = ∞) and parameter families A_x with |A| ≤ √q and |det| = 1, such that each Rankin–Selberg product L(A_x × Ā_y, σ) times (σ−1)^{δ_xy} is analytic at real σ > 0. If two finite families of (x, real shift) have identical twisted power sums at every w and every k, they agree up to a bijection. | **Mathlib only** (abstract structures `Sys`, `Primes` are explicit and nondegenerate) | Jacquet–Shalika / Moreno-style strong multiplicity one from Rankin–Selberg | **High** for Dirichlet/Hecke L-function distinctness and multiplicity-one style arguments |
| `PositivityTheory.RgJS.PrimeSumConvergesAndDiverges.not_summable_all`, `prime_sum_converges_and_diverges` | `…/AbsoluteRigidity/PrimeNonSummability/PrimeSumConvergesAndDiverges.lean:23, :53` | For any number field E, Σ_𝔭 1/N𝔭 diverges, also with finitely many primes removed, and Σ N𝔭^{−σ} converges for σ > 1. | Mathlib only | Divergence of Σ 1/N𝔭 | Medium–high |
| `…ZetaEulerProducts.dedekindZeta_eq_exp`, `summable_primes_rpow`, `two_le_absNorm'` | `WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/SummablePrimesRpow.lean:13, :59, :52` | For Re s > 1, Mathlib's `dedekindZeta K s` equals exp(−Σ_𝔭 log(1 − N𝔭^{−s})). Σ_𝔭 N𝔭^{−σ} < ∞ for σ > 1. N𝔭 ≥ 2. | **Mathlib only** | Euler product for ζ_K | **High** |
| `…ZetaEulerProducts.gammaInv_zo`, `invGammaR_zo`, `invGamma_zo` | `…/ZetaEulerProducts/ZetaOrd.lean:42`, `InvGammaRZo.lean:58, :12` | Exact zero orders at nonpositive integers of 1/Γ, 1/Γ_ℝ and 1/(Γ_ℝ^{r₁} Γ_ℂ^{r₂}) (via an explicit internal predicate `ZO` = "f = (s−x)^m·u with u analytic, u(x) ≠ 0 near x"). | Mathlib + 1-line faithful def | Trivial zeros of completed ζ_K | Medium |
| `PositivityTheory.PfDR.deligneRibet_holds` / `PositivityTheory.PfDRL.deligneRibet` | `WeilBound/CoreStatements/AutomorphicKernels/DeligneRibet/DeligneRibetHolds.lean:7`, `NotDvdAbsNorm.lean:135` (stmt `AbelianVarietyTheory/PublishedTheorems/Divisors₂/SiegelKlingenDeligneRibet.lean:49`) | F totally real, l prime, n ≥ 1, ε an l-integral ℚ-valued function on narrow ray classes mod l^n, 𝔠 prime to l. For k ≥ 1, L(ε, 1−k) − N𝔠^k·L(ε(𝔠·), 1−k) ∈ ℤ_(l). Values are defined via the unique analytic continuation of Σ ε(I) N I^{−s} to ℂ∖{1}. | NumberField, ideals, `absNorm`; `CoprimeTo`/`RayRel` (faithful narrow-ray-class defs in `Formalism/SharpRestriction/GlobalSchurBounds/ShortIntervalPrimes.lean:25-30`) | Deligne–Ribet 1980 / Cassou-Noguès (integrality of smoothed partial zeta values) | **High** if the partial-zeta continuation (proved in `AutomorphicSpectrum`) is accepted. WeilBound only assembles. |
| `siegelKlingen_holds`, `partialZetaFunctionalEquation_holds` (re-exports) | `WeilBound/CoreStatements/AbelianHeightsDuality/PublishedTheoremStatements/ProvedMore.lean:105, :90` | Siegel–Klingen: for F totally real and any ray-class-invariant ε, L(ε, 1−k) ∈ ℚ for all k ≥ 1. Functional equation of partial zeta functions of (wide) ideal classes of a totally real field, with Γ_ℝ^n and d_F^{s/2}. | Mathlib-level | Siegel 1970 / Klingen 1962; Hecke | High, but **proved in `CompanionTheory`**, not here |
| `PositivityTheory.tft.PlacesPf.split_infinite`, `unique_of_not_split`, `unr_cofinite`, `absNorm_eq` | `WeilBound/NonsplitUniqueness/Places.lean:29, :50, :39, :62` | For E/F Galois, infinitely many primes of F split completely (via Dirichlet density 1/[E:F]). If [E:F] is prime and v does not split, there is a unique place above v. Almost all v are unramified. N𝔓 = N𝔭^{f}. | Mathlib (+ two-line internal `Split`/`Unr`) | Chebotarev for split primes (density cited from `GroundTheory/GlobalFields/TateThesis/DegreeOneDensity`) | Medium–high |
| `UpperTheory.V.LinAlg.simEig` | `WeilBound/SimpleEigenvalues/SimpleEigenvalueExtension/SimEig.lean:7` | A commuting family of endomorphisms of a finite-dimensional space over an algebraically closed field has a common eigenvector in any nonzero invariant subspace. | Mathlib only | Standard | Medium (small, clean) |
| `…ChowMahlerFamilies.conj_of_charpoly_eq` | `WeilBound/CoreStatements/TorusUniformisation/ChowMahlerFamilies/CharZeroFreeModule.lean:150` | Two semisimple endomorphisms (of possibly different spaces) with equal characteristic polynomials are conjugate. | Mathlib only | Standard | Medium |
| `PositivityTheory.Xgn.kernel_rank_norm_bound`, `charpoly_lsmul` | `…/ChowMahlerFamilies/KernelRankNormBound.lean:189, :87` | For a ℤ-free finite 𝓞_E-module Λ and 0 ≠ a ∈ 𝓞_E, the char-p kernel of multiplication by a has dimension ≤ rank·v_p(N(a)), and the char poly of a on Λ is (char poly on 𝓞_E)^{rank}. | Mathlib only | | Medium |
| `natAbs_discr_mem_different`, `coprime_different`, `not_sq_dvd`, `glue_split` | `…/ChowMahlerFamilies/NatAbsDiscrMemDifferent.lean:161`; `WeilBound/CoreStatements/HodgeTatePoints/Gsplit.lean:13, :26, :45` | \|disc F\| lies in the different. p ∤ disc ⇒ (p) is coprime to the different and squarefree, with idempotent-like separating elements. | Mathlib only | Dedekind's discriminant theorem (one direction) | Medium |
| `GlobalTheory.T.number_field_to_mod_p_squared` | `WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/NumberFieldToModPSquared.lean:9` | For finitely many elements of a number field and any n, there is a prime p > n with a ring map from the subring they generate to ℤ/p². | Mathlib only | | Low–med |
| `…LineFunctionPlaceValuation.exists_place`, `place_unique` | `…/ChowMahlerFamilies/LineFunctionPlaceValuation.lean:21, :25` | Every embedding K → ℂ_p comes from a unique finite place 𝔭 of K (same unit ball). | Mathlib only | | Medium |
| `…MinimalPrimeDimensions.mem_of_forall_valuationSubring` | `WeilBound/CoreStatements/MinimalPrimeDimensions/MemOfForallValuationSubring.lean:11` | An integrally closed domain equals the intersection of the valuation rings of its fraction field that contain it. | Mathlib only | Krull | Medium |
| `…SchwartzMoments.dense_compactSupport` | `WeilBound/ThetaLifts/SchwartzMoments/DenseC.lean:14` | Compactly supported Schwartz functions are dense in 𝓢(V, ℂ) for finite-dimensional real V. | Mathlib only | | Medium |
| `…PolynomialGaussianIntegrals.fourierInv_poly_gauss` | `WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean:188` | The inverse Fourier transform of (polynomial) × Gaussian on Euclidean space is (polynomial of no larger degree) × Gaussian. | Mathlib only | | Medium |
| `…covol_unique`, `right_of_fd`, `fd_fin`, `int_indep`, `integral_right` | `…/SiegelWeilFormula/WhittakerCovolume/CovolUnique.lean:11`; `WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/RightOfFd.lean:41, :29, :79`; `ThetaLifts/CartanFactorisation/IntegrableOnRight.lean:25` | Haar measures on Γ\G: a cocompact discrete Γ has a fundamental domain of finite measure. Finite covolume forces right-invariance (unimodularity). Integrals over normalised fundamental domains do not depend on the choices. Right translation preserves integrals of Γ-invariant functions. | Mathlib only | Standard | Medium |
| `…FacNeGauss.gauss_ne_zero` | `WeilBound/ThetaLifts/WeilDomination/FacNeGauss.lean:430` | A local Gauss sum of a continuous character of F_v^× that is ramified (nontrivial on units), against an unramified additive character, is nonzero. | Mathlib completions + internal `gauss`, `PsiUnr` | Local Gauss sums (Tate) | Low–med |
| `PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound` | `WeilBound/CoreStatements/PublishedTheorems/JacquetShalikaBound/JacquetShalikaBound.lean:83` (stmt `AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/StrongMultiplicityOne.lean:201`) | For unitary cuspidal π of GL_a over a **totally complex** number field E, every unramified Satake parameter α at w satisfies N w^{−1/2} < \|α\| < N w^{1/2}. | NumberField + internal `CG E a` (not audited) | Jacquet–Shalika 1981 bound | Medium (only totally complex E; depends on `CG`) |
| `PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity` | `WeilBound/CoreStatements/PublishedTheorems/JacquetShalikaRigidity/JacquetShalikaRigidity.lean:17` (stmt same file as above, :193) | Strong multiplicity one / rigidity of isobaric sums: if two finite families of cuspidal π have equal Satake-parameter multisets at almost all w, they agree up to permutation. | internal `CG` | Jacquet–Shalika 1981 | Medium |
| `GlobalTheory.nefRiemannRoch`, `NefProductNonneg` | `WeilBound/CoreStatements/PublishedTheorems/NefNumerics/NefRiemannRoch/NefRiemannRoch.lean:24`, `NefProductNonneg.lean:24` (stmts `AbelianVarietyTheory/PublishedTheorems/Divisors₂/ExistsAlgClosedBaseChange.lean:19-35`) | For X projective of dimension D over an algebraically closed field and L nef: h^0(L^m) = (L^D/D!)·m^D + O(m^{D−1}). Intersection numbers of nef bundles are ≥ 0. | Mathlib schemes + internal `LB`, `coh`, `interNum` (Snapper-style χ alternating sum; looks faithful, not audited) | Asymptotic Riemann–Roch for nef bundles; Kleiman | Medium |
| `PositivityTheory.Lit1.ClozelPurity.clozelPurity` | `WeilBound/CoreStatements/PublishedTheorems/ClozelPurity/Bridge.lean:10` | Cohomological cuspidal π of GL_a over totally complex E: the infinitesimal characters at τ and τ̄ are related by z ↦ w₀ − z for one integer w₀. | internal `CuspSub` | Clozel's purity lemma | Low–med |
| `PositivityTheory.Lit1.GF.globalFiniteness`, `GlobalEulerChar`, `poitouTateNormalised_holds` | `WeilBound/CoreStatements/PublishedTheorems/GlobalFiniteness/GlobalFiniteness.lean:14`, `GlobalEulerCharacteristic/GlobalEulerCharOfLemmaX.lean:17`, `PoitouTateDuality/PoitouTateNineTerm/PoitouTateNormalisedHolds.lean:22` (stmts `ReciprocityTheory/Hypotheses/GalCoh.lean:160-172`) | Finite ℤ/l^r-modules with continuous G_{F,S}-action: finiteness of H^i(G_{F,S}, M), Tate's global Euler characteristic formula, Poitou–Tate. | NumberField + internal profinite cohomology and `GS` (not audited) | Tate 1962, Poitou–Tate | Medium if the internal cohomology is faithful |
| `CrystallineSemistableComparison.HT.hodgeTate_of_etale_side`, `Onto.htBij_of_parts` | `WeilBound/CoreStatements/PadicHodgeComparison/EtaleCohomologyComparison/HodgeTateResidues/HodgeTateComparisonSmoothProjective.lean:21`; `…/HodgeSurjectivity/HtBijOfParts.lean:21` | For smooth proper "models" over finite extensions K/ℚ_l: a Hodge–Tate comparison map, with dim H^n_et = Σ_a dim H^{a,n−a}. Discharged in `AutomorphicArithmetic/Foundations/GaloisRepresentations/CrystallineTowers/ClosedHT.lean:19-25`. | internal `Model`, `HTPre` (not audited) | Faltings / Hodge–Tate decomposition | Low–med (heavy internal dependencies) |
| `PositivityTheory.DM.dixmierMalliavinFactorisation_holds` | `WeilBound/CoreStatements/AbelianHeightsDuality/DixmierMalliavin/DixmierMalliavinFactorisationHolds.lean:108` | Dixmier–Malliavin factorisation (statement in `AbelianVarietyTheory/.../IsClosedEmbeddingOfLocallyCompact.lean:18`, not read in detail). | mixed | Dixmier–Malliavin 1978 | Low–med |
| `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement` | `WeilBound/CoreStatements/AutomorphicKernels/MoriwakiBigness/MoriwakiBigTheorem/Outright.lean:13` | Arithmetic bigness criterion (Moriwaki). Statement in `ReciprocityTheory/.../MoriwakiSt.lean:22`, not audited. | internal Arakelov | Moriwaki | Low |

Re-exports without proofs here (`CoreStatements/StandardPublishedResults/StandardTheoremStatements/*`,
`ProvedMore.lean`): global Artin reciprocity, Hecke L entire and nonzero at 1, quadratic class field theory, Weber
ray class fields, the CM main theorem for elliptic curves, Stone–von Neumann, the Hermitian Hasse principle, Siegel–Klingen, and the
partial zeta functional equation. Their statements look faithful (I checked `IsGlobalArtin`,
`WeberRayFieldSt`, `EllipticMainTheoremCM`, `StoneVonNeumann`), but the proofs live in `CompanionTheory`,
`AbelianVarietyTheory` and `AutomorphicSpectrum`. They belong in those subtrees' inventories.

## 4. Internal definitions worth knowing

| Definition | Where | Verdict |
|---|---|---|
| `FunctorialResolution.IsEffectiveCartier`, `IsBlowup` / `Blowup.IsBlowupAlongIdealSheaf` | `ResolutionOfSingularities/Statements.lean`, `Foundations/BlowupUniversalProperty.lean:17-24` | **Faithful.** "Locally generated by one nonzerodivisor on affine opens" plus the universal property of the blowup, using Mathlib's `IdealSheafData.comap` (the inverse-image ideal sheaf). |
| `IsRegularSystemOfParameters`, `IsStrictNormalCrossings(At)` | `Statements.lean` | **Faithful.** Regular local stalk; the divisor ideal is locally a product of a subset of a regular system of parameters. Uses Mathlib `IsRegularLocalRing`, `ringKrullDim`. |
| `BlowupSequence`, `IsPullbackSequence`, `CentersOver`, `nonSmoothLocus`, `reducedPreimage` | `Statements.lean` | **Faithful.** A tower indexed by ℕᵒᵖ, with only the first `length` steps required to be blowups. The pullback relation allows dropping blowups with empty centers, as functorial resolution requires. |
| `HasSimpleNormalCrossings(With)`, `IsSmoothDivisor`, `strictTransform`, `IsPrincipalizingSequence` | `Statements.lean` | **Faithful.** SNC via étale charts to 𝔸^m over k, with each divisor a coordinate hyperplane. |
| `PrincipalizationCertificate` / `OrderCertificate` | `ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/…` | A mutual reflexive inductive certificate of the order-reduction recursion. Sound in Lean, but some external kernels reject it (NOTES.md). |
| `GlobalTheory.EtC.Shv`, `Spc`, `chains`, `res`, `H`, `Ht q E n i`, `HQ`, `pull`, `cup` | `AbelianVarietyTheory/Definitions/Divisors/GalMapMul.lean:86-151`, `PullHlComp.lean:70-255` | **Faithful in design.** Sheaves of `ULift R`-modules on Mathlib's big `Scheme.etaleTopology`. A "space" is a simplicial presheaf, H^n is homotopy classes from its free sheafified chain complex to a chosen injective resolution (hypercohomology = H^n_et), and `Ht q` uses ℤ/q coefficients twisted by μ_q^{⊗i}. Nonvacuity rests on the proven axioms (A9 identifies H^0 with sections). |
| `GlobalTheory.EtC.A1…E8` | `AbelianVarietyTheory/Definitions/Divisors/DivisorSupportCondition.lean` | Statements of standard étale facts, not axioms. All are proved somewhere except **E8 (Poincaré duality), which is unproved**. |
| `LateralTheory.CohomologicalPurity.SP d` (smooth pair) | `EtaleCohomology/CohomologicalPurity/InrFold.lean:110` | Faithful: X smooth of relative dimension e+d over S, Z ⊂ X closed and smooth of relative dimension e, U = X∖Z. |
| `LateralTheory.EtaleTrace.Lefschetz`, `FrobTrace`, `EWeil.WtIn` / `EWeil.Model` | `EtaleTrace/LadicH0LocallyConstant.lean:102-130`, `WeilConjectures/FermatCount.lean` | Faithful-looking statements (Lefschetz number = fixed-point count, Frobenius weights via eigenvalue absolute values), but **unproved**. They are only defined or reduced to unproved leaves. |
| `PositivityTheory.RgJS.Primes`, `Sys`, `eul`, `lterm`, `Rel`, `AbsRig` | `WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLow.lean:15-71` | **Faithful and nondegenerate.** Everything is explicit: real weights, complex parameters, `tsum`/`tprod`, `AnalyticAt`. A user would have to construct `Sys` for their own L-functions (bounds \|α\| ≤ √q, \|det\| = 1, and Rankin–Selberg analyticity with a pole only on the diagonal). |
| `CoprimeTo`, `RayRel` | `Formalism/SharpRestriction/GlobalSchurBounds/ShortIntervalPrimes.lean:25-30` | **Faithful.** Narrow ray class equivalence mod 𝔣·∞ (totally positive a, b ≡ 1 mod 𝔣 with aI = bJ). |
| `ZO f x m` | `WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean:14` | Faithful: "f has a zero of order exactly m at x (punctured nbhd)". |
| `CG E a`, `CuspSub E a`, `HChar`, `Ideles`, `IsGlobalArtin` | `AbelianVarietyTheory/...` | Not audited here. `IsGlobalArtin` (open quotient map, kernel = closure of E^× · connected component, inertia, Frobenius and decomposition compatibility) looks faithful. Note that every GL_n result is over **totally complex** fields only. |
| `LB`, `IsNef`, `interNum`, `lbH0`, `coh` | `AbelianVarietyTheory/Definitions/...` | Looks faithful: nef via curves, intersection numbers via Snapper's alternating χ. `lbH0` uses `finrank`, which silently returns 0 for an infinite-dimensional space, but the theorems assume projectivity. Not audited further. |

## 5. Mechanical families

- `EtaleCohomology/**/Fin*.lean`, `*Cut.lean`, `*Pf.lean`, `Leaf*.lean` (about 900 files): each `Leaf…` is a named
  lemma-`Prop`, each `…Pf` proves it, and each `Fin…` assembles the proofs. Many assembled theorems carry the
  meaningless name `intersectionNumber_baseChange`, about 40 times. Characterise by the `Leaf` statement, never by the name.
- `CohomologicalPurity/Leaf*` (202 files): diagram chases (five-lemma, filtered colimits of long exact sequences),
  Thom class construction, excision and henselisation for the Gysin sequence.
- `EtaleSheaves/*` (625): sheaf-level exactness criteria, Čech/Mayer–Vietoris, ind-étale and henselian limits,
  the Kummer sequence, and charts of the projective line.
- `TateTwists/*` (224): μ_q^{⊗i} sheaves, Alexander–Whitney cup products and their Leibniz rule and associativity.
- `WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange` (762) and `SiegelWeilProof` (635): local and global GL_n and
  unitary-group computations (Satake exponents, Iwahori factorisations, theta norm commutation). Helpers mostly
  concern specific internal structures.
- `WeilBound/CoreStatements/AutomorphicKernels` (852), `PadicHodgeComparison` (521), `HodgeTatePoints` (299),
  `TorusUniformisation` (194): chains of `XStatement`/`St…` `Prop`s with `…_holds` proofs. About 7,000 small Mathlib-level
  helpers in total (valuations, adic completions, Haar, Schwartz seminorms, tensor products).
- `ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization` (219) and `ResolutionDescent` (69): order and
  coefficient ideals, maximal contact, marked blowup sequences, descent from affine to global. This is real
  mathematics, but only useful through the headline theorems.
- `EtaleCohomology/DivisorCycles` (56): matrix and Zariski-closure lemmas (`Zcl`, `Tan`, idempotent systems).
  `CyclotomicDiscriminants` (12): signed-sum and chain identities for cyclic group homology.

## 6. Standalone value

**Proved in usable, general form:**
- **Functorial resolution of singularities and functorial principalization in characteristic 0**
  (Hironaka, Włodarczyk-style), for reduced quasi-compact finite-type schemes over any char-0 field, in any universe.
- Existence, properness and iso-off-center of **blowups of arbitrary schemes along ideal sheaves**.
- **Landau's theorem** for exponentials of nonnegative generalised Dirichlet series.
- **Abstract Rankin–Selberg rigidity** (`AbsRig`): an abstract strong-multiplicity-one theorem.
- The Euler product of `dedekindZeta` as exp-log, Σ N𝔭^{−σ} < ∞ (σ > 1), Σ 1/N𝔭 = ∞.
- Infinitely many split primes in Galois extensions (from a Dirichlet-density result proved in `GroundTheory`).
- Small linear-algebra and Haar/Schwartz facts (common eigenvectors, conjugacy from char polys, density of
  C_c in Schwartz space, unimodularity from a finite-covolume lattice).

**Proved, but only in a special case or modulo internal definitions:**
- Deligne–Ribet: only for moduli l^n and totally real F. Fine as stated, but WeilBound only assembles it.
- Purity / Gysin sequence: smooth pairs only, and it lives in the repo's own étale cohomology, not Mathlib's
  (Mathlib has none). Usable only by adopting that API.
- Jacquet–Shalika bound, strong multiplicity one, Clozel purity, cuspidal spectrum: GL_n over **totally complex**
  number fields only, on internal automorphic objects.
- Nef asymptotic Riemann–Roch: projective varieties over algebraically closed fields, internal coherent cohomology.
- Galois cohomology (finiteness, Euler characteristic, Poitou–Tate) and Hodge–Tate comparison: internal cohomology objects, not audited.

**Misleading names:**
- `WeilBound`: no Weil bound for curves, exponential sums or Kloosterman sums anywhere.
- `EtaleCohomology/WeilConjectures`: étale-neighbourhood and Chevalley-type lemmas. The Weil-weight statement is defined, never proved.
- `EtaleCohomology/EtaleTrace`: the Lefschetz / Frobenius trace formulas are conditional skeletons.
- `EtaleCohomology/DivisorCycles` (matrices) and `CyclotomicDiscriminants` (group-homology chains).
- `CohomologicalPurity/FinLeafExc.lean:34 intersectionNumber_baseChange` and its siblings prove unrelated
  `Prop`s; the name is a stamp.
- `WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/*` reuses the names `A1`, `A2`, `A9`, `C5`, `D1` for
  statements unrelated to the étale `GlobalTheory.EtC.A1…`, so beware of name collisions when grepping.

## 7. Open questions / not verified

- Nothing was compiled. "Proved" means: a theorem exists with this type, the subtree contains no `sorry`/`axiom`,
  and its hypotheses are discharged by named theorems I traced one or two levels deep. The whole-repo axiom
  check is in `verification/NOTES.md` (comparator accepted `Main` with the standard three axioms).
- I did not trace whether every leaf of `functorialResolutionCharZero` is reached without hidden hypotheses beyond
  the `HironakaTheorem.lean` chain. All the top-level arguments are closed terms, but I read only the top two levels.
- The faithfulness of `CG`/`CuspSub` (cuspidal automorphic representations), `HChar`, the profinite cohomology behind
  `GlobalFiniteness`/`PoitouTate`, `Model`/`HTPre` (Hodge–Tate), and the coherent `coh` was not audited.
- `PartialZetaFunctionalEquation` uses the **wide** class group with a Γ_ℝ(s)^n factor and pairs C with C′ where
  C·C′ = [different]. That is plausible for unramified class characters, but I did not check signs or normalisations.
- Whether `EtaleTrace`'s unproved leaves are proved under other names elsewhere: a regex search over the repo for
  theorems of types `LFin`, `LKunneth`, `LPd`, `LTr`, `LFix`, `LCycle`, `LFrobId`, `Lefschetz` and `FrobTrace`
  found none, but a differently phrased proof could exist.
- E8 (étale Poincaré duality) appears only as a hypothesis. I found no proof, so treat it as unproved.
