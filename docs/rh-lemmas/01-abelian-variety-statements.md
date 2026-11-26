# riemann-hypothesis lemma inventory 01: `Development/AbelianVarietyTheory` (everything except `Proofs/`)

Repo: [riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) at `507a75d91d`. Paths below are relative to
`src/Development/AbelianVarietyTheory/` unless they start with `src/`. Nothing was built: every
"proved" claim below means "a closed term `theorem foo : P := ...` with no hypotheses exists in the
source tree". Whether Lean accepts it was not checked (the build is the untrusted community cache;
see the workspace `AGENTS.md`). No code is quoted, only paraphrase.

## 1. Scope and method

| Subdir | .lean files | lines | `theorem`/`lemma` | `def`/`structure`/... |
|---|---|---|---|---|
| Definitions | 1862 | 338,118 | ~17,400 | ~20,300 |
| BlockTheory | 488 | 44,463 | ~720 | ~4,570 |
| PublishedTheorems | 363 | 37,084 | ~1,440 | ~1,320 |
| Counterexamples | 148 | 11,672 | ~570 | ~50 |
| Statements | 78 | 6,462 | ~130 | ~380 |
| CrystallinePeriods | 12 | 3,030 | ~250 | ~20 |
| (Proofs/, not mine) | 78,548 | 6.56 M | | |

Method:
- **PublishedTheorems**: I extracted all 391 `def X : Prop` names (the "published theorem"
  statements) and read the full statement of about 70 of them, chosen for being about Mathlib
  objects or for having a big classical name. For each of the 391 I checked whether it is proved:
  (a) by grepping all of `src/` for a closed `theorem _ : X :=` (197 hits), and (b) by checking
  whether it is a target of one of the `*_of_literature` theorems in
  `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`,
  which is on the path to `Main.lean` (another 23). The remaining ~170 have no closed proof I could
  find. A proof spread over several lines in an unusual form could have escaped the grep, so
  "no proof found" is weaker than "unproved".
- **Statements**: extracted 210 Prop names and ran the same proved-or-not check (91 have a closed
  proof, 1 is a literature target, 118 neither). Read about 10 in full.
- **Counterexamples**: listed every file, read the theorem signatures of about 25. Looked for
  negated statements (`: ¬ ...`): there are only 2.
- **Definitions / BlockTheory / CrystallinePeriods**: structural survey (directory listing, file
  counts), keyword grep for Mathlib analytic and arithmetic names, plus the definitions that the
  PublishedTheorems statements depend on (`IsFrob`, `IsRay`, `HChar`, `IsHeckeL`, `coh`,
  `IsNef`/`IsBig`, `IsAbelianScheme`, `PolAV`, `D7`, `ZerosDisc`). I did not read the 17k helper
  lemmas.
- Skipped: `Proofs/` (another agent has it). I traced into it, and into other top-level trees, only
  to find where a statement defined here is proved.

## 2. What this subtree actually is

The directory name suggests abelian varieties. In fact this subtree is the **statement layer and
shared vocabulary** for a huge "literature bundle". `PublishedTheorems/` defines about 390 named
classical theorems as Lean `Prop`s: class field theory, Chebotarev, Hasse norm, Landherr,
Poitou–Tate, local and global Langlands-type statements, Hecke L-functions, Kawamata–Viehweg,
toroidal compactifications, Siegel–Weil, Stone–von Neumann, Radford, Linnik, and others. The
proofs live elsewhere: `Proofs/` here, `src/Development/WeilBound`, `src/Development/AutomorphicArithmetic`,
`src/CompanionTheory`. They are gathered into hypothesis structures (`GlobalTheory.CovTop.Hypotheses2`,
`GlobalTheory.CovTop.PublishedHodgeBundleTheorems`, and others), which the 5,950-line file
`EveryCharacterOfLiteratureOfVWin.lean` fills in field by field through `*_of_literature` theorems.
These theorems formally take a bundle `O : OpenLiteratureStatements` with three fields, which
`MainConclusion.lean` supplies, and most of them ignore it. So every literature statement on the
path to `riemannHypothesis` is discharged inside the repo: none stays an open hypothesis.

Not everything in this subtree is on that path. In particular the structure
`GlobalTheory.Fc.S0.ArithmeticGeometryHyps` (`Definitions/GlobalTwisting/DiscreteSeriesCoefficientsCuspidal.lean:300`,
about 230 fields, including the analytic `ExplZeta`, `ExplChi`, `Jutila`, `PageThm`, `TZRat` and
`QuadraticHeckeZeroEstimates`) is **never constructed anywhere in `src/`**. Its fields that have no
other proof are stated and never proved. That bundle is dead weight.

The genuinely mathematical content of my subtree, as opposed to its statements, sits in a few
`*Holds.lean` files inside `PublishedTheorems/`: Radford, Stone–von Neumann, the Hermitian Hasse
principle, Hecke L nonvanishing on Re s ≥ 1, Schur orthogonality, ray-class-field maximality and
the tame quotient. Beyond those it holds a large amount of plumbing in `Definitions/`: Čech and
sheaf cohomology of `X.Modules`, line bundles, nef and big classes, Weierstrass σ and ζ functions,
Riemann theta functions, hermitian lattices over CM fields, adelic groups. `BlockTheory/` and most of
`Definitions/` and `Statements/` are about the bespoke data bundle `D7`
(`src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:80`): a CM host field plus
ranks, hermitian spaces, "rows", "words" and divisor data. That is the scaffolding of the unitary
Shimura-variety / theta-lift argument and is not reusable outside it. `Counterexamples/` contains
almost no counterexamples: it is mostly helper lemmas and "premises are inhabited" checks.
`CrystallinePeriods/` builds Fontaine's period rings (A_inf, A_cris, B_cris, B_dR, Fontaine's θ, the
crystalline logarithm) over Mathlib's `ℂ_[p]` and Witt vectors.

## 3. Inventory (most reusable first)

"Proved at" is where the closed proof lives (often outside this subtree). M = the statement uses
only Mathlib objects; I = it depends on repo-internal definitions, which I checked as noted.

| Declaration | path:line | Statement (paraphrased) | M / I | Classical name | Reusability |
|---|---|---|---|---|---|
| `GlobalTheory.Lin.PrimesRel` (def) | `Definitions/GlobalTwisting/ZerosDisc.lean:39` | There are constants c₁ ≤ 1/8, c₂, c₃, C_A, c_S > 0 such that for every modulus M ≥ 3: at most one real character has an exceptional zero β > 1 − c₁/log M; that zero satisfies 1 − β ≥ c_S/(M² log M); and for X ≥ M^{c₂}, φ(M)·π(X; M, b) = Li-type main term with Siegel-zero correction, with relative error C_A(exp(−c₃ log X/log M) + exp(−√(c₃ log X))). Proved: `GlobalTheory.T.primesInProgressions_relativeError` (`Proofs/GlobalInterpolation/PrimesInProgressionsRelativeErrorStatement.lean:12`) | M (Dirichlet `LFunction`, `Nat.Prime`, `totient`; `Emain` is an explicit li-type main term in `src/Formalism`) | PNT in arithmetic progressions with Landau–Page exceptional zero (Davenport ch. 20), with an effective but weak lower bound 1−β ≫ 1/(M² log M) | **High**. Unconditional and effective. Directly useful for least-prime and prime-in-AP problems |
| `GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion` | `Proofs/GlobalInterpolation/ExceptionalDirichletZeroUniqueZeroFreeRegionStatement.lean:12` (Prop vocabulary in `Definitions/GlobalTwisting/ZerosDisc.lean`) | For characters mod M ≥ 3, every zero ρ of L(s,χ) with Re ρ < 1 satisfies Re ρ ≤ 1 − c/log(M(\|Im ρ\|+2)), except possibly one real simple zero β ≥ 7/8 of one nontrivial real χ, with 1−β ≥ c/(M² log M) | M | Classical zero-free region + Landau–Page | **High** |
| `GlobalTheory.T.chebyshevPsiProgression_relative_error` | `Proofs/GlobalInterpolation/ChebyshevPsiProgressionRelativeErrorStatement.lean:12` | ψ(u; M, b) version of the line above, with main term u − θ u^β/β | M | Siegel–Walfisz-type ψ in APs with exceptional term | **High** |
| `GlobalTheory.Published.Linnik` | `PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean:13` | There are C, L > 0 such that for all coprime a ≥ 1, q ≥ 1, the least prime p ≡ a (mod q) is ≤ C q^L. Proved: `UpperTheory.Lit.linnik` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/Linnik.lean:146`), derived from `PrimesRel` | M | Linnik's theorem (non-explicit L) | **High**. Pure Mathlib statement. `linnik_iff_exists_prime` (same file, :24) restates it as an existence statement |
| `GlobalTheory.Published.HeckeLPartialContinuation` | `PublishedTheorems/TwistedTraceFormula/HeckeLPartialContinuationHolds.lean:19`, proved at `:85` (in this subtree) | For any number field K and finite set T of primes: for every unitary Hecke character χ (a continuous idele-class character) not of the form \|·\|^{it}, the partial Euler product L^T(s,χ) has an entire continuation that is nonzero on Re s ≥ 1; and (s−1)ζ_K^T(s) has an entire continuation that is nonzero on Re s ≥ 1 | I, checked faithful: `HChar` = continuous characters of Ideles trivial on K^× (`src/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean:15`); Euler factors are taken at unramified places | Hecke: continuation + nonvanishing on Re s = 1 (the input to the prime ideal theorem for Hecke characters) | **High**. Covers all number fields and all unitary Hecke characters |
| `GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne` | `PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean:32`; proved at `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/HeckeLEntireAndNonzeroAtOne.lean:22` | Unitary χ, not a norm power: L(s,χ) is entire. χ ≠ 1: L is analytic at 1 and L(1,χ) ≠ 0 | I (same, faithful) | Hecke, L(1,χ) ≠ 0 | High |
| `GlobalTheory.Published.RayClassFieldSt` (= `GlobalTheory.NT.RayField`) | `PublishedTheorems/PublishedFoundations/NonemptyAlgHomOfIsRayOfDvd.lean:21`; proved at `src/Development/WeilBound/.../GlobalArtinReciprocity.lean:15` | For every number field K and nonzero modulus 𝔪 there is an abelian L/K and an isomorphism Art from the (narrow) ray class group mod 𝔪 to Gal(L/K), such that every prime 𝔭 ∤ 𝔪 is unramified with Frobenius Art([𝔭]). Equivalent forms: `rayClassFieldSt_iff_artinIso` (:23) and `_iff_isRayField` (:31) | I, checked faithful: `IsFrob`, `InInertia`, `UnramIn`, `RayPair` (`Definitions/GlobalTwisting/SmulCommClassGalIntegers.lean:39-61`) are the textbook congruence definitions | **Existence theorem of class field theory** (ray class fields, narrow at all real places) | **High** if the proof is sound. A landmark, not in Mathlib |
| `GlobalTheory.Published.RayClassFieldMaximalSt` | same file `:36`, proved `:208` (here) | If L is a ray class field mod 𝔪 and L′/K is abelian with all characters of conductor dividing 𝔪, then L′ embeds into L over K | I (faithful) | Maximality of the ray class field | High |
| `GlobalTheory.Published.GlobalArtinReciprocity` | `PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:74`; proved `src/CompanionTheory/AutomorphicTheory/PlaceSeparation/IsOpenQuotientMapArt0.lean:237` | For every number field E there is a homomorphism from the ideles to Gal(Ē/E)^ab satisfying `IsGlobalArtin` | I (`IsGlobalArtin` not read) | Global Artin reciprocity | High if `IsGlobalArtin` is faithful (unverified) |
| `GlobalTheory.Published.WeberRayFieldSt` | `PublishedTheorems/WeberRayClassFields/WeberRayFieldSt.lean:14`; proved `src/Development/WeilBound/.../ProvedMore.lean:96` | Imaginary quadratic K with disc < −4, L = 𝓞_K as a Mathlib `PeriodPair`: K adjoin j and the Weber values g₂g₃/Δ·℘(z/n) is an abelian extension and is the ray class field mod n | I (`IsRay`, `weberSet`, `Definitions/HeightFunctions/FiniteDimensionalOfSz.lean:20,27`, faithful; uses Mathlib's `PeriodPair.weierstrassP`) | Weber / Hasse, CM main theorem for ray class fields | High |
| `GlobalTheory.Published.HilbertClassFieldJ` | `PublishedTheorems/Divisors₂/ExistsEqOfNatCastMulMem.lean:70`; proved `src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HilbertClassFieldJ.lean:11` | Imaginary quadratic K: K(j(𝓞_K)) is the Hilbert class field, [K(j):K] = h_K, j(𝔞) = j(𝔟) iff [𝔞] = [𝔟], ... | I (`latticeCurve` built on a Mathlib `WeierstrassCurve`) | Hilbert class field via j (CM theory) | High |
| `GlobalTheory.Published.EllipticMainTheoremCM` | same file `:60`; proved `ProvedMore.lean:99` | Shimura's main theorem of CM for elliptic curves over ℂ with CM by imaginary quadratic K: Galois action on the analytic uniformisation ℂ/𝔞 is given by the Artin idele | I (`IsGlobalArtinMap`, `Transports` not read) | Main theorem of CM (Shimura) | Med–high |
| `GlobalTheory.Published.ChebotarevDegreeOne` | `PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:16`; proved `Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:21` | For F a number field, L/F finite Galois inside an algebraic closure, g ∈ Gal(L/F) and finite S: some prime v ∉ S of residue degree 1 is unramified in L and has a Frobenius restricting to g. Corollary `.dense` (:47): Frobenii of degree-one primes are dense in G_F | I, checked faithful: `IsPlaceOver`, `IsFrob`, `Ine` in `src/Formalism/ConjugateSelfDual/Statement.lean:25-33` are valuation-theoretic and standard | Chebotarev, qualitative "infinitely many" form, no density | **High** |
| `GlobalTheory.Published.HasseNormSt` | `PublishedTheorems/Landherr₂/ExistsNormTensor.lean:16`; proved `Proofs/AdelicLatticeProofs/HasseNormTheoremQuadraticExtensionStatement.lean:16` | F a number field, δ, x ≠ 0: if x = a² − δb² is solvable at every real embedding and in every completion F_v, then it is solvable in F | M | Hasse norm theorem (quadratic) | **High**. Pure Mathlib (`adicCompletion`) |
| `GlobalTheory.Published.HermitianHassePrinciple` | `PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean:432`, proved `:441` (here) | For E/F a quadratic extension of number fields with conjugation σ: two nondegenerate σ-hermitian r×r matrices that are congruent over every completion of F (finite and infinite) are congruent over E | M (`CongrOver` is local congruence) | Landherr's theorem (Hasse principle for hermitian forms) | **High** |
| `GlobalTheory.Published.HermitianLocalGlobal` | `PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean:388`, proved `:405` (here) | (i) Over a nonarchimedean local field with 2 ≠ 0 and a quadratic extension L, hermitian forms are classified by det modulo norms; (ii) over a CM field, local congruence at all finite places of E⁺ (plus the signature hypothesis, not read in full) gives global congruence | M | Jacobowitz local classification + Landherr | High |
| `GlobalTheory.Published.Landherr` / `LandherrSt` | `PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean:14`, `PublishedTheorems/Landherr₂/LandherrStIffLandherr.lean:16` | CM field E: hermitian G, G′ that are congruent at every complex embedding and whose dets differ by a norm z·z̄ are congruent over E. `LandherrSt` is proved on the main path (`GlobalTheory.QNorm.landherr_and_landherrSt`); `landherrSt_of_landherr` (:35) is here | M | Landherr (CM case) | High |
| `GlobalTheory.Published.FinitenessOfHermitianClasses` | `PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean:17`, proved `:127` (here) | CM field, nondegenerate hermitian G: lattices with prescribed dual (c·Λ), together with finitely many marked vectors, fall into finitely many U(G)(E)-classes | M | Finiteness of class number of hermitian lattices (Borel/Harish-Chandra type) | Med–high |
| `GlobalTheory.Published.StoneVonNeumann` | `PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean:52`, proved `:663` (here) | F a nonarchimedean local field (2 ≠ 0), W a finite-dim symplectic F-space, ψ a nontrivial continuous additive character: the Heisenberg group has an irreducible smooth representation with central character ψ, and it is unique up to isomorphism | I (`Heisenberg`, `IsIrrSmoothOf` repo-internal, not read in full) | Stone–von Neumann (p-adic, smooth version) | Med–high |
| `GlobalTheory.Published.SchurOrthogonalitySquareIntegrable` | `PublishedTheorems/TwistedTraceFormula/SchurOrthogonalitySquareIntegrable.lean:18`, proved `:196` | Locally compact group with a regular right-invariant Haar measure, irreducible unitary rep on a Hilbert space with one nonzero L² matrix coefficient: all matrix coefficients are L² and the Schur orthogonality relations hold with a formal degree d > 0 | M | Schur orthogonality for discrete series (Godement) | **High**. Fully general, pure Mathlib |
| `GlobalTheory.Published.RadfordShufflePolynomial` | `PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean:676`, proved `:688` (here) | Over a char-0 field, the shuffle algebra on a totally ordered alphabet is the free polynomial algebra on the Lyndon words. Corollary: Lyndon words are algebraically independent | M (`ShuffleAlgebra` and `IsLyndon` defined locally, standard) | Radford's theorem (1979) | High. Self-contained combinatorics |
| `GlobalTheory.Published.BrauerDegreeZero` | `PublishedTheorems/GaloisCohomology₂/BrauerDegreeZero.lean:16`; proved `Proofs/InertiaEigenvalues/BrauerDegreeZero.lean:207` | For a finite group G and a finite-dim complex rep ρ: χ_ρ − dim ρ is a ℤ-combination of (Ind_H χ − Ind_H 1) over linear characters χ of subgroups H | M | Brauer induction, degree-zero form | **High** |
| `GlobalTheory.Published.ChevalleyUnits` | `PublishedTheorems/GaloisCohomology₂/ChevalleyUnits.lean:11`; proved `Proofs/InertiaEigenvalues/ChevalleyUnits.lean:178` | For a number field E and m, b > 0 there is a > 0 coprime to b such that every unit u ≡ 1 mod a is an m-th power of a unit | M | Chevalley's theorem on units | High |
| `GlobalTheory.Published.TameQuotient` | `PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean:121`, proved `ExistsCoprimePowOfMemIneKer.lean:603` (here) | At a place v ∤ l of a number field: the wild-plus-prime-to-l part of inertia is closed and normal, its open normal subgroups have index prime to l, and inertia surjects continuously onto ℤ_l (tame l-quotient), ... | I (`Ine`, `Dec` faithful) | Structure of tame inertia | Med |
| `GlobalTheory.Published.LocalArtinExists` | `PublishedTheorems/GaloisCohomology₂/LocalArtinExists.lean:20`; proved `Proofs/InertiaEigenvalues/LocalArtinExistsHolds.lean:60` | For each finite place w of a number field, a local Artin map W_{E_w} → E_w^× satisfying `IsLocalArtin` exists | I (`IsLocalArtin`, `Weil` not checked) | Local reciprocity | Med (faithfulness of `IsLocalArtin` unverified) |
| `GlobalTheory.Published.AbMulNSt` | `PublishedTheorems/Landherr₂/DimEqZero.lean:14`; proved `Proofs/CoherentCohomologyProofs/AbelianVarietyTorsionCardEqPowProofStatement.lean:17` | Abelian variety B of dimension g over an algebraically closed field k (a group object in `Over (Spec k)` that is commutative, smooth, proper and geometrically connected), n invertible in k: #B[n](k) = n^{2g} | I, checked faithful: `IsAbelianScheme` (`src/ReciprocityTheory/.../IsAbelianScheme.lean:17`), Mathlib `SmoothOfRelativeDimension` | Structure of n-torsion of abelian varieties | High if sound. Not in Mathlib |
| `GlobalTheory.Published.KawamataViehweg` | `PublishedTheorems/Divisors₂/KawamataViehweg.lean:20`; on the main path via `kawamata_viehweg_of_literature` | X a smooth projective integral variety over an algebraically closed field of char 0, N a nef and big line bundle: H^q(X, K_X ⊗ N) = 0 for q > 0 | I, checked faithful: `coh` is Mathlib `Sheaf.H'` (Ext) of the abelian sheaf (`Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean:30-33`); `IsNef` = nonnegative degree on complete curves, `IsBig` = h⁰(mN) ≥ c·m^{dim} infinitely often (`Definitions/Divisors/LineBundleGlobalSectionsDimCongrPicardClass.lean:44,52`); `CanonLB` = top forms (not fully read) | Kawamata–Viehweg vanishing | High if sound. Extraordinary for Lean; check it independently before relying on it |
| `GlobalTheory.Published.NeronOggShafarevichSt` | `PublishedTheorems/Divisors₂/TateUnramifiedOfTorsionUnramified.lean:117`; proved `src/Development/AutomorphicArithmetic/ThetaCorrespondence/GoodReduction/NeronOggShafarevich.lean:26` | Abelian variety over the fraction field of a DVR with perfect residue field: TFAE good reduction / all prime-to-p torsion unramified / infinitely many such m / T_l unramified for one l | I (`HasGoodReduction`, `TorsionUnramified` not read) | Néron–Ogg–Shafarevich | Med–high |
| `GlobalTheory.Published.SemistableReductionSt` | `PublishedTheorems/SemistableReduction₂/SemistableReductionSt.lean:19`; proved `Proofs/DegenerationProofs/SemistableReductionPpavPadicFieldStatement.lean:19` | Polarised abelian variety over a finite extension K/ℚ_p: after a finite extension K′, it extends to a semiabelian group scheme over 𝓞_{K′} | I (`PolAV`, `IsSemiAbelian` look faithful; `IsGrpPullback` not read) | Grothendieck's semistable reduction | Med–high |
| `GlobalTheory.Published.PartialZetaFunctionalEquation` | `PublishedTheorems/Divisors₂/PartialZetaFunctionalEquation.lean:15`; proved `ProvedMore.lean:90` | Totally real F, ideal classes C, C′ with C·C′ = [different]: the partial zetas satisfy d^{s/2} Γ_ℝ(s)^n Z_C(s) = d^{(1−s)/2} Γ_ℝ(1−s)^n Z_{C′}(1−s) | I (`IsPartialZeta` not read; uses Mathlib `ClassGroup`, `Gammaℝ`, `differentIdeal`) | Hecke's functional equation for partial zeta functions | Med–high |
| `GlobalTheory.Published.HeckeTateFunctionalEquation` / `HeckeEntire` | `PublishedTheorems/Divisors₂/HeckeTateFunctionalEquationCM.lean:191` / `:185` (`HeckeEntire_holds` :189 here); FE proved `src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HeckeTateFunctionalEquation.lean:258` | Totally complex E, unitary algebraic Hecke character of CM type with infinity type n ≠ 0: the completed L-function satisfies Λ(s) = ε_∞ ε_fin(s) Λ′(1−s) with the dual character; entire continuation | I (`IsCompletedL`, `archEps`, `finEps`) | Hecke–Tate functional equation (algebraic CM type) | Med (special class of χ) |
| `GlobalTheory.Mem.An.ZeroCount` | `PublishedTheorems/AutomorphicForms₂/ZeroCount.lean:16`; proved `Proofs/GlobalInterpolation/ZeroCountHolds.lean:11` | Primitive χ mod q: the number of zeros (with multiplicity) with \|Im ρ − t\| ≤ 1 is ≤ C log(q(\|t\|+2)) | M (+ `zsumR`, a zero sum) | Local zero count (Davenport ch. 16) | **High** |
| `GlobalTheory.Mem.An.LogDerOne` | `PublishedTheorems/AutomorphicForms₂/LogDerOne.lean:16`; proved `Proofs/DivisorProofs/LogDerOneHolds.lean:15` | Primitive χ mod q > 1: \|L′/L(1,χ) − Σ_{\|Im ρ\|≤1} 1/(1−ρ)\| ≤ C log 3q | M | Standard partial-fraction estimate for L′/L near 1 | High |
| `GlobalTheory.Published.PoitouTateNormalised` | `PublishedTheorems/GaloisCohomology₂/PoitouTateNormalised.lean:16`; proved `src/Development/WeilBound/.../PoitouTateNormalisedHolds.lean:22` | For a number field, l^r torsion coefficients (l odd or F totally complex), finite S containing the places above l: normalised local invariants exist, and the Poitou–Tate nine-term sequence is exact, Ш duality holds and H^n = 0 for n ≥ 3 | I (`NineTermExact`, `ShaDual`, `Hn` continuous cohomology: not read) | Poitou–Tate (finite l-power modules) | Med. Faithfulness of the cohomology definitions unverified |
| `GlobalTheory.Published.LanglandsExhaustionGL` | `PublishedTheorems/GaloisCohomology₂/LanglandsExhaustionGL.lean:14`; proved `.../LanglandsExhaustion/Outright.lean:12` | p-adic field k of char 0: every irreducible smooth rep of GL_n(k) is the Langlands quotient of a multiset of segments | I (`IrrGL`, `Segment`, `IsL` not read) | Bernstein–Zelevinsky / Zelevinsky classification | Med |
| `GlobalTheory.Published.SuccMinTransference` | `PublishedTheorems/BesselIntegrals/ExistsLinearIndependentNormLe.lean:14` | Lattice L ⊂ ℝⁿ: λ_i(L)·λ_{n−i+1}(L*) ≤ n | M | Banaszczyk transference (weak constant) | **Stated only**: no proof found |
| `GlobalTheory.Mem.An.ExplZeta`, `ExplChi` | `PublishedTheorems/AutomorphicForms₂/ExplZeta.lean:16`, `ExplChi.lean:16` | Truncated explicit formula for ψ(x) and ψ(x,χ) with error ≪ log x + (x/T) log²(qxT) | M | Truncated explicit formula (Davenport ch. 17, 19) | **Stated only** (fields of the dead bundle). The workspace already has its own weighted explicit formula in erdos-985 |
| `GlobalTheory.Mem.An.Jutila` | `PublishedTheorems/AutomorphicForms₂/Jutila.lean:16` | For α ≥ 4/5: Σ_{q≤Q} Σ_{χ prim} N(α,T,χ) ≪_ε (Q²T)^{(2+ε)(1−α)} | M | Jutila's zero-density estimate | **Stated only** |
| `GlobalTheory.Mem.An.PageThm` | `PublishedTheorems/AutomorphicForms₂/PageThm.lean:16` | Two primitive real characters of conductor ≤ Q with real zeros > 1 − c/log Q are the same character | M | Landau–Page | **Stated only** here, though the uniqueness part follows from `exceptionalDirichletZero_unique_zeroFreeRegion` for a single modulus |
| `GlobalTheory.Mem.An.TZRat`, `QuadraticHeckeZeroEstimates` | `PublishedTheorems/AutomorphicForms₂/IsExcRat.lean:21`, `QuadraticHeckeZeroEstimates.lean:16` | `PrimesRel` with c₁ = 1/8 for M ≢ 2 (mod 4); the analogue for ray classes of imaginary quadratic fields | M | Prime ideal theorem in ray classes with exceptional zero | **Stated only** |
| `GlobalTheory.Published.LocalLanglandsGL` | `PublishedTheorems/AutomorphicForms₂/LocalLanglandsGL.lean:100` | Unique reciprocity map IrrGL_n(E_w) → WD reps with `IsRec`, compatible across fields | I | Local Langlands for GL_n (Harris–Taylor, Henniart) | **Stated only**. The main path instead uses `RecTExists`, proved in `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands` (outside my scope) |
| `GlobalTheory.Published.WeylIntegrationFormula`, `ChebotarevOpenNormal`, `PoitouTateDuality`, `Zuckerman`, `DSExist`, `CanonKeySt`, `TateCharPolySt`, `RosatiTracePosSt` | various | — | — | — | Stated only (no proof found) |
| `GlobalTheory.Published.principalPolarisationOneSection` | `PublishedTheorems/AbelianLaws/PrincipalPolarisationOneSection.lean:15`; proved `Proofs/AbelianSchemeLawProofs/PrincipalPolarisationUniqueSection.lean:11` | For a polarised abelian variety over an algebraically closed field, h⁰(L) = 1 | I. **Suspicious**: `PolAV` (`src/ReciprocityTheory/.../NonzeroLocus.lean:63`) has no "principal" field, so this asserts h⁰ = 1 for every polarisation that `PolAV` allows. Either `PolAV`'s `KTriv` field forces principality (plausible: K(L) trivial ⇔ principal) or the statement is false | Riemann–Roch for principal polarisations | Low until `KTriv` is understood. It is a good test of faithfulness |

## 4. Internal definitions worth knowing

| Definition | Where | Verdict |
|---|---|---|
| `IsFrob`, `InInertia`, `UnramIn`, `heckeVal`, `heckeIdeal`, `RayPair`, `IsModulus` | `Definitions/GlobalTwisting/SmulCommClassGalIntegers.lean:39-61` | Faithful (Frobenius congruence σx ≡ x^{N𝔭} mod 𝔓; narrow ray equivalence) |
| `IsRay`, `weberSet`, `Sz` | `Definitions/HeightFunctions/FiniteDimensionalOfSz.lean:15-27` | Faithful. `IsRay` = unramified outside 𝔮, Frobenii generate, kernel of Artin on ideals = narrow ray principal ideals |
| `IsPlaceOver`, `normV`, `IsFrob`, `Inertia` (valuation version) | `src/Formalism/ConjugateSelfDual/Statement.lean:25-33` | Faithful |
| `HChar`, `IsUnitary`, `val`, `UnrAt`, `IsCond` | `src/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean` | Faithful: continuous idele-class characters |
| `eulerFactor`, `IsHeckeL` | `Definitions/Divisors/EntireEqOfHalfPlane.lean:56-61` | Faithful (Euler product over unramified places; entire Λ agreeing on Re s > 1) |
| `heckeL`, `zetaOff` | `Definitions/Foundations/NormEulerPolySubOneLe.lean:280-282` | Partial Euler products. Faithful |
| `zerosBox`, `zerosDisc`, `IsExc`, `ExcData`, `psiAP`, `PrimesRel` | `Definitions/GlobalTwisting/ZerosDisc.lean` | Faithful. Pure Mathlib (`DirichletCharacter.LFunction`, `analyticOrderNatAt`, `Λ`) |
| `cohOn`, `coh` | `Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean:30-33` | Faithful: Mathlib `Sheaf.H'` (derived-functor cohomology) of `X.Modules` |
| `IsNef`, `IsBig`, `IsPsEff`, `IsCompleteCurve`, `strHom` | `Definitions/Divisors/LineBundleGlobalSectionsDimCongrPicardClass.lean:30-66` | Faithful (bigness through growth of h⁰ along infinitely many m) |
| `LB` (line bundles as cocycle data), `CanonLB` | `Definitions/Divisors/IsUnitMkOfFormallyUnramified.lean:297` and nearby | Plausible, hand-rolled (not Mathlib's Picard group). Not fully read |
| `IsAbelianScheme`, `IsSemiAbelian`, `TorusExtension` | `src/ReciprocityTheory/.../IsAbelianScheme.lean:17,45` | Faithful |
| `PolAV` | `src/ReciprocityTheory/.../NonzeroLocus.lean:63` | Mostly faithful (rigidified, symmetric, relatively ample, `KTriv`). See the caveat on `principalPolarisationOneSection` |
| `GlobalTheory.Fc.S0.ArithmeticGeometryHyps`, `Hypotheses1`, `Hypotheses2` | `Definitions/GlobalTwisting/DiscreteSeriesCoefficientsCuspidal.lean:300`, `.../JacquetShalikaRigidity.lean:27`, `.../DepthZeroSupport.lean:16` | Hypothesis bundles with ~230 fields. **Never constructed**: dead |
| `GlobalTheory.CovTop.Hypotheses2` | `Definitions/Divisors/ToKnownTheoremsOf.lean:29` | Hypothesis bundle (about 30 published theorems). Discharged by its sibling `PublishedHodgeBundleTheorems` in the literature file |
| `weierstrassZeta`, `weierstrassSigma`, `canonicalSigma`, `sTwo` | `Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean:64-877` | Faithful extensions of Mathlib's `PeriodPair`: ζ, σ, the addition formula ℘(u)−℘(v) in terms of σ (:1045), and factorisation of periodic entire functions through σ (:1119). Reusable |
| `D7`, `Host`, `HSp`, `Datum`, `Level`, `Moduli`, `Model`, `Coeff` | `src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:80` and others | A bespoke, highly non-canonical data bundle (CM host plus about 30 coherence fields). Not degenerate on its face (`Counterexamples/.../PremisesInhabited`, `Statements/HyperbolicHypotheses/...:94 hypotheses_inhabited` build instances), but anything quantified over `D7` can't be used without building one. Treat as not reusable |
| `Per.Ainf`, `Acris`, `Bcris`, `BdR`, `θ`, `IsCrisDR` | `CrystallinePeriods/RingIface.lean` | Fontaine period rings over Mathlib `ℂ_[p]` and `WittVector`. Faithful at the level read |

## 5. Mechanical families

- `Definitions/` (1862 files, ~17k theorems): the vocabulary plus helper lemmas, organised by the
  internal "chapter" names (`Divisors` 468 files, `AutomorphicMembership` 287, `NonGaloisDescent`
  176, `Foundations` 158, `LatticeFrames` 153, `GaloisGeometry` 134, `SemilocalFrames` 86, ...).
  559 file names contain `Of` and 151 contain `Iff`: one-lemma-per-file plumbing (`foo_of_bar`).
  About 15k theorem signatures don't mention `D7`/`Host`/`HSp`, but a sample shows they are
  overwhelmingly local API lemmas (`cechOpen_*`, `powL_*`, `root_*`, `gmap_*`), not results.
- `BlockTheory/` (488 files, ~720 theorems, ~4,570 defs): definition-heavy blocks of the
  theta-lift / unitary Shimura-variety argument over `D7` (`TwistedDiscreteSeries` 107,
  `DivisorBase` 84, `GlobalSignature` 50, `NonGaloisCusps` 44, `TorsionBlocks` 35, ...). Low
  reuse.
- `PublishedTheorems/` (363 files): about 390 `Prop` statements plus their API lemmas (`X.of_…`,
  `X_iff_…`). The bulk sits in `Divisors₂` (112 files, ~130 statements: arithmetic and algebraic
  geometry), `GaloisCohomology₂` and `TwistedTraceFormula` (61 each), and `AutomorphicForms₂` (48).
- `Statements/` (78 files, 210 Props): internal statements of the Shimura-variety argument
  (`PlaceShiftStatements` 22 files with ~60 `…At`/`…K` per-place variants, `HeckeThetaIntegrals`,
  `CuspFrameWeights`, ...). 91 have closed proofs. All are about `D7`/`Host`/`Moduli` and none is
  reusable. Examples: `GlobalTheory.HkFam.HeckeInFamilies` (`Statements/HeckeInFamilies/HeckeInFamilies.lean:16`,
  Hecke correspondences on the internal moduli, proved), `GlobalTheory.ShFam.Pad.HTBoundSt`
  (`Statements/HeightBoundStatement/HTBoundSt.lean:14`, a p-adic Hodge–Tate lattice bound, proved).
- `Counterexamples/` (148 files, ~570 theorems): mostly helper lemmas, "the hypotheses are
  inhabited" checks (`JetSurvey/PremisesInhabited.lean`, `HeightSurvey/MatchingNotVacuous.lean`) and
  "surveys". Only 2 theorems are negations, and neither is a counterexample to a published
  statement. Small Mathlib-level bits: `GlobalTheory.…isIrrChar_iff`,
  `sum_subgroup_eq_zero_iff` (`SubgroupCharacterSums/SumSubgroupEqZeroIff.lean:35,44`, characters of
  finite groups vs `FDRep`).
- `CrystallinePeriods/` (12 files, ~250 theorems): ring API for A_inf→B_dR (σ-actions, θ,
  Frobenius lift, `exists_incl : B_cris ↪ B_dR` at `CrisIncl.lean:21`, crystalline log uniqueness).

## 6. Standalone value

**Effectively proved here (or proved elsewhere for a statement defined here), in a usable
Mathlib-level form**, subject to the global trust caveat:
- Unconditional prime number theory for Dirichlet L: the zero-free region with Landau–Page
  exceptional zero, the local zero count, L′/L(1) estimates, PNT in APs with a Siegel-zero term,
  and **Linnik's theorem** (non-explicit exponent). These are the most immediately useful for the
  workspace (the erdos-985, ankeny-grh and grosswald-grh style arguments), because they hold
  *without* GRH.
- Hecke L-functions of arbitrary number fields: entire continuation and nonvanishing on Re s ≥ 1,
  L(1,χ) ≠ 0, (s−1)ζ_K entire and nonvanishing on Re s ≥ 1.
- Class field theory: existence and maximality of ray class fields, global Artin reciprocity (modulo
  `IsGlobalArtin`), the CM main theorem, Weber's ray class fields, the Hilbert class field via j.
- Qualitative Chebotarev, the Hasse norm theorem (quadratic), the Landherr/Hasse principle for
  hermitian forms, Chevalley's unit theorem, Brauer induction (degree-zero form), Schur
  orthogonality, Radford's theorem.
- Algebraic geometry: #A[n] = n^{2g}, Kawamata–Viehweg vanishing, Néron–Ogg–Shafarevich,
  semistable reduction (the definitions look faithful, the proofs are elsewhere and unread).

**Proved only in a special case**: Hecke–Tate functional equation (algebraic CM-type characters
only); hermitian results (CM fields / quadratic extensions only); Chebotarev without density;
the Linnik exponent is unspecified (no explicit L); the effective Siegel-zero bound is only
1−β ≫ M^{−2}/log M.

**Stated but not proved** (avoid): truncated explicit formulae `ExplZeta`/`ExplChi`, `Jutila`,
`PageThm`, `TZRat`, `QuadraticHeckeZeroEstimates`, `SuccMinTransference`, `LocalLanglandsGL`,
`PoitouTateDuality` (the general form; the normalised version is proved), `ChebotarevOpenNormal`,
`WeylIntegrationFormula`, and about 160 more `GlobalTheory.Published.*` Props.

**Misleading names**: `AbelianVarietyTheory` (mostly CFT, analytic NT and unitary groups);
`PublishedTheorems` (statements, mostly proved elsewhere); `Definitions` (17k theorems);
`Counterexamples` (almost none); `BesselIntegrals/BesselXiIntegrable` (an alias for a Fourier-decay
Prop in `src/Formalism`); `TwistedTraceFormula` (holds CFT, Radford and Hecke L, no trace formula
statement I saw); `Landherr₂/DimEqZero.lean` (holds the torsion-count statement `AbMulNSt`).

## 7. Open questions / not verified

- Nothing was compiled. All "proved" claims rest on the existence of closed terms in the source,
  and on the repo's own (untrusted-cache) build.
- Not read in full: `IsGlobalArtin`, `IsLocalArtin`, `Weil`, `NineTermExact`/`ShaDual`/`Hn`
  (continuous cohomology), `IrrGL`/`Segment`/`IsL`, `Heisenberg.IsIrrSmoothOf`, `CongrOver`,
  `CanonLB`, `HasGoodReduction`, `IsPartialZeta`, `IsCompletedL`, `KTriv`. Each is a point where a
  "proved" landmark could turn out degenerate.
- `principalPolarisationOneSection`: is h⁰ = 1 forced by `PolAV.ktriv`, or is the statement false
  (and therefore its "proof" a sign of a degenerate definition elsewhere)? Worth checking first:
  it's the cheapest faithfulness test in the subtree.
- Non-circularity: the analytic lemmas (`PrimesRel`, `linnik`) are dependencies of `Main.lean`, so
  they can't use RH/GRH. I did not trace their full import closure to rule out a dependency on
  some other unproved-looking bundle.
- The proved-or-not grep can miss proofs written in unusual syntax. The ~170 PublishedTheorems Props
  marked "no proof found" may include a few that are proved.
- Heavy claims (Kawamata–Viehweg, class field theory existence, #A[n], local Langlands-type
  exhaustion) would each be major Mathlib contributions. That alone is a reason to be sceptical of
  the build until it is independently re-verified.
