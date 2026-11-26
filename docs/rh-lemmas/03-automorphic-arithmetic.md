# Reusable lemmas in `src/Development/AutomorphicArithmetic` (riemann-hypothesis @ 507a75d91d)

Inventory pass only. Nothing was built and `#print axioms` was not run (brief: no `lake`/`lean`).
No code is quoted. Paths are relative to
[riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) `src/Development/AutomorphicArithmetic/`.

## 1. Scope and method

- **Size.** About 17,500 `.lean` files and about 1.8M lines. There are 66,111 `theorem`/`lemma`
  declarations (about 28,000 of them non-private) and about 17,300 `def`/`structure`/`class`/`abbrev`.
  Lines per directory: AutomorphicVarieties 879k, Foundations 429k, ThetaCorrespondence 225k,
  IntegralCasts 104k, CommutativeAlgebra 48k, CyclotomicBounds 16k, WhittakerHecke 15k. The other
  45 top-level directories hold 1–10k lines each.
- **`sorry` / `axiom` / `opaque`:** `rg` finds none in this subtree.
- **Method.**
  1. Extracted every declaration header (name and statement up to `:=`) with a Perl script:
     83,623 headers.
  2. Built a "pure statement" filter. It collects every name defined anywhere in the repo,
     subtracts every name declared in the pinned Mathlib checkout
     (`.lake/packages/mathlib`), and keeps the theorems whose statements use none of the
     remaining repo-only identifiers. That leaves 3,141 theorems, 1,029 of them closed `∀`
     statements. The filter is heuristic: section `variable`s leak through, and short repo
     names that collide with Mathlib names slip past it.
  3. Grepped statements for Mathlib number-theory vocabulary: `LFunction`, `LSeries`,
     `riemannZeta`, `jacobiSym`, `ClassGroup`, `discr`, `IsCyclotomicExtension`, `gaussSum`,
     `vonMangoldt` and so on.
  4. Read the strongest candidates and their supporting definitions in full or near-full.
- **Read in full or nearly in full:** `DedekindLFunctions/` (35 files),
  `ThetaCorrespondence/Linnik.lean`, the `StickelbergerTheorem/`, `BernoulliNumbers/` and
  `ClassFieldRamification/` headlines, `FerreroWashingtonIndex/FerreroWashington.lean`, the
  `PublishedTheorems/` defs, `Foundations/Convolution/SplitEigenfunctions/Entire.lean` and
  `InfinitePlaceGluing/Landau.lean`, `ShortNorms/ShortNorm.lean`, `CharacterBoxes/MainConclusion.lean`,
  the `OpenLiteratureStatements` block of
  `ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`, and
  the `HostRaw`/`HostAx` structure (it lives outside the subtree, in `Formalism/…/ConjEMemHostFIff.lean`).
- **Statement headers only:** CyclotomicBounds, PrimeDiscriminants, MeanSquareBounds,
  WhittakerHecke, CommutativeAlgebra, PrimitiveCosets, ConductorsKronecker, ResidueCharacters,
  OrbitLabellings, LocalEmbeddings, TwistedTraces, AdelicQuotients, DivisorFrames. I also read
  the "pure ∀" headers of every directory.
- **Mostly skipped, characterised only by structure and sampling:** the large internal proof mass
  in `Foundations/GaloisRepresentations` (2,914 files), `AutomorphicVarieties/ModularityArgument`
  (2,449), `ThetaCorrespondence/ThetaPairLifts` (2,913) and `IntegralCasts/CapelliIdentities` (800).
  I did not trace `CharacterBoxes`; another agent covers that spine.

## 2. What this subtree actually is

The subtree carries the final proof spine. `src/Main.lean` imports
`CharacterBoxes/MainConclusion.lean`, whose `UpperTheory.FinalTheorems.everyCharacter` (`:19`)
calls `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` in
`ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`.
That theorem takes a bundle `OpenLiteratureStatements` (`:5330`). The bundle has three fields: a
local–global Galois-representation row, existence of local Langlands reciprocity, and Galois
representations for polarized pairs. `MainConclusion` discharges the bundle with
`UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`
(`Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:10`) and `UpperTheory.Zero.LLC.recTExists`.
In other words, the subtree claims to prove inside Lean the existence of Galois representations
attached to regular algebraic polarized cuspidal representations of `GL_a` over CM fields
(`Row0b`, `Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:73`). It also
claims about 150 further "Published" literature statements as outright theorems. Most of the
`…_of_literature (O : OpenLiteratureStatements)` wrappers never use `O`; they point at proofs
elsewhere in the repo (PositivityTheory, AbelianVarietyTheory, GlobalTheory). Those statements
are almost all about repo-internal objects: `CuspSub`, `HChar`, `TR.Sm`, Weil data, Shimura data.
I did not verify that they are faithful.

The analytic end is a clean, reusable **Landau-type criterion**. It sits in `DedekindLFunctions/`
(namespace `Deduction`). Take a finite positive combination of Riesz-smoothed twisted Chebyshev
functions with their main terms removed, `Gm F y = Σ aᵢ Re Gchi(χᵢ, y)`. If it is bounded above by
`y^θ` on windows `[Y, Y^{1+δ}]` along a sequence `Y → ∞`, then every `L(s, χᵢ)` is nonzero for
`Re s > θ`. `PrimitiveCosets/LevelFamily.lean:60` connects the automorphic machinery's `Level`
objects to this `CharFamily`. Around it sit "hosts", which are genuine abelian CM fields
`E ⊂ ℚ(ζ_{QS·q·d})` containing `√−d` with an explicit Artin map (`HostRaw`), together with
Chebotarev and character-sum bookkeeping (CyclotomicBounds, PrimeDiscriminants, ConductorsKronecker,
MeanSquareBounds). Most of the rest is a very large body of commutative algebra, étale cohomology,
`p`-adic Hodge and deformation theory, theta correspondence and representation theory. It is
stated over internal structures and serves as a step toward the Galois-representation theorem.

**Names versus content.** Directory and declaration names are a poor guide. `CyclotomicBounds`,
`DedekindLFunctions` and `GaloisLibrary` do contain real Mathlib-level number theory. On the
other hand, `arithmeticGroup_congruenceSubgroupProperty` is a lemma about internal level
structures, and `affine_proper_base_change`, `etale_duality_trace_isomorphism` and
`chow_lemma_projective_cover` prove internal `Prop` packages (`GlobalTheory.EtC.E1`, `.D2`,
`LateralTheory.E.ChowCut.ChowL`) about the repo's own étale-cohomology definitions. Directories
such as `ThetaCorrespondence/HoweDuality`, `RallisInnerProduct` and `PrismaticDieudonne` are
statements over internal Weil-representation and lattice data. `DedekindLFunctions` has nothing
about Dedekind zeta functions; it is about Dirichlet L-functions only.

A small but real **classical algebraic number theory library** sits in
`AutomorphicVarieties/GaloisLibrary`: Kronecker–Weber, Stickelberger, Ferrero–Washington
(bounded `l`-rank form), generalized Bernoulli numbers with `L(1−k, χ)`, and Bauer's theorem. All
of these are stated purely in Mathlib terms. Linnik's theorem is also stated in Mathlib terms
(`ThetaCorrespondence/Linnik.lean`), though its analytic input is proved outside this subtree.

## 3. Inventory (most reusable first)

"M" means the statement uses only Mathlib objects; "I" means it involves internal definitions. All
names are fully qualified. For declarations without a namespace prefix, the namespace is given in
brackets.

| Declaration | path:line | Statement (paraphrased) | M / I | Classical name / reference | Reusability |
|---|---|---|---|---|---|
| `UpperTheory.Lit.linnik` | `ThetaCorrespondence/Linnik.lean:146` | `GlobalTheory.Published.Linnik`: there are `C, L > 0` such that for all `a, q ≥ 1` with `gcd(a,q)=1`, the least prime `p ≡ a (mod q)` satisfies `p ≤ C q^L`. Definition at `Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean:13`, which is faithful | M | Linnik (1944) | **High.** Unconditional, uniform Linnik with an unspecified `L`. Proved from `GlobalTheory.T.primesInProgressions_relativeError` (outside the subtree) |
| `UpperTheory.Lit.exists_prime_modEq_le_rpow_of_primesRel` | `ThetaCorrespondence/Linnik.lean:44` | From `PrimesRel` (a PNT in arithmetic progressions with one possible Siegel zero and `1−β ≥ c/(M² log M)`; def `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ZerosDisc.lean:39`): there is `A ≥ 1` with a prime `p ≡ a (mod M)`, `p ≤ M^A`, for every `M > 2` and every `a` coprime to `M` | M | Gallagher-style PNT in APs ⇒ Linnik | High; shows how to use `PrimesRel` |
| `UpperTheory.T3.smallOne` | `ShortNorms/Primes.lean:11` | `SmallOne` (`ShortNorms/ShortNorm.lean:17`): there is `A ≥ 1` such that every `M ≥ 2` has a prime `p ≡ 1 (mod M)` with `p ≤ M^A` | M | Linnik for the residue class 1 | High (special case of Linnik) |
| `UpperTheory.T3.shortNorm` | `ShortNorms/Primes.lean:9` | `ShortNorm` (`ShortNorm.lean:12`): for primes `d ≡ 3 (mod 4)`, `d ≥ 100`, and short intervals `[X, X(1+h)]` with `h ≥ exp(−c√log X)` and `log(4dM²) ≤ c√log X`, the count of primes `p` represented as norms `u² + uv + ((d+1)/4)v²` with `M ∣ u−1`, `M ∣ v` is at least `c′hX/((4dM²)^A log X)` | M (`normPrimes` is a concrete finset) | Primes represented by ray classes of `ℚ(√−d)` in short intervals (Hecke / Gallagher type) | High. A re-export; the proof is outside the subtree |
| `Deduction.lemmaL` | `DedekindLFunctions/LandauTheorems/lemmaL.lean:17` | Let `F` be a finite family of Dirichlet characters `χᵢ` (each trivial of modulus 1 or nontrivial) with weights `aᵢ > 0`, and `0 < θ < 1`. If `WindowHyp F θ δ` holds, then `L(s, χᵢ) ≠ 0` for all `i` and `Re s > θ`. `WindowHyp`: for every `η > 0` there are arbitrarily large `Y` and a majorant `R ≥ max(0, Gm F)` on `[Y, Y^{1+δ}]` with `∫ R(y) y^{−θ−1} ≤ Y^η` | M (`CharFamily`, `Gchi`, `ramp` are explicit Mathlib-level defs; `CharFamily.lean`) | Landau's oscillation theorem / one-sided Tauberian zero-free criterion | **High.** Turns a one-sided prime-sum bound into a zero-free half-plane, for arbitrary `θ` |
| `Deduction.zeroFree_of_rpow_window` | `DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:15` | Same conclusion under the simpler hypothesis: `Gm F y ≤ C y^θ` on `[Y, Y^{1+δ}]` for arbitrarily large `Y` | M | Same | **High** |
| `Deduction.landau_window` | `DedekindLFunctions/LandauTheorems/landauWindow.lean:87` | Abstract version. Suppose `Φ` is the Laplace transform of a measurable `g` with `|g(u)| ≤ C e^{2u}`, meromorphic on `Re s > 0` with isolated simple poles in `Z`, residues nonzero and positive real at real poles (`PoleData`, `LandauZeroFreeCriterion.lean:19`). If `g` satisfies the exponential window bound `WindowHypU g θ δ`, then every pole has `Re ρ ≤ θ` | M | Landau's theorem, iterated-derivative / Pólya proof | High. Usable for any Dirichlet series, not only Dirichlet L-functions |
| `Deduction.poleData_char` | `DedekindLFunctions/LandauTheorems/poleData.lean:141` | For `χ` (modulus 1 or nontrivial), the Laplace transform of `Gchi χ (e^u)` extends to a function that is analytic off the zeros of `L(·, χ)` with `ρ ≠ 0`. At each zero it has a simple pole with residue `m·(−1/(ρ(ρ−1)))`, where `m` is the zero's multiplicity (equal to `analyticOrderAt`); and the zeros are isolated | M | Explicit formula for the Riesz mean of `ψ(x, χ)` | High |
| `Deduction.mellin_Gchi_of_ne_one` | `DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean:118` | For `χ ≠ 1` and `Re s > 1`: `∫₁^∞ Gchi(χ,y) y^{−s−1} dy = −(L′/L(s,χ) − s·L′/L(1,χ)) / (s(s−1))` | M | Mellin transform of the `ψ₁(x,χ)` Riesz mean | High |
| `Deduction.mellin_Gchi_modOne` | `DedekindLFunctions/LandauTheorems/mellinGchiModOne.lean:119` | The same for the trivial character mod 1: the transform equals `−(ζ′/ζ(s) + 1/(s−1) + 1 − (1+γ)s) / (s(s−1))` | M | Same, with Euler's constant | High |
| `Deduction.mellin_Gchi_of_ne_one_ramp` | `DedekindLFunctions/LandauTheorems/mellinGchiOfNeOne.lean:69` | For any `f` with `Σ f(n)Λ(n)n^{−s}` summable: `∫₁^∞ (ramp f(y) y^{−s−1} + g) = LSeries(fΛ)(s)/(s(s−1)) + ∫ g`, where `ramp f y = Σ_{n≤y} Λ(n) f(n) (y/n − 1)₊` | M | Perron / Riesz-mean formula | Medium–high |
| `Deduction.LFunction_conj` | `DedekindLFunctions/LandauTheorems/LFunctionConj.lean:92` | `L(conj s, χ⁻¹) = conj L(s, χ)` for every Dirichlet character, at all `s` (including the analytic continuation) | M | Reflection under conjugation | High; likely missing from Mathlib |
| `Deduction.hurwitz_conj` | `DedekindLFunctions/LandauTheorems/LFunctionConj.lean:80` | `ζ(conj s, a) = conj ζ(s, a)` for the Hurwitz zeta, all `a : UnitAddCircle` and all `s` | M | — | High |
| `Deduction.Gchi_conj_LFunction` | `DedekindLFunctions/LandauTheorems/GchiConj.lean:24` | As functions, `L(·, χ⁻¹) = conj ∘ L(·, χ) ∘ conj` | M | — | High |
| `Deduction.mertens_upper` | `DedekindLFunctions/LandauTheorems/mertensUpper.lean:107` | `Σ_{n≤y} Λ(n)/n ≤ log y + 2` for `y ≥ 1`. Companion results: `Σ_{n≤N} Λ(n) + 1 + log N ≤ 3N` (`:35`) and `Σ log n ≤ N log N − N + 1 + log N` (`:13`) | M | Mertens' first theorem (upper bound), Chebyshev `ψ(N) ≤ 3N` | High |
| `Deduction.logDeriv_local` | `DedekindLFunctions/LandauTheorems/LogDerivLocal.lean:13` | If `f` is analytic at `ρ` and not locally zero, then near `ρ`, `f′/f = m/(s−ρ) + analytic`, where `m = analyticOrderAt f ρ` and `m = 0 ↔ f(ρ) ≠ 0` | M | Residue of a logarithmic derivative | High; generic complex analysis |
| `Deduction.landau_pole_asym`, `Deduction.landau_cauchy`, `Deduction.iteratedDeriv_laplace` | `LandauPoleAsym.lean:23`, `LandauCauchy.lean:13`, `IteratedDerivLaplace.lean:88` | Taylor-coefficient asymptotics near a simple pole; Cauchy estimates for `f^{(k)}(z)/k!`; differentiation under the Laplace integral | M | — | Medium; analytic utilities |
| `UpperTheory.ConvolutionTheory.RankTwoDescent.landau_of` | `Foundations/Convolution/SplitEigenfunctions/InfinitePlaceGluing/Landau.lean:12` | `Landau` (`…/SplitEigenfunctions/Entire.lean:155`): if `b ≥ 0`, `b 1 = 1`, `LSeries b` converges for `Re s > 4` and extends to an entire function, then `{n : b n ≥ 1}` is finite | M (`Entire` at `Entire.lean:108` means "agrees with an entire function on `Re s > 4`") | Landau's theorem: a nonnegative Dirichlet series that extends to an entire function | High |
| `UpperTheory.false_of_landau_nonneg_euler_factors_entire` | `WhittakerHecke/FalseOfLandauNonnegEulerFactorsEntire.lean:37` | Two multiplicative `a, a′` (normalised, vanishing at primes dividing `N`) whose product Euler factors have nonnegative coefficients, whose L-series converge for `Re s > 4`, and that are both entire, together with `Landau`, give a contradiction | M | Landau's non-negativity trick (used for Rankin–Selberg-type positivity) | Medium |
| `UpperTheory.eq_convolution_squareIndicator_of_euler_factors` | `WhittakerHecke/EqConvolutionSquareIndicatorOfEulerFactors.lean:106` | If `b`'s local Euler factors equal those of `a` times `(1 − X²)` at `p ∤ N`, then `a` is the Dirichlet convolution of `b` with the indicator of squares coprime to `N` | M | `L(s)·ζ_N(2s)` factorisation | Medium |
| `UpperTheory.V.CF.kw` | `AutomorphicVarieties/GaloisLibrary/ClassFieldRamification/Kw.lean:13` | Every finite abelian extension `L/ℚ` inside an algebraically closed `Ω` of characteristic 0 lies in `ℚ(ζ)` for some primitive `N`-th root of unity `ζ` | M | **Kronecker–Weber** | **High.** Not in Mathlib at this pin |
| `UpperTheory.V.CF.kwHom`, `UpperTheory.V.CF.kwRam` | `ClassFieldRamification/KwHom.lean:13`, `KwRamSplit.lean:30` | Every abelian number field embeds in some `CyclotomicField N ℚ`; if it is unramified outside the primes of `M`, it embeds in `ℚ(ζ_{M^n})` | M | Kronecker–Weber with conductor control | **High** |
| `UpperTheory.V.CF.minkRam` | `ClassFieldRamification/MinkRam.lean:11` | A number field of degree `> 1` is ramified at some prime (`UnramAt`, `IsClassFieldHilbert.lean:55`: every prime above `p` has ramification index 1) | M | Minkowski's theorem (ℚ has no unramified extensions) | High |
| `UpperTheory.V.CF.minkGen` | `ClassFieldRamification/MinkGen.lean:12` | For Galois `K/ℚ`, the inertia subgroups generate `Gal(K/ℚ)` | M | Corollary of Minkowski | High |
| `UpperTheory.V.CF.bauer` | `ClassFieldRamification/BauerFixIff.lean:94` | For Galois `A, C` over a number field `K`: if, apart from finitely many places, every place that splits completely in `C` also splits completely in `A`, then `A ⊆ C` | M plus `GroundTheory.Global.SplitsCompletely` (outside the subtree; not opened) | **Bauer's theorem** (Chebotarev corollary) | High, if `SplitsCompletely` is faithful |
| `UpperTheory.V.CF.cheb` | `ClassFieldRamification/Cheb.lean:12` | For Galois `L/K` and `σ ∈ Gal(L/K)`, and outside any finite set of places, there is an unramified prime `w` of `L` with arithmetic Frobenius `σ` | M | Chebotarev (existence form). The density version comes from `GroundTheory.GlobalFields.TateThesis.Chebotarev` | High (but the real content is outside the subtree) |
| `UpperTheory.V.CF.ineCard`, `UpperTheory.V.CF.unramIff` | `ClassFieldRamification/IneCard.lean:12`, `UnramIff.lean:12` | `|inertia group| = ramification index` for Galois extensions of number fields; `p` is unramified exactly when all inertia groups above `p` are trivial | M | Standard | Medium–high (check against current Mathlib) |
| `UpperTheory.V.CF.gauss` | `ClassFieldRamification/ExistsQuadraticGaussSum.lean:73` | For an odd prime `p` and a primitive `ζ_p` in characteristic 0: `√(p*)` exists in `ℚ(ζ_p)`, and an automorphism with `ζ ↦ ζ^b` sends it to `(b/p)·√(p*)` | M | Quadratic Gauss sum, quadratic subfield of `ℚ(ζ_p)` | High |
| `exists_gauss` [no namespace] | `QuadraticCharacters/GaussRoot.lean:14` | The same for a prime `d ≡ 3 (mod 4)`: there is `G` with `G² = −d` on which Galois acts through the quadratic character | M | — | High |
| `UpperTheory.V.Stick.coef` | `AutomorphicVarieties/GaloisLibrary/StickelbergerTheorem/ImportsAlt.lean:13` | For `K = ℚ(ζ_M)` and every ideal class `c`: if `β, γ : (ℤ/M)ˣ → ℤ` satisfy `Mγ(t) = Σ_s β(s)·⟨st⟩_M`, then `Π_t σ_t⁻¹(c)^{γ(t)} = 1`. That is, `β·θ` annihilates `Cl(K)`, where `θ` is the Stickelberger element; `σ_t` comes from Mathlib's `galEquivZMod` | M | **Stickelberger's theorem** | **High.** Not in Mathlib |
| `UpperTheory.V.Stick.jacobi`, `UpperTheory.V.Stick.jacDvd`, `UpperTheory.V.Stick.teich` | `StickelbergerTheorem/Jacobi.lean:22`, `JacDvd.lean:10`, `ImportsTer.lean:10` | Prime factorisation of Jacobi sums: there is `J ∣ p` lying in exactly the conjugates `P^{σ_t}` with no carry in `at + bt`. Also `jacobiSum χ φ ∣ p` for nontrivial `χ, φ, χφ`, and the existence of a Teichmüller-type character of order `M` | M | Stickelberger congruence / Jacobi sums | High |
| `UpperTheory.V.FW.ferreroWashington` | `AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:108` | `FerreroWashington` (`AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:11`): let `K/ℚ` be abelian containing `ζ_l` (`ζ_4` if `l = 2`). Then `|Cl(K_n)/Cl(K_n)^l|` is bounded uniformly in `n` over all `K_n = K(ζ_{l^n})` | M | **Ferrero–Washington (μ = 0)**, bounded-`l`-rank form | **High.** A major theorem, not in Mathlib |
| `UpperTheory.V.FW.cyc` | `FerreroWashingtonIndex/FerreroWashington.lean:22` | For `f` coprime to `l`, `f > 1`: `[Cl(ℚ(ζ_{f l^n})) : Cl^l]` is bounded for large `n` | M | Cyclotomic case of the above | High |
| `UpperTheory.V.FW.sinnott` | `FerreroWashingtonIndex/Sinnott.lean:14` | `ℤ_l`-units that are pairwise ℤ-independent have reductions with a separation property (a key lemma of Sinnott's proof) | M | Sinnott's proof of Ferrero–Washington | Medium |
| `UpperTheory.V.Bern.b_lprim`, `UpperTheory.V.Bern.b_lval` | `AutomorphicVarieties/GaloisLibrary/BernoulliNumbers/BLprim.lean:11`, `BLval.lean:26` | For `k ≥ 1`: `L(1−k, χ) = −B_{k,χ}/k` (for the primitive character as well), and `ZMod.LFunction Φ (1−k) = −B_{k,Φ}/k` for any `Φ : ZMod N → ℂ`. Here `B_{k,Φ} = N^{k−1} Σ_{a=1}^N Φ(a) B_k(a/N)` (def `MapGenBChar.lean:15`, which is faithful) | M | Values of Dirichlet L at negative integers, generalised Bernoulli numbers | **High** |
| `UpperTheory.V.Bern.b_nzC`, `UpperTheory.V.Bern.b_primlevel`, `UpperTheory.V.Bern.b_level`, `UpperTheory.V.Bern.b_upper`, `UpperTheory.V.Bern.b_denint`, `UpperTheory.V.Bern.b_polybound` | `BernoulliNumbers/BNzC.lean:14`, `Primlevel.lean:11`, `GeneralizedBernoulliChangeLevel.lean:59`, `BUpper.lean:11`, `Denint.lean:12`, `Polybound.lean:50` | `B_{k,χ} ≠ 0` when `χ(−1) = (−1)^k`; `B_{k,χ} = B_{k,χ_prim}·Π_{p∣N}(1 − χ_prim(p)p^{k−1})`; invariance under change of level; `‖B_{k,Φ}‖ ≤ 4N^k k!/(2π)^k` for `|Φ| ≤ 1`; `N·primorial(k+1)·B_k(a/N)N^{k−1}` is an integer; `|B_k(x)| ≤ 4k!/(2π)^k` on `[0,1]` | M | Standard Bernoulli-number facts | High |
| `UpperTheory.V.Bern.b_gauss` | `BernoulliNumbers/GaussMulGaussInv.lean:29` | For primitive `χ` mod `N`: `‖τ(χ)‖ = √N` and `‖rootNumber χ‖ = 1` | M | Gauss-sum modulus | Medium (Mathlib may already have most of it) |
| `UpperTheory.V.Bern.b_hurzero` | `BernoulliNumbers/Hurzero.lean:12` | `ζ(0, x) = 1/2 − x` for `0 < x ≤ 1` | M | Hurwitz zeta at 0 | Medium |
| `KStar.IdealCounting.log_classNumber_le` | `CyclotomicBounds/ClassNumberBounds/IdealCounting/ClassC.lean:70` | For every number field `K` of degree `n`: `log h_K ≤ (log|d_K|)/2 + n·log(1 + (log|d_K|)/2)` | M | Explicit Minkowski / Landau class-number bound | **High** |
| `UpperTheory.V.Odd.logH` | `AutomorphicVarieties/OddResidueBounds/LogH.lean:11` | If `E` embeds in `ℚ(ζ_N)` (`N ≥ 2`), then `log h_E ≤ 3·[E:ℚ]·log N` | M | Class-number bound for abelian fields | High |
| `UpperTheory.V.Odd.logDisc`, `UpperTheory.V.Win.disc` | `AutomorphicVarieties/OddResidueBounds/LogDisc.lean:10`, `AutomorphicVarieties/LayeredIsomorphisms/Imports.lean:10` | If `E ↪ ℚ(ζ_N)`, then `|d_E| ≤ N^{[E:ℚ]}`, `[E:ℚ] ≤ N` and `log|d_E| ≤ [E:ℚ] log N` | M | Conductor–discriminant bound | High |
| `UpperTheory.V.X.hQuad` | `AutomorphicVarieties/LevelCohomology/HQuad.lean:14` | For a prime `l ≥ 5` and a quadratic field with discriminant `l`: `h < l` | M | Elementary class-number bound for real quadratic fields | Medium |
| `[KStar…].exists_quadField` | `CyclotomicBounds/ClassNumberBounds/ExplicitConstants/SplitCharY.lean:14` | For a prime `d ≡ 3 (mod 4)` there is a number field `K` of degree 2 with `disc K = −d` | M | — | Medium |
| `[KStar…].relDifferent_eq_span_prod`, `[KStar…].map_differentIdeal_eq_span_prod` | `CyclotomicBounds/ClassNumberBounds/InertiaRamification/CycDifferent.lean:95`, `:133` | Explicit generator of the (relative) different of `ℚ(ζ_N)/E` and of `E/ℚ` for `E ⊆ ℚ(ζ_N)`, as a product of `ζ − σζ` | M | Different of cyclotomic subfields | Medium–high |
| `[KStar…].annihilator_charKer` | `CyclotomicBounds/ClassNumberBounds/InertiaRamification/Duality.lean:30` | Annihilator / kernel duality between subgroups of Dirichlet characters mod `N` and subgroups of `(ℤ/N)ˣ`, with `|X| = [(ℤ/N)ˣ : ker X]` | M | Character duality | Medium |
| `UpperTheory.torsionOrder_le_two_mul_finrank_sq`, `UpperTheory.V.Win.rootdeg` | `WeightCongruences/TorsionOrderLeTwoMulFinrankSq.lean:89`, `AutomorphicVarieties/LayeredIsomorphisms/Rootdeg.lean:10` | `w_K ≤ 2[K:ℚ]²`; if `ζ_{l^k} ∈ L` then `l^k ≤ 2[L:ℚ]` | M | Roots of unity in number fields | Medium |
| `UpperTheory.V.KT.mink3` | `AutomorphicVarieties/HermiteNormalForms/Mink3.lean:12` | A finite subgroup of the units of a ring that is free of rank `r` over ℤ has order `≤ 3^r` | M | Minkowski's bound on finite subgroups of `GL_r(ℤ)`-type | Medium |
| `[FrobeniusLocalisation].log_prime_indep` | `FrobeniusLocalisation/LogPrimeIndep.lean:52` | `{log p}` is linearly independent over ℚ | M | Fundamental theorem of arithmetic, analytic form | Medium |
| `UpperTheory.V.KH.det_natAbs_le_prod_l1_norms` | `AutomorphicVarieties/TorsionBoundsChains/DetNatAbsLeProdL1Norms.lean:9` | `|det M| ≤ Π_i Σ_k |M_ik|` for integer matrices | M | Hadamard-type bound | Medium |
| `UpperTheory.V.Kum.h90` | `AutomorphicVarieties/GaloisLibrary/KummerTheory/Imports.lean:10` | Hilbert 90 for continuous (locally constant) 1-cocycles `G_K → Ω^×`, over a number field `K` with algebraic closure `Ω` | M | Hilbert's Theorem 90 (profinite) | Medium |
| `UpperTheory.V.ZK.Ct.lte` | `AutomorphicVarieties/ModularityArgument/ClassCounting/SelmerOrderCounts/TorsionExponentBound.lean:60` | `v_l((1 + l^c)^E − 1) = c + v_l(E)`, plus an iterated version | M | Lifting-the-exponent | Medium |
| `QH.twistK` | `MeanSquareBounds/twistK.lean:158` | For admissible parameters (`admitted ε Y U m₀ a₀`, an internal predicate whose definition I could not locate): there is one exceptional modulus `n*` such that for all other odd squarefree `s ≤ Y^A` coprime to `m₀`, `|Σ_{q∈P} (q/s)| ≤ Y^{−B}·|P|`. Here `P` is the set of primes `q ≡ a₀ (mod m₀)` in `(√U, U]` | M + I | Equidistribution of Jacobi symbols over primes in APs (Siegel–Walfisz plus one exceptional character) | Medium. Needs `admitted` unfolded first |
| `UpperTheory.ConvolutionTheory.FX.cheb_facts` | `Foundations/Convolution/PolynomialCoefficientBounds/ChebClosed.lean:23` | Chebyshev `T_m`: `|T_m| ≤ 1` on `[−1,1]`, closed form for `y ≥ 1`, and `|T_m(y)| ≤ (2y)^m` | M | — | Low–medium |
| `UpperTheory.Lit.Cusp.fourier_zero` | `ThetaCorrespondence/RealBands/Fourier.lean:12` | A continuous integrable `u : ℝ → ℂ` whose Fourier transform vanishes identically is 0 | M | Fourier uniqueness | Medium |
| `UpperTheory.exists_injective_h1_gm_to_pic` | `CommutativeAlgebra/ExistsInjectiveH1GmToPic.lean:106` | For every commutative ring `A`, `H¹(Spec A, G_m)` (the repo's cohomology `H`) injects into `CommRing.Pic A` | I (repo `H`) | `H¹(G_m) = Pic` | Low; internal cohomology |
| `UpperTheory.V.CF.kwAbs`, `UpperTheory.V.CF.kwAbsRam` | `ClassFieldRamification/KwAbs.lean:11`, `KwAbsRam.lean:107` | Profinite form: an open subgroup of `G_ℚ` containing the commutator subgroup contains the kernel of the cyclotomic character mod `N` for some `N`, with control of `N` by ramification | M (repo `G ℚ Ω` is `Ω ≃ₐ[ℚ] Ω`) | Kronecker–Weber, Galois-group form | High |

## 4. Internal definitions worth knowing

| Definition | Location | Verdict |
|---|---|---|
| `Deduction.ramp`, `Deduction.Gchi`, `Deduction.CharFamily`, `Deduction.Gm`, `Deduction.ZeroFree`, `Deduction.WindowHyp` | `DedekindLFunctions/CharFamily.lean` | **Faithful.** `ramp f y = Σ_{n≤y} Λ(n) f(n)(y/n−1)₊` is the Riesz mean of `ψ(·, f)`. `Gchi` subtracts the correct main term (`y log y − (1+γ)y` for `χ = 1` mod 1, `−y·L′/L(1,χ)` otherwise). `CharFamily` is a finite family with positive weights, each character either trivial mod 1 or nontrivial. Nothing is vacuous |
| `Deduction.PoleData`, `Deduction.WindowHypU` | `DedekindLFunctions/LandauZeroFreeCriterion.lean:19,29` | Faithful abstract hypotheses: Laplace transform, isolated simple poles, positive residues at real poles |
| `…RankTwoDescent.Entire`, `…RankTwoDescent.Landau` | `Foundations/Convolution/SplitEigenfunctions/Entire.lean:108,155` | Faithful. The rest of `Entire.lean` (`Ext`, `Fac`, `Hol`, …) is about internal `Dat`/`CuspSub` objects |
| `GlobalTheory.Published.Linnik` | outside subtree (`AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/PrimesInProgressionNonempty.lean:13`) | Faithful; `linnik_iff_exists_prime` is the usable form |
| `GlobalTheory.Lin.PrimesRel`, `GlobalTheory.Lin.IsExc` | outside subtree (`AbelianVarietyTheory/Definitions/GlobalTwisting/ZerosDisc.lean:30,39`) | Looks faithful: PNT in arithmetic progressions with an error term `exp(−c log X/log M) + exp(−√(c log X))` relative to the main term, one exceptional real zero, and a Siegel-type lower bound `1−β ≥ c/(M² log M)` (weaker than Siegel's ineffective `M^{−ε}`, but effective) |
| `UpperTheory.V.Published.FerreroWashington` | `AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:11` | Faithful: bounded `l`-rank of class groups up the cyclotomic `ℤ_l`-tower, equivalent to μ = 0 |
| `UpperTheory.V.Stick.sg`, `UpperTheory.V.Stick.conjI`, `UpperTheory.V.Stick.carry`, `UpperTheory.V.Kum.clMap` | `StickelbergerTheorem/StickelbergerAt.lean:44–65`, `KummerTheory/Mk0IdMapCongr.lean:49` | Faithful: Mathlib's Galois iso `(ℤ/M)ˣ ≅ Gal`, conjugate ideals, carries, and the induced map on `ClassGroup` |
| `UpperTheory.V.Bern.genB`, `UpperTheory.V.Bern.bcoef`, `UpperTheory.V.Bern.Bprim`, `UpperTheory.V.Bern.Lprim` | `BernoulliNumbers/MapGenBChar.lean:13–26` | Faithful standard definitions |
| `UpperTheory.V.CF.UnramAt` | `ClassFieldRamification/IsClassFieldHilbert.lean:55` | Faithful: every prime above `p` has `e = 1` |
| `Formalism.HC.HostRaw`, `Formalism.HC.HostAx` (the "hosts" used by CyclotomicBounds, PrimeDiscriminants, ConductorsKronecker, FrobeniusLocalisation, PrimitiveCosets) | outside subtree (`Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:16,176`) | **Faithful, not degenerate.** Data: primes `q, d`; a Galois number field `E` with `Gal(E/ℚ) ≅ φ.GG`; `√−d ∈ E`; an embedding into `ℚ(ζ_{QS·q·d})`; and an Artin map with its specification. `HostAx` adds that `E` is CM of degree `4·ord`. Theorems quantified over hosts are genuine statements about this family of abelian CM fields. Hosts exist by `CharacterBoxes/FieldChi.lean:25` (not checked by me) |
| `Formalism.HC.Frame` | outside subtree | Finite group-theoretic combinatorics (`GG`, `Psi`, `cc`, `placeOf`); not checked in detail |
| `UpperTheory.T3.ShortNorm`, `UpperTheory.T3.SmallOne`, `GlobalTheory.Mem.An.normPrimes` | `ShortNorms/ShortNorm.lean`, `AbelianVarietyTheory/Definitions/Foundations/RayPrimes.lean:49` | Faithful concrete counting statements |
| `CuspSub`, `HChar`, `TR.Sm`, `IsAutForm`, `Newform`, `Qbar`, `G F Ω` | mostly outside the subtree (`Formalism/…`, `AbelianVarietyTheory/Definitions/AutomorphicMembership/ExpoConjOfIsCsd.lean:52,96`) | `IsAutForm` has the right shape (left `GL_a(E)`-invariance, open level, `K`-finite, `Z`-finite, moderate growth) and `Qbar l = PadicAlgCl l`. I did **not** check `CuspSub`, `HChar` or the Galois-representation property bundle `PropsB` for faithfulness. Every "Published" statement about automorphic or Galois objects depends on them |
| `GlobalTheory.EtC.E1`, `.D2`, `.B4`, `UpperTheory.Gal.Int.Geo.GrpCong`, `LateralTheory.E.ChowCut.ChowL` | various | Internal `Prop` packages. The theorem names (`affine_proper_base_change`, `etale_duality_trace_isomorphism`, `etaleCohomology_excisionAxiom_holds`, `arithmeticGroup_congruenceSubgroupProperty`, `chow_lemma_projective_cover`) promise far more than the statements are known to deliver. `GrpCong` (`Foundations/GaloisRepresentations/IntegralStructures/GeometricFlagBases/FinModel.lean:172`) is a level-subgroup conjugation statement about internal `Datum`/`HTGroup`/`Link` objects, **not** the congruence subgroup property |

## 5. Mechanical families

- `IntegralCasts/CapelliIdentities/` (800 files, namespace `UpperTheory.Reformulated.B.*`): a
  grab-bag of small restated library lemmas, for example Artin's independence of characters
  (`Artin.lean:7`), p-adic norm facts, integrality, existence of primes above `p`. About 474 are
  pure Mathlib statements, each small. The "Capelli identities" name does not match the content.
- `AutomorphicVarieties/ModularityArgument/` (2,449 files): `ThresholdArguments/DenseThresholdCases`
  (530, including multi-thousand-line case files such as `TemperedProductOfSquareIntegrable.lean`),
  `SymmetricPowerTransfer` (430), `TraceFormula` (287), `InductionEstimates` (215). These are
  statements over internal automorphy data; about 29 closed pure statements.
- `ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/` (2,246 files) and `LocalTypeDictionary`
  (535): theta-lift bookkeeping, plus the big literature wrappers
  (`EveryCharacterOfLiteratureOfVWin.lean`, 5,950 lines, about 150 `*_of_literature` one-liners).
- `Foundations/GaloisRepresentations/` (2,914 files; `ThetaParseval` alone has 772): internal
  Galois-representation and deformation lemmas. 16 closed pure statements.
- `Foundations/Convolution/` (1,081 files): adelic and real-group analysis over `Dat`/`CuspSub`.
  About 50 closed pure analysis lemmas (Gaussian/Hermite integrals, Chebyshev polynomials,
  integral estimates).
- `CyclotomicBounds/DeRhamLattices` (~60) and `AutomorphicVarieties/PadicHodgeTheory` (211):
  `p`-adic lattice and period lemmas over internal `LocPrime`/`LocAinf`/`QLat` structures.
- `CommutativeAlgebra/` (412 files, 76 in `EtaleCohomology/`): a scheme- and étale-cohomology
  library on Mathlib `Scheme`s. Some lemmas are pure (for example
  `dedekind_spec_open_isAffine`, `isFinite_of_isPullback_fpqc`,
  `exists_section_lift_of_etale_of_henselian`, `connectedSpace_spec_local_and_laurent`). The
  headline names target internal packages.
- Small `Host`-indexed helper families (`CyclotomicBounds/SmallFacts`, `RamifiedDiscriminants`,
  `PrimeDiscriminants/BadPrimes`, `ConductorsKronecker`, about 200 lemmas): facts about
  `H.condN`, `H.small`, discriminant divisibility, and Frobenius/inertia for the host fields.
  Genuine, but specific to the host family.
- `DedekindLFunctions/LandauTheorems/Ch*.lean` and `SplitInertia.lean`: explicit character-sum
  balance (`ch_balance`, `ch_core`, `ch_top`) over internal `ArithData`/`Data`. This is the
  analytic heart of the window bound, stated over internal data.
- `AutomorphicVarieties/LiteratureResults/` (514 files) and `PublishedTheorems/` (8): `Prop`
  definitions of literature statements, mostly over internal automorphic objects, discharged
  elsewhere.

## 6. Standalone value

**Proved here in usable form, over Mathlib objects:**
- Landau's oscillation criterion for Dirichlet L-functions (`Deduction.lemmaL`,
  `Deduction.zeroFree_of_rpow_window`, the abstract `Deduction.landau_window`) and Landau's theorem
  on entire nonnegative Dirichlet series (`…RankTwoDescent.landau_of`).
- Explicit Mellin formulas for twisted Riesz–Chebyshev means, `L(s̄, χ̄) = conj L(s, χ)`
  everywhere, and Mertens/Chebyshev upper bounds.
- Kronecker–Weber, in field, embedding and profinite forms (`UpperTheory.V.CF.kw`, `.kwHom`,
  `.kwRam`, `.kwAbs`).
- Minkowski's theorem that every nontrivial extension of ℚ ramifies (`UpperTheory.V.CF.minkRam`).
- Stickelberger's theorem for `ℚ(ζ_M)` and the prime factorisation of Jacobi sums.
- Ferrero–Washington, as bounded `l`-rank in cyclotomic `ℤ_l`-towers of abelian fields.
- `L(1−k, χ) = −B_{k,χ}/k` with the standard generalised-Bernoulli facts.
- An explicit class-number bound `log h ≤ ½ log|d| + n log(1 + ½ log|d|)`, and abelian-field
  versions of it.
- Linnik's theorem (`UpperTheory.Lit.linnik`) and `p ≡ 1 (mod M)`, `p ≤ M^A` (`UpperTheory.T3.smallOne`),
  given the `PrimesRel` theorem proved elsewhere in the repo.

**Only a special case or a weak form:**
- Chebotarev appears here only in existence form (`UpperTheory.V.CF.cheb`); the density theorem
  lives in `GroundTheory`.
- The Siegel-type bound inside `PrimesRel` is `1−β ≥ c/(M² log M)`, not Siegel's.
- `UpperTheory.V.X.hQuad` covers only quadratic fields of prime discriminant.
- `QH.twistK` is conditional on the internal `admitted` parameter predicate.

**Misleading names:**
- `DedekindLFunctions`: no Dedekind zeta functions inside.
- `arithmeticGroup_congruenceSubgroupProperty`: not the congruence subgroup property.
- `affine_proper_base_change`, `etale_duality_trace_isomorphism`, `chow_lemma_*`: internal packages.
- `IntegralCasts/CapelliIdentities`: a grab-bag.
- `ThetaCorrespondence/HoweDuality`, `RallisInnerProduct`, `PrismaticDieudonne`: internal data.
- `CyclotomicBounds/DeRhamLattices`: internal period structures.
- The `…_of_literature` theorems: their `OpenLiteratureStatements` argument is usually unused.

The "Published" names whose definitions I did open (`Linnik`, `FerreroWashington`) are faithful.
The rest, for example `HasseNormSt`, `ChebotarevDegreeOne` and `HeckeLEntireAndNonzeroAtOne`,
are defined in `AbelianVarietyTheory` and need checking there.

## 7. Open questions / not verified

- No `#print axioms` was run. I found no `sorry`/`axiom` in this subtree, but the transitive
  closure (GroundTheory, Formalism, AbelianVarietyTheory, PositivityTheory) was not checked here,
  and the statements above inherit the repo's general trust caveat: an untrusted cache, never
  independently rebuilt.
- I did not check whether `CuspSub`, `HChar`, `PropsB`/`Row0b` (the Galois-representation
  theorem on the spine) and the about 150 automorphic "Published" statements are faithful. That
  is the central question for everything internal in this subtree.
- `GroundTheory.Global.SplitsCompletely`, used by `UpperTheory.V.CF.bauer`, was not opened.
- I could not locate the definition of `admitted ε Y U m₀ a₀` used by `QH.twistK` and
  `MeanSquareBounds/StagePow.lean`.
- `GlobalTheory.T.primesInProgressions_relativeError` and
  `GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound` (inputs to `linnik` and
  `shortNorm`) are proved outside this subtree. Their proofs and dependencies belong to whichever
  agent covers `AbelianVarietyTheory`/`Formalism`.
- Lean `v4.33.1` and `module` syntax versus our `v4.36.0` pin: importing any of these needs the
  same Mathlib `fc4f59e5`, and a whole-repo import costs about 19 GB of RAM. Extracting a lemma
  means re-proving it locally (the repo has no licence, so its code can't be copied).
- Overlap with current Mathlib (Gauss-sum norms, inertia cardinality, Hurwitz conjugation) was
  not checked item by item.
