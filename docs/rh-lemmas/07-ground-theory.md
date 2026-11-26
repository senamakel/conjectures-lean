# 07 · `src/GroundTheory`: reusable lemmas inventory

Repo: [riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) at commit 507a75d91d (Lean v4.33.1 `module` syntax,
Mathlib `fc4f59e5`). All paths below are relative to `src/GroundTheory/`. The repo has no licence, so this
file quotes no code: each statement is a paraphrase.

## 1. Scope and method

| Directory | `.lean` files | lines | `theorem`/`lemma` decls |
|---|---:|---:|---:|
| HeightsAndTheta (Heights 4859, Theta 19) | 4878 | 474,825 | 16,768 |
| AutomorphicForms | 478 | 121,669 | 6,309 |
| ProfiniteCohomology | 445 | 82,327 | 3,858 |
| GlobalFields | 355 | 65,026 | 3,821 |
| ArithmeticGeometry | 178 | 33,273 | 1,793 |
| LocalFields | 136 | 32,928 | 1,956 |
| PAdicHodge | 103 | 21,658 | 1,428 |
| TateCohomology | 50 | 7,812 | 453 |
| PowerSubgroups | 16 | 990 | 26 |
| FunctionField | 12 | 3,355 | 191 |
| IdeleRoots | 9 | 992 | 51 |
| Brauer | 7 | 791 | 23 |
| **Total** | **6,667** | **~845k** | **36,677** |

Trust escapes: `rg` finds no `sorry`, `admit`, `axiom` or `native_decide` anywhere in the subtree. (The two
hits for `extern` are a Mathlib lemma name, `externalCoveringNumber`.) I did not build anything, so none of
this has been typechecked by me.

Method:
- `ls` and file counts for every subdirectory. Then the import fan-in from the rest of the repo: 3,548
  files outside GroundTheory import it. The most imported targets are the Heights `Statements*` files
  (around 200 importers each), `AutomorphicForms.MultiplicityOne.Injective` (127) and
  `GlobalFields.TateThesis.AdeleScaling` (56).
- `rg` for headline declarations and Mathlib anchors (`NumberField`, `IsNonarchimedeanLocalField`,
  `AdeleRing`, `groupCohomology`, `tateCohomology`, `HasDirichletDensity`, `arithFrobAt`, `ClassGroup`,
  `WeierstrassCurve`, `IsRegularLocalRing`, `Scheme`, `dedekindZeta`, ...).
- I read the statements in full, plus the `variable` context, of roughly 60 headline theorems: local and
  global class field theory, Chebotarev, Hecke/Tate, Poitou–Tate, local duality, Euler characteristic,
  Brauer, Tate's theorem, CM, Casselman–Shalika, Dixmier–Malliavin, Brouwer, Auslander–Buchsbaum, Serre
  vanishing, Riemann's inequality, the Tate twist, B_dR. I opened the key internal definitions:
  `IdeleGroup`, `HeckeCharacter`, `ClassFieldAxiom`, `CMCurve`, `ArithVariety`, `HermLine`, `height`,
  `IsIntersectionFamily`, `eulerChar`, `IsFunctionField`, `IsUnramifiedEverywhere`, `SplitsCompletely`.
- **Not read**: the large majority of the 4,859 Heights files (I sampled statement names and about 30
  statement bodies), most of AutomorphicForms (Bernstein–Zelevinsky, Jacquet modules, Hermitian-form
  classification and Harish-Chandra modules were seen by file name only), `IdeleRoots`, `PowerSubgroups`,
  `Theta`, and most of the p-adic Hodge internals (A_inf, A_cris, B_cris construction).

Universe caveat: many global results are stated for `K L : Type u`, and the duality theorems for
`Type`/`Type 0`. Poitou–Tate is stated for `K : FiniteSubfield`, a number field realised inside
`AlgebraicClosure ℚ`. Transporting to an arbitrary `NumberField K` needs an embedding.

## 2. What this subtree actually is

GroundTheory is the arithmetic background library of the RH proof, and most of it is the real thing, built
on Mathlib's own objects. It contains:

1. A complete **local class field theory** for every `IsNonarchimedeanLocalField` (char 0 and char p).
   It follows Neukirch's abstract class formations: the class field axiom is *proved* for `Ωˣ`. The
   theory includes Lubin–Tate theory, the existence theorem, local Kronecker–Weber for ℚ_p, and the
   compatibility of upper ramification groups with unit groups (which gives Hasse–Arf for abelian
   extensions).
2. A complete **global class field theory for an arbitrary number field**, on Mathlib's `𝔸[K]`
   (`NumberField.AdeleRing`). It covers the first and second inequalities, the Artin reciprocity map
   `C_K → Gal(K^ab/K)` with kernel the identity component, the existence theorem, ray class fields, the
   Hilbert class field with `ClassGroup (𝓞 K) ≃* Gal(H/K)` sending primes to `arithFrobAt`, the Hasse
   norm theorem for cyclic extensions, and the Dirichlet S-unit theorem.
3. **Tate's thesis and Hecke L-functions** for unitary Hecke characters (`C_K →ₜ* Circle`): continuation,
   functional equation with root number, non-vanishing on Re s ≥ 1, continuation and functional equation
   of Mathlib's `dedekindZeta`, and from these the **Chebotarev density theorem** (Dirichlet density, as
   Mathlib's `HasDirichletDensity`).
4. **Galois cohomology of profinite groups** (continuous cochains on Mathlib `Rep`, with a proved
   comparison to `groupCohomology` for discrete groups). It contains the local invariant
   `Br(K) ≅ ℚ/ℤ`, local Tate duality, Tate's local Euler characteristic formula, the global Brauer
   reciprocity (Σ inv = 0, with local-global injectivity), and Poitou–Tate (perfect pairings, the nine-term
   exact sequence, finiteness of Ш¹/Ш² and the Ш pairing for G_S). On top of Mathlib's `tateCohomology`
   it proves Tate's theorem.
5. A **CM theory**: the main theorem of complex multiplication (Shimura's idelic form) and
   `K(j(E)) = H_K` for imaginary quadratic K, on Mathlib `WeierstrassCurve ℂ`. Alongside it, elliptic
   curve basics: `#E[n] = n²`, the dual isogeny, Frobenius degree.
6. **Representation theory for GL_n**: the Casselman–Shalika formula, Dixmier–Malliavin, and Whittaker
   injectivity for cusp forms.
7. **Arakelov and Philippon height theory** (the 4.9k-file `Heights`): heights of points and cycles on
   multiprojective space over ℤ, Chow forms, Mahler measures, arithmetic Hilbert–Samuel ingredients,
   geometry of numbers. Mixed in are analytic-geometry results stated on Mathlib objects (Brouwer,
   invariance of domain, change of variables for degree-one maps, injective holomorphic maps are
   biholomorphic onto open images).

Directory names are mostly accurate, with one exception: **"Heights" does not mean Weil heights,
Northcott or Mordell–Weil**. There is no Northcott theorem, no Néron–Tate height and no Mordell–Weil.
Heights here are Arakelov heights of points and subvarieties of multiprojective ℤ-schemes, presented by
prime ideals in `MvPolynomial _ ℤ`. Many Heights "theorems" are `X.Statement : Prop` definitions proved
only from other `Statement`s, and are closed (if at all) outside GroundTheory, in `Development/`. A large
family is universally quantified over an abstract `IsIntersectionFamily I` (three axioms for an arithmetic
intersection number), and I found **no** proof anywhere in the repo that such an `I` exists, so those
results may be vacuous. The direct `height` of points in `HeightsOfSets` is concrete and faithful.

## 3. Inventory table (most reusable first)

"Mathlib" means the statement mentions only Mathlib objects, or Mathlib objects plus thin, faithful
wrappers like `IdeleGroup K := (𝔸[K])ˣ`.

| Declaration | path:line | Statement (paraphrased) | Objects | Classical name | Reusability |
|---|---|---|---|---|---|
| `GroundTheory.Global.hasDirichletDensity_chebotarevSet` | GlobalFields/TateThesis/Chebotarev.lean:205 | L/K Galois number fields, C ⊆ Gal(L/K) conjugation-stable: the set of primes v of K, unramified in L with every Frobenius `arithFrobAt` above v in C, has Dirichlet density #C/#G | Mathlib (`HasDirichletDensity`, `arithFrobAt`, `HeightOneSpectrum`) | Chebotarev density theorem (Dirichlet density) | **high**: closed, general |
| `…hasDirichletDensity_setOf_arithFrobAt_mem` / `…_exists_arithFrobAt_mem` | Chebotarev.lean:246 / :253 | Same, phrased with ∀ or ∃ Frobenius over v | Mathlib | Chebotarev | **high** |
| `…hasDirichletDensity_setOf_splitsCompletely` | GlobalFields/TateThesis/DegreeOneDensity.lean:355 | Primes splitting completely in Galois L/K have density 1/[L:K] | Mathlib + `SplitsCompletely` (e=f=1 for all w above v: faithful) | Bauer/Chebotarev special case | high |
| `…hasDirichletDensity_setOf_map_eq` | GlobalFields/TateThesis/RayClassDensity.lean:310 | Continuous surjection q from ideles to a finite abelian group with open kernel: primes whose uniformizer class is c have density 1/#G | Mathlib + `IdeleGroup` | Dirichlet's theorem for ray classes / generalized Dirichlet | high (covers primes in arithmetic progressions in number fields) |
| `GroundTheory.Global.artinMap`, `ker_artinMap`, `artinMap_surjective`, `artinQuotientEquiv` | GlobalFields/GlobalArtinMap/ArtinMap.lean:102; Kernel.lean:173, :111, :220 | For any number field K and algebraic closure Ω: a continuous surjective hom C_K → Gal(K^ab/K) compatible with every finite abelian L; its kernel is the identity component; C_K/D_K ≃ₜ* Gal(K^ab/K) | Mathlib `AdeleRing`, `IntermediateField`, plus internal `maximalAbelianExtension` (fixed field of the closed commutator: faithful) | Global Artin reciprocity | **high** |
| `GroundTheory.Global.reciprocityMapEquiv`, `ker_reciprocityMap`, `index_range_ideleClassNorm_eq_finrank_of_isMulCommutative` | GlobalFields/GlobalReciprocity/General.lean:240, :205, :244 | L/K abelian: C_K / N C_L ≃* Gal(L/K), so [C_K : N C_L] = [L:K] | Mathlib + `ideleClassNorm` (from `Algebra.norm` on adeles) | Artin reciprocity (finite level) | **high** |
| `GroundTheory.Global.firstInequality` | GlobalFields/FirstInequality.lean:106 | For cyclic L/K: [L:K] ≤ #(C_K / N C_L) | Mathlib | First inequality | med (subsumed by the above) |
| `normGroupOrderIso` (global) | GlobalFields/ExistenceTheorem/ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini.lean:228 | Order anti-isomorphism between finite abelian subextensions of Ω/K and open finite-index subgroups of C_K | Mathlib + subtype wrappers | Existence theorem and classification | **high** |
| `hilbertClassFieldArtinEquiv`, `hilbertClassFieldArtinEquiv_mk0`, `le_hilbertClassField_iff`, `isUnramifiedEverywhere_hilbertClassField` | GlobalFields/ClassFieldConsequences/HilbertClassField.lean:73, :77, :53, :35 | H = Hilbert class field: `ClassGroup (𝓞 K) ≃* Gal(H/K)` sending [𝔭] to `arithFrobAt 𝔭`; H is unramified at all places (finite and infinite); an abelian L ⊆ Ω lies in H iff L/K is unramified everywhere | Mathlib (`ClassGroup`, `arithFrobAt`, `Algebra.IsUnramifiedIn`, `InfinitePlace.IsUnramifiedIn`) | Hilbert class field theorem | **high**: e.g. "𝔭 splits in H iff principal" |
| `Modulus.rayClassArtinEquiv`, `splitsCompletely_rayClassField_iff`, `exists_le_rayClassField` | GlobalFields/ClassFieldConsequences/RayClassField.lean:112, :151, :159 | Ray class group mod 𝔪 ≃ Gal of the ray class field; 𝔭 ∤ 𝔪 splits completely iff its class is trivial; every finite abelian L lies in some ray class field | internal `Modulus`, `IdealRayClassGroup` (not opened) | Ray class field theory | high, after checking `Modulus` |
| `mem_range_norm_iff_forall_local` (+ `_of_finrank_eq_two`) | GlobalFields/HasseNorm.lean:60, :86 | L/K cyclic: x ∈ Kˣ is a global norm iff it is a local norm at every finite and infinite place | Mathlib + local norm maps | Hasse norm theorem (cyclic) | **high**: norm-form problems, quadratic forms |
| `finrank_eq` (S-units), `fg` | GlobalFields/SUnits.lean:166, :159 | The S-unit group (Mathlib `S.unit K`) is f.g. of ℤ-rank `Units.rank K + #S` | Mathlib | Dirichlet S-unit theorem | high |
| `HeckeCharacter.exists_LFunction_continuation`, `…_of_forall` | GlobalFields/TateThesis/HeckeTheorem.lean:51, :135 | Unitary Hecke character χ: its L-series (Re s > 1) extends to an entire function, unless χ = abs^{iτ}, in which case it is holomorphic off 1−iτ with a nonzero simple-pole residue | `HeckeCharacter := IdeleClassGroup K →ₜ* Circle` (faithful); `LFunction` built from conductor and ideal coefficients | Hecke's theorem | high |
| `HeckeCharacter.completedLFunction_eq_rootNumber_mul`, `continuedLFunction_functional_equation`, `rootNumber_mul_rootNumber_inv` | GlobalFields/TateThesis/HeckeTheoremFE.lean:74; AnalyticClassNumber/HeckeContinued.lean:156; HeckeTheoremFE.lean:108 | Λ(χ,1−s) = W(χ)·Λ(χ̄,s), with W(χ)W(χ̄) = 1 | internal completed L (gamma factor and discriminant–conductor term) | Hecke functional equation | high (gamma factor definition not audited) |
| `HeckeCharacter.continuation_ne_zero_of_one_le_re` | GlobalFields/TateThesis/Nonvanishing.lean:197 | Any entire continuation of L(χ,s) for χ ≠ abs^{iτ} is nonzero on Re s ≥ 1 | as above | Non-vanishing on Re s = 1 (Hecke/Landau) | high: PNT-type and Chebotarev inputs |
| `HeckeCharacter.LFunction_hasProd_all`, `LFunction_ne_zero`, `LFunction_one` | GlobalFields/TateThesis/HeckeLFunction.lean:390, :398, :443 | Euler product for Re s > 1, non-vanishing there, and L(1,s) = Mathlib `dedekindZeta K s` | Mathlib anchor | Euler product | high |
| `continuedDedekindZeta`, `meromorphicOn_continuedDedekindZeta`, `tendsto_sub_one_mul_continuedDedekindZeta`, `completedDedekindZeta_one_sub` | GlobalFields/TateThesis/DedekindZetaContinuation.lean:44, :97, :72; DedekindContinuation.lean:175 | Mathlib's `dedekindZeta K` extends meromorphically to ℂ, holomorphic off 1, with residue Mathlib `dedekindZeta_residue K`; the completed ζ_K satisfies Λ(1−s) = Λ(s) | Mathlib | Hecke: continuation and FE of ζ_K | **high**: Mathlib lacks this |
| `tateZeta_eq_tateZeta_one_sub` | GlobalFields/TateThesis/TateMain.lean:345 | Global Tate zeta integral Z(F,χ,s) = Z(F̂,χ⁻¹,1−s) for Schwartz–Bruhat F on 𝔸_K | internal `schwartzBruhat`, `tateZeta` | Tate's thesis, global FE | med |
| `localEpsilon_mul_localEpsilon_inv`, `exists_localEpsilon_eq_monomial` | LocalFields/LocalZeta.lean:236, :255 | Local ε-factor relations; ε(χ,ψ,s) = c·q^{−ns} | internal local zeta and ε | Tate local FE | med |
| `GroundTheory.LocalField.localArtinMap`, `injective_localArtinMap`, `continuous_localArtinMap`, `ker_restrictAb_localArtinMap`, `surjective_restrictAb_localArtinMap`, `eq_localArtinMap_of` | LocalFields/LocalArtinMap.lean:30, :133, :111, :54, :62; LocalArtinUniqueness.lean:70 | Any nonarchimedean local field K (Mathlib `IsNonarchimedeanLocalField`), separable closure Ω: an injective continuous Kˣ → Gal(K^ab/K) whose restriction to finite abelian L is onto with kernel N(Lˣ); uniqueness from the uniformizer/unramified normalisation | Mathlib | Local Artin reciprocity | **high** |
| `localReciprocity` | LocalFields/LocalReciprocityFinite.lean:119 | Any finite Galois L/K: Gal(L/K)^ab ≃* Kˣ/N Lˣ | Mathlib | Local reciprocity (finite level) | high |
| `exists_range_normUnits_eq`, `normGroupOrderIso` (local) | LocalFields/Existence.lean:164; NormCorrespondence.lean:89 | Every open finite-index H ≤ Kˣ is the norm group of a unique finite abelian L | Mathlib | Local existence theorem | high |
| `Padic.maximalAbelianExtension_eq_adjoin_rootsOfUnity`, `maximalUnramifiedExtension_eq_adjoin_rootsOfUnity`, `exists_le_adjoin_rootsOfUnity` | LocalFields/KroneckerWeber.lean:235, :203, :171 | ℚ_p^ab = ℚ_p(all roots of unity); ℚ_p^ur = ℚ_p(prime-to-p roots of unity); a finite abelian L/ℚ_p lies in ℚ_p(μ_N) | Mathlib (`ℚ_[p]`, `IntermediateField.adjoin`) | Local Kronecker–Weber | **high** |
| `maximalUnramifiedExtensionGaloisEquiv` | LocalFields/MaximalUnramified.lean:474 | Gal(K^ur/K) ≃ₜ* ℤ̂ (Frobenius ↦ 1) | Mathlib + internal ℤ̂ | Structure of the unramified Galois group | med-high |
| `map_unitFiltrationUnits_restrictAb_localArtinMap`, `upperRamificationGroup_eq_ceil` | LocalFields/ConductorReciprocity.lean:180, :193 | For L/K finite abelian: Artin map sends U^(n) onto the upper ramification group G^n, and G^v = G^⌈v⌉ | internal upper numbering (`herbrandPsi`, lower groups) | Hasse–Arf (abelian) and the conductor–ramification link | high once the upper numbering is checked |
| `map_upperRamificationGroup` | LocalFields/UpperNumbering.lean:222 | Upper numbering is compatible with quotients: (G^v) maps onto (G/H)^v | internal | Herbrand's theorem | med-high |
| `GroundTheory.ProfCoh.bijective_localDualityPairing` | ProfiniteCohomology/LocalTateDuality/TensorHomDualRepRootsOfUnityIsoCartierPairing.lean:125 | Local field K, finite discrete G_K-module M with #M ≠ 0 in K, r+s=2: the cup product into Br(K) ≅ ℚ/ℤ gives a perfect pairing H^r(M) × H^s(M^∨(1)) → ℚ/ℤ | Mathlib `Rep`, internal continuous cohomology (faithful; iso to `groupCohomology` for discrete G) | Local Tate duality | **high** |
| `subsingleton_cohomology_localField` | same file:120 | H^r(G_K, M) = 0 for r ≥ 3 (same hypotheses) | as above | cd(G_K) ≤ 2 for prime-to-p | high |
| `eulerChar_galois`, `card_cohomology_mul_div_eq` | ProfiniteCohomology/LocalEulerCharacteristic/EulerCharGaloisOfCardEq.lean:97, :102 | #H⁰·#H²/#H¹ = 1/#(𝒪_K/#M) | as above | Tate's local Euler characteristic formula | **high** |
| `brauerInv_bijective`, `brauerInvZOfIsSepClosure_bijective` | ProfiniteCohomology/LocalClassFormation/InvariantSplit.lean:179; CupSymbolSep.lean:26 | inv: H²(G_K, Ω^×) → ℚ/ℤ is an isomorphism | internal `galoisBrauerGroup` = cohomological Br (not CSAs) | Local invariant map | high |
| `brauerSumInv_eq_zero`, `brauerLocal_injective` | ProfiniteCohomology/GlobalClassFormation/SumInvariants.lean:36; EqZeroOfBrauerLocalApplyEqZero.lean:68 | Number field K ⊂ ℚ̄: H²(G_K, ℚ̄^×) → ⊕_v H²(G_{K_v}) is injective, and the sum of local invariants is 0 | internal cohomology, `FiniteSubfield`, `LocalEmbeddings` | Albert–Brauer–Hasse–Noether (injectivity and reciprocity; surjectivity onto the kernel not found) | high for Brauer-group arguments |
| `poitouTate_duality_gs`, `poitouTate_sha_gs`, `poitouTate_nineTerm_gs` | ProfiniteCohomology/PoitouTate/PoitouTateNineTermGs.lean:41, :47, :55 | G_S = Galois group of the maximal extension unramified outside finite S ⊇ {v ∣ N}; finite M with N·M = 0 and (N odd or K totally complex): compact-support duality is bijective, Ш¹(M) and Ш²(M^∨) are finite and perfectly paired, the nine-term sequence is exact | internal `galUnramifiedOutside`, `ptSha`, local families | Poitou–Tate | high, with care: real places are handled only through the odd-N / totally-complex hypothesis |
| `eulerChar_gs_pos` and the `GlobalEulerCharacteristic/*` family | ProfiniteCohomology/GlobalEulerCharacteristic/DefsForms.lean:81 | Global Euler characteristic of G_S (exact form not read) | internal | Tate's global Euler characteristic formula (probably) | med (unverified) |
| `GroundTheory.GroupCoh.tateTheoremIso` | TateCohomology/TateTheorem.lean:54 | Finite G, M with H¹(S,M) = 0 for all S ≤ G and u ∈ H²(G,M) restricting to generators of order #S: Ĥⁿ(S,ℤ) ≅ Ĥⁿ⁺²(S,M) | Mathlib `tateCohomology`, `groupCohomology` | Tate's theorem (Tate–Nakayama) | **high** |
| `herbrandQuotient_eq_mul_of_shortExact`, `…_eq_one_of_finite` | TateCohomology/HerbrandAbstract.lean:391, :89 | Herbrand quotient is multiplicative in short exact sequences and 1 on finite modules | abstract endomorphism pairs | Herbrand quotient lemma | med-high |
| `exists_unit_conj` | Brauer/SkolemNoether.lean:129 | A central simple, B simple, finite-dimensional over K: any two K-algebra maps B → A are conjugate by a unit | Mathlib | Skolem–Noether | **high** |
| `finrank_mul_finrank_centralizer` | Brauer/DoubleCentralizer.lean:143 | dim B · dim C_A(B) = dim A | Mathlib | Double centralizer (dimension part) | high |
| `exists_algEquiv_matrix_algebraicClosure` | Brauer/Degree.lean:21 | A CSA over K: dim A = n² and K̄ ⊗ A ≅ M_n(K̄) | Mathlib | Degree of a CSA is a square | high |
| `main_theorem_complexMultiplication` | GlobalFields/ComplexMultiplication/MainTheorem.lean:71 | K imaginary quadratic, σ ∈ Aut(ℂ/K), idele s with artin(s) = σ on K^ab, f: ℂ/𝔞 ≅ E(ℂ): there is a unique f': ℂ/s⁻¹𝔞 ≅ E^σ(ℂ) with f'(s⁻¹t) = σ(f(t)) on K/𝔞 | Mathlib `WeierstrassCurve ℂ`, Mathlib idele/adele objects; internal `IsAnalyticUniformization` (faithful) | Main theorem of CM (Shimura) | **high** |
| `Elliptic.adjoin_j_eq_hilbertClassField` | GlobalFields/ComplexMultiplication/HilbertClassField.lean:38 | For a CM curve by 𝓞_K: K(j(E)) = Hilbert class field of K | internal `CMCurve` (End ≅ 𝓞_K via internal isogeny ring) | Weber–Fueter: j generates H_K | high (e.g. p = x² + ny²) |
| `modularJ_smul`, `g₂_latticeOfTau`, `g₃_latticeOfTau` | GlobalFields/ComplexMultiplication/JInvariant.lean:85, :57, :63 | j is SL₂(ℤ)-invariant; g₂, g₃ in terms of Mathlib E₄, E₆ | Mathlib modular forms | classical | med |
| `card_zsmul_eq_zero` | ArithmeticGeometry/AbelianVarieties/KernelCard.lean:175 | E elliptic over a separably closed field, n invertible: #E[n] = n² | Mathlib `WeierstrassCurve` | n-torsion count | **high** |
| `Isogeny.dual`, `degree_dual`, `dual_comp`, `comp_dual`, `pointMap_surjective` | ArithmeticGeometry/AbelianVarieties/DualIsogenyExists.lean:290–311 | Dual isogeny exists, has the same degree, and φ̂φ = [deg φ]; isogenies are surjective on points | internal `Isogeny` (function-field comap) on Mathlib curves | Dual isogeny | med-high |
| `card_torsion_lt` | ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean:131 | In char p: #E[p] < p² | Mathlib | Inseparability of [p] | med |
| `IsRegularLocalRing.uniqueFactorizationMonoid`, `…isIntegrallyClosed` | ArithmeticGeometry/SchemeCohomology/RegularUFD.lean:173, :272 | Regular local rings are UFDs (and normal) | Mathlib `IsRegularLocalRing` | Auslander–Buchsbaum | **high**: Mathlib lacks this |
| `finite_H_of_isProper` | ArithmeticGeometry/SchemeCohomology/ProperFiniteness.lean:28 | X proper over Noetherian A, F coherent: every Hᵖ(X,F) is a finite A-module | Mathlib `Scheme`, `IsProper`, `Sheaf.H`; `IsCoherent` not checked | Grothendieck/Serre finiteness | high |
| `finite_H`, `exists_subsingleton_H_twist` | ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ExistsGeneratingSectionsTwist.lean:46, :52 | Closed X ⊂ ℙⁿ_A: Hᵖ finite, and Hᵖ(F(q)) = 0 for p > 0, q ≫ 0 | Mathlib schemes + internal `projectiveSpace`, `twist` | Serre vanishing | high |
| `Divisor.riemann_inequality`, `genus_eq_genusInt`, `indexOfSpeciality_eq_genusInt` | FunctionField/ExistsBoundDegSubFinrankL.lean:165, :160, :226 | K/k a function field of one variable, k algebraically closed in K: ℓ(D) ≥ deg D + 1 − g; i(D) = ℓ(D) − deg D − 1 + g via repartitions | internal `IsFunctionField` (∃ transcendental x with K/k(x) finite: faithful), divisors and places | Riemann's theorem; RR via adèles (no canonical-divisor form found) | med-high |
| `cpTwistRep_invariants_zero`, `cpTwistRep_invariants_eq_bot` | PAdicHodge/ExistsGalFixCyclotomicLayerCycloCharNeOne.lean:289, :301 | K/ℚ_p finite (inside Mathlib `PadicAlgCl p`): ℂ_p^{G_K} = K and ℂ_p(j)^{G_K} = 0 for j ≠ 0 | Mathlib `ℂ_[p]`, `PadicAlgCl` | Tate's theorem on ℂ_p(j) (Tate–Sen) | **high** |
| `exists_eq_coe_of_forall_smul_eq` | PAdicHodge/AxLemma.lean:530 | A G_K-fixed element of ℂ_p lies in K | Mathlib | Ax–Sen–Tate | high |
| `bDeRham_fixed`, `bCris_fixed`, `bCris_fixed_mem_maxUnramified` | PAdicHodge/BdRInvariants.lean:110; BCrisRegular.lean:94; FontaineLemmaInvariants.lean:407 | (B_dR)^{G_K} = K; fixed points of B_cris land in K (and in K₀ = K ∩ ℚ_p^ur) | internal B_dR, B_cris (built on Mathlib `PreTilt`/Witt vectors; not audited) | Fontaine's period-ring invariants | med |
| `casselman_shalika` | AutomorphicForms/MacdonaldFormula.lean:145 | Nonarchimedean F, ψ unramified, W a spherical Whittaker function on GL_n(F) that is a Hecke eigenfunction with Satake parameter z: W(ϖ^λ) = W(1)·δ^{1/2}(ϖ^λ)·s_λ(z) for dominant λ, else 0 | Mathlib `GL (Fin n) F`; internal Hecke algebra and Satake transform | Shintani / Casselman–Shalika formula | med-high |
| `macdonald_formula_hlR` | AutomorphicForms/MacdonaldFormula.lean:107 | Macdonald's spherical function formula (Hall–Littlewood form) | internal | Macdonald formula | med |
| `dixmierMalliavin` | AutomorphicForms/DixmierMalliavin.lean:129 | Closed linear Lie group G ⊂ 𝔸ˣ (Banach algebra) with Lie algebra 𝔤: every smooth compactly supported f is a finite sum of convolutions φᵢ * ψᵢ of smooth compactly supported functions | internal `IsExpLieAlgebra` (exp-chart condition: faithful) | Dixmier–Malliavin | med |
| `eq_zero_of_whittaker_eq_zero` | AutomorphicForms/MultiplicityOne/Injective.lean:81 | A continuous, left-invariant, cuspidal, right K_f-finite φ on GL_n(𝔸_K) with vanishing Whittaker function is 0 | internal `AdelicGL`, `IsCuspidal` | Piatetski-Shapiro–Shalika (Whittaker injectivity) | med |
| `AutoClose.brouwer_fixed_point_holds` | HeightsAndTheta/Heights/LocalFiniteness/InjectiveHolomorphicJacobianNeZeroHolds.lean:260 | Every continuous self-map of the closed unit ball in ℝⁿ has a fixed point | Mathlib | Brouwer fixed point theorem | **high**: Mathlib lacks it |
| `AutoClose.invariance_of_domain_holds` | HeightsAndTheta/Heights/LocalFiniteness/ParametrisationSheetsConnectedHolds.lean:86 | Continuous injective f on open U ⊆ ℝⁿ has open image | Mathlib | Invariance of domain | **high** |
| `ChangeOfVariablesDegree.proof` | HeightsAndTheta/Heights/ComplexAnalyticSets/PChangeOfVariablesDegree.lean:190 | φ smooth, φ − id compactly supported: ∫ f∘φ · det Dφ = ∫ f for smooth compactly supported f | Mathlib | Degree-one change of variables | med-high |
| `…InjectiveHolomorphicInverse` / `…JacobianNeZero` (`AutoClose.injective_holomorphic_inverse_holds`) | ParametrisationSheetsConnectedHolds.lean (≈ :89); StInjectiveHolomorphic*.lean | Injective holomorphic f on open U ⊆ ℂᵏ has nonzero Jacobian, open image and holomorphic inverse | Mathlib | Osgood / injective ⇒ biholomorphic | high |
| `RiemannExtensionAnalytic.proof`, `LinearNoetherNormalization.proof`, `LocalDimDomain.proof` | HeightsAndTheta/Heights/ComplexAnalyticSets/PRiemannExtensionAnalytic.lean:240; PLinearNoetherNormalization.lean:58; PLocalDimDomain.lean:15 | Riemann extension theorem (form not read); linear Noether normalization; local Krull dimension of a prime is constant along its zero set over ℂ | Mathlib | classical | med |
| `MinkowskiCovolumeBound.proof` | HeightsAndTheta/Heights/CountingLowerBound/PMinkowskiCovolumeBound.lean:16 | Lattice L in Euclidean V of dim n: (λ₁/√n)ⁿ ≤ covol L | Mathlib `IsZLattice`, `ZLattice.covolume` | Minkowski/Hermite-type bound | high |
| `SymplMinkowskiBox.full`, `SymplMinBound.full`, `SymplMinExists.full` | HeightsAndTheta/Heights/HeightKernels/AssemblySympl.lean:73, :85, :76 | |det A| = 1, ∏aᵢ > 1 gives a nonzero integer v with |(Av)ᵢ| < aᵢ; a positive-definite quadratic form attains its minimum on ℤⁿ∖0, and for det 1 that minimum is ≤ n | Mathlib matrices | Minkowski linear forms; Hermite bound (weak) | high |
| `GaussianSum.full` | HeightsAndTheta/Heights/HeightKernels/AssemblyAnalytic.lean:41 | Uniform bound for shifted theta sums Σ exp(−π/2·Y[k+u]) in terms of the lattice minimum | Mathlib matrices | Theta-series bound | med |
| `mahlerMul`, `sphereMeanLinear` | HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean:57; SphereMean.lean:71 | Sphere-Mahler measure is additive on products; mean of log|⟨z,p⟩| over the unit sphere in ℂⁿ is −H_{n−1}/2 | internal `mahler` (unit-sphere measure, not the torus one) | Philippon's sphere Mahler measure | med |
| `HeightComparison.main` | HeightsAndTheta/Heights/HeightsOfSets/HeightsSetAll.lean:16 | For a smooth hermitian O(d) on multiprojective space and an arithmetic variety P: |h_A(x)| ≤ k·h_std(x) + C on P(ℚ̄) | internal `ArithVariety`, `HermLine`, `height` (all faithful; `height` is the normalised sum over Mathlib `FinitePlace` and complex embeddings) | One piece of the height machine | med (weak) |
| `DenseBoundedHeight.main` | HeightsAndTheta/Heights/HeightsOfSets/HeightsSetAll.lean:18 | Every arithmetic variety has a Zariski-dense set of ℚ̄-points of bounded height | internal, faithful | "dense set of small points" (easy direction) | low-med |
| `SlopeMaxExtension.main` | HeightsAndTheta/Heights/HeightsOfSets/HeightsSetAll.lean:20 | For hermitian vector bundles over 𝓞_K in a short exact sequence: μ_max(E) ≤ max(μ_max E′, μ_max E″) | internal `HermitianBundle` (𝓞_K-module + metrics) | Arakelov slope inequality | med |
| `KrullAkizuki.full`, `ProjNullstellensatz.full`, `MultigradedHilbertPolynomial.full` | HeightsAndTheta/Heights/IntegralModels/Assembly.lean:42; ChowForms/Assembly.lean:30; HilbertSamuel/AssemblyBase.lean:327 | Krull–Akizuki; projective Nullstellensatz; multigraded Hilbert polynomial (statements not read) | Mathlib by name | classical | med (unverified forms) |

## 4. Internal definitions worth knowing

| Definition | Where | Verdict |
|---|---|---|
| `IdeleGroup K := (𝔸[K])ˣ`, `IdeleClassGroup K := IdeleGroup K ⧸ diagonal` | GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean:16, :54 | **Faithful.** `𝔸[K]` is Mathlib's `NumberField.AdeleRing (𝓞 K) K` |
| `ideleNorm`, `ideleClassNorm` | GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean:158, :195 | Faithful: `Algebra.norm 𝔸[K]` on `𝔸[L]` |
| `ideleSymbol`, `reciprocityMap K L` | NormResidueSymbol/RangeIdeleNormLeKerIdeleSymbol.lean:25; GlobalReciprocity/General.lean:194 | Faithful: product of local Artin symbols, then descended to C_K once reciprocity is proved |
| `maximalAbelianExtension F Ω` | LocalFields/MaximalAbelianExtension.lean:24 | Faithful: fixed field of the closure of the commutator subgroup |
| `maximalUnramifiedExtension` | LocalFields/MaximalUnramified.lean:338 | Faithful: sup of unramified subextensions |
| `ClassFieldAxiom`, `ClassFieldTheory` | LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean:202, :208 | Faithful Neukirch axiom (cyclic layers: #Ĥ⁰ = degree, #Ĥ⁻¹ = 1). It is **proved** for local `Ωˣ` (LocalAxiom.lean:153) and the global idele class limit (IdeleClassGroup/NatCardTateOfIsCyclic.lean:47), not assumed |
| `FirstInequality` | GlobalFields/FirstInequalityStatement.lean | A Prop, proved (`firstInequality`). Lemmas taking `hFI` are therefore unconditional |
| `HeckeCharacter K := IdeleClassGroup K →ₜ* Circle` | GlobalFields/TateThesis/HeckeChar.lean:19 | Faithful (unitary Grössencharacters); `conductor`, `LFunction` derived |
| `chebotarevSet`, `SplitsCompletely`, `IsUnramifiedEverywhere` | TateThesis/ChebotarevCount.lean:21; KummerTheory/Splitting.lean:60; ClassFieldConsequences/TrivialModulus.lean:23 | Faithful, built from Mathlib `ramificationIdx`, `inertiaDeg`, `arithFrobAt`, `IsUnramifiedIn` |
| `cohomology A n` (continuous cochains), `IsDiscreteRep` | ProfiniteCohomology/ContinuousCochains.lean:123; DiscreteModules.lean:48 | Faithful: locally constant cochains on Mathlib `Rep`; `cohomologyIsoGroupCohomology` (Functoriality.lean:105) for discrete G |
| `galoisBrauerGroup K L := cohomology (galUnits K L) 2` | ProfiniteCohomology/GaloisCohomology/UnitsInflationCochainsFHomApply.lean:64 | Faithful cohomological Brauer group. **Not** linked to Mathlib's CSA `BrauerGroup` (none found) |
| `eulerChar A = ∏_{q<3} #Hq^{(−1)^q}` | ProfiniteCohomology/EulerCharDefs.lean:29 | Faithful (as a rational number) |
| `FiniteSubfield` | GlobalFields (many) | A number field realised as a finite-dimensional subfield of `AlgebraicClosure ℚ`. Faithful, but transport is needed for an abstract `NumberField` |
| `CMCurve K` / `ELL K` | GlobalFields/ComplexMultiplication/ClassGroupAction.lean:74, :90 | Elliptic `WeierstrassCurve ℂ` with `isogEnd ≃+* 𝓞 K`, modulo variable change. Faithful if `isogEnd` is (internal isogeny ring, not audited) |
| `IsAnalyticUniformization Λ f` | ComplexMultiplication/AnalyticUniformization.lean:20 | Faithful: additive surjection ℂ → E(ℂ) with kernel Λ, analytic in affine and infinity charts |
| `IsFunctionField k K` | FunctionField/PlaceDefs.lean:17 | Faithful: there is a transcendental x with K/k(x) finite. Distinct from Mathlib's `FunctionField` (which is over `RatFunc Fq`) |
| `ArithVariety n`, `HermLine n`, `height` | HeightsAndTheta/Heights/HeightsOfSets/Points.lean:33, :71, :137 | Faithful: a prime, multihomogeneous, relevant, horizontal ideal of ℤ[X]; O(d) with a smooth positive metric; the usual normalised Arakelov height of a ℚ̄-point over Mathlib `FinitePlace` and complex embeddings |
| `IsIntersectionFamily I` | (outside the subtree) ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/IsIntersectionFamily.lean:194 | **Possibly vacuous.** An axiomatic arithmetic intersection number (symmetric, additive, recursive Bost–Gillet–Soulé formula). No existence proof found. Every Heights statement of the form `∀ I, IsIntersectionFamily I → …` (≈152 files) is only as good as an existence proof |
| `IsExpLieAlgebra G 𝔤` | AutomorphicForms/RealGroupsLie.lean:123 | Faithful: a closed subgroup of the units of a Banach algebra with exp-chart Lie algebra |
| `cpTwistRep K j` | PAdicHodge/TateCpTwist.lean:67 | Faithful: ℂ_p with σ acting by χ_cyc(σ)^j · σ |

## 5. Mechanical families

- **Heights `Statement`/`proof`/`full` triples**: 2,511 `def X.Statement : Prop` across GroundTheory, about
  2,490 of them in Heights. There are 516 `X.full`/`X.main` closers in HeightsAndTheta, and 1,757
  occurrences of a `Statement` taken as a hypothesis. A sizeable fraction is closed only in
  `Development/…` (for example `MahlerSection`, `KodairaGeneric`, Weierstrass preparation) or not at all
  as far as `rg` shows (`ChowHeightRecursion`, `HilbertSamuelProjective`, `WeierstrassDivision`,
  `RueckertNullstellensatz`).
- **Heights ComplexAnalyticSets** (864 files): local analytic geometry. Germs, Weierstrass
  preparation/division (conditional on sub-statements), Lelong numbers, Bergman kernels, area formula,
  Chow forms over ℂ.
- **Heights HilbertSamuel / KleimanAmpleness / DiscreteValuationNumbers / Intersections / ArithmeticBezout**
  (739 / 474 / 425 / 304 / 231 files): arithmetic Hilbert–Samuel machinery for multiprojective
  arithmetic varieties, ampleness, vertical/horizontal intersection numbers. Mostly internal
  `MRing ι`/`HermLine` objects, often `∀ I, IsIntersectionFamily I → …`.
- **Heights `Comb*`** (≈ 30 statements): tableau and Young-diagram combinatorics feeding symmetric
  function identities (`hsymm`, Vandermonde).
- **ProfiniteCohomology RestrictedRamification** (91), **GlobalClassFormation** (76), **RealPlaces** (32):
  plumbing for G_S, idele cohomology limits and real-place 2-torsion.
- **AutomorphicForms GL2** (83), **GeometricLemma*** (≈ 20), **FiniteLength*** (≈ 12), **Hermitian*** (≈ 12),
  **Macdonald*** (8): Bernstein–Zelevinsky geometric lemma, admissible finite length, Jacquet modules,
  local Hermitian-form classification. Not read in detail.
- **ComplexMultiplication** (96 files): reduction of elliptic curves, analytic–algebraic comparison, Weber
  functions, residue theorem on rectangles. All feeds `main_theorem_complexMultiplication`.
- **PAdicHodge `SenTate*`, `BCrisNewton*`, `FieldOfNorms*`** (≈ 40 files): Sen–Tate normalised traces,
  Newton polygons in B_cris, field of norms for the cyclotomic tower.

## 6. Standalone value

**Proved in usable form (statements read):**
- Global class field theory for every number field on Mathlib's adeles: reciprocity, existence,
  Artin map kernel, ray class and Hilbert class fields with Frobenius ↔ prime classes.
- Local class field theory for every `IsNonarchimedeanLocalField`, and local Kronecker–Weber for ℚ_p.
- The Chebotarev density theorem (Dirichlet density, Mathlib `HasDirichletDensity`), and density of
  primes in ray classes.
- Continuation and functional equation of Mathlib's `dedekindZeta` with its residue; Hecke L-functions
  of unitary Hecke characters (continuation, FE, non-vanishing on Re s ≥ 1).
- The Hasse norm theorem (cyclic) and the Dirichlet S-unit theorem.
- Tate's theorem on Mathlib `tateCohomology`; local Tate duality; Tate's local Euler characteristic
  formula; local Br ≅ ℚ/ℤ; the global Brauer injectivity and reciprocity; Poitou–Tate for G_S
  (N odd or K totally complex).
- Skolem–Noether, dim B · dim C(B) = dim A, CSA degree is a square.
- The main theorem of CM and K(j) = H_K for imaginary quadratic K.
- #E[n] = n² and the dual isogeny for elliptic curves on Mathlib `WeierstrassCurve`.
- Auslander–Buchsbaum (regular local ⇒ UFD); coherent cohomology finiteness for proper schemes; Serre
  vanishing on closed subschemes of ℙⁿ_A.
- Tate's ℂ_p(j)^{G_K} theorem and Ax–Sen–Tate; (B_dR)^{G_K} = K.
- Brouwer fixed point and invariance of domain in ℝⁿ; injective holomorphic maps of ℂᵏ are biholomorphic
  onto open images.
- Minkowski-type lattice bounds on Mathlib `IsZLattice`.
- The Casselman–Shalika formula for GL_n.

**Special cases only:**
- Kronecker–Weber is local, over ℚ_p only. No global "ℚ^ab = ℚ(μ_∞)" headline was found.
- Brauer–Hasse–Noether: injectivity and Σinv = 0 only; exactness at ⊕ Br(K_v) (surjectivity onto the
  kernel) was not found.
- Poitou–Tate needs N odd or K totally complex.
- Riemann–Roch for function fields: Riemann's inequality and the repartition form of i(D); no
  canonical-divisor form ℓ(D) − ℓ(K−D) = deg D + 1 − g was found. The scheme-level `RiemannRoch.lean`
  only sets up instances and degrees.
- Hasse–Arf: only for abelian extensions, through `upperRamificationGroup_eq_ceil`.

**Misleading names:**
- `HeightsAndTheta/Heights`: there is no Northcott, no Weil height machine for general varieties, no
  Néron–Tate height and no Mordell–Weil. It is Arakelov/Philippon heights of points and cycles on
  multiprojective ℤ-schemes. The one comparison theorem (`HeightComparison`) only covers O(d) on
  multiprojective space.
- `Brauer/`: only central simple algebra lemmas. The Brauer *group* lives as H² in ProfiniteCohomology,
  and the two are not linked.
- `ArithmeticGeometry/AbelianVarieties`: elliptic curves only (Weierstrass), not higher-dimensional
  abelian varieties. `JacobianSmoothness` was not read.
- `ArithmeticGeometry/ModularCurves`: a single file about Weierstrass genus.
- `SiegelCoordinates.intersectionNumber_baseChange` proves the Siegel-coordinates statement despite its
  name.
- Heights `KodairaGeneric`, `HilbertSamuelProjective`, `ChowHeightRecursion`, `MahlerSection`: stated
  here, but not proved inside GroundTheory.

## 7. Open questions / not verified

- Nothing was built or `#print axioms`-checked. No `sorry`, `axiom` or `native_decide` appear in the
  subtree. Proofs that depend on files outside GroundTheory (`ReciprocityTheory/…`, `Development/…`)
  inherit their status.
- Whether `IsIntersectionFamily` is inhabited. If it is not, the ≈152 files of Heights results quantified
  over it are vacuous. A search of the whole repo for an existence theorem found none.
- The exact definitions of `upperRamificationGroup`/`herbrandPsi`, `Modulus`/`IdealRayClassGroup`,
  `isogEnd`, `gammaFactor`/`discrNormConductor`, `schwartzBruhat`, B_dR/B_cris, `IsCoherent` and the
  internal `projectiveSpace` were not audited for faithfulness.
- Statements I did not read: the global Euler characteristic theorem, `GlobalFields/Artin/*` (Artin
  conductors and series), `WeilGroups`, `KummerTheory`, the `AutomorphicForms` Hermitian classification
  and finite-length theorems, `DefiniteClassNumber`, `TensorProductTheorem` (Flath), `CuspidalDiscreteness`,
  `IdeleRoots` (Satake bounds), `PowerSubgroups`, `Theta`.
- Whether `poitouTate_*_gs` includes the Archimedean places in its local terms, or only finite S under the
  odd/totally-complex hypothesis.
- How many of the 2,511 Heights `Statement`s are closed somewhere in the repo. I traced about 40.
