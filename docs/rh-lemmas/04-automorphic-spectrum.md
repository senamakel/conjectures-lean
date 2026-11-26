# riemann-hypothesis lemma inventory 04: `Development/AutomorphicSpectrum` and `Development/DiscreteGroups`

Repo: [riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), commit `507a75d91d`. All paths below are relative to
`src/Development/AutomorphicSpectrum/` unless prefixed with `DiscreteGroups/` or `src/`. This was read only. Nothing
was built, and no code is reproduced here. Statements are paraphrased.

## 1. Scope and method

| Subtree | `.lean` files | Lines | `theorem`/`lemma` | `def`/`structure`/... |
|---|---|---|---|---|
| AutomorphicSpectrum | 13,644 (Proofs 13,432; Definitions 152; Statements 43; PublishedTheorems 16; RootSurvey 1) | 1,112,573 | 49,596 | 7,433 |
| DiscreteGroups | 125 (GlobalIrreducibility 89; PiInvariants 36) | 12,716 | 576 | n/a |

Inside `Proofs/`: BlockDecomposition 7,067, GeometryProofs 2,972, MetricProofs 1,545, AlgebraProofs 809, GlobalProofs 462,
DivisibilityProofs 369, plus small AdelicProofs (62), TwistedProofs (53), MembershipProofs (52), NonGaloisProofs (24),
HermitianForms (10), JetProofs (4), SemilocalMultiplicity (3).

What I did:
- **Read in full:** all 16 `PublishedTheorems` files, the `RootSurvey` file, and every declaration in the 43 `Statements`
  files (I stripped imports and blank lines and read the rest, about 1,100 lines).
- **For every `def X : Prop` in Statements/PublishedTheorems (61 names)** I searched the whole `src/` for a theorem of
  type `X` (or `... → X`) to find out whether it is proved, proved conditionally, or only stated (table in §6).
- **Index of headline wrappers:** 5,674 files in `Proofs/` contain a one-line re-export
  `theorem _root_.GlobalTheory.T.<name> : <statement>`. I extracted all 5,674 signatures and scored each by how many of its
  identifiers are defined in the repo but not in Mathlib (Mathlib names came from `.lake/packages/mathlib`). 558
  signatures use only Mathlib vocabulary, and another 992 use one repo identifier. I read the names of all 558, read
  about 60 full signatures, and followed the definitions behind the ones that looked significant.
- **Checked:** `rg` for `sorry`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern` found **none** in either
  subtree.
- **DiscreteGroups:** listed every file, read the top-level theorem of each family and traced
  `LocalConverseGL` to its definitions.
- **Skipped:** the bodies of the ~13k proof files (they are lemma-by-lemma case work), and the full dependency chains
  into `WeilBound`, `AbelianVarietyTheory`, `GroundTheory`, `ReciprocityTheory` (other agents' subtrees). Many
  definitions used here live there. Where I opened one, I say so.

## 2. What this subtree actually is

The directory names (`AutomorphicSpectrum`, `BlockDecomposition`, `DiscreteGroups`) say little about the content, and
the file names inside `BlockDecomposition` are mixed together (`CuspRapidDecaySiegelGL`, `LubinTateUnramifiedDegreeOne`,
`SobolevSpaceComplete`, `MirabolicDoubleCosetDecomposition`, ...). The **Statements** and **PublishedTheorems** layers
show what the subtree is actually about: **Arakelov geometry and p-adic Hodge theory on integral models of unitary
(PEL-type) Shimura varieties over CM fields**. The objects are `Host E` / `Datum H` / `Moduli D l` / `Model Xo c β`
(CM field, signature (p,q), level, integral model), `HodgeCpt` (Hodge components with Hodge–Tate lattices), root
towers (`RootTower`, `GoodOrigin`), metrized line bundles (`HermLine`, `IntersectionSystem`), and heights. Typical
targets: an arithmetic degree formula for a flat metrized line bundle in terms of `L'(1,χ)/L(1,χ)` for the Kronecker
character (`FlatDegree`, a Chowla–Selberg/Colmez-type formula), volume theorems for the towers (`VolumeTheoremX`), slope
and height bounds. Inputs from the literature are stated as `Prop` definitions in `PublishedTheorems`:
Fargues's Hodge–Tate exact sequence, Zarhin's trick, quotients of abelian schemes by finite flat subgroups,
Hironaka's resolution and principalisation in characteristic 0, GAGA for sections, arithmetic Poincaré–Lelong, the
arithmetic Hilbert–Samuel formula, the prismatic Dieudonné module. Most of them are later proved somewhere in the repo
(§6).

`Proofs/` divides roughly into: (i) the Shimura-variety and Arakelov machinery itself (GeometryProofs, MetricProofs,
DivisibilityProofs, much of AlgebraProofs), which is about internal structures; and (ii) a large layer of general
support lemmas in BlockDecomposition and GlobalProofs. That layer covers GL_n over p-adic fields (Jacquet modules,
mirabolic subgroups, Bernstein–Zelevinsky-style analysis, Hecke algebras), Siegel–Weil integrals for hermitian forms over
CM extensions, Hecke characters and their L-functions (Euler product, functional equation), partial zeta functions of
totally real fields (Shintani cones), ray-class primes, local and global class field theory compatibilities, Čech
cohomology, Kähler differentials and commutative algebra. **Layer (ii) is where the reusable mathematics is.**

`DiscreteGroups/GlobalIrreducibility` proves a **local converse theorem for GL_{m+1} over a p-adic field (twists by
GL_m)** (`LConvFinal.lean:22`). `PiInvariants` is internal glue (θ-fixed cusp forms, Casimir eigenvalues), apart from
Schur's lemma, Burnside's theorem and uniqueness of the trace, all over ℂ.

How this enters the RH proof (inferred from imports, not traced to `Main.lean`): 3,529 distinct modules of
AutomorphicSpectrum are imported from outside it. The heaviest importers are `WeilBound`, `AbelianVarietyTheory` and
`CompanionTheory/AutomorphicTheory`. The final RH and GRH theorems use the Shimura-variety height bounds through those
subtrees. I did not trace the chain.

## 3. Inventory (most reusable first)

"Mathlib" means the statement mentions only Mathlib objects, so it can be imported and used as is. "Internal" means it
depends on repo definitions; §4 says what I checked about those. Every row is a theorem with no `sorry`
(no `sorry`/`axiom` anywhere in the subtree), but nothing has been rebuilt here.

| Declaration | path:line | Statement (paraphrased) | About | Classical name / reference | Reusability |
|---|---|---|---|---|---|
| `GlobalTheory.CompanionTheory.Hypotheses₂.partialZetaFunctionalEquation` (proves `GlobalTheory.Published.PartialZetaFunctionalEquation`, defined in `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PartialZetaFunctionalEquation.lean:15`) | `Proofs/GlobalProofs/PartialZetaFunctionalEquation.lean:142` | For a **totally real** number field F and ideal classes C, C' with C·C' = class of the different: there are functions Z, Z' that are holomorphic on ℂ∖{1}, equal the partial zeta Σ_{J∈C} N(J)^{-s} for Re s > 1, and satisfy \|d_F\|^{s/2} Γ_ℝ(s)^n Z(s) = \|d_F\|^{(1-s)/2} Γ_ℝ(1-s)^n Z'(1-s) (away from the trivial-zero points) | Mathlib (ClassGroup, absNorm, differentIdeal, Gammaℝ; `IsPartialZeta` is a transparent def: differentiable off {1}, Dirichlet series for Re s>1) | Hecke: continuation and functional equation of partial zeta functions, totally real case | **High**. Summing over C gives continuation + FE of the Dedekind zeta of a totally real field, which Mathlib lacks. Not enough for the Kummer fields in artin-grh (not totally real) |
| `functionalEquation_classHecke` | `Proofs/GlobalProofs/PartialZetaFunctionalEquation.lean:126` | Totally real F: the L-function of a class-group character (as a Hecke character, `continuedLFunction`) satisfies the completed functional equation, with a root number ψ(class of the different) | Mathlib + `GroundTheory.Global.HeckeCharacter` (continuous character of the idele class group to the circle) | Hecke L-functions of class-group characters | High (same caveat) |
| `GlobalTheory.CompanionTheory.HeckeFE.heckeTateFunctionalEquation` (proves `GlobalTheory.Published.HeckeTateFunctionalEquation`, `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/HeckeTateFunctionalEquationCM.lean:191`) | `Proofs/GlobalProofs/HeckeTateFunctionalEquation.lean:258` | E totally complex with a CM type φ; χ a unitary Hecke character (continuous character of the ideles trivial on E^×) whose infinity type is n w.r.t. φ, **n ≠ 0**, with conductor exponents a. Then completed L-functions Λ(χ), Λ(χ⁻¹) exist (entire; for Re s>1 equal to the Γ-factor times the Euler product) and Λ(χ,s) = ε_∞(n)·ε_fin(χ,a,s)·Λ(χ⁻¹,1−s) | Mathlib-level objects (ideles, adic completions, Γ), packaged in repo defs `HChar`, `IsCompletedL`, `finEps` (all opened, look faithful) | Hecke / Tate's thesis: functional equation of Hecke L-functions, CM-type infinity type | **High** for CM-field work. Excludes infinity type 0 (finite-order characters), so it says nothing about Dedekind ζ or Artin L of finite order |
| `GlobalTheory.T.hecke_L_function_euler_product` | `Proofs/GlobalProofs/HeckeLFunctionEulerProductStatement.lean:17` | For a unitary Hecke character χ over a number field and Re s>1, the Euler product of local factors converges (`HasProd`) to `(toHecke χ).LFunction s` | Mathlib + HChar/HeckeCharacter | Euler product of Hecke L-functions | Med-high |
| `GlobalTheory.T.hecke_gauss_sum_local_term` | `Proofs/GlobalProofs/HeckeGaussSumLocalTermStatement.lean:17` | The local finite test-function sum at a ramified place with conductor exponent m equals the local Gauss sum of χ | Internal (HChar, `gaussSumAt`) | Local Gauss sums / Tate local ε-factor | Med |
| `exists_degOne_prime_in_rayClass` | `Proofs/BlockDecomposition/ExistsLargePrimeInRayClass.lean:145` | Number field F, modulus 𝔣 ≠ 0, ideal 𝔞 coprime to 𝔣, finite set W of nonzero integers, bound B: there is a prime 𝔠 with prime absolute norm > B, coprime to 𝔣, in the **narrow** ray class of 𝔞 mod 𝔣, avoiding every element of W | Mathlib + two transparent defs (`RayRel`: 𝔞𝔠⁻¹ generated by totally positive a ≡ b ≡ 1 mod 𝔣; `CoprimeTo`) | Infinitely many degree-one primes in every narrow ray class (qualitative Dirichlet/Chebotarev for ray classes) | **High** |
| `exists_degOne_isFrob` | `Proofs/BlockDecomposition/ExistsLargePrimeInRayClass.lean:140` | For L/F finite Galois number fields, g ∈ Gal(L/F), and finite S: some place v ∉ S of F has inertia degree 1 over ℚ and Frobenius g | Mathlib + `GlobalTheory.NT.IsFrob` (not opened) | Qualitative Chebotarev for degree-one primes (wraps `chebotarevDegreeOne'` from AbelianVarietyTheory, which is proved via cyclotomic crossing fields) | **High** (directly usable for artin-grh-style sieve inputs, but with no density) |
| `GlobalTheory.T.exists_prime_degree_one_avoiding` | `Proofs/GlobalProofs/ExistsPrimeDegreeOneAvoidingStatement.lean:12` | Same as the ray-class result without the class condition: prime of prime norm > B, coprime to 𝔣, avoiding W | Mathlib | Infinitely many degree-one primes | High |
| `GlobalTheory.T.sum_prime_log_div_le` | `Proofs/DivisibilityProofs/SumPrimeLogDivLeStatement.lean:9` | For x ≥ 1, Σ_{p≤x} log p / p ≤ log x + log 4 | Mathlib | Mertens' first theorem (explicit upper bound) | **High** for explicit analytic NT |
| `GlobalTheory.T.sum_log_div_n_sq_le_two` | `Proofs/DivisibilityProofs/SumLogDivNSqLeTwoStatement.lean:9` | For any finite S ⊆ {n ≥ 2}, Σ log n / (n(n−1)) ≤ 2 | Mathlib | elementary | Med |
| `GlobalTheory.T.rat_product_formula` | `Proofs/AdelicProofs/RatProductFormulaStatement.lean:12` | For r ∈ ℚ^×: log\|r\|_p ≠ 0 for only finitely many p, and log\|r\|_∞ + Σ_p log\|r\|_p = 0 (norms in ℂ and ℂ_p) | Mathlib | Product formula over ℚ | Med |
| `GlobalTheory.T.discriminant_valuation_different` | `Proofs/GeometryProofs/DiscriminantValuationDifferentStatement.lean:10` | E/ℚ Galois, P \| p: v_p(disc E)·e(P) = v_P(different)·[E:ℚ] | Mathlib | Discriminant = norm of the different (local form) | High |
| `GlobalTheory.T.ramified_prime_contains_discriminant` | `Proofs/GlobalProofs/RamifiedPrimeContainsDiscriminantStatement.lean:10` | F ⊆ E number fields, E/F unramified outside a finite S: every prime of E dividing the absolute different contains \|disc F\|·∏_{v∈S} N(v) | Mathlib | Ramification is controlled by disc(F) and S | Med-high |
| `GlobalTheory.T.different_dvd_ramified_prime_power` | `Proofs/GlobalProofs/DifferentDvdRamifiedPrimePowerStatement.lean:10` | If t lies in every prime dividing the different of E, then the different divides (t^{[E:ℚ]}) | Mathlib | Bound on the different | Med |
| `GlobalTheory.T.gauss_sum_valuation_teichmuller` | `Proofs/AlgebraProofs/GaussSumValuationTeichmullerStatement.lean:11` | For F = 𝔽_{p^f} (≠ 𝔽_2), σ a multiplicative character to the valuation ring that is additive mod p (a Teichmüller lift), ψ ≠ 1 additive: v(Σ σ⁻¹(a)ψ(a))^{p−1} = v(p), so the Gauss sum has valuation 1/(p−1) | Mathlib | Stickelberger, digit-sum-one case | Med-high |
| `GlobalTheory.T.teichmuller_character_exists` | `Proofs/AlgebraProofs/TeichmullerCharacterExistsStatement.lean:11` | Over the valuation ring of an algebraically closed C with v(p)<1, the finite field 𝔽_{p^f} has a multiplicative character that is additive mod p | Mathlib | Teichmüller character | Med |
| `GlobalTheory.T.gauss_sum_quadratic_character_bound` | `Proofs/BlockDecomposition/GaussSumQuadraticCharacterBoundStatement.lean:29` | X a 2nd-countable LCA group with Haar m, L ≤ X compact open, q a unitary "quadratic character" (q(x+y)=q(x)q(y)B(x,y), B bimultiplicative): \|∫_{x₀+L} q\|² ≤ m(L)·m(radical of B on L) | Mathlib | Weil-index / quadratic Gauss sum bound | Med |
| `GlobalTheory.T.abelian_frobenius_lift` | `Proofs/DivisibilityProofs/AbelianFrobeniusLiftStatement.lean:18` | E/ℚ abelian Galois, p prime: there is φ ∈ Gal(E/ℚ) with τ(φx) ≡ τ(x)^p mod n for every prime n ∋ p of any ring receiving 𝓞_E | Mathlib | Existence of Frobenius at p in an abelian extension (even ramified, as a lift) | Med |
| `GlobalTheory.T.artin_map_abelian_unique` | `Proofs/BlockDecomposition/ArtinMapAbelianUniqueStatement.lean:14` | K totally complex: two global Artin maps (continuous, surjective, kernel = identity component, Frobenius at unramified places, ...) agree on every finite abelian L/K | Mathlib + `IsGlobalArtinMap` (in `src/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:114`, looks faithful) | Uniqueness of the global Artin map | Med (needs existence, which lives in GroundTheory) |
| `GlobalTheory.T.lubin_tate_unramified_degree_one` | `Proofs/BlockDecomposition/LubinTateUnramifiedDegreeOneStatement.lean:26` | For a nonarchimedean local field F, Lubin–Tate series f, unit u, and τ with unramified degree 1 acting on Lubin–Tate torsion by [u]: the local Artin map of u⁻¹ agrees with τ on F^{ab} | Mathlib + GroundTheory `localArtinMap`, `lubinTateTorsion` | Explicit local reciprocity (Lubin–Tate) | Med (local CFT itself is elsewhere) |
| `GlobalTheory.T.local_global_artin_compatible` | `Proofs/BlockDecomposition/LocalGlobalArtinCompatibleStatement.lean:26` | The local Artin map at w and the global one applied to the idele concentrated at w agree on finite abelian L/E | Mathlib + GroundTheory CFT defs | Local–global compatibility of CFT | Med |
| `GlobalTheory.T.exists_shintani_cone_domain` / `GlobalTheory.T.partial_zeta_ray_class_summable` | `Proofs/GlobalProofs/ExistsShintaniConeDomainStatement.lean:12`, `Proofs/GlobalProofs/PartialZetaRayClassSummableStatement.lean:12` | Totally real F: Shintani cone decomposition for the units mod 𝔣 exists (`IsConeDomain`, internal); ray-class partial zeta series converge for Re s>1 | Mathlib (+ `IsConeDomain`) | Shintani cone decomposition | Med |
| `GlobalTheory.T.analytic_continuation_from_strips` | `Proofs/GlobalProofs/RealDifferenceConeBoundStatement.lean:13` | If G_k is holomorphic on Re s > −k and G_k = S on Re s > 1 for all k, they glue to an entire T | Mathlib | identity-theorem gluing | Med (small, handy) |
| `GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive` | `Proofs/GlobalProofs/FiniteDimensionalOfCompactCoerciveStatement.lean:10` | On a complex Hilbert space, a subspace on which a compact operator A is coercive (Re⟨u,Au⟩ ≥ c‖u‖², c>0) is finite-dimensional | Mathlib | Riesz-type finiteness | Med |
| `GlobalTheory.T.harmonic_annulus_maximum_principle` | `Proofs/MetricProofs/HarmonicAnnulusMaximumPrincipleStatement.lean:12` | Harmonic h on an open annulus, continuous on the closed one, ≤ 0 on both boundary circles ⇒ h ≤ 0 on it | Mathlib | Maximum principle | Med |
| `GlobalTheory.T.implicit_root_analytic` | `Proofs/GeometryProofs/ImplicitRootAnalyticStatement.lean:9` | A simple root τ₀ of Σ c_j(w₀)τ^j with analytic coefficients continues to an analytic root function near w₀, and it is the only root nearby | Mathlib | Analytic implicit function theorem for polynomial roots | Med |
| `GlobalTheory.T.matrix_coefficient_orthogonality_relation`, `GlobalTheory.T.formal_degree_schur_lower_bound` | `Proofs/BlockDecomposition/MatrixCoefficientOrthogonalityRelationStatement.lean:12`, `.../FormalDegreeSchurOrthogonalityStatement.lean:12` | Unitary reps of a unimodular lc 2nd-countable group: the operator built from an integrable matrix coefficient is self-adjoint; with formal degree d, the Schur orthogonality lower bound ‖⟨z,iw₀⟩‖²/d ≤ Re⟨z, coefOp z⟩ | Mathlib + repo `IsU`, `IsFd`, `coefOp` (not opened) | Schur orthogonality for square-integrable reps | Low-med |
| `GlobalTheory.T.mirabolic_double_coset_decomposition` | `Proofs/BlockDecomposition/MirabolicDoubleCosetDecompositionStatement.lean:12` | Double-coset decomposition of a GL over a p-adic field relative to a parabolic and the mirabolic | Internal (`HPG`, `Mir`, `Cl`) | Bernstein–Zelevinsky geometry | Low |
| `GlobalTheory.T.siegel_weil_convergent_range` / `GlobalTheory.T.archimedean_siegel_weil_integral_identity` | `Proofs/BlockDecomposition/SiegelWeilConvergentRangeStatement.lean:16`, `.../ArchimedeanSiegelWeilIntegralIdentityStatement.lean:19` | For a nondegenerate hermitian M×M form over a CM extension E/F and 2n < M: the Siegel–Weil integral of a Schwartz–Bruhat function is absolutely integrable (adelic, and archimedean) | Mostly Mathlib + repo measures `SdW`, `SdHerm` | Weil's convergence range for Siegel–Weil (unitary groups) | Low-med |
| `GlobalTheory.T.chowla_selberg_period` | `Proofs/GeometryProofs/ChowlaSelbergPeriodStatement.lean:14` | For the Kronecker character χ of −d: some CM elliptic curve (`Curve0 H ρ`) has a "period" x with x = γ + log(2π/√d) − L'(1,χ)/L(1,χ) | Internal (`Curve0`, `Ell`, `HasPeriod`: not checked) | Chowla–Selberg formula (log form) | Low (the analytic side is Mathlib's `χ.LFunction`, but the geometric side is internal) |
| `flatDegree` (proves `FlatDegree`) | `Proofs/GeometryProofs/FlatDegreeHolds.lean:64` | On a unitary Shimura variety of signature (p,q) over CM E, a flat metrized line bundle has adelic degree ((p−q)/2)·Re logΩ(E,χ) + q(2 log √d − log rd(E)), where logΩ = γ + log(π/·) − L'(1,χ)/L(1,χ) | Internal (Host, Datum, FamilyUnif, LogNorms) | Colmez/Chowla–Selberg-type degree formula | Low outside this project |
| `GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme_holds` | `Proofs/AlgebraProofs/FreeQuotientSchemeHolds.lean:21` | S a scheme, G finite locally free group scheme over S acting freely on X, every orbit in an affine open ⇒ an fppf quotient X → Y exists and is a G-torsor | Mathlib (`Over S`, `GrpObj`, `ModObj`, fppf topology) + transparent defs in `PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean` | SGA3 V / Mumford: quotient by a free finite flat group action | Med-high for algebraic geometry, low for this workspace |
| `GlobalTheory.CompanionTheory.Ar.Flat.gagaSections` | `Proofs/GlobalProofs/GagaSections.lean:109` | X smooth proper over ℂ, L a line bundle: a compatible family of holomorphic local trivialisation values comes from an algebraic global section | Mathlib schemes + internal `LB` (cocycle line bundle) | GAGA for sections of line bundles | Low-med |
| `GlobalTheory.CompanionTheory.Relay.hodge_tate_of_fargues_exact` | `Proofs/AlgebraProofs/HodgeTateOfFarguesExact.lean:93` | Fargues's exactness ⇒ the Hodge–Tate map's cokernel is killed by any κ with v(κ)^{p−1} ≤ v(p) (v(κ) ≤ v(4) if p = 2) | Internal `PDivGroup` (opened, looks faithful) | Fargues, "La filtration de Harder–Narasimhan..." (Hodge–Tate cokernel) | Low-med. `FarguesExact` itself is proved in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/PrismaticDieudonne/PrismaticDieudonneHodge.lean:31` |
| `GlobalTheory.T.flat_of_flat_special_fibre` | `Proofs/GeometryProofs/FlatOfFlatSpecialFibreStatement.lean:11` | R noetherian local, P, Q finite R-algebras, Q flat: a map P → Q that is flat on special fibres is flat | Mathlib | Local flatness criterion (fibrewise) | Med (algebra) |
| `GlobalTheory.T.finitePresentation_of_faithfully_flat` | `Proofs/AlgebraProofs/FinitePresentationOfFaithfullyFlatStatement.lean:9` | C → D finite projective faithfully flat and D finitely presented over R ⇒ C finitely presented over R | Mathlib | descent of finite presentation | Med (algebra) |
| `GlobalTheory.T.henselian_quasi_finite_finite_part` | `Proofs/GeometryProofs/HenselianQuasiFiniteFinitePartStatement.lean:10` | Separated quasi-finite finite-type X over a henselian local ring: some open containing the closed fibre is finite over the base | Mathlib | Henselian structure theorem for quasi-finite morphisms (EGA IV 18.5.11) | Med (algebra) |
| `GlobalTheory.T.integral_closure_finite` | `Proofs/GeometryProofs/IntegralClosureFiniteStatement.lean:14` | For a domain essentially of finite type over ℤ, the integral closure in a finite extension of its fraction field is finite | Mathlib | Japanese/Nagata property of ℤ-algebras | Med (algebra) |
| `GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ` | `Proofs/BlockDecomposition/KrullDimQuotientEqTrdegSuccStatement.lean:11` | For a finite-type ℤ-algebra chart and a point with char-0 residue field: dim(B/q) = trdeg + 1 | Mathlib | dimension formula over ℤ | Med (algebra) |
| `GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective` | `Proofs/GeometryProofs/GeometricallyConnectedOfCommGroupNsmulSurjectiveStatement.lean:17` | A finite-type quasi-compact commutative group scheme on which every multiplication by n ≠ 0 is surjective is geometrically connected | Mathlib | (divisible ⇒ connected) | Low-med |
| `GlobalTheory.T.ultrametric_det_norm_le` | `Proofs/AlgebraProofs/UltrametricDetNormLeStatement.lean:13` | Ultrametric normed field, entries ≤ r ⇒ ‖det M‖ ≤ r^n | Mathlib | ultrametric Hadamard | Med (small) |
| `DiscreteGroups.…localConverseGL` (proves `GlobalTheory.Published.LocalConverseGL`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/LocalConverseGL.lean`) | `DiscreteGroups/GlobalIrreducibility/LConvFinal.lean:22` | k a char-0 nonarchimedean local field, ψ nontrivial: two irreducible smooth **cuspidal** reps of GL_{m+1}(k) (m>0) with the same twisted ε-factor for every irreducible τ of GL_m(k) are isomorphic | Mathlib `Representation`, plus repo `IrrRep`, `IsCuspidal` (faithful: no nonzero vectors fixed by any proper standard unipotent radical), `HasPairEps` (non-standard, see §4) | Local converse theorem (n×(n−1) form; Henniart 1993, Chen 2006) | Med. Major result, but the ε-factor hypothesis is phrased unusually |
| `schur`, `burnside`, `trace_unique` | `DiscreteGroups/PiInvariants/CompactSupportTwists/TraceUnique.lean:22,42,97` | Schur's lemma (commuting endomorphism of an irreducible ℂ-module is scalar), Burnside (irreducible ⇒ φ onto End), any trace-like functional on End(V) is c·trace | Mathlib | Schur, Burnside | Low (mostly in Mathlib already) |

## 4. Internal definitions worth knowing

| Definition | Where | Verdict |
|---|---|---|
| `Formalism…HChar L` (= `hcharSub`): continuous homomorphisms of the ideles to ℂ^× trivial on L^×; `IsUnitary`, `HasInf φ n` (infinity type w.r.t. a CM type) | `src/Formalism/LocalToGlobal/UnitaryNorms/IsUnitaryNormOf.lean:15–96` | **Faithful** (standard Hecke characters) |
| `IsCompletedL χ n Λ`: Λ entire and Λ(s) = ∏_i 2(2π)^{−(s+\|n_i\|/2)}Γ(s+\|n_i\|/2) × (Euler product) for Re s>1 | `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CompletedLStripBounds.lean:19` | **Faithful**. Entire because n ≠ 0 is assumed |
| `IsPartialZeta C Z`: Z holomorphic off {1} and = Σ_{J ∈ C} N(J)^{−s} for Re s>1; `dF F = \|disc F\|` | `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean:22,99` | **Faithful** |
| `RayRel F 𝔣 I J`: aI = bJ with a, b totally positive and ≡ 1 mod 𝔣 (narrow ray class); `CoprimeTo` | `src/Formalism/SharpRestriction/GlobalSchurBounds/ShortIntervalPrimes.lean:25,27` | **Faithful** |
| `IsGlobalArtinMap` | `src/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:114` | Looks faithful: continuity, surjectivity, kernel = connected component, Frobenius at unramified places, local unit behaviour |
| `PDivGroup p O`: tower of finite projective cocommutative Hopf O-algebras of rank p^{nh}, surjective restrictions whose kernels are the p^n-torsion ideals | `src/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean:16` | **Faithful in substance** (affine p-divisible group). Tate module, dual and Hodge–Tate map are defined on top of it; I did not audit those |
| `FinalTheorems.Blowup`, `EffCartier`, `Snc`, `Rsp` | `src/ReciprocityTheory/AnalyticForms/RegularLocalRings/FinalTheorems.lean:11–26` | **Faithful**: blow-up by its universal property; SNC via a regular system of parameters at every point (so it also forces the ambient space to be regular) |
| `IsBlowupSeq` (iterated blow-ups along **arbitrary** ideal sheaves) | `PublishedTheorems/Geometry₂/ConclusionOfSmooth.lean:437` | Faithful to "resolution by a sequence of blow-ups", but the centres are unrestricted (so this is closer to "projective birational" than to Hironaka's smooth centres) |
| `IrrRep G`: smooth irreducible complex representation (algebraic irreducibility) | `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NontrivialOfIrreducible.lean:167` | Faithful |
| `IsCuspidal ρ`: no nonzero vector fixed by any proper standard unipotent radical | `src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean` | Equivalent to the usual definition only together with smoothness (vanishing Jacquet modules ⇔ no invariants for smooth reps over compact-open exhaustion). Not verified |
| `HasPairEps ψ π τ e` | `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/HasExponentZeroIff.lean:82` | **Non-standard.** It quantifies over every linear functional I on *all* functions GL_m(k) → ℂ that is right-invariant on test functions, and over every Whittaker functional pair. The usual gamma factor uses the Rankin–Selberg zeta integrals of Whittaker functions. This may make the hypothesis stronger than Henniart's, and so the theorem weaker. Faithfulness not established |
| `Host`, `Datum`, `Level`, `Moduli`, `Model`, `HodgeCpt`, `RootTower`, `GoodOrigin`, `HermLine`, `IntersectionSystem` | `Definitions/GlobalGeometry`, `Definitions/DivisibilityTowers`, `src/ReciprocityTheory/.../ArithmeticHilbertSamuelLowerBound.lean:90` | Internal Shimura-variety and Arakelov data. `IntersectionSystem` is **just a function** (ideal, list of hermitian lines) → ℝ. Theorems quantify over every `II` with `IsFullIntersectionSystem II` (an axiomatic interface: multilinearity, projection formula, contraction), and existence is the separate Prop `ArithIntersectionSystemStatement`. Not degenerate, but abstract |
| `Top.Given`, `PB.Inputs` | `Definitions/DivisibilityTowers/GoodOrigin.lean`, `Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean:172` | **Hypothesis bundles**: conjunctions of about 15–25 named literature statements (GAGA, Fargues, resolution, Hilbert–Samuel, convergence results ...). Many headline theorems here have the form `Given → ...` or `Inputs → ...`. I did not find a theorem of type `Given` or `PB.Inputs` (§7) |

## 5. Mechanical families

- `Proofs/**/*Statement.lean` re-export wrappers: 5,674 files, each `theorem _root_.GlobalTheory.T.<name> : … := by exact <proved lemma>`.
  They are a usable index of the subtree: one public name per result.
- BlockDecomposition GL_n local representation theory (Jacquet, Levi, Parabolic, Unipotent, Mirabolic, Hermitian, Lattice
  in the file names): ≈4,000 files of matrix-block, coset and integration lemmas for p-adic GL_n and unitary groups.
- GeometryProofs Hodge/Lattice/Chart/Frame/Lie files: ≈2,500 files about `HodgeCpt`, Hodge–Tate lattices and charts of
  the Shimura models (`IsLatFamilyCongr`, `ExistsLieModel`, ...). All internal.
- MetricProofs Flag/Chart/Frame/Resolution/Snc files: ≈1,300 files on flag-variety metrics, local potentials and
  chart integrals for heights.
- AlgebraProofs Hopf/Order/Lattice/Dual files: ≈600 files on Hopf orders, Raynaud-style finite flat group schemes and
  `PolarisedAF` lattice computations.
- DivisibilityProofs Tower/Height/Intersection files: ≈300 files on volumes of root towers.
- `DiscreteGroups/GlobalIrreducibility/LConv*` (≈50 files): the steps of the local converse proof (cuspidal
  generation, Kirillov bumps, big cell, separation, uniformisation, gluing). `Dz*` (≈30 files): depth-zero/tame type
  bookkeeping for the same proof.
- `DiscreteGroups/PiInvariants` (36 files): θ-fixed cusp forms, Casimir eigenvalues, compact-support twists. Internal.

## 6. Standalone value: which published theorems are claimed, and their status

**Proved unconditionally** (a theorem of exactly this type exists somewhere in `src/`):

| Statement | Defined at | What it claims | Proved at |
|---|---|---|---|
| `FreeQuotientScheme` | `PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean:168` | fppf quotient by a free finite locally free group action (orbits in affines), any base scheme S | `Proofs/AlgebraProofs/FreeQuotientSchemeHolds.lean:21` (this subtree) |
| `FarguesExact` | `PublishedTheorems/Algebra₂/FarguesExact.lean:15` | Hodge–Tate sequence of a p-divisible group over O_C is exact (kernel of HT = annihilator of the dlog image under the Weil pairing) | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/PrismaticDieudonne/PrismaticDieudonneHodge.lean:31` |
| `FarguesHodgeTate` | `PublishedTheorems/Algebra₂/FarguesHodgeTate.lean:40` | the above, plus the cokernel of HT is killed by p^{1/(p−1)} (4 if p = 2) | from `FarguesExact` in `Proofs/AlgebraProofs/HodgeTateOfFarguesExact.lean:93` |
| `HodgeTateCokerSharp` | `Statements/GeometryStatements/HodgeTateCokerSharp.lean` | the cokernel bound alone | `Proofs/GeometryProofs/HodgeTateCokernelSharp.lean:11` |
| `ResolutionCharZero` | `PublishedTheorems/Geometry₂/ConclusionOfSmooth.lean:467` | **Hironaka in char 0**: a reduced, separated, finite-type X over k ⊇ ℚ has a blow-up sequence X' → X that is smooth, an iso over the smooth locus, with the exceptional preimage SNC. A projective corollary is proved in the same file (`ResolutionCharZero.projective`, line 474) | `src/Development/WeilBound/CoreStatements/ResolutionCharZero/ResolutionCharZero.lean:10` (via `FunctionalResolution.functorialResolutionCharZero`) |
| `PrincipalisationCharZero` | `PublishedTheorems/Geometry₂/NotSubsetOfDenseCompl.lean:581` | principalisation of an ideal on smooth X in char 0 by SNC blow-ups | `src/Development/WeilBound/CoreStatements/ResolutionCharZero/PrincipalisationCharZeroClosed.lean:11` |
| `GagaSections` | `PublishedTheorems/Geometry₂/GagaSections.lean:501` | GAGA for line-bundle sections on smooth proper X/ℂ | `Proofs/GlobalProofs/GagaSections.lean:109` |
| `NefRR` | `PublishedTheorems/Geometry₂/NefRR.lean:523` | asymptotic Riemann–Roch: D!·h⁰(τa)/τ^D → degree, for nef a on a multiprojective variety given by coordinates y | `src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/NefDivisors/NefRR.lean:18`. The dimension-0 case is in this subtree (`PublishedTheorems/Geometry₂/ProjLineLimit.lean:686`) |
| `PoincareLelong`, `PoincareLelongInv` | `PublishedTheorems/Metrics₂/*.lean` | arithmetic Poincaré–Lelong formula (internal `ptsIntegral`, `HermLine`) | `src/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/PoincareLelong/PoincareLelongInv.lean:17,23` |
| `QuotientByFiniteFlatStatement` | `PublishedTheorems/Algebra₂/QuotientByFiniteFlatStatement.lean:78` | an abelian scheme with ample L, modulo a finite flat subgroup, is an abelian scheme with ample L' | `src/Development/WeilBound/CoreStatements/HodgeTatePoints/AhSlim.lean:310` |
| `HeckeTateFunctionalEquation`, `PartialZetaFunctionalEquation` | AbelianVarietyTheory (see §3) | see §3 | this subtree, `GlobalProofs/…` (§3) |
| `LocalConverseGL` | AbelianVarietyTheory | see §3 | `DiscreteGroups/GlobalIrreducibility/LConvFinal.lean:22` |
| `CurveSemiAbelianConjecture`, `RootLineDeRhamModel` | `Statements/GeometryStatements/CurveSemiAbelianConjecture.lean`, `...SeparableFormGroupElementFixesUniquePositiveLine.lean` | a positivity of slopes (`lmuNum ≥ 0`) for Lie lattices of semi-abelian families over curves in char p > 2. Despite "Conjecture" in the name, it is an internal lemma, not a known open conjecture | `Proofs/GeometryProofs/M2CurveEstablished.lean:64`, `M2ModelEstablished.lean:17` |
| Also proved: `ChartSequence`, `FlagStatement`, `PolarisedAFStatement`, `HodgeTateDatumStatement`, `OrdinaryCurveStatement`, `RelationsStatement`, `HTChartExists`, `LemmaBT`, `LevelCoverSt`, `TwistAut`, `HodgeComparisonCompatibility`, `FlagModelStatement`, `PropZ`, `PropFTop`, `KeyBadSt`, `FinConst`, `FinConstAll`, `FlatDegree`, `AgreementPos`, `Coefficients`, `Antisymmetry`, `Proportional`, `NefPol`, `FlagHeight`, `HS`, `An` | `Statements/**` | internal Shimura/Arakelov statements | `Proofs/**/…Holds.lean` and friends (see the `GlobalTheory.T.*` wrappers) |

**Proved only conditionally, as implications:**
- `ZarhinStatement` (Zarhin's trick: A ↪ principally polarised P with a retraction): proved from `DualAbelianScheme` and
  `CubeTheorem` (`src/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/ZarhinStatementOfDualCubeQiR.lean:72`).
  I did not check whether those two are proved.
- `SymmetricBundleSt` from `DualAbelianScheme` + `CubeTheorem` (`Proofs/AlgebraProofs/RelAmpleOfCls.lean:262`).
- `PointHT`, `TrivFlagOnHodge` from `FarguesHodgeTate` (so unconditional in effect, since that one is proved).
- `FlatLineGenerator`, `FlatLineGeneratorComponent` from `ResKStatement` + `GagaSections` (both proved, so
  unconditional in effect).
- `ThmFlatA` from `PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst`.
- `CmpPair` from `PB.Inputs → CmpSt → HodgeComparisonCompatibility → ThetaUnifAV`. `CmpSt` from `CxSt` or from
  `Inputs → AvoidStatement → …`.
- `HodgeLatticeFlagBound` from `FamilyExistsPos`.
- `FlagModelExists`, `BaseMetricExists` from `Top.Given`.
- `VolumeTheoremX` from `Top.Given`, `PtsIntegrableStatement`, `WeilSt`, `NineGeoU`, ... (10 hypotheses).
- `SubquotientStatement` from `QuotientByFiniteFlat` + `Zarhin` + ....
- `RootFlatOnHodge` from `FlatDegree` + `Given` (WeilBound).

**Stated only, with no proof found:** `PrismaticDieudonneIntegers` (`PublishedTheorems/Divisibility₂/PrismaticFilteredAtOfIntegersAt.lean:353`:
a prismatic Dieudonné functor over O_C with the expected properties); `CptFlatInputs`; `GoodTowerExistsX`. My search
was for an exactly matching type, so a proof under another name or form may exist.

**Misleading names:**
- `AutomorphicSpectrum`, `BlockDecomposition`, `DiscreteGroups` describe nothing in particular. There is no spectral
  decomposition of L²(Γ\G) here.
- `CurveSemiAbelianConjecture` is not a conjecture.
- `PrismaticFilteredAtOfIntegersAt.lean` contains `exists_padic_of_eigen` (Frobenius eigenvectors in A_inf), not a filtration result.
- `IsPermissibleOfCentre.lean` (Jets₂) contains only the definition `lieOf`.
- `RealDifferenceConeBoundStatement.lean` holds `analytic_continuation_from_strips`.
- The `PublishedTheorems/` folder mostly holds `def … : Prop` statements, not theorems.

**Effectively proved here in usable (Mathlib-facing) form:** Hecke's continuation and functional equation for
partial zeta functions of totally real fields; the functional equation for unitary Hecke L-functions over CM fields
with nonzero infinity type; infinitely many degree-one primes in every narrow ray class and with prescribed
Frobenius; Mertens' Σ log p/p ≤ log x + log 4; discriminant/different relations; Stickelberger for the Teichmüller
character (digit sum 1); a handful of commutative-algebra results (local flatness criterion, henselian quasi-finite,
Nagata finiteness over ℤ). **Special cases only:** Hecke's FE (totally real fields only, or CM fields only with
infinity type ≠ 0; finite-order characters of non-totally-real fields are not covered); Chebotarev (qualitative, no density).

## 7. Open questions / not verified

- Nothing was built. The "no sorry/axiom" claim is from `rg` over these two subtrees only. Proofs that delegate to
  other subtrees inherit their status.
- I did not find a theorem of type `Top.Given` or `PB.Inputs` (exact-type search). If none exists, every result of the
  form `Given → …` (VolumeTheoremX, FlagModelExists, BaseMetricExists, RootFlatOnHodge) is conditional. The final RH
  chain may discharge them under another name. Not traced.
- `HasPairEps` (local converse hypothesis): not compared with the standard gamma-factor definition. It could be
  stronger than Henniart's/Chen's hypothesis, or only rarely satisfiable.
- `GlobalTheory.NT.IsFrob`, `IsConeDomain`, `Curve0.HasPeriod`, `LB` (line bundles), `IsU`/`IsFd`/`coefOp`: not opened.
- I did not check whether the `HChar` (Formalism) to `HeckeCharacter` (GroundTheory) bridge `toHecke`
  (`Proofs/GlobalProofs/ContinuousIdeleCircle.lean:29`) identifies the two L-functions on the nose. The Euler-product
  theorem suggests it does.
- `ResolutionCharZero`, `FarguesExact` and `NefRR` are proved outside this subtree. Their proofs belong to other inventories.
- My heuristic flagged 558 signatures as Mathlib-only and 992 with one repo identifier. I read about 60 in full, so
  some reusable results among the remaining ≈1,500 are certainly not listed. To find them, sweep the output of
  `rg -n "^theorem _root_\.GlobalTheory\.T\." Proofs/` and filter it against Mathlib's declaration names.
