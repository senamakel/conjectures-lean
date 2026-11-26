# riemann-hypothesis inventory 08: ReciprocityTheory, CompanionTheory, PositivityTheory, Lemmata, Supplements

Repo: [riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) at commit `507a75d91d`. All paths below are relative to
`src/`. Line numbers point at the declaration line. Statements are paraphrased (the repo has no licence; no code
is copied). Nothing was built: every "proved" below means "a `theorem` with this type exists and its body is
not `sorry`", not "checked by Lean on this box".

## 1. Scope and method

| Subtree | Files | Lines | Coverage |
|---|---|---|---|
| `ReciprocityTheory` | 3,580 | 524k | ClassFieldTheory, NeutralLocalFields, L2DbarEstimates, CommutativeAlgebra, GeometryOfNumbers, SemistableReduction, GroupCohomology and the small dirs (Chebotarev, ReducedBases, Theta*, AdeleApproximation, AdicCompleteness, Burnside, EigenFrames, GaloisValuations, Hypotheses) read at the level of all top-level statements plus the key definitions. AnalyticForms: Osgood, NullZero and PlurisubharmonicFunctions read; RegularLocalRings, PotentialTheory and LeviForms sampled. DualLattices: statement files sampled. ReductiveGroups (2,660 files): every `def …Statement : Prop` name listed (280), about 30 opened, and the UnramifiedIntegrals (CM/modular forms) directory read in full at statement level. DiscreteSeries, FundamentalDomains, HeightTheory, PullbackSections, TaylorDiscriminants and ExtensionDescent were characterised by directory and statement names only. |
| `CompanionTheory` | 1,946 | 193k | All `theorem X : XStatement` headlines listed. SpectralGeometry/LocalGlobalProofs has 613 `*Statement.lean` files; about 20 were read in full. PadicCyclotomicFields (local Tate duality) was read. RealGroups and HarishChandraModules were sampled. |
| `PositivityTheory` | 355 | 44k | Headline theorems listed; HilbertEisenstein headline and its definition read; the rest sampled. |
| `Lemmata` | 158 | 9.4k | Every theorem statement extracted (229 declarations) and read. |
| `Supplements` | 1 | 19 | Read in full. |

Searches used: `rg` for `^theorem`, for `theorem X : XStatement` (the repo's headline convention), for
`sorry|axiom|opaque|native_decide`, and for Mathlib vocabulary (`riemannZeta`, `LFunction`, `LSeries`,
`dedekindZeta`, `ModularForm`, `WeierstrassCurve`, `ClassGroup`, `ZMod`, `PadicAlgCl`, `AdeleRing`, …).
In all five subtrees there are **0** files containing `sorry`, `axiom`, `opaque` or `native_decide`.

## 2. What this subtree actually is

The names are mostly misleading. Four groups of real, mostly general mathematics sit inside it:

1. **Local class field theory, proved.** `ReciprocityTheory/ClassFieldTheory/LocalClassField` (88 files) proves
   local Artin reciprocity and the existence theorem for every finite extension of ℚ_p inside `PadicAlgCl p`,
   using Galois cohomology (Brauer group ≅ ℚ/ℤ, Herbrand quotients, Kummer theory, norm limitation). It then
   transports the result to every characteristic-zero `IsNonarchimedeanLocalField`. The statement is about
   Mathlib objects (`Field.absoluteGaloisGroupAbelianization`, `Algebra.norm`). **Global** class field theory
   is not proved in this subtree: `ClassFieldTheory/GlobalClassField` has only 4 helper files.
   `NeutralLocalFields/Reciprocity.lean` *defines* `IsGlobalArtinMap` and `HilbertClassField.Statement`; the
   global proofs live in `GroundTheory/GlobalFields/GlobalReciprocity` (outside this pass).
2. **Several complex variables, proved.** `L2DbarEstimates` contains Hörmander's L² estimate for ∂̄ on Stein
   Riemann domains over ℂⁿ, Skoda division, a twisted (Berndtsson/Donnelly–Fefferman-type) estimate and the
   L² Riemann extension theorem. AnalyticForms contains multivariable Osgood (holomorphic ⇒ analytic),
   pluripotential theory (psh ⇔ Levi ≥ 0, sub-mean value, psh extension across divisors), mixed
   discriminants and a Stokes formula. In the RH proof these feed Arakelov geometry: arithmetic ampleness,
   Hilbert–Samuel and small sections.
3. **Commutative algebra, CM theory and modular forms.** `CommutativeAlgebra` proves that regular local rings
   are domains and Cohen–Macaulay, that CM rings localise and are unmixed, and that height plus dimension
   equals N in polynomial rings. `ReductiveGroups/UnramifiedIntegrals` (despite its name) proves the
   **integrality of singular moduli**: j(τ) is an algebraic integer when τ is fixed by a primitive integer
   matrix of non-square determinant, and the j-invariant of a lattice with CM by the maximal order of
   ℚ(√−d), d ≡ 3 (mod 4) squarefree, is integral. It also has the q-expansion principle for level-1 forms
   and Néron–Ogg–Shafarevich-type statements for torsion points. All of this is stated with Mathlib's
   `ModularForm`, `E₄`, `discriminant` and `PeriodPair`.
4. **Adelic harmonic analysis and algebraic groups.** `CompanionTheory/SpectralGeometry/LocalGlobalProofs`
   (1,233 files, 613 named statement/proof pairs) covers Poisson summation for Gaussians with complex
   symmetric matrices, the adeles of a number field being discrete-cocompact, self-dual measures, Fourier
   inversion for Schwartz–Bruhat functions, theta modularity, Siegel–Weil measures, Witt's theorem for
   hermitian forms, Cartan and Iwasawa decompositions, a point count for quadrics over 𝔽_q and finiteness
   of cusps. `CompanionTheory/AutomorphicTheory/PadicCyclotomicFields` proves **local Tate duality,
   finiteness and the Euler characteristic formula** for ℤ/ℓ^r-modules over finite extensions of ℚ_ℓ, using
   GroundTheory's profinite cohomology.

The rest is the RH-specific machinery: unitary representation theory of U(p,q) and G₂ (discrete series,
Bessel models, Capelli identities, Zuckerman functors, about 2,000 files across `ReductiveGroups/DiscreteSeries`,
`CompanionTheory/{RealGroups,HarishChandraModules,AutomorphicTheory}`), Arakelov intersection theory on
multiprojective varieties (`ReductiveGroups/ArithmeticGeometry`, about 1,500 files) and p-adic Hodge–Tate and
Hopf-order length computations for CM abelian varieties (`DualLattices`). These are faithful, but they are
built on repo-internal structures (`IsURepOn`, `KType`, `HermLine`, `IsArithVar`, `HodgeTateDatum`) and are
hard to reuse on their own.

**PositivityTheory** is not about "positivity". It is `AutomorphicForms/PublishedInputs`: weight-one
Hilbert Eisenstein series, Jacquet–Langlands torus kernels, Bushnell–Kutzko-style types, cyclic base change
and real Galois representations. The only literal "positivity" is a 59-line lemma that a positive-definite
cone is open. Several of its theorems take `GlobalTheory.Published.*` hypotheses (cited theorems), e.g.
`AutomorphicFormsFiniteGL` and `JacquetShalikaRigidity`.
**Supplements** is a single 19-line file that restates the final RH/GRH theorems (`allChi`, `rhOfAll`,
`critAll`).

## 3. Inventory (most reusable first)

"M" means the statement is purely about Mathlib objects. "I" means it involves repo definitions; see §4 for
verdicts on them.

| Declaration | path:line | Statement (paraphrased) | M / I | Classical name | Reusability |
|---|---|---|---|---|---|
| `ReciprocityTheory.DiscreteGroups.LocalClassField.artin_reciprocity_char_zero` | `ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportC.lean:159` | For every characteristic-0 nonarchimedean local field K (Mathlib `IsNonarchimedeanLocalField`) there is a continuous, injective, dense-image homomorphism Kˣ → G_K^ab. It sends uniformisers to Frobenius lifts. For each finite abelian L/K it surjects onto Gal(L/K) with kernel the norm group N(Lˣ). | M (via `Neutral.B1.LocalReciprocity`, faithful) | Local Artin reciprocity (char 0) | **High.** A theorem Mathlib lacks, stated in Mathlib terms |
| `…LocalClassField.exists_isArtinK` | `…/LocalClassField/RecArtin.lean:91` | The same reciprocity map for a finite extension K/ℚ_p inside `PadicAlgCl p`, with Gal via `PadicAlgCl p ≃ₐ[K] …` | I (thin wrappers on Mathlib) | Local reciprocity | High |
| `…LocalClassField.existence` | `…/LocalClassField/Existence.lean:108` | Every finite-index subgroup H of Kˣ (K/ℚ_p finite) is the norm group of some finite abelian L/K | I (thin) | Local existence theorem | High |
| `…LocalClassField.eq_one_of_forall_mem_normGrp` | `…/Existence.lean:131` | An element that is a norm from every finite abelian extension is 1 | I (thin) | Norm groups separate points | Med |
| `…LocalClassField.normGrp_eq_of_soluble` | `…/NormLimit.lean:337` | Norm limitation: the norm group of a soluble (Galois) extension equals that of its maximal abelian subextension | I (thin) | Norm limitation theorem | Med |
| `…LocalClassField.invBr_bijective`, `invBr_res` | `…/Brauer.lean:80`, `:91` | inv: H²(G_K, K̄ˣ) → ℚ/ℤ is bijective, and restriction to L multiplies inv by [L:K] | I (continuous cochain H², faithful) | Brauer group of a local field | High for cohomology work |
| `CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate` | `CompanionTheory/AutomorphicTheory/PadicCyclotomicFields/GcohTop.lean:15` | For K/ℚ_ℓ finite and M a finite discrete ℤ/ℓ^r-module with continuous G_K-action: H²(μ_{ℓ^r}) ≅ ℤ/ℓ^r, and the cup products H⁰×H², H¹×H¹ and H²×H⁰ into H²(μ) with the twisted dual are perfect | I (`Formalism.GaloisCohomology.LocalTateDualityK`; Mathlib `PadicAlgCl`, `Representation`) | Local Tate duality (ℓ = p case) | **High**; the proof depends on GroundTheory profinite cohomology |
| `…Gcoh.top_euler`, `…Gcoh.top_locfin` | `…/GcohTopEuler.lean:10`, `GcohTop.lean:17` | #H¹ = #H⁰·#H²·#M^{[K:ℚ_ℓ]}; Hⁱ finite, and zero for i ≥ 3 | I (same) | Tate's local Euler characteristic formula | High |
| `ReciprocityTheory.L2DbarEstimates.hormander` | `ReciprocityTheory/L2DbarEstimates/NormFibrations/Hormander.lean:31` | Let X be a Riemann domain over ℂⁿ with a smooth psh exhaustion, φ smooth psh, F₀ smooth, and \|∂̄F₀·ξ\|² ≤ h·i∂∂̄φ(ξ,ξ) pointwise. Then some holomorphic F has ∫\|F₀−F\|²e^{−φ} ≤ ∫h e^{−φ} | I (`EtaleStein`, `vol`; faithful) | Hörmander's L² ∂̄ estimate | High for complex analysis; none for our number-theory targets |
| `ReciprocityTheory.L2DbarEstimates.skoda` | same file `:37` | Division by g₁..g_p (p ≥ 2, no common zero, t > p−1) with the weighted L² bound t/(t−(p−1)) | I | Skoda's division theorem | Med |
| `…L2DbarEstimates.tw` | same file `:42` | Twisted L² bound for the Bergman projection residual | I | Berndtsson / Donnelly–Fefferman twist | Low–Med |
| `…L2DbarEstimates.ext`, `extNull`, `mv`, `mvInt` | `…/NormFibrations/MvBlowup.lean:13,27,30,55` | An L² holomorphic function on a ball minus {F=0} extends holomorphically; the zero set of F ≢ 0 is Lebesgue-null; weighted sub-mean value; ∫_{B}\|y\|^{−2s} < ∞ ⇔ s < n | M | L² Riemann extension; null zero sets | Med |
| `ReciprocityTheory.AnForm.Osgood.osgood` | `ReciprocityTheory/AnalyticForms/AnalyticCharts/Osgood.lean:184` | A ℂ-differentiable f: open U ⊆ ℂᵉ → ℂ is analytic on U | M | Osgood / Cauchy formula in ℂⁿ | **High** (Mathlib has only one variable) |
| `ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd` | `…/AnalyticCharts/NullZero.lean:124` | The zero set of a not-identically-zero analytic function on a connected open set in ℂᴰ has measure 0 | M | Zero sets are null | High |
| `ReciprocityTheory.AnForm.A.PshLap.isPsh_iff_isLeviPsh_thm` etc. | `…/PlurisubharmonicFunctions/PshBasic.lean:156,158,178,181` | For C² φ: psh ⇔ Levi form ≥ 0; a finite max of psh is psh; psh is L¹_loc; sub-mean value over balls | I (`IsPsh` = usc plus circle sub-mean; faithful) | Basic pluripotential theory | Med |
| `…AnForm.A.pshExtension_thm` | `…/PshExt.lean:357` | A psh function on U∖{coordinate divisor} with log-log growth extends (after truncation) to a psh function on U | I (faithful) | Psh extension across divisors | Low–Med |
| `…AnForm.A.det_smul_add_smul_eq_sum_mdisc`, `norm_mdisc_le_of_abs_le`, `mdisc_re_mono` | `…/MdiscSt.lean:170,242,209` | Binomial expansion of det(sA+tB) in mixed discriminants; monotonicity and ±-bounds for PSD arguments | M | Mixed discriminants | Med |
| `ReciprocityTheory.CA.RegA.IsRegularLocalRing.isDomain` | `ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RegGensA.lean:382` | A regular local ring (Mathlib `IsRegularLocalRing`) is a domain | M | Regular ⇒ domain | **High** (Mathlib candidate; check against the pin) |
| `ReciprocityTheory.CA.isCM_of_isRegularLocalRing` | `…/CohenMacaulay/IsCMOfIsRegularLocalRing.lean:12` | Regular local rings are Cohen–Macaulay | I (`IsCM` = Noetherian with a regular sequence of length dim; faithful) | Regular ⇒ CM | High |
| `ReciprocityTheory.CA.RegGens.exists_regular_gens` | `…/CohenMacaulay/RegGens.lean:86` | The maximal ideal of a regular local ring of dimension d is generated by a regular sequence of length d | M | Regular system of parameters | High |
| `ReciprocityTheory.CA.IsCM.localization_atPrime`, `IsCMMod.associatedPrimes_eq_minimalPrimes` | `…/CohenMacaulay/LocDim.lean:59`, `Unmixed.lean:114` | CM localises at primes; CM modules are unmixed | I (faithful) | CM localisation; unmixedness | Med–High |
| `ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field`, `ringKrullDim_eq_of_trdeg_eq_field` | `…/PolynomialHeights/HeightAddRingKrullDimQuotientMvPolynomialField.lean:52,103` | In k[x₁..x_N], ht 𝔔 + dim k[x]/𝔔 = N; a finitely generated domain has dim = trdeg | M | Dimension formula | High |
| `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT` | `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AlgDim.lean:12` | V prime in k[x], s ∉ V, W a minimal prime over V+(s) ⇒ dim(k[x]/W)+1 = dim(k[x]/V) | M | Krull PIT, dimension form | Med |
| `ReciprocityTheory.ChartRestriction.L1.cm1` | `ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/IsIntegralOfRoot.lean:56` | d squarefree, d ≡ 3 (4), and lattice L (Mathlib `PeriodPair`) stable under (1+√−d)/2 ⇒ j(L) = 1728g₂³/Δ is an algebraic integer | M (plus one small def `HasCMBy`) | Integrality of singular moduli (maximal order, odd discriminant) | **High** |
| `…L1.jT_isIntegral` | same file `:41` | If τ ∈ ℍ is fixed by some integer matrix of non-square determinant m (Gm m τ = 0), then j(τ) is integral over ℤ | M (modular forms) | Weber/Deuring integrality of j | High |
| `…L1.qPrin`, `qPrin_low`, `exists_integral_poly_of_qExpansion` | `…/UnramifiedIntegrals/ModQPrin.lean:232,239,125` | A level-1 modular form of weight 12N with q-coefficients in a subring R ⊆ ℂ equals Δ^N·P(j) with P ∈ R[X], deg ≤ N (leading coefficient controlled) | M (`ModularForm 𝒮ℒ k`) | q-expansion principle (level 1) | High |
| `…L1.dC_eq`, `eisenstein_cube_sub_sq_eq`, `sigma_congr` | `…/ModDeltaInt.lean:92,57,21` | Δ has integral q-expansion with coefficient 1 at q; E₄³−E₆² = 1728·(explicit integral series); 12 ∣ 5σ₃(n)+7σ₅(n) | M | Integrality of Δ | Med |
| `…L1.torsUnit2`, `torsUnit3` | `…/TorsUnit2.lean:17`, `TorsUnit3.lean:55` | On y² = 4x³−g₂x−g₃ over an ultrametric field with unit discriminant, an n-torsion point (n a unit, odd or prime to 3) has \|x\| = 1 | M (Mathlib Weierstrass points) | Torsion is integral under good reduction | Med |
| `…L1.jInt`, `cm4` | `…/ModJInt.lean:47`, `TorStatus.lean:42` | j of a CM lattice is ℓ-adically integral for every ℓ; prime-to-ℓ torsion of a good model has unramified, integral coordinates | M/I | Néron–Ogg–Shafarevich direction (CM case) | Med. Note: the companion `CM2` (good reduction) is assumed via `[Fact CM2]` in `Formalism/…/CmAll.lean`; in this subtree it is proved only conditionally (`goodReduction_of_integral_unramified`, `RedStatus.lean:17`) |
| `…L1.prime_choice` | `…/RedPrime.lean:109` | For d squarefree, d ≡ 3 (4), 3 ∣ d, d ≠ 3, and any b, there is a prime p > b, d with p ≡ 2 (3) and p ∥ r²+d for some even r | M | (auxiliary prime existence) | Low–Med |
| `GlobalTheory.T.poisson_summation_gaussian` | `CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PoissonSummationGaussianStatement.lean:13` | For Z complex symmetric with Im Z ≻ 0, g ∈ GL_n(ℝ) and a ∈ ℝⁿ: Σ_n f(a+gn) = \|det g\|⁻¹ Σ_n f̂(g^{−T}n)e^{−2πi⟨a,·⟩} for f = e^{πi xᵀZx}, with both sums absolutely convergent | M | Poisson summation / theta inversion | **High** |
| `GlobalTheory.T.adele_ring_cocompact_discrete_number_field` | `…/AdeleRingCocompactDiscreteNumberFieldStatement.lean:11` | F ⊂ 𝔸_F (Mathlib `AdeleRing`) is discrete (compacts meet F finitely) and cocompact, and 𝔸_F is noncompact | M | Discreteness and cocompactness of F in 𝔸_F | High |
| `GlobalTheory.T.finite_field_quadratic_form_point_count` | `…/FiniteFieldQuadraticFormPointCountStatement.lean:13` | For a nondegenerate quadratic form in 2M ≥ 2 variables over 𝔽_q, q odd: \|#{Q(x)=s} − q^{2M−1}\| ≤ q^M | M | Points on quadrics over 𝔽_q | High |
| `GlobalTheory.T.cusp_representatives_finite` | `…/CuspRepresentativesFiniteStatement.lean:12` | Finitely many SL₂(F) elements and a constant C suffice to complete any (c,d) ≠ 0 in 𝓞_F, up to units and a scalar of norm ≤ C, to an SL₂(𝓞_F)-translate | M | Finiteness of cusps (class number) | Med–High |
| `GlobalTheory.T.discriminant_different_product_formula` | `…/DiscriminantDifferentProductFormulaStatement.lean:13` | √\|d_F\| · Π_v N(v)^{−e_v(different)/2} = 1 | M plus GroundTheory `differentExp` | Discriminant = norm of the different | Med |
| `GlobalTheory.T.cartan_decomposition_gl_nonarchimedean` | `…/StableLattices/CartanDecompositionGlNonarchimedeanStatement.lean:11` | GL_n(L) = K·diag(ϖ^a)·K with a antitone, K the integral points, for a locally compact ultrametric L | I (light: `congK`, `dPow`) | Cartan decomposition | Med–High |
| `GlobalTheory.T.fourier_inversion_schwartz_bruhat`, `adeles_self_dual`, `theta_function_modularity`, `witt_extension_global`, `archimedean_gaussian_fourier` | `…/AdelicAnalysis/*Statement.lean:12` | Fourier inversion on Schwartz–Bruhat functions for a self-dual pair; 𝔸_F self-dual for the standard character; modularity of adelic theta series; Witt extension for hermitian forms over a CM extension; Gaussian Fourier transform on ⊕_w ℝ^ι | I (`NADual`, `SB`, `IsStdChar`, `QSetup`, `IsCMExt`) | Tate thesis / Weil / Witt toolkit | Med (on internal defs) |
| `GlobalTheory.T.picard_group_of_field_trivial`, `seesaw_triviality_abelian_scheme` | `…/StableLattices/PicardGroupOfFieldTrivialStatement.lean:38`, `SeesawTrivialityAbelianSchemeStatement.lean:20` | Pic(Spec k) = 0; seesaw triviality for line bundles on A ×_S Y | I (internal `Pic`, `LB`, `IsAbelianScheme`) | Seesaw principle | Low–Med |
| `ReciprocityTheory.GeometryOfNumbersTheory.measure_div_le_ncard_inter_lattice` | `ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/CountZSt.lean:67` | For S convex, symmetric, bounded and measurable, and L a ℤ-lattice: vol(S)/(2ⁿ·covol L) ≤ #(S∩L) | M | Quantitative Minkowski (Blichfeldt-type count) | High |
| `…GeometryOfNumbersTheory.covol_div_covol_eq_relIndex` | `…/CountStA.lean:15` | covol L₁/covol L₂ = [L₂:L₁] for lattices L₁ ≤ L₂ | M | Index = covolume ratio | High |
| `…GeometryOfNumbersTheory.gramSt_hadamard`, `gramSt_fischer`, `det_re_le_of_sub_posSemidef` | `…/GramSt.lean:123,72,143` | Hadamard's inequality for PD hermitian matrices; Fischer's inequality for blocks; det monotone in Loewner order | M | Hadamard, Fischer | Med (partly in Mathlib) |
| `…GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily`, `deg_of_le` | `…/ArakelovDegreeEqDegreeOfFamily.lean:32,39` | The Arakelov degree of a hermitian 𝓞_K-lattice does not depend on the frame; deg E' = deg E − log[E:E']/[K:ℚ] | I (`HermFam`, `deg`; faithful) | Arakelov degree | Med |
| `ReciprocityTheory.MultiplicativeHeights.Closed.semistable` | `ReciprocityTheory/SemistableReduction/SemiAll.lean:15` | Every lattice self-dual for a hermitian form over a number field has a majorant for which it is semistable of degree 0, and every lattice endomorphism contracting at all places is 0 | I (`HermForm`, `Majorant`, `IsSemistableZero`; faithful) | Stuhler–Grayson semistability (self-dual case) | Med. The directory name ("semistable reduction") is about lattices, not curves |
| `…MultiplicativeHeights.Closed.degAdd` | `…/LatAll.lean:22` | Additivity of the Arakelov degree in 0 → saturated sub → L → quotient → 0 | I | Degree additivity | Med |
| `…MultiplicativeHeights.Closed.torus_l2_cauchy_inequality`, `gram`, `sj`, `gauss_height_additivity`, `sphere_height_lower_bound` | `…/TorusL2CauchyInequality.lean:35,37,21,25,27` | Mahler measure ≤ log ‖f‖₂ and \|coeff\| ≤ sup on the torus; exp(2\|S\|m(F)) ≤ Gram det of {F·monomials}; for homogeneous f, log\|f(u)\| − (a/2)H_{n−1} ≤ sphere mean of log\|f\|; the Gauss/sphere height h₀ is additive; h₀(f) ≥ −Σ a_b(log n + ½) | M (except h₀, a faithful def) | Mahler measure and height inequalities, Gelfond-type lemma | **Med–High** (heights of polynomials) |
| `ReciprocityTheory.MultiplicativeHeights.unipotent_holds` | `…/SemistableReduction/Unipotent.lean:51` | An r×r matrix γ over a number field that is near-isometric at all embeddings and has trace(γⁿ) ≡ r mod g (g large) is unipotent | M | Kronecker-type rigidity | Low–Med |
| `ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT` | `ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean:182` | Over any field, Vandermonde × Gelfand–Tsetlin generating sum = det(t_i^{λ_j+n−j}) | M (the defs `gtChar`, `alt`, `wden` are elementary) | Bialternant formula for Schur polynomials | High |
| `…ChartRestriction.G.Key.Chi.spGen` | `…/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenMain.lean:166` | Sp_{2g}(ℤ) (Mathlib `symplecticGroup`) is generated as a monoid by the translations [[1,S],[0,1]] (S symmetric), the block-diagonal diag(U,U^{−T}), and J | M | Generators of Sp_{2g}(ℤ) | High |
| `…ChartRestriction.G.SA.locGen` | `…/StrongApproximation/LocGen.lean:45` | Over a quadratic étale algebra K/k (2 invertible), SU(J) of a nondegenerate hermitian form with a hyperbolic pair e,f is generated by Eichler transformations along e and f | M (`SU`, `eich` are explicit matrix defs) | Eichler generation | Med. The adelic strong approximation `SAStatement` is *stated* here but proved in `GroundTheory/…/StrongApproximation/Assembly.lean:54` |
| `…ChartRestriction.G.FreeQuotientRank.galoisDescent_holds` | `…/Rationality/DescPf.lean:61` | For K₂/K finite Galois, a Gal-stable K₂-subspace of K₂⊗V is spanned by its K-rational points | M | Galois descent (Speiser) | Med–High |
| `…ChartRestriction.G.AI.index_thm` | `…/ArithmeticIntersection/CardQuotEqNatAbsNorm.lean:79` | For any order O in a number field and f ≠ 0, #(O/f) = \|N(f)\| = Π_σ\|σf\| | M | Index = norm, for orders | Med–High |
| `…ChartRestriction.G.AI.archimedes_thm` | `…/ArithmeticIntersection/KappaB.lean:118` | On S² ⊂ ℝ³, ∫f(⟨n,u⟩) = ½∫_{−1}^{1}f, plus the first and second moment versions | M | Archimedes' hat-box theorem | Med |
| `…ChartRestriction.DS.Lap.Capelli.capelliCentral` | `…/DiscreteSeries/LaplaceOperators/CapelliIdentity/WhittakerZeroStatement.lean:19` | In any ℂ-algebra with elements satisfying the gl_n relations, the Capelli determinant commutes with all E_ab | I (`GlRelR`, `capelliC`; explicit) | Capelli identity (centrality) | Med |
| `ReciprocityTheory.Cheb.cyclotomic_irreducible_of_forall_isUnramifiedAt` | `ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean:130` | If ℓ is unramified in a number field K, then Φ_ℓ is irreducible over K | M | Linear disjointness of ℚ(ζ_ℓ) | Med–High |
| `ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity`, `DedekindZetaReal.tendsto_primeIdealZetaSum_univ` | `ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean:182`, `TendstoPrimeIdealZetaSumUniv.lean:252` | A set of primes with positive Dirichlet density has degree-one primes outside any finite set; Σ_𝔭 N𝔭^{−s} → ∞ as s → 1⁺ | M (Mathlib `HasDirichletDensity`, `primeIdealZetaSum`) | Degree-one primes carry all density | **High** for Chebotarev/density work |
| `ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal`, `dedekindZeta_eq_idealZetaR` | `ReciprocityTheory/Chebotarev/EulerSum.lean:85,59` | Σ_I N(I)^{−s} converges for s > 1 and equals `dedekindZeta` there | M | Convergence of ζ_K | Med (Mathlib may already have it) |
| `ReciprocityTheory.UG.AdeleIntA.exists_approx_adele` | `ReciprocityTheory/AdeleApproximation/AdeleIntA.lean:107` | Every finite adele differs from some u ∈ K by an integral adele | M | Strong approximation 𝔸_f = K + Ô | Med–High |
| `ReciprocityTheory.P1.isAdicComplete_ps` | `ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean:107` | R complete Noetherian local ⇒ R⟦X⟧ is complete for its maximal ideal | M | | Med |
| `ReciprocityTheory.GC.burnside_surj_of_irred` | `ReciprocityTheory/BurnsideSurjectivity/Burnside.lean:174` | An irreducible finite-dimensional representation over an algebraically closed field maps the algebra onto End(V) | M | Burnside's theorem | Med–High |
| `ReciprocityTheory.Coh.fiveTerm_holds`, `shapiro_holds`, `zHat_holds`, `lES_holds`, `cupCor_holds`, `transgression_holds`, `finiteLevel_holds` | `ReciprocityTheory/GroupCohomology/FiveTerm.lean:11`, `Shapiro.lean:155`, `LengthKerEqCoker.lean:41`, `ConnNatHolds.lean:258`, `CupCor.lean:22`, `Transgression.lean:18`, `FiniteLevel.lean:190` | Continuous-cochain cohomology of profinite groups: long exact sequences, inflation–restriction five-term sequence, Shapiro, cor∘res = index, cup/cor projection formula, H¹(Ẑ, M) ≅ M/(σ−1)M with Hⁿ = 0 for n ≥ 2, classes come from finite levels and are torsion | I (`TRep`, `Cx`; faithful continuous cochains) | Profinite group cohomology basics | Med (parallel to Mathlib's new continuous cohomology) |
| `ReciprocityTheory.PGsh.Up.u3`, `ReciprocityTheory.PGsh.L2.h1` | `ReciprocityTheory/DualLattices/SqIdeal.lean:203`, `ImportsAlt.lean:14` | Classification of Hopf orders in C[ℤ/p] (C algebraically closed of char 0) by a generator x with x^p = δx; Cartier duality of Hopf orders via Fourier, with colength product v(#N)^{#N} | I (`HopfOrder`, `HasColen`) | Tate–Oort (rank p), Hopf-order duality | Low–Med |
| `ReciprocityTheory.PTheta.thetaQuasiPeriod_holds` (and siblings in `ThetaQuasiPeriods/`) | `ReciprocityTheory/ThetaQuasiPeriods/Transl.lean:103` | Riemann theta with characteristics: quasi-periodicity under z ↦ z+τn+n', holomorphy and absolute convergence on the Siegel domain | I (explicit theta defs) | Theta transformation | Med |
| `UpperTheory.V.Published.hilbert_eisenstein_weight_one_holds` | `PositivityTheory/AutomorphicForms/PublishedInputs/HilbertEisenstein/HilbertEisensteinWeightOneHolds.lean:23` | For F totally real and ω an odd finite-order Hecke character with nontrivial conductor, there is a holomorphic weight-1 Hilbert modular form with Fourier coefficients Σ_{𝔯∣𝔪} ω(𝔯) | I (`TR.Sm`, `IsHol`, `HasExp`, `HChar`; not checked for faithfulness) | Weight-one Eisenstein series (Hecke) | Med if the defs hold up |
| `ReciprocityTheory.ChartRestriction.G.T0.ufd_mem_of_forall_prime` | `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/Hartogs.lean:9` | In a UFD, an element of the fraction field that is integral at every prime is in R | M | Algebraic Hartogs (UFD) | Low (easy) |

## 4. Internal definitions worth knowing

| Definition | Where | Verdict |
|---|---|---|
| `Neutral.B1.IsLocalArtinMap`, `LocalReciprocity`, `IsFiniteAbelian`, `abRestrict`, `normGroup`, `IsFrobeniusLift`, `IsUniformiser` | `ReciprocityTheory/NeutralLocalFields/Reciprocity.lean:17–80` | **Faithful.** Built from Mathlib's absolute Galois group, `Algebra.norm` and integral closure. `normGroup L` is the range of the norm on Lˣ. |
| `Neutral.B1.IsGlobalArtinMap`, `Ideles`, `IdeleClassGroup` | same file `:88–140` | Faithful statement of global reciprocity (continuous, surjective, kernel the identity component, Frobenius at unramified v, complex conjugation at real places). **Defined here, not proved here.** |
| `…LocalClassField.IsArtinK`, `IsAbLK`, `normGrp`, `GK`, `KbarMult`, `Br`, `invUr` | `ClassFieldTheory/LocalClassField/RecDefs.lean:20–35`, `ExistsIntEKMulVbar.lean`, `NeutralLocalFields/Duality.lean:357` | Faithful. `normGrp` uses Σ over cosets of conjugates in additive notation, i.e. the product norm. `invBr` and `invUr` are `Classical.choose` of a specification `IsInv`; existence is proved (`invUr_bijective`), so this is not vacuous. |
| `ReciprocityTheory.Gal.H0/H1/H2/Hn`, `Z1`, `B2` (continuous cochains, discrete modules) | `ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean` | Faithful continuous-cochain cohomology. |
| `ReciprocityTheory.Gal.LocalTateDuality`, `GlobalEulerChar`, `ShaDuality`, `GreenbergWiles`, … | `ReciprocityTheory/Hypotheses/GalCoh.lean` | Faithful Prop **statements**: Poitou–Tate, Greenberg–Wiles, Sha duality. Only definitions here. `LocalTateDuality` is proved in `Development/AutomorphicSpectrum/Proofs/GlobalProofs/DualityForAbsGal.lean:60`; the global ones were not traced. |
| `ReciprocityTheory.L2DbarEstimates.EtaleStein`, `vol`, `Holo`, `Levi`, `SmoothR`, `wint` | `L2DbarEstimates/IsLocalHomeomorph.lean:14–130` | Faithful. `EtaleStein` is a local homeomorphism to ℂⁿ with a smooth psh exhaustion (compact sublevels). `vol` is defined as 0 unless `VolAdditive` holds, but `volAdditive` (`ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean:156`) proves it for every local homeomorphism, so the Hörmander statement is **not** degenerate. |
| `ReciprocityTheory.AnForm.A.IsPsh` | `AnalyticForms/PlurisubharmonicFunctions/IsPshLocallyIntegrableStatement.lean:17` | Faithful: upper semicontinuous plus sub-mean value on every complex disc. |
| `ReciprocityTheory.CA.IsCM`, `IsCMMod`, `DepthGE` | `CommutativeAlgebra/ChainConnInDim.lean:21`, `CohenMacaulay/ModDepthGE.lean:11` | Faithful (Noetherian local, regular sequence of length dim, or supportDim for modules). |
| `ReciprocityTheory.GeometryOfNumbersTheory.HermFam`, `deg`, `degreeOfFamily`, `IsFrame` | `GeometryOfNumbers/LatticeCovolumes/ConjSymm.lean:14–60` | Faithful hermitian 𝓞_K-module with the normalised Arakelov degree. `deg` chooses a frame, and the frame-independence theorem shows the choice is harmless. |
| `ReciprocityTheory.MultiplicativeHeights.HermForm`, `Majorant`, `IsSemistableZero`, `latDeg`, `h0` | `SemistableReduction/TorsionNonvanishStatement.lean:72`, `LatSemiSt.lean` | Faithful. `HermForm` needs an involution c inducing complex conjugation at every embedding (CM or totally real). |
| `Formalism.L2.Th1.CM.HasCMBy`, `jInv`, `omegaK`, `MaximalUnramifiedExtension` | `Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:12–19` (used here) | Faithful. CM means stability under ω = (1+√−d)/2, i.e. the maximal order for d ≡ 3 (4). `MaximalUnramifiedExtension l` is the closure of prime-to-l roots of unity in ℂ_l. |
| `ReciprocityTheory.ChartRestriction.L1.IsMF`, `DD`, `jT`, `Gm` | `ReductiveGroups/UnramifiedIntegrals/ModDefs.lean:14–41` | Faithful wrappers over Mathlib `ModularForm 𝒮ℒ k`, `ModularForm.discriminant` and `E₄`. |
| `Formalism.GaloisCohomology.LocalTateDualityK`, `LocalEulerCharK`, `LocalFinitenessK` | `Formalism/GaloisCohomology/LocalTateDualityK.lean:35–55` | Faithful, but only the ℓ = p case: the module is ℓ-power torsion over K/ℚ_ℓ. |
| `GlobalTheory.T.*` "Statement" files in `CompanionTheory/SpectralGeometry` | 613 files | Each is a **theorem**, not a hypothesis. It closes by `exact` of a sibling proof. Many use internal defs (`NADual`, `SB`, `QSetup`, `IsCMExt`, `IsHermND`); the sampled ones looked faithful. |
| `IsURepOn`, `KType`, `IsDS`, `KG`, `UJset` (U(p,q) representation framework) | `Formalism/MainNotions`, `Formalism/REAL` | Unitary representations modelled as maps `Matrix → (H →L[ℂ] H)` with conditions on a subset. Looked plausible; not audited. |
| `HermLine`, `IsArithVar`, `IFamily`, `IsFieldIntersection` (multiprojective Arakelov setup) | `ReductiveGroups/ArithmeticGeometry/*` | Not audited. These are bespoke encodings of arithmetic varieties as multihomogeneous prime ideals with hermitian line bundles given by explicit metrics. |

No degenerate or vacuous definitions were found among those opened. The one place that looked like a trap
(`vol = 0` fallback) is discharged.

## 5. Mechanical families

- `Lemmata/GeneralBFact*` (91 dirs, one lemma `goal1` each, each in its own `Bl.*` namespace) and
  `Lemmata/FirstBlockLemma{A..K}`, `MiscLemmas{A..R}`, `SecondBlockLemmaA`: about 120 small, standalone
  Mathlib-level lemmas. Many are near-duplicates. The "clearing denominators" fact (if v is in the K-span of
  an 𝓞-module L, then d•v ∈ L for some nonzero d ∈ 𝓞 or ℤ) appears about 20 times. Full list in §6b.
- `CompanionTheory/SpectralGeometry/LocalGlobalProofs/*Statement.lean` + `*.lean`: 613 statement/proof pairs
  (AdelicAnalysis 583 files, StableLattices 479, ConvexCones 134). ConvexCones is Voronoi reduction theory:
  perfect forms, polyhedral fans and star subdivisions.
- `ReductiveGroups/DiscreteSeries/*` (985 files) and `CompanionTheory/{RealGroups,HarishChandraModules,
  AutomorphicTheory}` (about 700): U(p,q)/G₂ representation theory. Pieri rules, Capelli eigenvalues,
  interlacing walks, Bessel uniqueness, formal degrees, Garding and Poulsen density, Harish-Chandra
  admissibility (`HCMult`). About 150 `theorem x : XStatement` steps.
- `ReductiveGroups/ArithmeticGeometry/*` (1,522 files): about 230 `…Statement` defs for Arakelov intersection
  theory, arithmetic Hilbert–Samuel, Kleiman/Moriwaki ampleness and fundamental domains. Several are proved
  elsewhere (`SAStatement` and `PackingStatement` in GroundTheory and Development).
- `DualLattices` (175): length and colength bookkeeping over valuation rings of ℂ_p for Hodge–Tate data
  (`HodgeTateDatum`, `UnramData`); mostly RH-specific.
- `AnalyticForms/RegularLocalRings` (73): charts, SNC divisors and weighted blow-ups for specific projective
  constructions. `FinalTheorems.lean` defines `Blowup`, `Snc`, `QE`. These are **not** a resolution-of-
  singularities theorem.
- `PositivityTheory/AutomorphicForms/PublishedInputs/JacquetLanglands/TorusKernels` (87): orbit-integral
  bookkeeping (hyperbolic and elliptic terms) for a trace-formula comparison.
- `PositivityTheory/…/NonzeroTypes` (86): smooth representations of p-adic GL_n (types, Jacquet modules,
  Maschke for compact groups).

## 6. Standalone value

**Effectively proved, in usable form (Mathlib objects or thin, faithful wrappers):**
- Local class field theory for characteristic-0 local fields: reciprocity, existence and norm limitation, plus
  the Brauer invariant. Directly usable for anything needing local Artin maps (local conductors, local Kummer
  symbols, Hilbert symbols).
- Local Tate duality and Euler characteristic, ℓ = p case, finite coefficients.
- Integrality of singular moduli (j(τ) is integral for CM τ), the q-expansion principle at level 1, and
  integrality of Δ.
- Hörmander's L² ∂̄ estimate (general Stein Riemann domains), Skoda division, L² Riemann extension, and
  Osgood's lemma in ℂⁿ.
- Regular ⇒ domain ⇒ CM, CM localisation and unmixedness, and the dimension formula in polynomial rings.
- Poisson summation for complex Gaussians on ℤⁿ-cosets; F discrete and cocompact in 𝔸_F; strong
  approximation 𝔸_f = K + Ô; the 𝔽_q quadric point count.
- Quantitative Minkowski (#(S∩L) ≥ vol S/(2ⁿ covol L)) and covolume = index.
- Positive-density prime sets contain degree-one primes; divergence of Σ N𝔭^{−s}.
- Bialternant formula for Schur polynomials; generators of Sp_{2g}(ℤ); Burnside; Galois descent for
  subspaces.

**Proved only in a special case:**
- Singular moduli: `cm1` covers only discriminant −d with d ≡ 3 (mod 4) squarefree (maximal order, odd
  discriminant). `jT_isIntegral` is more general: any τ fixed by a primitive non-square-determinant matrix.
- Local Tate duality: only for ℓ-power torsion modules over ℚ_ℓ-extensions (ℓ = p). Local class field theory:
  characteristic 0 only.
- Skoda: only p ≥ 2 and t > p−1. Semistability: only self-dual hermitian lattices.

**Misleading names:**
- `ReciprocityTheory` overall: only LCFT is "reciprocity". Global CFT is merely stated (NeutralLocalFields)
  and proved in GroundTheory.
- `Chebotarev/`: no Chebotarev density theorem, only cyclotomic irreducibility and ζ_K convergence.
- `SemistableReduction/`: semistable hermitian lattices and polynomial heights, not curves or abelian varieties.
- `GeometryOfNumbers/`: Arakelov degree, lattice counting and Bergman/sphere integrals. There is no
  Minkowski second theorem or successive minima for 𝓞_K-lattices: `smallVec` is defined but no counting
  theorem for it was found.
- `ReductiveGroups/UnramifiedIntegrals`: CM elliptic curves and modular forms, not unramified Hecke integrals.
- `DualLattices`: Hopf orders and Hodge–Tate lengths.
- `L2DbarEstimates`: accurate.
- `PositivityTheory`: automorphic "published inputs". The only positivity is a cone-openness lemma.
- `CompanionTheory/SpectralGeometry`: adelic analysis and lattice theory, not spectral geometry.
- `Supplements`: only a restatement of the main theorems.

### 6b. Lemmata, listed (all in `Lemmata/<Dir>/…`, namespace `Bl.<…>`, main lemma usually `goal1`)

Mathlib-level unless noted:
- **Determinants and matrices:** Cauchy–Binet-type expansion of det(AB) over maps Fin i → Fin N (`GeneralBFact`);
  d/dt det A(t) at A(0) = 1 is tr A′ (`B110`, `MovedPointExistence`, `ProductIdentities`); Hadamard \|det A\| ≤
  Π‖rows‖ (`DetNormLeProdRows`); det monotone in Loewner order (`DetMonotoneStarMulSelf`); uniqueness of LU
  with unipotent lower factor (`GeneralBFactForm`, `GeneralBFactTer`, `GeneralBFactVariant`); diagonal of a
  product of lower-triangular matrices (`GeneralBFactRightBisAlt`); a root of the charpoly has an eigenvector
  (`GeneralBFactRightBis`); aeval(A)·w = f(λ)w for an eigenvector (`PowMulVecEigen`, `PowerApplication`,
  `GeneralBFactUpperVariant`); invariant subspaces are stable under polynomials (`PowerMembership`,
  `GeneralBFactUpperForm`); generalised eigenspaces of commuting maps multiply (`GeneralBFactLeftLast`);
  injectivity of mulVec is preserved by an embedding K → ℂ (`GeneralBFactUpperAltForm`); linear independence
  is preserved under a field embedding (`MiscLemmasI`); LDU-type factorisation over a local ring with
  congruence conditions (`MiscLemmasA`).
- **DVRs and lengths:** length(O^ι/N) = v(det of a basis change) (`AddValuationProducts`); length(M/φM) =
  v(det φ) for injective φ on a free module (`DiscreteValuationQuotients`); v(Π) = Σv (`GeneralBFactLast`,
  `SecondBlockLemmaA`); a DVR's fraction field is the localisation away from ϖ (`GeneralBFactFurther`,
  `MiscLemmasN`); length of intersections (`GeneralBFactSecondExtra`).
- **Clearing denominators and lattices:** if v ∈ K-span(L) then d•v ∈ L, in about 20 variants (`Denominators`,
  `IntegerMulIntegral`, `NatMulIsIntegral`, `GeneralBFact{AltForm,BisAlt,LeftBis,LeftBisAlt,LeftTerForm,
  RightAltForm,Second,SecondAlt,ThirdAlt,ThirdMore,…}`, `MiscLemmas{D,J,L,O}`); a saturated submodule of a
  finite free module over a PID has a complement (`ComplementLifts`); a free ℤ_p-basis for f.g. lattices in
  ℚ_p[X] (`B1962s`, via `FreeLat`).
- **Number fields:** Tr_{E/ℚ} x = Σ_w 2 Re w(x) for E totally complex (`FiberEquations`); x² = x + c with
  c ∈ ℤ ⇒ x ∈ 𝓞 (`FirstBlockLemmaE`, `GeneralBFactRightTerForm`); every rational prime lies under some prime of
  𝓞_F (`GeneralBFactLeftTail`); a prime ideal containing n contains a prime factor p of n
  (`GeneralBFactRightVariant`); ζ^M = 1, ζ ≠ 1, ζ−1 ∈ P ⇒ M ∈ P (`GeneralBFactUpperVersion`); the CRT/approximation
  property of HeightOneSpectrum valuations (`Cancellation`); a common nonzero multiplier exists for finitely many
  ideal conditions (`GeneralBFactRightTer`); approximation in completions (`NearbyExistence`).
- **Ultrametric:** a monic integral polynomial forces \|root\| ≤ 1 (`GeneralBFactThird`, `GeneralBFactLeftTer`);
  \|xⁿ−yⁿ\| ≤ \|x−y\| (`GeneralBFactUpper`, `GeneralBFactRightExtra`); roots of unity have norm 1 in `PadicAlgCl`
  (`FirstBlockLemmaC`); prime-to-p roots of unity η ≠ 1 have ‖η−1‖ = 1 (`PadicNatCastNorm`); ultrametric sums
  (`FirstBlockLemmaD/F`, `GeneralBFactUpperTerForm`, `GeneralBFactLeftExtra`).
- **Complex analysis:** Cauchy estimate ‖Df(y)‖ ≤ C/R (`GeneralBFactBisForm`, `GeneralBFactVersion`,
  `GeneralBFactSecondBisForm`); vanishing order drops by one under differentiation (`CharacterDirections`);
  identity theorem on balls (`FirstBlockLemmaJ`); an entire function with ‖g(t)‖ ≤ A(1+\|t\|)^k is a polynomial of
  degree ≤ k (`IterateZero`); continuous unitary characters of ℝ are t ↦ e^{ibt} (`FunctionAtZero`,
  `GeneralBFactLeftVariant`, `GeneralBFactThirdFurther`); e^{2πix} = 1 ⇔ x ∈ ℤ (`GeneralBFactRightSide`); z with
  \|zⁿ−1\| < ½ for all n is 1 (`MiscLemmasM`).
- **Algebra and rings:** a unit plus a nilpotent or Jacobson element is a unit (`FirstBlockLemmaG/I/K`); idempotent
  lifting in an I-adically complete ring (`MiscLemmasH`); dim R/Q + 1 ≤ dim R/P (`FirstBlockLemmaB`);
  associated-prime step for quotients by regular elements (`GeneralBFactRest`); homogeneous polynomials scale
  by c^d (`FirstBlockLemmaA`, `GeneralBFactRightAlt`); a − a(p) ∈ (Xᵢ − pᵢ) (`GeneralBFactLeftMore`); degree and
  top coefficient of products of linear powers (`GeneralBFactMore`); total degree of ∂q·L (`PartialDerivativeDegree`);
  (not in Lemmata but similar in kind) `KrullIntersectionUnits.KrullIntersectionLemmas.exists_unit_kills_of_idempotent`
  and `GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills`
  (`PositivityTheory/PublishedTheorems/UnitKilling/UnitAnnihilation/UnitAnnihilators/ExistsUnitKillsOfIdempotent.lean:9,71`):
  for a finite ring map A → B with B = φ(A) + JB and kernel in ⋂Jⁿ, some s ≡ 1 mod J kills the kernel and
  satisfies s·B ⊆ φ(A) (a Krull-intersection / Nakayama corollary);
  an integral element has finite σ-orbit (`GeneralBFactRightVersion`); Frobenius-fixed points of 𝔽̄_g are 𝔽_g
  (`GeneralBFactSecondBis`, internal `Fbar`).
- **Finite fields and combinatorics:** a nondegenerate binary form x²+txy+my² over 𝔽_q represents every e
  (`GeneralBFactLeft`); uniqueness of base-B digit expansions with \|c\| < B (`GeneralBFactSecondLast`); index =
  card of a fibre-type quotient (`GeneralBFactLeftRest`); averaging over a surjective group hom
  (`MiscLemmasC`); multiset lifting (`GeneralBFactRightRest`); downward-closed predicate counting on Fin n
  (`GeneralBFactSecondTer`, `GeneralBFactLeftForm`, `B1959r`, `GeneralBFactRightFurther`); periodic sums
  (`PeriodicFunctions`); sums over piFinset (`MiscLemmasE`).
- **Measure theory:** curry and transposition of product measures are measure-preserving (`CurryModusPonens`,
  `GeneralBFactThirdBisForm`); a measurable fundamental domain exists for a discrete subgroup of a
  second-countable group (`MiscLemmasB`).
- **Representation theory:** simple modules over algebras over an algebraically closed field (density, `ScalarExtension`);
  twisted idempotents for finite groups (`TwistedIdempotents`); rank-one orbit forms for irreducible
  representations (`RankOneOrbitForms`); simultaneous eigenvectors for gl_n-representations (`SimultaneousEigenvectors`, internal `IsGlRep`).
- **Internal-def lemmas (low reuse):** `ClearingDenominators`, `DualWeylPullback`, `GeneralBFactLeftAltForm`,
  `GeneralBFactLeftVersion`, `GeneralBFactLeftFurther`, `IdempotentTraceVanishing`, `PaddedFamilies`,
  `PlaneOverMembership`, `HermitianSesquilinear`, `MultivariateIntegrals`, `MiscLemmasF`.

## 7. Open questions / not verified

- **Nothing was compiled.** Absence of `sorry`/`axiom` was checked only by text search over these five subtrees.
  The proofs of `top_tate`/`top_euler` and the `GlobalTheory.T.*` adelic theorems delegate to
  GroundTheory and Development code that this pass did not read.
- `artin_reciprocity_char_zero` passes through `Model`/`exists_model` (`TransportA.lean:258`). The transport
  lemmas were read only at signature level.
- Whether Mathlib at `fc4f59e5` already contains some of these results (regular ⇒ domain, `dedekindZeta`
  convergence, parts of Hadamard/Fischer, Burnside) was not checked; they may duplicate Mathlib.
- `CM2` (existence of good models for CM curves) is taken as a `Fact` instance in
  `Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/CmAll.lean:24`, outside this subtree. Inside the
  subtree it is proved only from `JInt` and `JUnram`. `JInt` is proved (`ModJInt.lean:47`); no proof of
  `JUnram` was found. Anyone reusing `cm4`/`cm2` should trace this first; `cm1`, `jT_isIntegral` and
  `qPrin` are not affected.
- PositivityTheory theorems that take `GlobalTheory.Published.*` hypotheses (`AutomorphicFormsFiniteGL`,
  `JacquetShalikaRigidity`, `BernsteinZelevinskyFiniteness`, `AdmissibleReal`) are conditional. Whether those
  hypotheses are discharged elsewhere was checked only for some: a `bernsteinZelevinskyFinite` exists in
  Development; `AutomorphicFormsFiniteGL` has no proof found.
- The faithfulness of `TR.Sm`/`IsHol`/`HasExp` (Hilbert modular forms) and of the U(p,q) representation
  framework was not audited.
- ReductiveGroups/ArithmeticGeometry (1,522 files) and DiscreteSeries (985) were characterised by statement
  names and about 30 opened statements. A deeper pass could turn up more Mathlib-level results (e.g. in
  `TaylorDiscriminants/DiscriminantEstimates`, `FundamentalDomains`, `HeightTheory`).
