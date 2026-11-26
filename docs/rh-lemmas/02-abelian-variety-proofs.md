# riemann-hypothesis inventory 02: `Development/AbelianVarietyTheory/Proofs`

Repo: [riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) at `507a75d91d`. All paths below are relative to
`src/Development/AbelianVarietyTheory/Proofs/` unless they start with `src/`. Nothing was built. Every
statement below comes from reading source text, not from `#print axioms`.

## 1. Scope and method

- **Size.** 78,548 `.lean` files and 6.56M lines, in 36 flat sub-directories (no nesting below
  `Proofs/<Area>/`). The largest: DivisorProofs 29,995 files (2.10M lines), InertiaEigenvalues 8,536,
  IwasawaDecomposition 5,895, TwistedOperators 5,883, DecoratedLatticeProofs 4,576, FlagMeasures 3,918,
  FoundationProofs 3,333, SatakeParameters 3,188, DegenerationProofs 1,544, ModuliProofs 1,486,
  JetHarmonics 1,366, GlobalInterpolation 1,217. The other 24 have between 4 and 844 files each.
  Median file is 2.9 KB, the 90th percentile 12 KB, the largest 214 KB (`DivisorProofs/CoefMapNormEquivariantBasisOfFive.lean`).
- **Soundness grep.** No `sorry`, `axiom`, `opaque`, `native_decide`, `implemented_by` or `extern`
  anywhere in the subtree. Across all of `src/`, the only `sorry` is in `src/Challenge.lean` (the
  challenge stub) and there are no `axiom` declarations. Kernel re-checking was not done.
- **Structure-first pass.**
  1. I extracted every closed `def X : Prop` in the sibling dirs `../PublishedTheorems` (391) and `../Statements`
     (210). Then I matched them against every closed `theorem t : X` in `src/` (48,890 candidate lines).
     Result: 290 of the 601 are discharged somewhere, 172 of them inside `Proofs/`.
     The other discharges are mostly in `src/Development/WeilBound/CoreStatements` (72),
     `src/Development/AutomorphicSpectrum/Proofs` (29) and `.../AutomorphicArithmetic/Foundations` (25).
  2. I read the discharging theorem line for all 172 and the `Prop` definition for about 35 of them.
  3. I counted import fan-in, both inside and outside the subtree.
  4. A script flagged theorems whose statement mentions no identifier the repo itself defines. That
     gives 15,650 candidates, 657 of them closed `GlobalTheory.T.*` statements. I read the names of all
     657 and the statement text of about 120.
  5. I read in full, or nearly in full, the statements in about 45 files: all the analytic number
     theory in GlobalInterpolation, HomogeneousIdeals and IwasawaDecomposition, the Chebotarev chain,
     Brauer, Hasse norm, and the abelian-scheme laws. I also opened the definitions they rest on:
     `IsAbelianScheme`, `PolAV`, `LB`, `IsFrob`, `Ine`, `IsGlobalArtin`, `PrimesRel`, `LFam`, `D7`, `Host`.
  6. I sampled six random leaves from each of the four largest dirs.
- **Skipped.** I did not read proofs, only statements. I did not follow most `Published.*` `Prop`s
  for automorphic and p-adic Hodge objects (CuspSub, SmIrr, WD, LocPrime, FCrys, ...) down to their
  definitions, so faithfulness there is unverified (section 7).

## 2. What this subtree actually is

The directory name is misleading. This is not an abelian-variety library in any focused sense. It is
the main **proof bank** of the whole development: 11,464 files outside the subtree import
`Proofs.DivisorProofs`, about 5,000 each import InertiaEigenvalues, IwasawaDecomposition and
TwistedOperators, and the heaviest importers are `AutomorphicSpectrum/Proofs`,
`AutomorphicArithmetic/ThetaCorrespondence` and `WeilBound/CoreStatements`. Four kinds of content sit
side by side:

- **(i) Analytic number theory for Mathlib's Dirichlet L-functions** (GlobalInterpolation,
  HomogeneousIdeals, parts of IwasawaDecomposition and FoundationProofs). This is a near-complete
  Linnik-theorem toolkit: zero-free regions with an exceptional zero, Deuring–Heilbronn repulsion,
  log-free zero density, the multiplicative and hybrid large sieve, Turán's power-sum theorem, the
  truncated explicit formula, Brun–Titchmarsh, and the prime number theorem in progressions with
  relative error (Gallagher form). It feeds `UpperTheory.Lit.linnik : GlobalTheory.Published.Linnik`
  (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/Linnik.lean:146`), which is Linnik's
  theorem `p(a,q) ≤ C q^L`, unconditional. The same area also has the class number formula, the
  Kronecker limit formula and Chowla–Selberg for imaginary quadratic fields, stated on Mathlib's
  `dedekindZeta`, `LFunction` and `ModularForm.eta`.
- **(ii) Algebraic number theory and class field theory on Mathlib objects.** Chebotarev in
  existence form, the Hasse norm theorem for cyclic extensions, Brauer's induction theorem, Chevalley's
  theorem on units, and a long tail of commutative algebra and adelic lemmas.
- **(iii) A from-scratch theory of abelian schemes over Mathlib `Scheme`s.** Line bundles are Čech
  cocycles. `IsAbelianScheme` means a commutative group object that is smooth, proper and geometrically
  connected. `PolAV` adds a symmetric, rigidified, relatively ample bundle with `K(L)` trivial. On top of
  that the subtree proves 24 "laws": rigidity, cube, square, `[n]` finite flat with `#A[n] = n^{2g}`,
  Weil pairing, and so on. It also proves the dual abelian scheme with biduality, semistable reduction
  for principally polarised abelian varieties over p-adic fields, de Rham and crystalline structure,
  Grothendieck–Messing-type lifting, formal GAGA, and toroidal compactification.
- **(iv) The proof-specific core.** 17,156 files (22%) mention the bespoke data bundle `D7`, and 4,703
  mention `Geo.Tor.Host`/`Datum`. These are CM-field hosts carrying hard-coded prime and size
  conditions, used for theta lifts, Fock spaces, Bessel models, Hermitian lattice counts and Satake
  parameters for unitary groups. Nothing here is reusable outside the RH argument.

Names are frequently obfuscated or misleading. `abelian₂ n` is the von Mangoldt function
(`src/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FiltrationCocycleLiftCriterion.lean:14`).
The Linnik toolkit sits in a dir called `GlobalInterpolation`. Mertens' estimate sits in
`IwasawaDecomposition`. The files named `Imports*.lean` (162 of them) are ordinary leaves, not
aggregators. The subtree has no aggregator file at all.

## 3. Inventory (most reusable first)

"Mathlib" means the statement mentions only Mathlib objects; "internal" means it relies on repo
definitions, with a verdict on those. All of these are closed theorems with no hypotheses unless the
statement says otherwise.

### 3a. Analytic number theory (Dirichlet L-functions, primes)

| Declaration | path:line | Statement (paraphrased) | Objects | Classical name | Reusability |
|---|---|---|---|---|---|
| `GlobalTheory.Lin.primesRel_holds` (re-stated as `GlobalTheory.T.primesInProgressions_relativeError`) | `GlobalInterpolation/PrimesInProgressionsRelativeError.lean:27` | There are constants `c₁ ≤ 1/8, c₂, c₃, C_A, c_S > 0` such that for every `M ≥ 3`: (a) at most one "exceptional" real χ mod M has a real zero β > 1 − c₁/log M of its primitive L-function, and that zero is unique; (b) such a β satisfies `1 − β ≥ c_S/(M² log M)`; (c) for `(b,M)=1` and `X ≥ M^{c₂}`, `φ(M)·#{p ≤ X, p ≡ b (M)} = (Li X − θ Li X^β)(1 + O(exp(−c₃ log X/log M) + exp(−√(c₃ log X))))`, with θ = χ(b) ∈ {±1} or 0 | Mathlib (`LFunction`, `primitiveCharacter`, `Nat.Prime`); `PrimesRel` at `../Definitions/GlobalTwisting/ZerosDisc.lean:39` is faithful | Gallagher's PNT in progressions with the Siegel–Landau exceptional term; Linnik's main lemma | **High**. Fully explicit-form statement on standard objects; gives Linnik's theorem |
| `GlobalTheory.T.chebyshevPsiProgression_relative_error` | `GlobalInterpolation/ChebyshevPsiProgressionRelativeErrorStatement.lean:12` | The same as above for ψ(u; M, b) = Σ_{n≤u, n≡b} Λ(n): `|φ(M) ψ − (u − θ u^β/β)| ≤ C(...)·(u − θ u^β/β)` for u ≥ M^{c₂} | Mathlib (`psiAP` is a plain sum of `Λ`) | Gallagher, ψ form | High |
| `GlobalTheory.ZeroFreeComplex.zero_free_region` | `GlobalInterpolation/LFunctionConjEqZero.lean:294` | There is c > 0 such that for every q, every χ ≠ 1 mod q, and every zero s of `LFunction χ` that is not a real zero of a real χ: `Re s < 1 − c/log(q(|Im s|+2))` | Mathlib | de la Vallée Poussin zero-free region for L(s,χ) | **High** |
| `GlobalTheory.ZeroFreePrincipal.zero_free` | `GlobalInterpolation/ZeroFreePrincipal.lean:286` | The same region for the principal character mod q (all zeros except s = 1) | Mathlib | de la Vallée Poussin for ζ times finitely many Euler factors | High |
| `GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion` | `GlobalInterpolation/ExceptionalDirichletZeroUniqueZeroFreeRegionStatement.lean:12` | For small c₁: for M ≥ 3, the exceptional pair (χ, β) is unique; it has χ ≠ 1, β ≥ 7/8, β a simple zero and `1 − β ≥ c/(M² log M)`; every other zero ρ with Re ρ < 1 has `Re ρ ≤ 1 − c/log(M(|Im ρ|+2))` | Mathlib + `IsExc` (faithful) | Landau–Page, with an effective (weak) lower bound for 1 − β | High |
| `GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion` | `GlobalInterpolation/RepulsionStatement.lean:12` | If χ₁ is real with L(β, χ₁) = 0 for some 1/2 ≤ β < 1, then every other zero ρ of any L(s, χ) mod q in the strip satisfies `1 − Re ρ ≥ c·log(c/((1−β)L))/L` with L ≥ log(q(\|Im ρ\|+2)) | Mathlib | Deuring–Heilbronn phenomenon | **High** |
| `GlobalTheory.Lin.LogFree.zero_density` | `GlobalInterpolation/LogFreeZeroDensityDirichletOneModulus.lean:327` | For one modulus q: `Σ_χ N(σ, T, χ) ≤ C (qT)^{A(1−σ)}` for σ ≥ 1 − η and T ≥ 2, zeros counted with multiplicity | Mathlib (`zerosBox` and `ord` are faithful) | Log-free zero density (Linnik, Gallagher) | High |
| `GlobalTheory.ZeroDensityMult.zero_density_mult` | `GlobalInterpolation/ReLtOneOfZero.lean:42` | Over all primitive χ of conductor ≤ Q, zeros with Re ρ ≥ 1 − 1/400 and \|Im ρ\| ≤ Q number at most C Q^{1/4} with multiplicity | Mathlib | Zero density near 1 over moduli (a weak Jutila-type bound) | Med-high |
| `GlobalTheory.MultSieve.multiplicative_large_sieve` | `GlobalInterpolation/MultiplicativeLargeSieve.lean:148` | `Σ_{q≤Q} Σ*_{χ mod q} \|Σ_{M<n≤M+N} a_n χ(n)\|² ≤ (Q² + 2πN) Σ \|a_n\|²` | Mathlib | Multiplicative large sieve (Bombieri, Davenport–Halberstam constant) | **High** |
| `GlobalTheory.HybridLargeSieve.hybrid_large_sieve` | `GlobalInterpolation/HybridLargeSieve.lean:131` | `Σ_q Σ*_χ ∫_{−T}^{T} \|Σ a_n χ(n) n^{−it}\|² dt ≤ C Σ (Q²T + n)\|a_n\|²` | Mathlib | Gallagher's hybrid large sieve | High |
| `GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime` | `GlobalInterpolation/ArithmeticLargeSieveOneResidueClassPerPrimeStatement.lean:10` | If S ⊆ (M, M+N] avoids one residue class mod every prime p ≤ Q with p ∤ q, then `\|S\|·(φ(q)/q)·log Q ≤ Q² + 2πN` | Mathlib | Arithmetic large sieve (a special form) | Med-high |
| `GlobalTheory.Lin.brun_titchmarsh_const` | `GlobalInterpolation/BrunTitchmarshExistsConst.lean:53` | `#{x < p ≤ x+y : p ≡ a (q)} ≤ C y/(φ(q) log(y/q))` for (a,q) = 1 and y ≥ 2q | Mathlib (`primesIoc` is a plain filter) | Brun–Titchmarsh (unspecified C) | **High** |
| `GlobalTheory.powerSum_second_main` | `GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean:210` | There is C ≥ 1 such that for z : Fin N → ℂ and any i₀ there is k ∈ [M+1, M+N] with `(N/(C(M+N)))^N \|z_{i₀}\|^k ≤ \|Σ z_i^k\|` | Mathlib (pure ℂ) | Turán's second main theorem | **High** (pure analysis) |
| `GlobalTheory.ExplicitFormula.truncated_explicit_formula` | `GlobalInterpolation/TruncatedExplicitFormula.lean:16` | For primitive χ mod N and 2 ≤ T ≤ u: ψ₀(u, χ) + Σ_{\|γ\|<T} m_ρ u^ρ/ρ is bounded by `C(u log²(Nut)/T + log(Nu) + Σ_{\|γ\|<1} m_ρ/\|ρ\|)`; the zero set is finite | Mathlib (`psi0` is Σ Λ(n)χ(n) − [χ=1]u) | Truncated explicit formula (Davenport ch. 19) | **High** |
| `GlobalTheory.T.explicit_formula_dirichlet_zeros_right_half` | `GlobalInterpolation/ExplicitFormulaDirichletZerosRightHalfStatement.lean:12` | The same for any χ mod q, summing only zeros with Re ρ ≥ 1/2; error `C(u/T + √u q³) log²(quT)` | Mathlib | Explicit formula, crude version | Med-high |
| `GlobalTheory.T.dirichletL_few_zeros_small_disc` | `GlobalInterpolation/DirichletLFewZerosSmallDiscStatement.lean:12` | The zeros of L(s, χ) in the disc \|s − (1+it)\| ≤ r ≤ 1/2 number at most C(1 + r log(q(\|t\|+2))) | Mathlib | Local zero count near Re s = 1 | Med |
| `GlobalTheory.Mem.An.zeroCount_holds` | `GlobalInterpolation/ZeroCountHolds.lean:11` | For primitive χ: #{ρ : \|Im ρ − t\| ≤ 1} ≪ log(q(\|t\|+2)), with multiplicity | Mathlib (`zsumR`/`zerosIn` faithful) | N(T+1) − N(T) ≪ log qT | High |
| `GlobalTheory.LogDerOneProof.logDerOne_holds` | `DivisorProofs/LogDerOneHolds.lean:15` | For primitive χ mod q > 1: `\|L'/L(1,χ) − Σ_{\|Im ρ\|≤1} 1/(1−ρ)\| ≤ C log 3q` | Mathlib | Partial-fraction bound for L'/L at 1 | Med |
| `GlobalTheory.LFunction_zero_of_re_nonpos` (namespace `GlobalTheory`) | `GlobalInterpolation/CompletedLFunctionNeZeroOfReNonpos.lean:90` | For primitive χ, a zero with Re s ≤ 0 is a simple trivial zero s = −n; s = 0 forces χ even and nontrivial; s = −1 forces χ odd. Also `completedLFunction_ne_zero_of_re_nonpos` (line 70) | Mathlib | Trivial zeros of L(s, χ) | **High** (an obvious Mathlib gap) |
| `GlobalTheory.LOneLower.inv_le_norm_LFunction_one` | `GlobalInterpolation/ExistsLeNormLFunctionOne.lean:344` | For real χ ≠ 1 mod q: `\|L(1,χ)\| ≥ 1/(36q)` | Mathlib | Effective (weak) lower bound for L(1,χ) | Med-high |
| `GlobalTheory.Mem.An.sum_vonMangoldt_le_two_mul` / `GlobalTheory.mertens_first_vonMangoldt` | `IwasawaDecomposition/SumVonMangoldtLeTwoMul.lean:74`, `IwasawaDecomposition/LogFactorialEqSumVonMangoldtMulDiv.lean:64` | ψ(y) ≤ 2y; and \|Σ_{n≤y} Λ(n)/n − log y\| ≤ C | Mathlib | Chebyshev bound; Mertens' first theorem | Med (Mathlib may already have them) |
| `GlobalTheory.T.norm_riemannZeta_sub_partial_sum_le` | `GlobalInterpolation/NormRiemannZetaSubPartialSumLeStatement.lean:10` | For Re s > 0, s ≠ 1: `\|ζ(s) − Σ_{n≤M} n^{−s} − M^{1−s}/(s−1)\| ≤ (\|s\|/Re s) M^{−Re s}` | Mathlib | Approximate formula for ζ | Med-high |
| `GlobalTheory.T.not_summable_inv_primes_congr_neg_one` | `FoundationProofs/NotSummableInvPrimesCongrNegOneStatement.lean:14` | Σ 1/p over primes p ≡ −1 (mod M) diverges | Mathlib | Dirichlet (one class) | Low (Mathlib has Dirichlet's theorem) |
| `GlobalTheory.Hk.normPrimes_short_interval_lower` | `GlobalInterpolation/NormPrimesImagQuadShortIntervalLowerBound.lean:103` | For d ≡ 3 (mod 4) prime ≥ 100 and M ≥ 3: primes p ∈ [X, X(1+h)] with 4p = A² + dB², M \| B and 2M \| A − 2 − B number at least `c' h X/((4dM²)^A log X)` whenever h ≥ exp(−c√log X) and log(4dM²) ≤ c√log X | Mathlib (`NormOne` at `../Definitions/Foundations/RayPrimes.lean:44` is explicit) | Primes in a ray class of Q(√−d) in short intervals | Med-high |
| `GlobalTheory.Hk.ShortInt.trivialClass_shortInterval` | `GlobalInterpolation/TrivialClassShortInterval.lean:223` | The same lower bound for an abstract `LFam` | Internal `LFam` (an axiomatised family of counting functions; the structure fields are the hypotheses) | Short-interval PNT for Hecke families | Low-med (you must supply an `LFam`) |
| `GlobalTheory.T.rayClassLFunction_zero_free_region` and related `LFam` results | `GlobalInterpolation/RayClassLFunctionZeroFreeRegionStatement.lean:12`, `...FamilyContinuationGrowthStatement.lean:12` | Zero-free region, continuation to Re s > 1/2 and growth for the L-functions of an `LFam` | Internal `LFam` | Hecke L zero-free region, axiomatic | Low-med |

### 3b. Quadratic fields, class numbers, modular functions

| Declaration | path:line | Statement | Objects | Classical name | Reusability |
|---|---|---|---|---|---|
| `GlobalTheory.QuadraticZeta.dedekindZeta_eq_mul_LFunction` | `HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean:506` | K imaginary quadratic with discr −d and χ its Kronecker character: ζ_K(s) = ζ(s) L(s, χ) for Re s > 1 | Mathlib (`dedekindZeta`, `riemannZeta`); `IsKroneckerChar` is internal, and existence is proved for d ≡ 0, 3 (mod 4) (`exists_isKroneckerChar`, line 458) | Factorisation of ζ_K | **High** |
| `GlobalTheory.QuadraticZeta.idealCount_eq_sum` | same file `:358` | #{ideals of norm m} = Σ_{e\|m} χ(e) | Mathlib | Ideal counts in quadratic fields | High |
| `GlobalTheory.QuadraticZeta.LFunction_one_and_mean_log_eta` | `HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean:121` | For d > 4: L(1, χ) = πh/√d, and the class average of log(Im τ_c · \|η(τ_c)\|⁴) = γ − log(2√d) − L'/L(1, χ) | Mathlib (`ModularForm.eta`, `classNumber`); `IsIdealClassPoint` is internal (class representatives in ℍ) | Dirichlet class number formula (imaginary quadratic) + Kronecker limit formula | **High** |
| `GlobalTheory.QuadraticZeta.chowla_selberg_eta`, `chowla_selberg_discriminant` | same file `:221`, `:258` | Chowla–Selberg in η form and in Δ = g₂³ − 27g₃² form | Mathlib + internal `PeriodPair` (a lattice with g₂, g₃; looks faithful) | Chowla–Selberg formula | Med-high |
| `GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two` | `GlobalInterpolation/ClassNumberLeAbsDiscrOfFinrankEqTwo.lean:14` | Quadratic K: h_K ≤ \|d_K\| | Mathlib | Trivial class number bound | Low-med |
| `GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow'` | `FlagMeasures/ClassNumberMulRegulatorLeSqrtDiscrRpowStatement.lean:11` | K totally complex, s > 1: h_K R_K ≤ \|d_K\|^{s/2} (s/(s−1))^{[K:ℚ]} | Mathlib | Siegel–Brauer-type upper bound | Med-high |
| `GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound` | `FlagMeasures/SumAbsNormRpowNegLeDedekindZetaBoundStatement.lean:11` | Σ_{I∈S} N(I)^{−s} ≤ (s/(s−1))^{[K:ℚ]} for any finite set S of nonzero ideals | Mathlib | ζ_K(s) ≤ ζ(s)^n-type bound | Med |
| `GlobalTheory.WeberProduct.weber_prod`, `eta_relation` | `GlobalInterpolation/WeberFunctionProductEqSqrtTwo.lean:100`, `:72` | f·f₁·f₂ = √2 for Weber's functions; the η-quotient identity behind it | Mathlib `ModularForm.eta` plus internal Weber defs | Weber's identity | Med |
| `GlobalTheory.T.jacobi_triple_product_limit` | `GlobalInterpolation/JacobiTripleProductLimitStatement.lean:12` | Truncated sums of Mathlib's `jacobiTheta₂_term` times finite q-Pochhammer coefficients tend to θ(z, τ)/(q²; q²)_∞ | Mathlib `jacobiTheta₂` + internal `finCoeff`/`qPochInf` | Jacobi triple product | Med (internal coefficients) |

### 3c. Algebraic number theory, class field theory, groups

| Declaration | path:line | Statement | Objects | Classical name | Reusability |
|---|---|---|---|---|---|
| `GlobalTheory.Published.chebotarevDegreeOne'` | `InertiaEigenvalues/ChebotarevDegreeOne.lean:21` | F a number field, L/F finite Galois inside an algebraic closure Ω, g ∈ Gal(L/F), S a finite set of primes. Then there is a prime v ∉ S of residue degree 1 over ℚ, unramified in L (inertia fixes L), with a Frobenius σ ∈ Gal(Ω/F) at a place above v that restricts to g | Mathlib + `IsFrob`, `Ine`, `IsPlaceOver` (`src/Formalism/ConjugateSelfDual/Statement.lean:33`, `src/ReciprocityTheory/GaloisValuations/Global.lean:49`), all faithful | Chebotarev density theorem, qualitative form (every class is Frobenius infinitely often), via Deuring's reduction to cyclotomic fields | **High** |
| `GlobalTheory.T.exists_prime_absNorm_eq_of_irreducible_cyclotomic'` | `InertiaEigenvalues/ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement.lean:13` | K a number field, m prime, Φ_m irreducible over K, τ ∈ (ℤ/m)ˣ: infinitely many primes P of K with N(P) prime and N(P) ≡ τ (mod m) | Mathlib | Dirichlet for number fields (degree-one primes in a class) | High |
| `GlobalTheory.BrauerZero.brauerDegreeZero` | `InertiaEigenvalues/BrauerDegreeZero.lean:207` | G finite, ρ a finite-dim complex representation: χ_ρ − dim ρ is a ℤ-combination of Ind_H^G(λ) − Ind_H^G(1) for linear characters λ of subgroups H | Mathlib `Representation`; `indFun` is internal and looks faithful | Brauer's induction theorem (degree-zero form) | **High** |
| `GlobalTheory.CNorm.hasseNorm` | `AdelicLatticeProofs/ExistsIsRealEmbeddingEqHom.lean:29` | L/K cyclic extension of number fields. If a ∈ Kˣ is a local norm at every finite and infinite place, then a = N_{L/K}(x) | Mathlib (adic completions, `InfinitePlace.Completion`, `Algebra.norm`) | Hasse norm theorem | **High** |
| `GlobalTheory.T.hasse_norm_theorem_quadratic_extension` | `AdelicLatticeProofs/HasseNormTheoremQuadraticExtensionStatement.lean:16` | x is of the form a² − δb² over F iff it is so at every real place and every finite completion | Mathlib | Hasse norm theorem, quadratic case | High |
| `GlobalTheory.Published.chevalleyUnits'` | `InertiaEigenvalues/ChevalleyUnits.lean:178` | For m, b > 0 there is a > 0 coprime to b such that every unit u ≡ 1 (mod a) is an m-th power of a unit | Mathlib | Chevalley's theorem on units | High |
| `GlobalTheory.globalArtinReciprocity_holds` | `IwasawaDecomposition/GlobalArtinReciprocityHolds.lean:9` | There is an open quotient map art: 𝔸_Eˣ → Gal(Ω/E)^{ab} with kernel the closure of Eˣ · (𝔸_∞ˣ)⁰, compatible with inertia, Frobenius and decomposition groups | Mathlib + internal `IsGlobalArtin` (faithful) | Global Artin reciprocity | **High**, but only re-exported here: the proof is `CompanionTheory.FamInh.globalArtin` (`src/CompanionTheory/AutomorphicTheory/PlaceSeparation/IsOpenQuotientMapArt0.lean:237`, built on `src/GroundTheory/GlobalFields/...`) |
| `GlobalTheory.T.exists_compact_adeleRing_mod_numberField` | `HeightProofs/ExistsCompactAdeleRingModNumberFieldStatement.lean:10` | 𝔸_F = F + K for some compact K | Mathlib | Compactness of 𝔸_F/F | Med-high |
| `GlobalTheory.T.finiteAdele_strong_approximation_mod_nat` | `UnitaryExistence/FiniteAdeleStrongApproximationModNatStatement.lean:12` | Every finite adele is x + N·a with x ∈ F and a integral; an integral finite adele is x + N·a with x ∈ 𝓞_F | Mathlib | Strong approximation (additive) | Med |
| `GlobalTheory.T.exists_approx_finite_places_numberField` | `IwasawaDecomposition/ExistsApproxFinitePlacesNumberFieldStatement.lean:10` | Simultaneous approximation at finitely many distinct finite places, to within v(c) | Mathlib | Weak approximation | Med |
| `GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le` | `DivisorProofs/CardAlgebraicIntegersBoundedArchimedeanLeStatement.lean:14` | #{ξ ∈ 𝓞_E : \|ξ\|_w ≤ T for all w} ≤ C T^m | Mathlib | Northcott-type count | Med |
| `GlobalTheory.T.card_divisors_le_absNorm_numberField` | `DivisorProofs/CardDivisorsLeAbsNormNumberFieldStatement.lean:13` | The number of ideal divisors of I ≠ 0 is at most N(I) | Mathlib | — | Low-med |
| `GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval` / `..._sq_dvd_eval_of_separable` | `DivisorProofs/ExistsLargePrimeDvdIntPolynomialEvalStatement.lean:10`, `DivisorProofs/SepIntPolyRootModPrimeSqStatement.lean:10` | A nonconstant f ∈ ℤ[X] has arbitrarily large prime divisors of its values; if f is separable over ℚ, arbitrarily large p with p² \| f(x) for some x | Mathlib | Schur's theorem, and a Hensel strengthening | **High** (small, clean) |
| `GlobalTheory.T.classGroup_dedekind_algClosed_divisible` | `DivisorProofs/ClassGroupDedekindAlgClosedDivisibleStatement.lean:10` | A finite-type Dedekind domain over an algebraically closed k has a q-divisible class group when q ≠ 0 in k | Mathlib | Divisibility of Pic of an affine curve | Med |
| `GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime` | `GlobalInterpolation/QuadraticAtMostTwoPrimesOverStatement.lean:10` | At most two primes of a quadratic field lie over q | Mathlib | — | Low |
| `GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful` | `FoundationProofs/ExistsLagrangeResolventOfPGroupFaithfulStatement.lean:12` | A nontrivial p-group acting faithfully on L and fixing a primitive p-th root ζ has σ and α ≠ 0 with σα = ζα and α^p invariant | Mathlib | Kummer / Lagrange resolvent | Med |
| `GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField` | `CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement.lean:12` | There is a multiplicative map F̄_qˣ → ℂ that is injective on nonzero elements | Mathlib | Teichmüller lift | Med |
| `GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus` | `TwistedOperators/MatrixConjTransposeBySymmetricTausskyZassenhausStatement.lean:9` | Every square matrix over a field is similar to its transpose via an invertible symmetric P | Mathlib | Taussky–Zassenhaus | Med-high |
| `GlobalTheory.DefiniteQuotient.exists_bound_unitary` | `DivisorProofs/ExistsBoundUnitary.lean:18` | If G is positive definite, the group {g : g*Gg = G} has uniformly bounded entries | Mathlib | Compactness of U(G) | Med |
| `GlobalTheory.T.isRegularLocalRing_adicCompletion'` | `IwasawaDecomposition/IsRegularLocalRingAdicCompletionStatement.lean:10` | The completion of a regular local ring is regular | Mathlib (`IsRegularLocalRing`) | Standard | Med (possibly a Mathlib gap) |
| `GlobalTheory.T.lattice_sum_dilate_haar_asymptotic` | `AdelicLatticeProofs/LatticeSumDilateHaarAsymptoticStatement.lean:11` | f smooth with compact support, L a ℤ-lattice: Σ_l f(t(l + x₀)) = ∫f/(covol(L) tⁿ) + O(t^A) for every A | Mathlib | Poisson / Riemann-sum asymptotic | Med |
| `GlobalTheory.T.legendre_bounds_factorial_multiIndex_capelli` | `UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelliStatement.lean:13` | Explicit two-sided Legendre bounds for v_l(N!) and for multinomial products | Mathlib | Legendre's formula | Low-med |
| `GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity`, `global_positivity_ineq_multiplicative_coeff` | `FoundationProofs/LseriesNeZeroReGeOneOfPositivityStatement.lean:14`, `FoundationProofs/GlobalPositivityIneqMultiplicativeCoeffStatement.lean:14` | Nonvanishing on Re s ≥ 1 for a multiplicative degree-2 Euler-product L-series with a positivity input and an entire continuation Λ | Mathlib `LSeries` (hypotheses are explicit) | Mertens/de la Vallée Poussin positivity argument for GL₂ | Med |

### 3d. Abelian schemes (internal but faithful definitions over Mathlib schemes)

| Declaration | path:line | Statement | Objects | Classical name | Reusability |
|---|---|---|---|---|---|
| `GlobalTheory.abelianSchemeLaws_all : Out.Laws ∧ Out.Laws2` | `AbelianSchemeLawProofs/AbelianSchemeLawsUnconditional.lean:19` | A bundle of 24 theorems on principally polarised abelian schemes `PolAV S` over locally Noetherian S: global sections of L^n have rank n^g; L^n is very ample for n ≥ 4; `[n]` is finite, flat and surjective, étale when n is invertible, with #A[n](k) = n^{2g}; cube and square theorems; rigidity; Weil pairing existence, bilinearity and nondegeneracy; Néron-type extension laws; and more. Field list at `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/GlobalSectionsRankAlgClosed.lean:191` | Internal: `IsAbelianScheme` (commutative group object, smooth, proper, geometrically connected; faithful), `LB` (Čech cocycle line bundle; faithful), `PolAV` (`.../ExtensionDescent/NonzeroLocus.lean:63`; faithful) | Mumford, *Abelian Varieties*, §§ 6–8, 16, 20, 23 | **High in content, med in practice**: a self-contained theory, but on a bespoke `LB` and not on Mathlib's `Pic` |
| `GlobalTheory.abMulN_holds` | `CoherentCohomologyProofs/AbelianVarietyTorsionCardEqPowProof.lean:23` | A over k = k̄, smooth of relative dimension g, n ≠ 0 in k: #A[n](k) = n^{2g} | Same | Structure of A[n] | High (same caveat) |
| `GlobalTheory.CubeTop.cubeTheorem` | `DivisorProofs/TheoremOfCubeAbelianSchemeOverArbitraryBase.lean:9` | Theorem of the cube for any line bundle on an abelian scheme over any base scheme | Same | Theorem of the cube | High (same caveat); re-exports `SpreadingModels.cubeTheorem_holds` |
| `GlobalTheory.dualAbelianScheme` | `DivisorProofs/DualAbelianSchemeExistsBiduality.lean:34` | Every abelian scheme A/S, over **any** S, has a dual abelian scheme B with a Poincaré bundle that is universal for additive bundles, plus biduality | Same | Dual abelian scheme | High if true. **Check this.** Over a general base the dual is in general only an algebraic space (Raynaud), so either the universal property here is weaker than the classical one or the claim is very strong. Not resolved |
| `GlobalTheory.SS.semistableReductionSt` | `DegenerationProofs/SemistableReductionPpavPadicField.lean:24` | A ppav over a finite K/ℚ_p acquires semiabelian reduction over the integral closure in some finite K'/K | Same + `IsSemiAbelian` | Grothendieck's semistable reduction theorem (p-adic, polarised) | High (same caveat) |
| `GlobalTheory.identityComponentOpen` | `DivisorProofs/UnitMemIdentityComponents.lean:29` | A smooth group scheme over any S has an open subgroup scheme G⁰ given by fibrewise identity components | Mathlib schemes + `GrpObj` | SGA 3 VI_B 3.10 | Med-high |
| `GlobalTheory.T.cmCurveGoodOutsidePrime` (`CMCurveGoodOutsidePrimeSt`) | `DivisorProofs/CmCurveGoodOutsidePrime.lean:51` | For p ≡ 3 (mod 4), p > 3: a CM elliptic curve over a number field inside ℂ, good outside p, with minimal discriminant −p³ | Mathlib `WeierstrassCurve` + internal `IsGoodCMCurve` | Gross's curves A(p) | Med |
| `weierstrassP_torsion_mem_and_distinct_mod_nonunits`, `weierstrassP_mul_congr_frobenius_of_primeNorm` | `HeightProofs/TorsionIntegralDistinctOfPosStatement.lean:13`, `HeightProofs/WeierstrassPMulCongrFrobeniusOfPrimeNormStatement.lean:13` | Integrality and distinctness of ℘ at m-torsion modulo a valuation ring of good reduction; a Frobenius congruence ℘(αt) ≡ a℘(t)^p for CM α of norm p | Internal `PeriodPair` (lattice with g₂, g₃) | Classical CM congruences (Deuring) | Med |

### 3e. Representation-theoretic and p-adic "published theorems" discharged here

These are faithful only if their repo definitions (CuspSub, SmIrr, WD, FCrys, LocPrime, ...) are. I did
not audit those (section 7). Rough list, with discharge sites from section 1:

- **Local Langlands and Bernstein–Zelevinsky for GL_n**: `LanglandsExhaustionGL`, `LanglandsMultisegments`,
  `SegmentRepresentation`, `StandardCosocleGL`, `GrothendieckRingPolynomial`, `ZelevinskyPolynomialRing`,
  `GeometricLemma`, `BernsteinZelevinskyFiniteness`. All are in `InertiaEigenvalues/*` and most are
  re-exports from `src/CompanionTheory/...`.
- **Global GL_n and unitary groups**: `JacquetShalikaRigidity` (`InertiaEigenvalues/JacquetShalikaRigidityHolds.lean:254`,
  strong multiplicity one), `CuspFormsBoundedGL`, `CuspRapidDecay`, `AutomorphicFormsFiniteGL`,
  `HeckeLEntireAndNonzeroAtOne` (`TwistedOperators/HeckeLEntireAndNonzeroAtOneHolds.lean:116`). The last one
  says a unitary Hecke character χ, not of the form \|·\|^{it}, has entire L-function, and L(1, χ) ≠ 0 for χ ≠ 1.
  The idele-class `HChar` it uses is internal.
- **Real groups**: HC modules, K-finite vectors and infinitesimal equivalence for U(p,q); holomorphic discrete series;
  the metaplectic and Weil representations; Howe duality for real and GL dual pairs; Kudla splitting;
  Weil–Eisenstein–Siegel convergence.
- **p-adic Hodge theory**: `BhattScholzeIntegral`, `FontaineBcris`, `DeRhamPotSemistable`, `LocalArtinExists`
  (local Artin map), `DepthZeroSupport`, `DepthZeroJacquetInjective`.
- **Class field theory**: `QuadraticClassFieldTheory` (`TwistedOperators/EtaProdEqOfEverywhereNormDiv.lean:51`):
  the quadratic Hilbert symbol's local characters, norm theorem, exact sequence and product formula,
  and base change.
- **Lattice volumes**: `MaxMass` (`FlagMeasures/MaximalHermitianLatticeMassRatio.lean:118`), which says the mass of
  a maximal definite Hermitian lattice over a CM field (unramified CM) equals c·λ_max. Also
  `GenLinVolume` and `SameKindIsometric` (Hermitian spaces of the same signature are isometric).

## 4. Internal definitions worth knowing

| Definition | Where | Verdict |
|---|---|---|
| `IsAbelianScheme A` | `src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/AbelianSchemeQuotients/IsAbelianScheme.lean:17` | **Faithful**: a commutative group object in `Over S`, smooth, proper, geometrically connected |
| `LB X`, `LB.IsLB` | `src/ReciprocityTheory/.../CubicalStructures/CubeSymmetricSwapFirst.lean:21` | **Faithful** but bespoke: an open cover with unit transition functions satisfying the cocycle condition. Not Mathlib's `Pic`/`Modules` |
| `PolAV S` | `src/ReciprocityTheory/.../ExtensionDescent/NonzeroLocus.lean:63` | **Faithful**: a principally polarised abelian scheme with rigidified, symmetric, relatively ample L and trivial K(L) |
| `IsFrob`, `Ine`, `Dec`, `IsPlaceOver`, `normV` | `src/Formalism/ConjugateSelfDual/Statement.lean:28-34`, `src/ReciprocityTheory/GaloisValuations/Global.lean`, `src/ReciprocityTheory/NeutralLocalFields/Duality.lean:404` | **Faithful**: valuation-subring definitions of the decomposition group, inertia and arithmetic Frobenius in Gal(Ω/F) |
| `IsGlobalArtin` | `../PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:29` | **Faithful**: an open quotient map with the correct kernel, inertia, Frobenius and decomposition compatibility |
| `GlobalTheory.Lin.PrimesRel`, `IsExc`, `ExcData`, `zerosBox`, `ord`, `psiAP` | `../Definitions/GlobalTwisting/ZerosDisc.lean` | **Faithful**, all on Mathlib's `LFunction` and `Λ`. `Emain θ β X = Li X − θ Li X^β` (`src/Formalism/GL3MeanSquares/SmoothedRemainderRealIntegralFormula.lean:78`) |
| `LFam` | `../Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean:16` | **Axiomatic**: a finite abelian group G with coefficient functions whose fields are the analytic hypotheses (counting asymptotics, theta bound, a convolution identity, positivity). Theorems about `LFam` are conditional on building one. `exists_lFam_normOne_of_mod_four_eq_three` builds one for norm forms of Q(√−d) |
| `D7`, `Host R` | `src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:80`, `src/Formalism/LocalRingCardinality/DataHost.lean:42` | **Proof-specific**: a CM-field host with chosen primes q, d and size constraints (`q ≠ 3`, `o^64 ≤ 2^e`, ...), plus rows, words and divisor data. Theorems over `D7` are useless outside the RH argument. I did not check whether it is inhabited non-degenerately |
| `GlobalTheory.Published.*`, `GlobalTheory.Mem.An.*` | `../PublishedTheorems/**` | Closed `Prop`s naming literature theorems. They are statements, not proofs. Some are discharged (section 1), the rest are not (section 7) |

## 5. Mechanical families

- **Statement wrappers**, 30,612 files (39% of the subtree). Each `<X>Statement.lean` restates a closed
  `theorem _root_.GlobalTheory.T.<x> : <full statement>` and proves it with the same three-way
  `first | exact @<impl> | exact <impl> | (intros; apply <impl> <;> assumption)` (28,552 files use
  exactly this). They are useful: the closed statement is the most readable form of each result.
- **`*Holds` / `*Closed` / `*Outright` discharge files**, 247 files. Each is a one- to five-line proof of a
  `Published.*` or `Statements` `Prop`, often by re-exporting a proof from `src/CompanionTheory` or `src/GroundTheory`.
- **`D7`-indexed construction lemmas**, 17,156 files. These are theta lifts, Fock spaces, Bessel models,
  lattice "rows/columns/tops/windows" and "true chains" for the specific host. Example families:
  `SzRow*` (34 files, GlobalInterpolation), `ExplicitChoice*`, `Level*`, `TrueChain*`, `Twisted*BundlePoints*`.
- **`Geo.Tor.Host`/`Datum`-indexed moduli and toroidal lemmas**, 4,703 files.
- **p-adic period-ring lemmas** (`LocPrime`, `FinExt l`, Breuil, Wach, `Acris`, `BdR`), about 2,120 files, mostly in
  InertiaEigenvalues and IwasawaDecomposition.
- **`Exists*` naming**: 6,544 of the 29,995 DivisorProofs files and 1,479 of the 8,536 InertiaEigenvalues
  files. This is a naming habit, not a family.
- **Generic Mathlib-only helpers**: my heuristic finds about 15,650 theorems whose statements mention no
  repo-defined identifier. Most are small: valuation, completion and adic lemmas, `MvPolynomial`,
  `Finset` sums, matrix identities. The 657 closed `GlobalTheory.T.*` ones are the best mining list
  (section 6). I regenerated them into `pure.tsv` (scratch only), and the script is described in section 1.

## 6. Standalone value

**Proved in usable form, on Mathlib objects** (and unconditional, assuming the build checks):

- The **Linnik package** for Dirichlet L-functions: the classical zero-free region, uniqueness and a
  weak effective bound for the exceptional zero, Deuring–Heilbronn repulsion, log-free zero density,
  the multiplicative and hybrid large sieve, the truncated explicit formula, local zero counts,
  trivial zeros, Brun–Titchmarsh, Turán's second main theorem, and Gallagher's PNT in progressions with
  the exceptional term. Downstream, Linnik's theorem `GlobalTheory.Published.Linnik` is proved in
  `src/Development/AutomorphicArithmetic/ThetaCorrespondence/Linnik.lean:146`, outside this subtree.
  This is the most directly reusable block in the subtree for analytic conjectures (least primes in
  progressions, Bombieri–Vinogradov-style inputs, unconditional versions of GRH consequences).
- **Imaginary quadratic fields**: ζ_K = ζ·L(χ), ideal counts, L(1,χ) = πh/√d, the Kronecker limit formula, Chowla–Selberg.
- **Chebotarev** in existence form, with infinitely many degree-one unramified primes.
  **Hasse norm theorem** for cyclic extensions. **Brauer induction** in its degree-zero form.
  **Chevalley's units theorem**. **Schur's theorem** on prime divisors of polynomial values.
  **Taussky–Zassenhaus**.
- **Global Artin reciprocity** is available (`globalArtinReciprocity_holds`), but its proof lives in
  `src/GroundTheory` and `src/CompanionTheory`. This subtree only re-exports it.

**Proved, but on bespoke definitions** (faithful, not Mathlib API): Mumford-level abelian scheme theory
over Mathlib schemes, i.e. rigidity, cube, #A[n], Weil pairing, ampleness, the dual scheme, and
semistable reduction for p-adic ppav's. Using it means adopting `LB`/`PolAV`.

**Only special or axiomatic forms**:

- Zero-free regions and short-interval prime counts for Hecke L-functions are stated for the abstract
  `LFam`, which is instantiated only for norm forms of Q(√−d) with d ≡ 3 (mod 4) prime.
- `HeckeLEntireAndNonzeroAtOne` uses an internal idele-class character type.
- `ZeroCount` is the near-zero density bound C Q^{1/4} over moduli. It is **not** Jutila's theorem:
  `GlobalTheory.Mem.An.Jutila` exists as a `Prop` but nothing proves it.
- The effective lower bound for L(1,χ) is the weak 1/(36q), not Siegel's theorem. I found no Siegel ineffective bound.

**Misleading names**:

- `AbelianVarietyTheory/Proofs` is mostly not about abelian varieties.
- `GlobalInterpolation` holds analytic number theory. `IwasawaDecomposition` holds Mertens and
  Chebyshev, among much else.
- `abelian₂` is the von Mangoldt function. `Imports*.lean` files are leaves.
- The `PublishedTheorems` folders (`GaloisGeometry₂`, `Landherr₂`, ...) group by an internal chapter, not
  by topic. `AbMulNSt` sits in `Landherr₂`.

## 7. Open questions / not verified

- **Kernel trust.** No build was run, so all of this rests on the sources compiling as committed. The
  sources contain no `sorry` or `axiom`.
- **Undischarged statements.** 311 of the 601 closed `Prop`s have no closed `theorem : X` anywhere. Examples:
  `Jutila`, `ExplZeta`, `ExplChi`, `QuadraticHeckeZeroEstimates`, `PageThm`, `PoitouTateDuality`,
  `ChebotarevOpenNormal`, `LandherrSt`, `RosatiTracePosSt`, `TateCharPolySt`, `WeylIntegrationFormula`.
  They may be discharged with arguments, used only as hypotheses of conditional lemmas, or be dead code.
  I did not trace which of them sit on the path to `riemannHypothesis`. Since `Main.lean` has no
  hypotheses, any that are on the path must be discharged in some form.
- **`dualAbelianScheme` over an arbitrary base** is stronger than I would expect classically. Before
  relying on it, check `IsDual`'s universal property: it quantifies only over additive bundles on
  `A ⊗ T` with T in `Over S`, universe 0.
- **Faithfulness of the automorphic and p-adic definitions** (`CuspSub`, `SmIrr`, `IsRec`, `WD`, `FCrys`,
  `LocPrime`, `IsCrys`, `Weil h`, `IsLocalArtin`, `HChar` from `Formalism.L2.Host`) was not checked. So the
  items in 3e are "named and closed", not "verified faithful".
- **Fully qualified names.** For a few GlobalInterpolation theorems I inferred the name from the file's
  `namespace` line. Confirm with `#check` before importing.
- **Statement sampling.** About 15,000 Mathlib-vocabulary helpers were classified only by name and
  heuristic. There are surely more standalone gems in DivisorProofs and InertiaEigenvalues (commutative
  algebra, adic completions, valuation theory) than the ones listed here.
- **Import cost.** Most of these files import `Mathlib` plus a chain into the repo. I did not measure the
  transitive import closure of, say, `GlobalInterpolation.MultiplicativeLargeSieve`. Some leaves look
  cheap, since they import only `Mathlib` plus one or two repo files.
