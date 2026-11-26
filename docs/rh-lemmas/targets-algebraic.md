# Algebraic-number-theory slice: what the riemann-hypothesis toolkit unlocks

Date 2026-11-24. RH repo at `507a75d91d`; paths are relative to its `src/`. Statements are paraphrased,
nothing is copied. Nothing was built. "Opened" means I read the Lean statement myself; everything else
comes from the inventories in `docs/rh-lemmas/`. formal-conjectures (FC) was read at `main` = `86a2f58a`.
Tiers are those in `AGENTS.md`.

**Caveat that applies to every target.** The inventories record the RH repo as Lean `v4.33.1`
(`module` syntax) and the workspace as `v4.36.0`. Importing needs both the same toolchain and the same
Mathlib `fc4f59e5`, so confirm that before any target below. Every theorem used here also inherits
the untrusted-cache caveat.

## (a) Does the RH repo discharge artin-grh's `DedekindContinuation`?

**Partly. Four of the six fields are supplied. The strip bound is not.**

`DedekindContinuation K` (`artin-grh/Artin/Analytic/Continuation.lean:96`) is `Nonempty
(ContinuationData K)`. That structure bundles:

1. `Z` with `IsDedekindZeta K Z`;
2. an entire `ξ`;
3. `ξ s = s(s−1)·γ_K(s)·Z(s)` for `Re s > 0`, `s ≠ 1`, where
   `γ_K = |d_K|^{s/2} Γ_ℝ^{r₁} Γ_ℂ^{r₂}`;
4. `ξ(1−s) = ξ(s)`;
5. `strip_bound`: `‖ξ s‖ ≤ M(1+‖s‖)²` on `1/2 ≤ Re s ≤ 2`.

What the RH repo has (opened, `GroundTheory/GlobalFields/TateThesis/`):

- `continuedDedekindZeta`, with `continuedDedekindZeta_eq` (equal to Mathlib `dedekindZeta` for
  `Re s > 1`) and `differentiableAt_continuedDedekindZeta` (`s ≠ 1`). Together these give field 1.
  This matches FC's `IsDedekindZeta` exactly (`DedekindZetaContinuation.lean:44–72`).
- `completedDedekindZeta K` is the completed L-function of the trivial Hecke character.
  `gammaFactor_one` gives `Γ_ℝ^{r₁}Γ_ℂ^{r₂}` and `discrNormConductor_one` gives `|discr K|`, so the
  factor is literally artin-grh's `gammaFactorK`. `normalizedDedekindZeta` is defined as
  `|d|^{−s/2}·Γ(...)⁻¹·completed`. That gives field 3 for `Re s > 0` (`DedekindContinuation.lean:31,
  102`).
- `completedDedekindZeta_one_sub` gives `Λ(1−s) = Λ(s)` for `s ≠ 0, 1` (field 4).
  `tendsto_sub_one_mul_completedDedekindZeta_rootNumber` and `tendsto_mul_completedDedekindZeta_zero`
  show the poles at 1 and 0 are simple, so `s(s−1)Λ` has removable singularities (field 2, after a
  `Function.update` and a removable-singularity argument, size S).

**Exact mismatch: field 5.** There is no growth, order or vertical-strip lemma anywhere for
`completedLFunction`, `completedDedekindZeta` or `continuedDedekindZeta`. I grepped `TateThesis/`,
`AnalyticClassNumber/` and every file in the repo that mentions `dedekindZeta` (43 files). The only
growth facts are decay bounds on the theta and test-function side (`TateThetaDecay.exists_decay_bound`,
`TateMain.isBigO_thetaFun_sub`). Those are the inputs a strip bound would need, but no bound is stated.
The `Continuation.lean` docstring already says the same thing.

So the remaining work is to prove that `ξ_K` is `O((1+|s|)²)` on `1/2 ≤ Re s ≤ 2`, from Tate's
integral representation plus those decay lemmas. Effort **M**. Phragmén–Lindelöf does not avoid it,
because it needs an a priori finite-order bound in the strip.

**Payoff.** The `hc` argument disappears. `effectiveKummerChebotarev_of_hooley`
(`Artin/Interfaces.lean:51`) can then be proved, and the FC target
`conditional_artin_primitive_roots.parts.i` in `Artin/Main.lean` is proved with only `HooleyHypothesis`.
That is tier **C** with no H hypothesis left. It does **not** reach tier U: Hooley's fields are
non-abelian for `k ≥ 3` (see (b)).

## (b) GRH for Dedekind zeta of abelian fields

**Not stated anywhere in the repo, but provable from what is there.** The only factorisation of
`dedekindZeta` I found is the imaginary quadratic one:
`GlobalTheory.QuadraticZeta.dedekindZeta_eq_mul_LFunction` (opened,
`Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean:506`).
It takes `finrank = 2`, `discr K = −d` and `IsKroneckerChar χ`, and concludes `ζ_K = ζ·L(χ)` for
`Re s > 1`.

Chebotarev in the repo is proved through prime-ideal zeta sums, not through a factorisation. There is
no Artin formalism and no `ζ_K = ∏ L` anywhere: an `rg` for products of L-functions equal to a zeta
function returned nothing.

**How to prove `DedekindZetaRH K` (FC's `IsDedekindZeta`-quantified form) for every abelian K:**

1. Embed K in `CyclotomicField N ℚ` with `UpperTheory.V.CF.kwHom` (opened,
   `Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/ClassFieldRamification/KwHom.lean:13`).
2. For `Re s > 1`, prove `ζ_K(s) = E(s)·∏_{χ∈X(K)} L(s,χ)`. Here the χ are the Dirichlet characters
   mod N trivial on `Gal(ℚ(ζ_N)/K)`, imprimitive characters allowed, and
   `E(s) = ∏_{p|N}∏_{𝔭|p}(1−N𝔭^{−s})^{−1}`.
   - This needs Euler factors **only at unramified p**: Frobenius of p is p, and
     `∏_{𝔭|p}(1−N𝔭^{−s}) = ∏_χ(1−χ(p)p^{−s})` by character orthogonality.
   - Using imprimitive characters mod N avoids the conductor and inertia bookkeeping at ramified
     primes, because `E` is zero-free and holomorphic on `Re s > 0`.
   - The Euler product of `dedekindZeta` is in the repo (`dedekindZeta_eq_exp`, inventory 05).
3. On `Re s > 1/2`, `s ≠ 1`, any `Z` with `IsDedekindZeta K Z` equals `E·∏L` by the identity theorem,
   and it is nonzero there by `LFunction_ne_zero_of_half_lt_re`. On `0 < Re s < 1/2`, use
   `completedDedekindZeta_one_sub` together with the gamma factors being nonzero.

Missing pieces: the Euler-factor identity, and "Frobenius at p is p" in `ℚ(ζ_N)`
(`GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean` may already have it; not opened).
Effort **M–L**. Result: **ERH for every abelian number field, tier U.** This is a new statement.
FC deliberately leaves ERH out until a continuation of `dedekindZeta` exists
(`Millennium/RiemannHypothesis.lean`, "NOTE: Extended Riemann Hypothesis"). FC's
`IsDedekindZeta`/`DedekindZetaRH` vocabulary already states it correctly.

**What becomes tier U because of it: less than hoped.** Check each case by *where* its GRH input lives:

- **Effective Chebotarev for L/ℚ abelian.** Already pure Dirichlet GRH: it is NEXT_TARGETS #3/#12.
  Nothing new.
- **Effective Chebotarev for abelian L/K with K ≠ ℚ.** Needs Hecke L-functions of K. These are
  Dirichlet L-functions only if L/ℚ is abelian. Not unlocked.
- **Weinberger 1973, Euclidean rings of integers (unit rank ≥ 1).** The input is ERH for Kummer fields
  `K(ζ_m, ε^{1/m})` *(from memory, unverified)*. These are non-abelian over ℚ even for real quadratic
  K. I found no abelian-only subcase. The NEXT_TARGETS rejection stands.
- **Bach's class-group generator bound (`12 log²|d|`).** Needs `L(s,ψ)` for class-group characters ψ
  of K, i.e. `ζ` of the Hilbert class field. H/ℚ is generalised dihedral, so non-abelian. Only the
  genus part `Cl/Cl²` (genus characters are Dirichlet) is unlocked, which is too niche to rank.
- **Class numbers of real cyclotomic fields under GRH (Miller, Math. Comp. 2015; van der Linden).**
  Confirmed by reading arXiv:1407.2373: Odlyzko's bounds are applied to the **Hilbert class field**,
  so the input is ERH for a non-abelian field. Rejected.
- **Artin with abelian Kummer fields.** Only `k ≤ 2`. Hooley needs every squarefree k. Rejected.

So the value of (b) is the ERH-for-abelian-fields theorem itself (rank 4), and the factorisation
step, which feeds Kummer's criterion (rank 5).

## (c) How much of NEXT_TARGETS #1 (Weinberger idoneal / class number one) the lemmas remove

**What the lemmas give:**

- The class number formula for imaginary quadratic **fields**:
  `GlobalTheory.QuadraticZeta.LFunction_one_and_mean_log_eta` (opened,
  `HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean:121`). It says `L(1,χ) = πh/√d` for
  `d > 4`, given `IsKroneckerChar χ`.
- Its class-point hypothesis is discharged by `exists_isIdealClassPoint` (`:80`).
- `exists_isKroneckerChar` for `d ≡ 0, 3 (mod 4)`.
- `idealCount_eq_sum`: the number of ideals of norm m is `Σ_{e|m} χ(e)`. That gives "χ(p) = 1 ⇒ an
  ideal of norm p".
- `dedekindZeta_eq_mul_LFunction`.

All of this removes step 2 of #1, but **for maximal orders only**.

**What is still missing:**

- Genus theory. `rg` finds none: no genus field, no ambiguous classes, no binary-form reduction.
- Class groups of **non-maximal orders**. The discriminant `−4n` of an idoneal number is usually not
  fundamental; Kani's Table 1 lists the order h.
- The order-to-field class number relation.

**Most of #1 does not need the class number formula at all.** This is the main finding of this slice;
it is my own derivation and should be checked before relying on it.

- **Idoneal (FC `Idoneal.idoneal_numbers_completeness`, research open).** FC defines `IsIdoneal n` as
  "n is not ab+bc+ca with 0<a<b<c" (Rains' equivalent form, OEIS A000926).
  - Suppose an odd prime `p ∤ n` has `(−n/p) = 1` and `p² < n`.
  - Take the root `0 < x < p/2` of `x² ≡ −n (mod p)`. Put `a = x`, `b = p−x`,
    `c = (x²+n)/p − x`.
  - Then `ab+bc+ca = n` and `0<a<b<c`. Check: `ab+bc+ca = pC − x²` with `C = (x²+n)/p > p`.
  - So **n is not idoneal as soon as the least prime with `χ_{−4n}(p) = 1` is below `√n`.**
  - Under GRH that prime is `≤ c·log²(4n)`. Hence `√n ≤ c log²(4n)`, which bounds n by roughly `10^6`
    for `c ≈ 4`. A `native_decide` witness check over that range closes it.
  - No class groups, no genus theory and no class number formula are involved.
  - The other direction (the 65 numbers are idoneal) is already proved in FC
    (`knownIdonealNumbers_are_idoneal`).
- **Class number one.** If `h(D) = 1` then every prime `p < |D|/4` is inert, so the least split prime
  `≤ c log²|D|` gives `|D| ≲ 700`. This is the NEXT_TARGETS round-2 remark, made concrete.

**The analytic input still missing for both: an explicit least prime in the kernel of a real character
under GRH.** This is the coset form of ankeny-grh's subgroup bound: weight `(1+χ)` instead of the
characters trivial on H.

- LLS Thm 1.4 (confirmed by reading arXiv:1309.3595) covers cosets including H itself, but it has an
  escape clause "either `p ≤ 10^9` or …". That makes it **unusable** for small thresholds.
- So we need our own Bach-style explicit-formula argument, analogous to ankeny's `21/5`. The RH repo
  contributes only the GRH itself (`LFunction_ne_zero_of_half_lt_re`, `Statements.lean:10`: all χ,
  including imprimitive ones, `Re s > 1/2`), plus the zero-counting and explicit-formula lemmas in
  inventory 02 §3a if needed.

## (d) Known theorems with open formal statements

- **FC `ClassNumberProblem.class_number_problem.variants.imaginary`** (Stark–Heegner, "research
  solved", stated with `AdjoinRoot (X² − C d)`). Reachable at **tier U** via GRH (rank 2). The
  unconditional route would need Heegner/Weber class invariants. The repo has the main theorem of CM,
  `K(j) = H_K`, integrality of singular moduli and Weber's `f·f₁·f₂ = √2`, but not Weber's algebraicity
  of `f(√−m)^k`, so that route is XL.
- **FC `RegularPrimes`** has three statements:
  - `isRegularPrime_iff_Bernoulli` (textbook, Kummer's criterion);
  - `small_regular_primes` (textbook);
  - `infinitude_of_irregularprimes` and `not_isRegularPrime_37`.
  The "p ∤ B_k ⇒ regular" half plus `small_regular_primes` follows from the repo's Stickelberger
  (`UpperTheory.V.Stick.coef`, opened) through Herbrand, plus Kummer reflection for the plus part (rank 5).
  The other half (`p | B_k ⇒ irregular`, used by `not_isRegularPrime_37` and Jensen's infinitude)
  needs the analytic `h⁻` formula: (b)'s factorisation, plus Mathlib's `dedekindZeta_residue`, which
  already contains `classNumber` and `regulator`, plus the unit index. XL.
- **FC `Catalan.catalans_conjecture`**: already has a Lean 4 proof (`formal_proof using lean4`,
  cadamcat/catalan-lean4). Rejected.
- **Kronecker–Weber**: no FC statement; Atlas `wiki-hilbert-s-twelfth-problem` names it. Proved in the
  repo as `UpperTheory.V.CF.kw`, `.kwHom` (opened) and `.kwRam`. Inventory 07 says no global
  Kronecker–Weber exists; that is wrong, it lives in AutomorphicArithmetic. Available by import.
- **Iwasawa μ = 0 for abelian fields** (Ferrero–Washington, `UpperTheory.V.FW.ferreroWashington`): no
  FC statement. Atlas `wiki-greenberg-s-conjectures` and the Iwasawa main conjecture rows are open and
  need far more.
- **Brauer–Hasse–Noether**: only injectivity and `Σ inv = 0` exist, on a cohomological Br that is not
  linked to central simple algebras. **Grunwald–Wang**: absent.
- **Cox, `p = x²+ny²`**: no FC statement. Provable at tier D for `ℤ[√−n]` maximal, from
  `hilbertClassFieldArtinEquiv_mk0` plus Chebotarev (rank 8). Non-maximal n needs ring class fields of
  orders, which are not in the repo.
- **Chebotarev consequences** (Bauer's theorem, density of split primes, primes in every ray class):
  the repo has them (`UpperTheory.V.CF.bauer`, `hasDirichletDensity_setOf_splitsCompletely`,
  `hasDirichletDensity_setOf_map_eq`). There is no FC statement.

## Ranked table

| # | Target | Source + Atlas id / FC file | RH-repo lemmas used (decl, path) | What is still missing | Expected tier | Effort |
|---|---|---|---|---|---|---|
| 1 | Idoneal completeness under GRH (Weinberger 1973) | FC `Wikipedia/IdonealCompleteness.lean` `idoneal_numbers_completeness` (open); Atlas `wiki-idoneal-number` | `LFunction_ne_zero_of_half_lt_re` (`Main.lean:10`); optional explicit-formula and zero-count lemmas (inventory 02 §3a) | Explicit GRH bound for the least p with `χ_{−4n}(p)=1` (adapt ankeny-grh); the elementary ab+bc+ca witness lemma; `native_decide` up to about `10^6` | **U** | M |
| 2 | Stark–Heegner (class number one) via GRH | FC `Wikipedia/ClassNumberProblem.lean` `…variants.imaginary` (solved); Atlas `wiki-class-number-problem` | `QuadraticZeta.idealCount_eq_sum`, `exists_isKroneckerChar` (`…/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean:358, :458`); GRH | Same least-split-prime bound as #1; `discr (AdjoinRoot (X²−d)) = quadFundDisc d` and its `𝓞_K`; `N(α) ≥ |D|/4` for `α ∉ ℤ`; `h = 1` for the 9 fields (Mathlib `isPrincipalIdealRing_of_abs_discr_lt` covers `|D| ≤ 8`, Minkowski with primes ≤ 8 covers the rest) | **U** | M–L |
| 3 | Discharge `DedekindContinuation`, closing FC's Artin target | FC `Wikipedia/ArtinPrimitiveRootsConjecture.lean` `conditional_artin_primitive_roots.parts.i`; artin-grh | `continuedDedekindZeta*`, `completedDedekindZeta_one_sub`, `tendsto_*_completedDedekindZeta_*`, `gammaFactor_one`, `discrNormConductor_one` (`GroundTheory/GlobalFields/TateThesis/Dedekind{Zeta,}Continuation.lean`) | Strip bound `‖ξ‖ ≤ M(1+|s|)²`, from `TateThetaDecay`/`TateMain` | **C** (H removed) | M |
| 4 | ERH for every abelian number field | new; FC vocabulary `DedekindZetaRH` | `UpperTheory.V.CF.kwHom` (`…/ClassFieldRamification/KwHom.lean:13`); RH + GRH; `continuedDedekindZeta`, `completedDedekindZeta_one_sub`; `dedekindZeta_eq_exp` (`Development/WeilBound/…/ZetaEulerProducts/SummablePrimesRpow.lean:13`) | `ζ_K = E·∏L(χ mod N)` at unramified p; Frobenius in `ℚ(ζ_N)` | **U** | M–L |
| 5 | Kummer criterion (⇐ half) + `small_regular_primes` | FC `Wikipedia/RegularPrimes.lean`; Atlas `wiki-regular-prime` | `UpperTheory.V.Stick.coef` (`…/StickelbergerTheorem/ImportsAlt.lean:13`), `Stick.jacobi`, `Bern.b_lval`, `b_primlevel`; `hilbertClassFieldArtinEquiv`; GroundTheory `KummerTheory/` | Eigenspaces of `Cl[p]` under the Teichmüller character, `B_{1,ω^{−i}} ≡ B_{p−i}/(p−i)`, Kummer's reflection for the plus part, Bernoulli mod p by `decide` | **D** | L |
| 6 | Gauss/Heilbronn: `h(−d) → ∞`, explicit `h ≥ c√d/log log d` | Atlas `wiki-class-number-problem` (no FC theorem) | `LFunction_one_and_mean_log_eta`, `exists_isIdealClassPoint` (`…/DedekindZetaEqSumRealEisenstein.lean:121, :80`); GRH | Littlewood lower bound for `L(1,χ)` (NEXT_TARGETS #13). The class-number step of #13 is now free | **U** | M–L |
| 7 | Kronecker–Weber, global CFT, Chebotarev density, Ferrero–Washington as cited re-exports | Atlas `wiki-hilbert-s-twelfth-problem` (context only) | `UpperTheory.V.CF.kw/kwHom/kwRam`; `GroundTheory.Global.artinMap`, `hilbertClassFieldArtinEquiv`, `hasDirichletDensity_chebotarevSet`; `UpperTheory.V.FW.ferreroWashington` | Nothing but wrappers and the trust caveat | D-by-import | S |
| 8 | Cox: `p = x²+ny² ⇔ p` splits completely in `H_K` (`ℤ[√−n]` maximal); density `1/(2h)` | none (Cox, *Primes of the form x²+ny²*, Thm 5.1) | `hilbertClassFieldArtinEquiv_mk0`, `le_hilbertClassField_iff`, `isUnramifiedEverywhere_hilbertClassField` (`ClassFieldConsequences/HilbertClassField.lean`); `hasDirichletDensity_setOf_splitsCompletely`; `idealCount_eq_sum` | H/ℚ is Galois (conjugation invariance); norm-form identification for `ℤ[√−n]` | D | M |
| 9 | `j((1+√−163)/2) ∈ ℤ` (and the other `h = 1`, `d ≡ 3 (mod 4)` cases) | none | `ReciprocityTheory.ChartRestriction.L1.cm1` (`…/UnramifiedIntegrals/IsIntegralOfRoot.lean:56`); `Elliptic.adjoin_j_eq_hilbertClassField` | `h = 1` for the field (from #2), j real ⇒ rational; tying `CMCurve` to `PeriodPair` | D | S–M |
| 10 | Every ideal class / ray class has infinitely many primes (density `1/h`) | none | `hasDirichletDensity_setOf_map_eq` (`TateThesis/RayClassDensity.lean:310`); `exists_degOne_prime_in_rayClass` | Wrapping into a `ClassGroup` statement | D | S |
| 11 | Explicit class-number upper bounds, cited | none | `KStar.IdealCounting.log_classNumber_le`; `HermitianLatticeCounting…classNumberBound`; `UpperTheory.V.Odd.logH` | Wrapper only | D | S |
| 12 | Hasse norm theorem (cyclic) | none | `mem_range_norm_iff_forall_local` (`GlobalFields/HasseNorm.lean:60`), `GlobalTheory.CNorm.hasseNorm` | Wrapper only | D | S |

## Top 10, one paragraph each

**1. Idoneal completeness.** The best target: an *open* FC statement, closable at tier U, with no
class-group machinery.

- The witness lemma is ten lines of `omega`/`nlinarith`.
- The real work is a GRH bound `p ≤ c log²(4n)` for the least prime with `(−4n/p) = 1`. This is the
  coset version of ankeny-grh's `BachSubgroupBound`, reusing its explicit formula and
  erdos-985's zero sums.
- For the range below the threshold, `n ≲ 10^6` for `c ≈ 4` (this threshold depends on the c we
  actually prove), supply witnesses `(a,b,c)` per n and check them with `native_decide`. This needs a
  proved-sound checker (rule 5).
- Unconditionally it is known that there are at most two more idoneal numbers, and none below
  `7.75·10^19` (OEIS A000926). A tier-U proof is therefore a formal result about an open problem.
- Primary sources: Weinberger, Acta Arith. 22 (1973) 117–124; Kani, Ann. Sci. Math. Québec 35 (2011),
  Cor. 23 and Remark 24 (both confirmed via OEIS and Wikipedia). The ab+bc+ca reduction from a split
  prime is my derivation; verify it.

**2. Stark–Heegner via GRH.** FC marks it "research solved"; Mathlib has no proof.

- Same analytic core as #1. If `h = 1`, every prime `p < |D|/4` is inert, which caps `|D|` at a few
  hundred.
- The RH repo supplies the bridge from `χ(p) = 1` to an ideal of norm p (`idealCount_eq_sum`), but for
  an abstract K with `finrank = 2` and `discr K = −d`.
- The cost is in FC's encoding: proving `discr (AdjoinRoot (X²−d)) = quadFundDisc d` and describing its
  ring of integers (the pin has `Algebra/QuadraticAlgebra`, unclear how far it goes); then
  `h = 1` for the nine fields.
- Do #1's analytic lemma first and share it.

**3. `DedekindContinuation`.** Everything except `strip_bound` is in `TateThesis/DedekindContinuation.lean`,
with the same gamma factor and discriminant normalisation as artin-grh. Proving the strip bound from the
theta-decay lemmas closes artin-grh's last `sorry` on the formal-conjectures statement. It leaves
`HooleyHypothesis` as the only hypothesis, which is rule 6's "C, done as far as it can go" for that
repo (or "C + Hecke formalised").

**4. ERH for abelian fields.** The repo proves GRH for Dirichlet L-functions, Kronecker–Weber and the
continuation of `ζ_K`. Assembling them gives the Riemann hypothesis for `ζ_K` of every abelian K. FC
explicitly lacks an ERH statement, and this one can be stated faithfully with `IsDedekindZeta`. Using
imprimitive characters mod N keeps ramified primes trivial. Its downstream payoff inside this workspace
is small (see (b)), but it is a clean headline and the factorisation lemma feeds #5.

**5. Kummer's criterion, easy half.** Stickelberger on Mathlib's `ClassGroup (𝓞 K)` with
`IsCyclotomicExtension {M} ℚ K` is the expensive ingredient of Herbrand's theorem, and the repo has it.

- Add the eigen-decomposition under `(ℤ/p)ˣ`, the Bernoulli congruence, and Kummer's reflection
  (`p | h⁺ ⇒ p | h⁻`, through Kummer theory and the Hilbert class field, both in GroundTheory).
- That gives `(∀k, p ∤ B_k) ⇒ p` regular, and `small_regular_primes` by computation.
- Check first whether flt-regular already has parts of this.

**6. `h(−d) → ∞` under GRH.** With the class number formula in hand, the only work is the Littlewood
lower bound for `L(1,χ)`. Revise NEXT_TARGETS #13: its class-number corollary costs no class-number
infrastructure any more.

**7. Re-exports.** Kronecker–Weber, global CFT, Chebotarev (Dirichlet density) and Ferrero–Washington
can be stated in Mathlib terms and imported. They are worth one small module of cited corollaries in a
future shared library, always with the untrusted-cache caveat. None is a formal-conjectures target.

**8. Cox for maximal `ℤ[√−n]`.** A textbook theorem missing from Mathlib, about a page of glue on top
of `hilbertClassFieldArtinEquiv_mk0`. The density `1/(2h)` comes from
`hasDirichletDensity_setOf_splitsCompletely`. The general n needs ring class fields of orders.

**9. Singular moduli for `h = 1`.** `cm1` gives integrality. Together with `K(j) = H_K = K` and j real,
it gives `j ∈ ℤ`; for `d = 163` that is `j = −640320³`, up to computing it. A nice showcase, but the
link between the internal `CMCurve` and `PeriodPair` needs checking.

**10. Primes in classes.** `hasDirichletDensity_setOf_map_eq` already gives density `1/#G` for any
finite idelic quotient. Specialising it to `ClassGroup` gives Dirichlet's theorem for ideal classes.
Small and Mathlib-worthy.

## Rejected, and why

- **Catalan/Mihăilescu**: already proved in Lean 4 (FC attribute points to cadamcat/catalan-lean4).
  Stickelberger alone would not suffice anyway: Thaine's theorem and Cassels' results are needed.
- **Miller / van der Linden, real cyclotomic class numbers under GRH**: Odlyzko's bound is applied to
  the Hilbert class field, so ERH for a non-abelian field; it also relies on Schoof's tables.
  Confirmed from arXiv:1407.2373.
- **Weinberger's Euclidean theorem** (unchanged from NEXT_TARGETS): Kummer fields of units are
  non-abelian *(detail unverified)*. **Harper–Murty** (unconditional): needs a large sieve and
  Bombieri–Vinogradov over number fields, XL.
- **Bach's class-group generator bound**: needs GRH for Hecke L of K, i.e. ζ of the non-abelian H/ℚ.
- **Effective Chebotarev for abelian L/ℚ**: no new content beyond Dirichlet GRH (NEXT_TARGETS #3/#12).
- **Unconditional Artin / `HooleyHypothesis`**: non-abelian for `k ≥ 3`. Even (a)+(b) leave artin-grh
  at tier C.
- **Unconditional Heegner via CM/Weber**: Weber's class-invariant theorems are missing. XL; the GRH
  route (#2) is cheaper.
- **`not_isRegularPrime_37`, `infinitude_of_irregularprimes`, the full Kummer iff**: need the analytic
  `h⁻` formula (factorisation, regulator ratio, unit index). XL; revisit after #4 and #5.
- **Brauer–Hasse–Noether (full), Grunwald–Wang**: the surjectivity half is missing and Br is not linked
  to central simple algebras; Grunwald–Wang is absent.
- **Kummer–Vandiver, Leopoldt, Greenberg, Iwasawa main conjecture, Brumer–Stark, Stark, Hilbert 12,
  real-quadratic class number problem**: open, and nothing in the toolkit touches them. Ferrero–Washington
  gives only μ = 0 for abelian fields.
- **LLS Thm 1.4 as the least-split-prime input for #1/#2**: its escape clause `p ≤ 10^9` makes the
  finite range about `10^18`. Prove a Bach-type bound instead.
