# Scoping: ERH for every abelian number field (NEXT_TARGETS #24)

Date 2026-11-24. Research only: no repo created, nothing built, no `lake` run. Sources read first-hand:
formal-conjectures `main` = `86a2f58a`; riemann-hypothesis checkout at `507a75d91d` (Lean `v4.36.0`, the
workspace's toolchain); Mathlib `fc4f59e5` (the copy under `riemann-hypothesis/.lake/packages/mathlib`);
artin-grh `origin/main` = `0ac17e6`; TauCeti `main` = `b79bd62f`; Washington, *Introduction to Cyclotomic
Fields*, 2nd ed. (1997), Ch. 4 (text read). riemann-hypothesis code is paraphrased; only names and
signature sketches appear below. LivingBrain (`projec1006`) was searched: it holds only the NEXT_TARGETS
text for this target, with no recorded dead ends.

**Corrections to the existing brief** (`NEXT_TARGETS.md` #24 and `rh-lemmas/targets-algebraic.md` (b)):

1. The directory is `FormalConjectures/Millennium/` (double n). `IsDedekindZeta` and `DedekindZetaRH`
   are **not** in `Millennium/RiemannHypothesis.lean`. They are in
   `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean:59–69`, namespace
   `ArtinPrimitiveRootsConjecture`.
2. "Statement. New." is wrong for the Lean statement and for the mathematics (see §1, §2). Both
   formal-conjectures and TauCeti already define an ERH predicate, and the mathematics is textbook.
3. "Frobenius at `p` is `p`" and the cyclotomic splitting law are **already in Mathlib at our pin**
   (`IsCyclotomicExtension.Rat.galEquivZMod_stabilizer`, `inertiaDegIn_eq_of_not_dvd`,
   `ramificationIdxIn_eq_of_not_dvd`). The Washington character/subfield correspondence is there too
   (`intermediateFieldEquivSubgroupChar`).
4. The functional-equation step (step 4 of the brief) is unnecessary. riemann-hypothesis's `Main.lean`
   also proves `LFunction_eq_zero_re : DirichletLZerosOnLine`, which says every zero of every
   `DirichletCharacter.LFunction` (any level `N`, imprimitive characters included) with `0 < Re s < 1`
   has `Re s = 1/2`. With that hypothesis, the factorisation on `Re s > 0` finishes the proof with no
   Dedekind functional equation.
5. The cyclotomic factorisation `ζ_{ℚ(ζ_n)} = ∏_χ L(s, χ*)` **has already been formalised** in TauCeti
   (merged 2026-11-19), so stage 1 is not new Lean either (§2.3).

---

## 1. The problem

**Statement.** For a finite abelian extension `K/ℚ`, every zero of the (continued) Dedekind zeta
function `ζ_K` with `0 < Re s < 1` has `Re s = 1/2`.

**Status.** Open. It already contains RH (`K = ℚ`) and is open for every abelian `K`, including `ℚ(i)`.
It is equivalent to GRH for all Dirichlet L-functions (§2). No zero-free strip of any width is known
for any `ζ_K`.

**formal-conjectures.**

- `FormalConjectures/Millennium/RiemannHypothesis.lean` states `RiemannHypothesis.riemannHypothesis`
  and `GRH.generalized_riemann_hypothesis` (primitive `χ`, with trivial zeros excluded through
  `GRH.trivialZeros`), both `@[category research open, AMS 11]`. A module docstring and a closing
  comment block headed "NOTE: Extended Riemann Hypothesis" explain that ERH is **deliberately not
  stated**. The reason given is that `NumberField.dedekindZeta` is the raw `LSeries`: it takes junk
  value `0` off `Re s > 1`, so a naive ERH would be provably false. ERH is to be added "once Mathlib
  provides a meromorphic continuation".
- `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`, namespace
  `ArtinPrimitiveRootsConjecture`, gets around this with a continuation-agnostic predicate. Verbatim:

  ```lean
  def IsDedekindZeta (K : Type*) [Field K] [NumberField K] (Z : ℂ → ℂ) : Prop :=
    DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta K s

  def DedekindZetaRH (K : Type*) [Field K] [NumberField K] : Prop :=
    ∀ Z : ℂ → ℂ, IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → s.re = 1 / 2
  ```

  These are `def`s and carry no category. They are used only inside `HooleyHypothesis` (and in
  `GreensOpenProblems/93.lean`'s docstring). **formal-conjectures has no theorem stating ERH, for
  abelian fields or for any field.** So there is no FC target to copy and no FC category to quote. The
  target theorem would be ours, built from FC's vocabulary.
- One property of `DedekindZetaRH` to keep in mind: it quantifies over all continuations `Z`. If no
  continuation existed it would hold vacuously. The headline therefore needs a companion
  non-vacuity theorem (§5).

**Other Lean statements found.** TauCeti (`TauCetiProject/TauCeti`, Apache-2.0, AI-written library
downstream of Mathlib) defines `TauCeti.DedekindERH K` in
`TauCeti/NumberTheory/LFunctions/Zeros/RiemannHypotheses.lean`, through the divisor of its continued
`dedekindZetaC K`. Its docstring admits that the predicate holds trivially for any `K` without a
whole-plane continuation, because the fallback is `0`. It is used nowhere except that file, and no
theorem proves it for any `K` (GitHub code search for `DedekindERH`, 2026-11-24).

## 2. What is already known

### 2.1 Unconditional
Nothing about zeros in the strip beyond the classical zero-free regions near `Re s = 1`. ERH for abelian
`K` is open.

### 2.2 The implication GRH ⇒ ERH for abelian fields: a textbook fact, also an equivalence
- **Washington, Thm 4.3** (2nd ed., Ch. 4, read from the book's text): *"Let X be a group of Dirichlet
  characters, K the associated field, and ζ_K(s) the Dedekind zeta function of K. Then
  ζ_K(s) = ∏_{χ∈X} L(s, χ)."* Washington's characters are primitive by convention, and the proof
  compares Euler factors at each `p` using Thm 3.7 (splitting in the associated field).
- **Cohen**, *Advanced Topics in Computational Number Theory*, Thm 10.5.25 states the same
  factorisation, as cited in arXiv:1005.1609 Remark 1.1 and on math.SE q. 4932947 *(not read in the
  book itself: unverified)*. The math.SE thread attributes a proof to Neukirch, Prop. VII.10.4 *(unverified)*.
- **arXiv:1005.1609** (Generalized Riemann hypotheses: sufficient and equivalent criteria), Remark 1.1:
  *"the Dedekind zeta function can be represented, whenever the field involved is an abelian extension
  of ℚ, as a product of Dirichlet L-functions …: then proving the Extended Riemann Hypothesis [their
  name for Dirichlet GRH] would provide a proof of the Generalized Riemann Hypothesis [their name for
  Dedekind ERH] for this kind of fields too."*
- **Wikipedia, "Generalized Riemann hypothesis", §ERH** settles the question: *"Generalized Riemann
  hypothesis for Dirichlet L-functions is equivalent to ERH for K being abelian extension of rational
  numbers, since for abelian extensions ζ_K is finite product of some Dirichlet L-functions depending on
  K. Conversely, all L-functions for character modulo n appears in product for K = ℚ(ζ_n)."*

**Answer to the key question.** "GRH ⇒ ERH for abelian K" is a **standard textbook consequence**. It is
a one-line corollary of a published, fully proved theorem (Washington Thm 4.3), and it is stated as
folklore in many places. It is in fact an **equivalence**: ERH for all abelian `K` ⇔ GRH for all
Dirichlet L-functions. A tier-U version therefore says nothing beyond riemann-hypothesis's own
(unverified) GRH claim.

### 2.3 Prior Lean work (searched: Mathlib at pin and upstream PRs; GitHub code search for
`dedekindZeta`, `ExtendedRiemannHypothesis`, `DedekindERH`, `kroneckerWeber`)
- **TauCeti** (`TauCeti/NumberTheory/NumberField/Cyclotomic/DedekindZeta.lean` and
  `…/LFunctions/DedekindZeta/Cyclotomic.lean`, merged 2026-11-19 in commit `b5d84ad6`, PR #40535; a
  follow-up PR #43178 is open). For every `IsCyclotomicExtension {n} ℚ K`:
  `dedekindZeta_eq_prod_LFunction_primitiveCharacter` (`ζ_K = ∏_{χ mod n} L(s, χ*)` on `Re s > 1`,
  exact at ramified primes too), the imprimitive version `dedekindZeta_mul_prod_eq_prod_LFunction`, the
  local identity `prod_primesOverFinset_one_sub_absNorm_cpow_neg`, the residue identity, and the
  continued versions for `dedekindZetaC K`. `…/DedekindZeta/Quadratic.lean` does the same for every
  quadratic field. Pins: Lean `v4.37.0-rc1`, Mathlib `31ce06ea`. These differ from ours, so it cannot be
  imported. It can be ported with credit (Apache-2.0). TauCeti also has `ClassFields/KroneckerWeber.lean`
  (`kroneckerWeber`, via its class field theory) and `Cyclotomic/CharacterSubfield.lean`. I did not
  audit its axioms. Because TauCeti already has the continuation for cyclotomic fields, "Dirichlet GRH ⇒
  `DedekindERH (ℚ(ζ_n))`" would be a short corollary there. Nobody has written it yet.
- **Mathlib upstream**: Kronecker–Weber is open as PR #46376 (xroblot, from the SKW project
  `github.com/xroblot/SKW`, a complete proof via Stickelberger). There is no Dedekind = ∏L factorisation
  and no Dedekind continuation in Mathlib. Doc PR #45878 is about to state that `dedekindZeta` is not the
  continuation.
- **riemann-hypothesis**: has its own Kronecker–Weber (`UpperTheory.V.CF.kwHom`), the Tate-thesis
  continuation, and the imaginary-quadratic factorisation `GlobalTheory.QuadraticZeta.dedekindZeta_eq_mul_LFunction`.
  It has no general factorisation and no ERH statement.
- Other repos: `CBirkbeck/AINTLIB` (`FltRegularBernoulli/HMinus.lean`) has an even-character
  factorisation for the maximal real subfield. `Rogerhu12/hecke-seven-eighths` has
  `dedekindZeta_zeroFree_of_abelian_extension`, a zero-free transfer for a different claim (Re > 7/8).
  Neither proves ERH for any field.

**So "not in Lean before" is true only in a narrow sense.** No Lean development proves the zeros-on-the-line
statement for `ζ_K` of any `K ≠ ℚ`, even conditionally. The analytic heavy lifting (the cyclotomic
factorisation) already exists in TauCeti, and Kronecker–Weber exists three times (riemann-hypothesis,
TauCeti, Mathlib PR #46376).

## 3. Genuineness verdict: **(a)**, and the label should be *RH-equivalent*

This is a published conditional theorem, or more exactly a textbook corollary of Washington Thm 4.3. We
would only be formalising it. Under AGENTS.md's labels it is **RH-equivalent**: ERH for abelian fields
is equivalent to the GRH input itself (Wikipedia, quoted above). The `Unconditional/` theorem therefore
restates riemann-hypothesis's unverified GRH claim through a known identity.

What a careful mathematician would say if we announced it: *"That's GRH for Dirichlet L-functions
rewritten through ζ_K = ∏L(s,χ); it's in Washington Chapter 4. The Lean factorisation for cyclotomic
fields is already in TauCeti."* Announcing it as "ERH proved for abelian fields" would be exactly the
foolish-looking claim the user wants to avoid.

The modest things that are true and could be claimed:
- (i) as far as I found, the first Lean proof that a Dirichlet-GRH hypothesis implies
  zeros-on-the-line for `ζ_K` of a non-trivial number field, stated against formal-conjectures'
  `DedekindZetaRH`;
- (ii) for stage 2, the first Lean factorisation `ζ_K = E·∏ L` for an arbitrary subfield of a
  cyclotomic field (TauCeti has only `ℚ(ζ_n)` and quadratic fields);
- (iii) a possible upstream contribution: formal-conjectures could gain an ERH statement in its
  `DedekindZetaRH` vocabulary, with our theorem as a `formal_proof` of the conditional abelian case.

None of these is new mathematics. Under the 2026-11-24 rule this target passes the "open problem" filter,
since ERH for abelian `K` is open. It is weak on the user's "genuine results" criterion: it is the least
genuine kind of target, a reformulation of the hypothesis.

## 4. Proof route

Notation: `G = (ZMod N)ˣ ≅ Gal(ℚ(ζ_N)/ℚ)` (Mathlib `galEquivZMod`); `H ≤ G` corresponds to
`Gal(ℚ(ζ_N)/K)`; `X(K) = H^⊥` = Dirichlet characters mod `N` trivial on `H` (Mathlib
`intermediateFieldEquivSubgroupChar`, with `card_intermediateFieldEquivSubgroupChar = finrank ℚ K`).
Imprimitive characters mod `N` are used throughout.

**Recommended route: von Mangoldt / log-derivative comparison (route C).** Of the three candidate routes,
it reuses the most existing Mathlib-only code and needs no ramified-prime bookkeeping.

| Step | Statement | Key fact | Input | Effort / lines |
|---|---|---|---|---|
| 0 | Statement file | copy FC `IsDedekindZeta`, `DedekindZetaRH`; copy `DirichletLZerosOnLine` from riemann-hypothesis `src/Statements.lean:14` (its body is Mathlib-only); copy the type of `kwHom` as a `Prop` `KroneckerWeberStatement` | rule 2 | S, 40 |
| 1 | Unramified splitting in `K ⊆ ℚ(ζ_N)`, `p ∤ N` | `e = 1`; `f_K = ord of p̄ in G/H`; `g_K = [K:ℚ]/f_K` | Cyclotomic level: Mathlib `ramificationIdxIn_eq_of_not_dvd`, `inertiaDegIn_eq_of_not_dvd`, `galEquivZMod_stabilizer` (decomposition group = `⟨p⟩`). Tower: Mathlib `RamificationInertia/Galois.lean` `ramificationIdxIn_mul_ramificationIdxIn`, `inertiaDegIn_mul_inertiaDegIn`, `ncard_primesOver_mul_ncard_primesOver`, `card_stabilizer_eq_card_inertia_mul_finrank`. Group theory: `f_rel = #(⟨p⟩ ∩ H)`, so `f_K = #⟨p⟩ / #(⟨p⟩∩H) = ord_{G/H}(p̄)` | **must be proved, M–L, 250–400** (stage 1: S, 40, read off Mathlib) |
| 2 | Character orthogonality on `H^⊥` | `Σ_{χ∈X(K)} χ(a) = #X(K)·[a ∈ H]` for `a ∈ G` | Mathlib `MulChar` duality (`subgroupOrderIsoSubgroupMulChar`, `Mathlib/NumberTheory/MulChar/Duality.lean`) | must be proved, S–M, 80–150 (stage 1: Mathlib's full-group orthogonality, S) |
| 3 | Coefficient identity | for `n` coprime to `N`: `Λ_K(n) = Σ_{χ∈X(K)} χ(n)Λ(n)`. At `p^k`: LHS `= #{𝔭∣p : f∣k}·f·log p = g f log p·[f∣k]`, RHS `= log p·#X·[p^k ∈ H] = fg log p·[f∣k]` | artin-grh `Artin.Analytic.vonMangoldtK` (`Artin/Analytic/Core/VonMangoldt.lean:34`), steps 1–2 | M, 120–200 |
| 4 | Ramified part | `Λ_ram(n) := Λ_K(n)` if `gcd(n,N) > 1`, else `0`. Supported on prime powers of the finitely many `p ∣ N`, with `Λ_ram(p^k)/log(p^k) ≤ [K:ℚ]/k`, so `Σ Λ_ram(n)/log n · n^{-s}` converges absolutely for `Re s > 0` | Mathlib `LSeries_analyticOnNhd` (`LSeries/Deriv.lean:161`) after bounding `abscissaOfAbsConv ≤ 0` | S–M, 80–120 |
| 5 | Factorisation on `Re s > 1` | `ζ_K(s) = E(s)·∏_{χ∈X(K)} L(s,χ)` with `E := exp(L(Λ_ram/log, s))` | ζ_K side: artin-grh `dedekindZeta_eq_exp` (`VonMangoldt.lean:602`, `ζ_K = exp(L(Λ_K/log))`) and `LSeries_vonMangoldtK` (`:662`). L side: Mathlib `LSeries_twist_vonMangoldt_eq` (`LSeries/Dirichlet.lean:412`) plus artin-grh's own technique (equal log-derivatives on the half-plane, both → 1 as `s → +∞`) to get `L(s,χ) = exp(L(χΛ/log, s))`. Then linearity of `LSeries` and step 3 | M, 150–250 |
| 6 | `E` on `Re s > 0` | analytic and **never zero** (it is an `exp`) | step 4 | S, 30 |
| 7 | Identity theorem | for any `Z` with `IsDedekindZeta K Z`: `Z = E·∏L` on `U = {Re s > 0} \ {1}` (`U` open and preconnected, both sides analytic: Mathlib `DirichletCharacter.differentiableAt_LFunction` (`s ≠ 1 ∨ χ ≠ 1`), `DifferentiableOn.analyticOnNhd`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) | preconnectedness of the half-plane minus a point: S lemma | S–M, 80 |
| 8 | Assembly | `Z s = 0`, `0 < Re s < 1` ⇒ `∏ L(s,χ) = 0` (since `E s ≠ 0`) ⇒ some `L(s,χ) = 0` ⇒ `Re s = 1/2` by `hGRH` | `Finset.prod_eq_zero_iff` | S, 40 |
| 9 | Subfield transport | for `φ : K →ₐ[ℚ] CyclotomicField N ℚ`, `K ≃ₐ φ.fieldRange`; `dedekindZeta` and `DedekindZetaRH` are invariant under `≃ₐ` (bijection of ideals preserving `absNorm`; cf. the lemma `Ideal.absNorm_comap_ringEquiv` in closed Mathlib PR #45912) | must be proved | S–M, 100–150 |
| 10 | `Unconditional/AbelianERHUnconditional.lean` | discharge `hGRH` by `LFunction_eq_zero_re` and `hKW` by `UpperTheory.V.CF.kwHom`; non-vacuity: `IsDedekindZeta K (GroundTheory.Global.continuedDedekindZeta K)` from `differentiableOn_continuedDedekindZeta` + `continuedDedekindZeta_eq` | riemann-hypothesis `src/Main.lean`, `…/ClassFieldRamification/KwHom.lean:13`, `GroundTheory/GlobalFields/TateThesis/DedekindZetaContinuation.lean:44–69` (artin-grh `Unconditional/ArtinUnconditional.lean` already imports this module) | S, 40 |

Total: about 1,100–1,600 lines for the full abelian case, and about 600–800 for stage 1.

**No explicit constants and no finite computation anywhere.** No `native_decide` is needed.

**The routes not chosen.**
- *Euler factors via orthogonality on `G/H` (the NEXT_TARGETS route).* It needs the product identity
  `∏_{χ∈X}(1−χ(p)x) = (1−x^f)^g`, which is harder than step 2's sum. It also needs an Euler product for
  `ζ_K` in Mathlib terms, which Mathlib lacks. riemann-hypothesis's `PositivityTheory.Lord.dedekindZeta_eq_exp`
  (`…/ZetaEulerProducts/SummablePrimesRpow.lean:13`, an `exp(Σ_P −log(1−N P^{-s}))` form) may be used
  only in `Unconditional/`, and the regrouping of a `tsum` over `HeightOneSpectrum` by rational prime
  costs about 250 more lines. Worse by about 300 lines.
- *Coefficient level (TauCeti's route).* Multiplicativity of ideal counts plus Bell series at every
  prime. That is exact at ramified primes only with primitive characters, so it needs conductor and
  inertia bookkeeping for subfields (L). Porting TauCeti's infrastructure (`normCoeff`,
  `IdealArithmeticFunction`, `BellSeries`, 9 files) across a Mathlib version gap is itself M–L. This
  route is worth it only if we want the exact `ζ_K = ∏ L(s,χ*)`, which ERH does not need.

**Where `riemann-hypothesis` is used.** Only `LFunction_eq_zero_re`, `kwHom` and (for non-vacuity) the
Tate-thesis continuation, all in `Unconditional/`. The main library depends only on Mathlib, erdos-985
(transitively) and artin-grh (for `vonMangoldtK`, `dedekindZeta_eq_exp`, `LSeries_vonMangoldtK`).
Depending on artin-grh is new: it requires erdos-985, so the dependency graph stays a tree. The
alternative is to copy those roughly 670 lines of `VonMangoldt.lean`.

## 5. Target Lean statements (`AbelianERH/Statement.lean` and `AbelianERH/Main.lean`)

Hypotheses (rule 2; the bodies below are paraphrases of the copied definitions):
- `ArtinPrimitiveRootsConjecture.IsDedekindZeta`, `DedekindZetaRH`: copied verbatim from FC (§1).
- `DirichletLZerosOnLine`: copied from riemann-hypothesis `src/Statements.lean`. For all `N` with
  `NeZero N`, every `χ : DirichletCharacter ℂ N` and every `s` with `0 < s.re`, `s.re < 1` and
  `χ.LFunction s = 0`, we have `s.re = 1/2`.
- `KroneckerWeberStatement : Prop`: the type of `UpperTheory.V.CF.kwHom`. For every
  `L : Type` with `[Field L] [NumberField L] [IsAbelianGalois ℚ L]` there is `N > 0` with
  `Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ)`. This is tier H in the main library: a known theorem we
  don't re-prove. It is discharged in `Unconditional/`. It could later be discharged inside the main
  library once Mathlib PR #46376 lands at a future pin.

Headline theorems, staged:

```lean
-- Stage 1 (tier C; tier U in Unconditional/)
theorem cyclotomic_dedekindZetaRH_of_GRH (hGRH : DirichletLZerosOnLine)
    (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] :
    ArtinPrimitiveRootsConjecture.DedekindZetaRH K

-- Stage 2a (tier C): every subfield of a cyclotomic field; no Kronecker–Weber
theorem dedekindZetaRH_of_GRH_of_algHom (hGRH : DirichletLZerosOnLine)
    (K : Type*) [Field K] [NumberField K] {N : ℕ} [NeZero N] (φ : K →ₐ[ℚ] CyclotomicField N ℚ) :
    ArtinPrimitiveRootsConjecture.DedekindZetaRH K

-- Stage 2b (tier C + H)
theorem abelian_dedekindZetaRH_of_GRH (hGRH : DirichletLZerosOnLine) (hKW : KroneckerWeberStatement)
    (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ArtinPrimitiveRootsConjecture.DedekindZetaRH K

-- Unconditional/ (tier U)
theorem abelian_dedekindZetaRH (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ArtinPrimitiveRootsConjecture.DedekindZetaRH K   -- := abelian_..._of_GRH LFunction_eq_zero_re kwHom K
theorem isDedekindZeta_continued (K : Type) [Field K] [NumberField K] :
    ArtinPrimitiveRootsConjecture.IsDedekindZeta K (GroundTheory.Global.continuedDedekindZeta K)
```

Also worth a lemma of its own: the factorisation `ζ_K(s) = E(s)·∏_{χ∈X(K)} L(s,χ)` on `Re s > 1`, with
`E` analytic and zero-free on `Re s > 0`. It is the reusable piece (rank-5 Kummer target).

Optional variant: the hypothesis in FC's own form, `GRH.generalized_riemann_hypothesis` (primitive `χ`,
trivial zeros excluded). The bridge "FC GRH ⇒ `DirichletLZerosOnLine`" needs `L(s,χ) = L(s,χ*)·∏_{p∣N}(1−χ*(p)p^{-s})`
(Mathlib `DirichletCharacter.LFunction_changeLevel`) and the fact that the extra factors vanish only on
`Re s = 0`. Cost S–M. It makes the theorem independent of riemann-hypothesis's choice of statement.

Weaker fallback if step 1 for subfields stalls: stage 1 only (cyclotomic fields). Add the imaginary
quadratic case in `Unconditional/` via riemann-hypothesis's `dedekindZeta_eq_mul_LFunction`. Do not add
it to the main library: rule 1.

## 6. Effort and risk

- **Stage 1 (cyclotomic fields): M.** Every arithmetic input is already in Mathlib at the pin. The work
  is the analytic glue (steps 3–8). Risk is low.
- **Stage 2 (all abelian fields): M–L** on top of stage 1. Steps 1 (tower splitting), 2 and 9.
- **Riskiest single step: step 1 for a proper subfield.** It has to show
  `f_K = ord_{G/H}(p̄)` through Mathlib's Galois-tower API. That means `IsGaloisGroup` instances for
  `𝓞 K → 𝓞 ℚ(ζ_N)` with `K` an `IntermediateField`, `Flat` and `Nonempty (primesOver …)` instances, and
  identifying the stabilizer of `Q` in `H` with `H ⊓ stabilizer G Q`. The mathematics is easy. The
  instance plumbing is the unknown. Second risk: depending on artin-grh, or copying its
  `VonMangoldt.lean`.
- **Smoke tests before building** ("How to run a target", step 4): `#print axioms` on `kwHom` (its
  closure includes `TateThesis.Chebotarev` and class-field modules, so check that no RH-dependent
  axiom or `sorryAx` appears), on `LFunction_eq_zero_re`, and on `continuedDedekindZeta_eq`.
- **Go / no-go.**
  - **Stage 1: conditional go.** It is cheap and correct, but the user should first decide whether a
    result labelled *RH-equivalent*, whose key factorisation is already in TauCeti, is worth a repo.
  - **Stage 2: go only if stage 1 is approved and the subfield factorisation is wanted for its own
    sake** (feeding #5, Kummer). As a headline it adds nothing a mathematician would call new.
  - If the bar is "genuine results", I would **not rank this target above** the candidates whose
    implication is unpublished.

## 7. Open questions for the user

1. Label: is **RH-equivalent** acceptable here? It is equivalent to the GRH hypothesis, not to RH.
   The other reading is *RH-consequence*. Either way the README must say "a reformulation of GRH for
   Dirichlet L-functions via Washington Thm 4.3".
2. Do we proceed knowing TauCeti already has the cyclotomic factorisation in Lean (Apache-2.0, other
   pin)? If yes, should we port it with credit, or prove our own via route C?
3. May the new repo require artin-grh, which is a lake dependency for `vonMangoldtK` and
   `dedekindZeta_eq_exp`? The alternative is to copy those roughly 670 lines.
4. Should the main-library hypothesis be riemann-hypothesis's `DirichletLZerosOnLine` (simplest), or
   formal-conjectures' primitive-χ `GRH.generalized_riemann_hypothesis` (an S–M bridge, closer to FC)?
5. Is upstreaming an ERH statement (`DedekindZetaRH`-based) to formal-conjectures's
   `Millennium/RiemannHypothesis.lean` wanted? That file currently says ERH should wait for a Mathlib
   continuation, so the maintainers may decline it.
