# Scoping: Erdős Problem 969, the error term for squarefree numbers

Scoped 2026-11-24. Research only: no repo was created or edited and `lake` was not run.
Claims I could not confirm from a primary source are marked *(unverified)*. Where the only
source is a survey or a reference list, the source is named.

## 1. The problem

Let `Q(x) = #{n ≤ x : n squarefree}` and `Q(x) = (6/π²)x + E(x)`. **Determine the order of
magnitude of `E(x)`.** Sources: [Er65b], [Er81h, p. 176], through
<https://www.erdosproblems.com/969>.

erdosproblems.com, verbatim: "It is elementary to prove E(x) ≪ x^{1/2}, and the prime number
theorem implies o(x^{1/2}). The best known unconditional upper bound is of the shape
x^{1/2−o(1)}, due to Walfisz [Wa63]. Evelyn and Linfoot [EvLi31] proved that E(x) ≫ x^{1/4},
and this is likely the true order of magnitude. The Riemann Hypothesis would follow from
E(x) ≪ x^{1/4}. **The true order of magnitude is unknown even assuming the Riemann
Hypothesis.** Conditional on this assumption, the best known upper bound is E(x) ≪
x^{11/35+o(1)}, due to Liu [Li16]." The discussion thread has no comments and the page lists
no proof expositions (fetched 2026-11-24).

**Status: open, and open even under RH.** The full problem is not attackable here.

### formal-conjectures

The file is `FormalConjectures/ErdosProblems/969.lean`. It was added in commit `8b6f6042`
(2026-10-23, PR #4091) and checked at `86a2f58a`. Its definitions, verbatim:

```lean
def squarefreeCounting (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter Squarefree).card

noncomputable def squarefreeCountingError (x : ℕ) : ℝ :=
  (squarefreeCounting x : ℝ) - 6 / Real.pi ^ 2 * x
```

It has three statements:

| Declaration | Category | Statement |
|---|---|---|
| `Erdos969.erdos_969` | `research open`, `question value` | `|E| =O[atTop] g ∧ ¬ |E| =o[atTop] g` for `g := erdos_969.answer` (a `sorry` answer) |
| `Erdos969.erdos_969.variants.prime_number_theorem` | `research solved` | `(fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ).sqrt)` |
| `Erdos969.erdos_969.variants.evelyn_linfoot` | `research solved` | `¬(fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ) ^ (1 / 4 : ℝ))` |

There is **no RH-conditional variant**: no Axer, Montgomery–Vaughan or Liu statement and no
"RH ⇒" form. Both `research solved` variants are `sorry` and carry no `formal_proof`
attribute.

## 2. What is already known

### Unconditional

- `E(x) = O(x^{1/2})`, elementary (Hardy–Wright; Montgomery–Vaughan, *Multiplicative Number
  Theory I*, Thm 2.1, p. 36, per a MathOverflow answer by O. Gorodetsky, question 507402).
- PNT ⇒ `E(x) = o(x^{1/2})` (erdosproblems; it is the formal-conjectures variant above).
- `E(x) ≪ x^{1/2} exp(−c(log x)^{3/5}(log log x)^{−1/5})`: Walfisz, *Weylsche
  Exponentialsummen in der neueren Zahlentheorie* (1963), via Vinogradov–Korobov. Restated in
  Mossinghoff–Oliveira e Silva–Trudgian (arXiv:1912.04972, §1, for general k).
- `E(x) = Ω(x^{1/4})`: Evelyn–Linfoot, Ann. of Math. (2) 32 (1931) 261–270 (from the
  erdosproblems reference list; I did not read the paper). Effective Ω± with constant 3 is in
  Mossinghoff–OeS–Trudgian. They also verify `|E(x)| < 1.12543 x^{1/4}` for `x ≤ 10^18`.
- `E(x) = O(x^{1/4−δ})` is impossible (MV book Exercise 15.1.1.5, per Gorodetsky).

### Under RH: the exponent chain, checked

| Exponent | Author, year, venue | How confirmed |
|---|---|---|
| 2/5 (+ε) | Axer 1911 *(paper not seen; venue unverified)* | Pappalardi's survey "A survey on k-freeness" (2003/04) gives `R_k ≪ x^{2/(2k+1)+ε}`, which is 2/5+ε at k = 2. The MV book, Exercise 13.2.1.14, "attributed to Axer (1911), shows R(x) = O(x^{2/5}) under RH" (per Gorodetsky; whether there is an ε or log factor is *unverified*) |
| 1/3 (+ε) general, **9/28** for k = 2 | Montgomery–Vaughan, "The distribution of squarefree numbers", *Recent Progress in Analytic Number Theory* vol. 1 (Durham 1979), Academic Press 1981, 247–256 | The general `1/(k+1)+ε` is stated by Mossinghoff–OeS–Trudgian and Pappalardi. **9/28 rests on Pappalardi's survey alone** ("In the same paper, they improved the above in the case k = 2 showing R_2(x) ≪ x^{9/28+ε}"). MV book Ex. 13.2.1.16, "based on" MV 1981, gives only 1/3+ε. The brief's "MV 1981 (9/28)" is plausible but **not confirmed from the primary source** |
| 8/25 | S. W. Graham, "The distribution of squarefree numbers", J. London Math. Soc. (2) 24 (1981) 54–64 | Pappalardi; the venue is confirmed by the reference lists of Liu 2016 and Graham–Pintz 1989 |
| 7/22 | R. C. Baker, J. Pintz, "The distribution of square-free numbers", Acta Arith. 46 (1985) 73–79 | EUDML record (keywords: "exponential sums; van der Corput method; Riemann hypothesis"); Pappalardi; PlanetMath. Pappalardi says Jia (1987) obtained the same exponent *(unverified)* |
| 17/54 | Jia Chaohua, "The distribution of square-free numbers", Science in China Ser. A, 1993 | CNKI abstract, verbatim: "we prove, under the Riemann hypothesis, that Σ_{n≤X} μ²(n) = 6/π² X + O(X^{17/54+ε})" |
| **11/35** | H.-Q. Liu, "On the distribution of squarefree numbers", J. Number Theory 159 (2016) 202–222, doi:10.1016/j.jnt.2015.07.013 | erdosproblems; Mossinghoff–OeS–Trudgian ("the best result is due to Liu [16], who proved in 2016 that R_2(x) = O(x^{11/35+ε})"); MathOverflow (Lewko) |

The brief's chain matches the sources, with two caveats: Montgomery–Vaughan's 9/28 is
survey-only, and Graham's 8/25 is in J. London Math. Soc. One warning for anyone citing this:
Cohen et al. claim that RH ⇒ `E ≪ x^{1/4} log x`. Mossinghoff–OeS–Trudgian (footnote 1) say
this "appears to be in error" and only gives 1/3+ε. Don't cite it.

### Key question: is "RH ⇒ E(x) ≪ x^{2/5+ε}" published?

**Yes.** It is Axer's 1911 theorem, now a textbook exercise (MV I, Ex. 13.2.1.14), and it is
superseded five times by stronger *published* RH-conditional exponents (best: 11/35). MV I,
Ex. 6.2.1.8 gives the exact reduction we would formalise (quoted by Gorodetsky):

> R(x) ≪ y + Σ_{m ≤ x/y²} |M(√(x/m))| + x ∫_y^∞ |M(u)| u^{−3} du for any y ≥ 1.

### (ii) The converse-type facts: exactly what is known

- **"E(x) ≪ x^{1/4+ε} ⇒ RH"**: true and standard. erdosproblems states it in the form
  "RH would follow from E(x) ≪ x^{1/4}". Mossinghoff–OeS–Trudgian go further: "If in fact
  R_k(x) = O(x^{1/2k}), then it is straightforward to show that the Riemann hypothesis follows,
  as well as the simplicity of the zeros"; one-sided boundedness of `R_k/x^{1/2k}` suffices
  (Landau, Ingham). The argument, my own write-up of the standard one: if `E ≪ x^θ`, then
  `ζ(s)/ζ(2s) − (6/π²)s/(s−1)` continues holomorphically to `Re s > θ`. Take
  `θ = 1/4 + η`. If a zero `ρ = β + iγ` had `β > 1/2`, then `ζ(2s)` vanishes at `ρ/2`, so
  `ζ(ρ/2) = 0`. Its reflection `1 − ρ̄/2` is a zero with real part `1 − β/2 ∈ (1/2, 3/4)` and
  ordinate `γ/2`. Iterating gives infinitely many distinct zeros with ordinates `γ/2^k → 0` in
  a compact part of `1/2 ≤ σ ≤ 1`. That is impossible: ζ has no zeros on the real segment
  `(0, 1)` and a pole at 1.
- **"E(x) = O(x^θ) for some θ < 1/2 ⇒ a zero-free half-plane"**: **folklore, stated without
  proof.** Gorodetsky (MathOverflow 507402, item 6): "It is a folklore theorem (stated in
  various works, without proof) that an estimate of the shape R(x) = O(x^{1/2−δ}) for some
  δ > 0 is equivalent to a 'quasi RH', that is, to a zero-free region of the shape
  Re s ≥ 1 − δ′." The ⇐ direction is easy: the Ex. 6.2.1.8 reduction with `M(x) ≪ x^α`, `α < 1`,
  gives `E ≪ x^{1/(3−α)}`. The ⇒ direction is the folklore part. The naive Mellin/reflection
  argument above does **not** give it for θ near 1/2: the reflected zero leaves the region after
  one step. I found no published proof.
- **"RH ⇔ E(x) ≪ x^{1/4+ε}"**: **not known.** ⇐ is the bullet above. ⇒ is exactly Erdős 969
  under RH, which is open (erdosproblems: "unknown even assuming the Riemann Hypothesis";
  Gorodetsky–Matomäki–Radziwiłł–Rodgers, GAFA 2021, §1.1: "obtaining an error term
  O_ε(x^{1/4+ε}) is an open problem, even conditionally on the Riemann Hypothesis"). The only
  RH equivalence I found in this area is GMRR's Theorem 3, for the *variance in short
  intervals*, not for `E(x)`.
- In this workspace, any "X ⇒ RH" statement is vacuous at tier U, because riemann-hypothesis
  claims RH. Converse directions have little value here.

### (iii) Montgomery–Vaughan (1/3, 9/28) and later: what extra input they need

Everything past 2/5 handles the short range `d ≤ y` non-trivially. It writes
`⌊x/d²⌋ = x/d² − ψ(x/d²) − 1/2` with the sawtooth `ψ` and expands `ψ` in a truncated Fourier
series. That leaves exponential sums `Σ_{d~D} μ(d) e(hx/d²)`. These are bounded by decomposing
μ (Vaughan-type identity) into type I/II sums and applying van der Corput / exponent-pair
estimates. Evidence: the Baker–Pintz keywords ("exponential sums; van der Corput method"), and
Liu's description of the MV method in *Ark. Mat.* 32 (1994) 449–454 ("By an argument using the
Fourier expansion of the function ψ (cf. [4])", and "invoking the decomposition of the Möbius
function, as was carried out in [4]", where [4] = MV 1981). The internal details of MV 1981 are
*(unverified)*: I did not read the paper.

Mathlib has none of this: no truncated Fourier expansion of ψ with error control (Vaaler),
no van der Corput A/B processes or exponent pairs, no Vaughan identity for μ. **Out of reach:
effort XL, and it would still only reproduce a 1981 result.**

### Lean prior art (searched 2026-11-24)

I searched Mathlib `fc4f59e5`, formal-conjectures `86a2f58a`, PrimeNumberTheoremAnd `a4fb6989`,
GitHub code search (`Squarefree` with `pi ^ 2`, Lean) and the rh-lemmas inventory.

- **`E ≪ √x`** is in Lean: Woett/Lean-files `ErdosProblem1102PropertyQDensity.lean` (commit
  `1e075c4f`, cited by formal-conjectures 1102). It has
  `sum_squarefree_indicator_eq_sum_moebius_floor` (the identity
  `Q(N) = Σ_{d≤√N} μ(d)⌊N/d²⌋`) and `SF_count_bound` (`|Q(n) − (6/π²)n| ≤ 4·√n`). Mathlib
  itself has neither.
- **`E = o(√x)`**: no Lean proof found. The formal-conjectures variant is `sorry`. Mathlib has
  PNT (`Chebyshev.isEquivalent_psi_id`, `Mathlib/NumberTheory/LSeries/WeakPNT.lean`) but not
  `M(x) = o(x)`. PrimeNumberTheoremAnd has `mu_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, μ n)
  =o[atTop] fun x ↦ x` (`PrimeNumberTheoremAnd/Consequences.lean:1959`, Lean v4.35.0, Apache
  2.0). Combining it with Woett's identity gives `o(√x)` in Lean at effort S. Nobody has done it.
- **Walfisz's bound**: no Lean proof anywhere I found. riemann-hypothesis has only the de la
  Vallée Poussin region (`Formalism.ZF.zeroFreeRegion`, `gzPNT`, Riesz-weighted ψ), not
  Vinogradov–Korobov, and no `M(x)` bound.
- **Axer or any RH-conditional squarefree bound**: none found.

### The Mertens input: mertens-rh, branch `finality` (head `f7ec42d2`, 2026-11-24)

`main` is still the scaffold ("nothing is proved here yet"). `finality` proves Littlewood's
bound with no `sorry` and standard axioms only (README `#print axioms` block, commit `1191f36`):

```lean
-- Mertens/Statement.lean
noncomputable def mertens (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, μ n
def MertensBound : Prop :=
  ∀ ε : ℝ, 0 < ε → (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε)
-- Mertens/Main.lean
theorem Mertens.mertens_of_RH (hRH : RiemannHypothesis) : Mertens.MertensBound
theorem Mertens.abs_mertens_nat_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/4) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → |(mertens N : ℝ)| ≤ K * ((N : ℝ) + 1) ^ (1/2 + 3*ε)
```

`Unconditional/MertensUnconditional.lean` provides `mertens_bound`. `Mertens/Abel.lean` has the
Abel-summation lemma `∑ μ(n) w(n) = −∑ M(n)(w(n+1) − w(n))` and an interpolation lemma, which
step 4 below can reuse. Rule 7 is a blocker: `finality` must merge to `main` before another
repo can pin it.

## 3. Genuineness verdict: **(a) published conditional theorem, we would only formalise it**

"RH ⇒ E(x) ≪ x^{2/5+ε}" is Axer (1911) and a textbook exercise (MV I, Ex. 13.2.1.14 with the
reduction Ex. 6.2.1.8). Five later published RH-conditional results are stronger: 1/3 or 9/28,
8/25, 7/22, 17/54, 11/35. Label: **RH-consequence**. The unconditional `x^{2/5+ε}` is open, since
the best unconditional bound is `x^{1/2−o(1)}`, so it passes the "open problems only" rule. It
says nothing new about Erdős 969 itself.

What a careful mathematician would say if we announced it: *"A Lean formalisation of Axer's
1911 conditional bound, which is a homework exercise in Montgomery–Vaughan and 30+ years behind
the RH-conditional state of the art (Liu's 11/35). Fine as a formalisation, no mathematical
news."* If it were announced through the riemann-hypothesis import as "E(x) ≪ x^{2/5+ε}
unconditionally", it would read as a claim resting on an unverified RH proof. AGENTS.md
already forbids that wording.

Does a Lean proof settle any formal statement?
- `erdos_969` (open): **no**.
- No RH variant exists upstream, so nothing in formal-conjectures is settled directly.
- As a by-product, the reduction plus a Mertens bound gives `E = o(√x)`, which **closes the
  `research solved` variant `erdos_969.variants.prime_number_theorem`**. Through RH (mertens-rh)
  that is tier U and label *known, via GRH here*. Through PNT+'s `mu_pnt` it is tier D and label
  *known*. Either way it would be the first Lean proof I found, and the variant has no
  `formal_proof` attribute, so it could be contributed upstream. Under the "open problems only"
  rule this cannot be the **target**, only a corollary.
- `erdos_969.variants.evelyn_linfoot` (`research solved`) is also within reach. It needs the
  Mellin continuation of `ζ(s)/ζ(2s)` past `Re s = 1/2`, a Landau-type pole argument, and one
  zero of ζ on the line. li-criterion-rh has
  `exists_nontrivialPosZeros_norm_gt : ∃ ρ ∈ nontrivialPosZeros, R < ‖ρ‖`
  (`LiCriterion/Zeros.lean:235`). Effort M–L. Label *known* (or *known, via GRH here* if RH is
  used to place the zero on the line), so it is again not an allowed target.

## 4. Proof route for (i), Axer

Write `M = Mertens.mertens`, `x ∈ ℕ` large, and `y ∈ [1, √x]` (in the end `y = x^{2/5}`). Use
the integer `Y = ⌊y⌋₊` throughout to avoid real/ℕ floor friction.

1. **Möbius identity.** `Q(x) = Σ_{d ≤ √x} μ(d) ⌊x/d²⌋`. Port Woett's
   `sum_squarefree_indicator_eq_sum_moebius_floor`, or reprove it from Mathlib's
   `Nat.sq_mul_squarefree` and `ArithmeticFunction.sum_moebius` style lemmas. Effort S.
2. **Hyperbola split.** For `1 ≤ Y ≤ √x`:
   `Σ_{Y<d≤√x} μ(d)⌊x/d²⌋ = Σ_{m ≤ x/Y²} (M(√(x/m)) − M(Y))`. Expand `⌊x/d²⌋ = #{m ≥ 1 : m d² ≤ x}`
   and swap the finite double sum over `{(d,m) : d > Y, m d² ≤ x}` (`Finset.sum_comm'` or
   `sum_sigma`). `m ≤ x/Y²` is exactly the range where `√(x/m) ≥ Y`. This is the main
   bookkeeping step: effort S–M.
3. **Short range.** `Σ_{d≤Y} μ(d)⌊x/d²⌋ = x Σ_{d≤Y} μ(d)/d² + O(Y)` (`|frac| ≤ 1`), and
   `Σ_{d≥1} μ(d)/d² = 1/ζ(2) = 6/π²`. Mathlib: `LSeries_zeta_mul_Lseries_moebius`
   (`Mathlib/NumberTheory/LSeries/Dirichlet.lean:296`), `LSeries_zeta_eq_riemannZeta`,
   `riemannZeta_two` (`HurwitzZetaValues.lean:224`), and summability from
   `LSeriesSummable_moebius_iff`. Effort S.
4. **Tail of the series.** Hypothesis `|M(u)| ≤ K u^{α'}` with `α' = 1/2 + ε'`. Abel summation
   gives `|Σ_{d>Y} μ(d)/d²| ≤ C K Y^{α'−2}`, using `w(n) = n^{−2}` and
   `|w(n+1) − w(n)| ≤ 2n^{−3}`, so `Σ_{n>Y} n^{α'−3} ≪ Y^{α'−2}`. Reuse mertens-rh
   `Mertens/Abel.lean`. Sum–integral comparison: Mathlib `AntitoneOn.sum_le_integral`
   (`Analysis/SumIntegralComparisons.lean`). Contribution `x·Y^{α'−2}`. Effort S–M.
5. **Hyperbola sum.** `Σ_{m≤X} |M(√(x/m))| ≤ K x^{α'/2} Σ_{m≤X} m^{−α'/2} ≤ C K x^{α'/2} X^{1−α'/2}`
   with `X = x/Y²`. That is `C K x·Y^{α'−2}`. The term `|M(Y)|·X ≤ K x Y^{α'−2}` is the same
   size. Sum–integral comparison again. Effort S.
6. **Optimise.** `|E(x)| ≤ C(Y + x·Y^{α'−2})`. Take `y = x^{1/(3−α')}`, so `Y ≍ x^{1/(3−α')}`
   and `x·Y^{α'−2} ≍ x^{1/(3−α')}`. With `α' = 1/2 + ε'`:
   `1/(3 − α') = 1/(5/2 − ε') = 2/(5 − 2ε') ≤ 2/5 + ε` for `ε' ≤ ε` small (since
   `2/(5−2ε') − 2/5 = 4ε'/(5(5−2ε')) < ε'`). Exponent check at `ε' = 0`:
   `1 − (3/2)(2/5) = 2/5`. Then pass to `=O[atTop]` on ℕ and handle `Y ≥ 1`, `Y ≤ √x` for
   large x. Effort S.
7. **Assemble.**
   - Main library: `axer_of_mertens` (D: hypothesis is a Mertens bound, no RH) and
     `axer_of_RH (hRH) := axer_of_mertens (Mertens.mertens_of_RH hRH)` (C).
   - `Unconditional/`: one line with `riemannHypothesis` (U).
   - Corollary `o(√x)`: the same reduction with `M = o(u)` and `y = δ√x`. Use the RH route
     (U), or a port of PNT+'s `mu_pnt` (D). Effort S.

No explicit constant and no finite computation is needed anywhere: every statement is an `O`.
The only constants are existential Ks from `abs_mertens_nat_le`. Dependencies: erdos-985
(transitively), mertens-rh after `finality` merges, lindelof-rh (transitively).

## 5. Recommended target statements (`Squarefree969/Statement.lean`, name illustrative)

Copy `squarefreeCounting` and `squarefreeCountingError` from formal-conjectures verbatim
(rule 3) and link `969.lean` at `86a2f58a`.

```lean
/-- Axer (1911): `E(x) = O(x^{2/5+ε})` for every `ε > 0`. -/
def AxerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℕ => squarefreeCountingError x) =O[atTop] fun x : ℕ => (x : ℝ) ^ (2 / 5 + ε)

-- general reduction, tier D (no RH): a Mertens exponent α gives the exponent 1/(3-α)
theorem squarefreeError_of_mertens {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hM : ∀ ε : ℝ, 0 < ε → (fun x : ℝ => (Mertens.mertens x : ℝ)) =O[atTop] fun x => x ^ (α + ε)) :
    ∀ ε : ℝ, 0 < ε →
      (fun x : ℕ => squarefreeCountingError x) =O[atTop] fun x : ℕ => (x : ℝ) ^ (1 / (3 - α) + ε)

theorem axer_of_RH (hRH : RiemannHypothesis) : AxerBound          -- tier C, RH-consequence
theorem axer_unconditional : AxerBound                            -- Unconditional/, tier U

-- corollary, matches the formal-conjectures variant verbatim
theorem erdos_969_variants_prime_number_theorem :
    (fun x => |squarefreeCountingError x|) =o[atTop] (fun x : ℕ => (x : ℝ).sqrt)
```

Weaker fallback, if step 2's bookkeeping fights back: the one-sided split without the
hyperbola trick. Bound the tail `Σ_{d>y} μ(d)⌊x/d²⌋` directly by Abel summation of
`⌊x/d²⌋` against `M`. That gives `E ≪ x^{1/2}` only and adds nothing, so there is no
meaningful fallback below 2/5. Step 2 is the content.

## 6. Effort and risk

- **(i) Axer: S–M.** Roughly 500–1000 lines. All inputs exist: the identity (Woett/Mathlib), the
  Mertens bound (mertens-rh `finality`), Abel summation (mertens-rh), sum–integral comparison
  (Mathlib).
- **Riskiest step:** step 2, the exchange of summation over `{(d,m) : Y < d, m d² ≤ x}` with
  nat floors and `Nat.sqrt`. Mathematically trivial, but it is where the time goes.
- **Process risk:** mertens-rh `finality` is not on `main`. Rule 7 needs it merged first.
- **(ii) converses: M**, but low value: vacuous at tier U, and the θ < 1/2 ⇒ quasi-RH direction
  is folklore without a proof, so it is not a sound target.
- **(iii) MV 1/3 / 9/28 and beyond: XL**, no exponential-sum infrastructure. No-go.

**Recommendation: no-go as a headline target, go only as a cheap add-on.** It is a 1911 result,
superseded five times, and does not touch Erdős 969 as posed. If done, the honest framing is
"a Lean formalisation of Axer's RH ⇒ x^{2/5+ε} (RH-consequence), with the formal-conjectures
`research solved` variant `E = o(√x)` as a corollary". The best home is a short module beside
mertens-rh (an application of `mertens_of_RH`), not a new flagship repo. For "genuine" results
this problem offers nothing: the open content (exponent < 11/35 under RH, or 1/4 + ε) is far out
of reach.

## 7. Open questions for the user

1. Is a superseded 1911 RH-consequence worth a slot at all, given the "most genuine results"
   goal? My answer is no, except as an add-on to mertens-rh.
2. If done: put it as a module in mertens-rh (simplest pins) or in a new `erdos-969` repo?
3. Should we contribute the `E = o(√x)` variant proof (and possibly Evelyn–Linfoot) upstream
   to formal-conjectures? They are *known* results, outside the target rule, but they are
   `research solved` sorries with no `formal_proof` link. Prefer the tier-D route via a port of
   PNT+'s `mu_pnt` over the RH route.
4. Do you want someone to read MV 1981 and Graham 1981 directly to settle whether 9/28 is MV's?
   That only matters if a README cites the chain.
