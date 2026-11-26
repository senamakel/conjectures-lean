# Lane `disproof-literature`: conjectures we can refute by connecting existing results

Lane `disproof-literature`, 2026-11-26. Research only. Nothing was built and no repository was
edited. Numbers come from C and `python3 -I` scripts in the session scratchpad (`disproof/mert.c`,
`disproof/hajos.py`). Claims I could not confirm from a primary source are marked *(unverified)*.
"fc" means formal-conjectures at `9097e2f` (2026-11-24); paths are relative to `FormalConjectures/`.

## Main finding

The literature has very few refutations that follow from **Dirichlet** GRH alone without LI, and
the ones that exist are taken: Knapowski–Turán (Kaczorowski 1995; NEXT_TARGETS, 1337, and fc's
`knapowski_turan_natural_density_false`) and Pomerance 1974 (1337). Every other GRH-conditional
refutation I found needs RH for the Dedekind zeta functions of non-abelian fields, or LI, or a
finite range far beyond `native_decide`.

The useful finds sit in the other two sub-lanes:

- **Sub-lane 2 (X ⇒ ¬Y).** fc states Granville's 1995 prime-gap conjecture next to three
  conjectures it contradicts: Shanks's `G(x) ~ log² x`, Cramér's `limsup = 1`, and the strict
  bound `g_n < log² p_n`. Firoozbakht's conjecture contradicts it too, once the prime number
  theorem is available. Each refutation takes a few lines, both sides are already fc statements,
  and none is in the atlas.
- **Sub-lane 3 (finite certificates).** Three famous refutations have short certificates and, as
  far as I could find, no Lean proof. Pólya's conjecture fails at `L(906150257) = 1` and von
  Sterneck's at `M(7725038629) = 43947`. Both values take a few million operations with the
  Dirichlet-hyperbola recursion, so one proved-sound checker settles both. Hajós's conjecture fails
  for Catlin's `C₅[K₃]`, and a 15-vertex counting certificate (computed here) settles it. fc
  states it as `HajosConjecture.hajos_conjecture`, with a `sorry` and no `formal_proof`.

The large 2026 vein, the Jacobian counterexample and everything it refutes, is already mined
(details under Rejected).

**Policy catch for sub-lane 3.** Pólya, von Sterneck, Hajós and Euler's Graeco-Latin conjecture
were refuted decades ago, so their literature label is *known*. The rule of 2026-11-24 ("open
problems only") excludes *known* results. The 2026-11-26 widening of scope does not change that:
it widens the *areas*, not the openness test. This lane was asked for explicitly, but starting
any sub-lane-3 item still needs the owner's sign-off, recorded in `NEXT_TARGETS.md`.

## Candidates, easiest first

### 1. Granville's prime-gap conjecture is incompatible with Shanks, Cramér's `limsup = 1` and the strict bound · S · class 2 (both sides open)

- **Statements (fc, word for word).**
  - `CramerConjecture.cramer_conjecture.variants.granville (c : ℝ) (hc : c < 2 * Real.exp (-Real.eulerMascheroniConstant)) : ∃ᶠ n : ℕ in Filter.atTop, c ≤ cramerRatio n`
    (`Wikipedia/CramerConjecture.lean`, research open). Here
    `cramerRatio n = primeGap n / (log (nth Prime n))²`.
  - `CramerConjecture.cramer_conjecture.variants.limsup_eq_one`, which starts
    `(∀ ε > 0, ∀ᶠ n in atTop, cramerRatio n ≤ 1 + ε) ∧ …` (research open).
  - `CramerConjecture.cramer_conjecture.variants.strict_bound (n) (hn : 4 ≤ n) : cramerRatio n < 1`
    (research open).
  - `MaximalPrimeGap.shanks_maximal_prime_gap_conjecture : (fun x => (sup_primeGap x : ℝ)) ~[atTop] (fun x => (log x)^2)`
    (`Wikipedia/MaximalPrimeGap.lean`, research open). Here
    `sup_primeGap x = (range (primeCounting' ⌈x⌉₊)).sup primeGap`
    (`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean:35`).
- **Edges.** `limsup_eq_one → ¬ granville-at-some-c`, `strict_bound → ¬ …`, `shanks → ¬ …`. Take
  `c = 1`. The proof needs only `1 < 2e^{−γ}`, which is `γ < log 2`, and Mathlib has both bounds:
  `Real.eulerMascheroniConstant_lt_two_thirds` (`Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean:174`)
  and `Real.log_two_gt_d9` (`Mathlib/Analysis/Complex/ExponentialBounds.lean:86`); `2/3 < 0.6931`.
  For `limsup_eq_one`, use `c = 1.1` and `ε = 0.05`. For Shanks, use
  `primeGap n ≤ sup_primeGap (p_n + 1)` and `log(p_n + 1)/log p_n → 1`; the fc lemma
  `sup_primeGap_mono` helps here.
- **Source.** The incompatibility is Granville's own remark (Granville, *Harald Cramér and the
  distribution of prime numbers*, Scand. Actuar. J. 1995, 12–28), and the fc docstrings record it
  ("contradicting Shanks's conjecture", "contradicts `cramer_conjecture.variants.granville`").
  I did not read Granville's paper *(unverified from the primary source; quoted from the fc
  docstrings)*.
- **Lean.** None of the four edges exists. FC proves no edge between these statements. The atlas
  has only the positive edges `limsup_eq_one ⇒ cramer_conjecture` and `shanks ⇒ cramer_conjecture`
  (lane `implications`).
- **Effort.** S (well under a day for the three edges).
- **Catch.** It is a theorem of the form `¬(X ∧ Y)` between two open heuristic conjectures. It
  settles neither, and most of its value is that the atlas then records the conflict formally.
  Granville's conjecture is the better-supported side (Maier's theorem), so in practice these
  edges say "Granville ⇒ ¬Shanks", "Granville ⇒ ¬Cramér limsup", and so on.

### 1b. Firoozbakht ⇒ ¬Granville · S–M · class 2

- **Statement.** `Firoozbakht.firoozbakht_conjecture (n) : firoozbakhtSeq (n+1) < firoozbakhtSeq n`,
  with `firoozbakhtSeq n = (nth Prime n)^(1/(n+1))` (`Wikipedia/Firoozbakht.lean`), against
  `granville` at `c = 1`.
- **Deduction (mine, short).** From the hypothesis, `p_{n+1} < p_n^{(n+2)/(n+1)}`, so
  `g_n < p_n (exp(log p_n/(n+1)) − 1)`. Write `n + 1 = π(p_n)`. If `π(x) ≥ κ x / log x` for
  large `x`, with `κ > e^γ/2 = 0.89054`, then `g_n ≤ (1 + o(1)) log² p_n / κ < 1.1229 log² p_n`,
  which contradicts Granville for `c` just below `2e^{−γ}`. Any `κ > 0.8906` will do, so
  `π(x) ~ x/log x` is more than enough.
- **Premise input.** You need PNT, or `π(x) ≥ x/log x` for large `x`. Two sources. One is
  PrimeNumberTheoremAnd (Apache-2.0), which `lemma-mining-external-inventory.md` lists as proving
  PNT consequences; check the exact π-asymptotic declaration name before using it. The other is
  schoenfeld-rh `pi_bound` (tier U), whose `|π − li| < √x log x/(8π)` gives it at once but would
  pull riemann-hypothesis into a statement that does not need RH.
- **Source.** Wikipedia's Firoozbakht page and Kourbatov (arXiv:1503.01744) say that Firoozbakht
  implies `g_n < log² p_n − log p_n` and so conflicts with Granville's heuristic *(unverified)*.
  fc's `firoozbakht_conjecture_consequence` is the strong form (L, per lane `implications`). The
  route above avoids it.
- **Effort.** S–M. **Catch.** As for #1. The PNT dependency should be imported, not reproved.

### 2. Hajós's conjecture is false: Catlin's `C₅[K₃]` · S–M · class 1 (no hypothesis) · *known*

- **Statement (fc).** `HajosConjecture.hajos_conjecture : ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ), (k : ℕ∞) ≤ G.chromaticNumber → ContainsSubdivision (completeGraph (Fin k)) G`
  (`Wikipedia/HajosConjecture.lean`). It is `research solved`, with a `sorry` and **no
  `formal_proof` attribute**. `ContainsSubdivision` is defined in the same file
  (`IsSubdivisionModel`: injective branch map, paths whose interiors avoid the branch vertices
  and are pairwise disjoint).
- **Source.** P. A. Catlin, *Hajós' graph-coloring conjecture: variations and counterexamples*,
  JCTB 26 (1979) 268–274. MathWorld ("Catlin graph") identifies the counterexample as the
  lexicographic product `C₅[K₃]`, with chromatic number 8 and no `K₈`-subdivision. I did not
  read Catlin's paper; the certificate below does not depend on his argument.
- **Certificate (computed, `disproof/hajos.py`).** `G = C₅[K₃]` has 15 vertices and is 8-regular.
  - `α(G) = 2`, so `χ(G) ≥ ⌈15/2⌉ = 8`: a 7-colouring would have a colour class of size 3.
  - No `K₈`-subdivision. Take any branch set `B` of size 8 (there are `C(15,8) = 6435`). Each pair
    of non-adjacent branch vertices `u, v` needs a path whose interior avoids `B`, so it has at
    least `d_{G−(B∖{u,v})}(u, v) − 1` interior vertices. Those interiors are disjoint and lie
    outside `B`. Summing this lower bound over the non-adjacent pairs gives at least
    `|V∖B| + 2 = 9 > 7` for **every** `B`; the largest slack over all 6435 sets is −2. For `k = 7`
    the bound fails (1530 sets have slack ≥ 0), as it should.
- **Lean work.** You need four pieces:
  1. `χ ≥ 8` from `α = 2`, by pigeonhole on colour classes.
  2. A lemma: the interior of a path from `u` to `v` in `G` that avoids `S` has at least
     `dist_{G−S}(u, v) − 1` vertices, and disjoint interiors give `Σ ≤ |V∖B|`.
  3. The finite check over 6435 sets: `decide +kernel`, a small `native_decide`, or a hand proof
     over the branch-count vectors `(a₁, …, a₅)` up to the dihedral symmetry of `C₅`.
  4. A `Fintype` instance on `Fin 5 × Fin 3`.
- **Lean prior art.** facebookresearch/atlas-lean
  `v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean` (Erdős–Fajtlowicz). Its
  `hajos_conjecture_counterexample` is conditional on a probability hypothesis about
  `probKtSubdiv`, so it is not an unconditional refutation. GitHub code search for
  `hajos_conjecture` found nothing else (fc and its mirrors). The later search for "Catlin" was
  blocked by the rate limit.
- **Effort.** S–M (2–4 days, mostly the path-interior counting lemma).
- **Catch.** The label is *known*, so the sign-off rule applies. Only `k = 8` is covered. fc's
  `hajos_conjecture.variants.catlin` (every `k ≥ 7`) needs Catlin's family and a `k = 7` graph,
  which I did not size.

### 3. Pólya's conjecture is false: `L(906150257) = 1` · S–M · class 1 · *known*

- **Statement.** Pólya (1919): `L(n) = Σ_{k≤n} λ(k) ≤ 0` for every `n ≥ 2`. Haselgrove (Mathematika
  5 (1958)) disproved it without an explicit `n`. Lehman (Math. Comp. 1960) found
  `L(906180359) = 1`, and Tanaka (Tokyo J. Math. 3 (1980)) found the smallest counterexample,
  `n = 906150257` (Wikipedia; Brent–van de Lune, arXiv:1112.4911). There is **no fc statement**
  (grep for Pólya, Liouville and `906150257` over fc: nothing relevant), so the statement has to
  be written here against Mathlib's `ArithmeticFunction.liouville`
  (`Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean`).
- **Certificate (computed, `disproof/mert.c`).** `L(906150257) = 1` and `L(906150256) = 0`,
  matching Tanaka. Also `L(906150259) = 3` and `L(906150260) = 4`. The method uses
  `L(x) = Σ_{d ≤ √x} M(⌊x/d²⌋)`, with `M` from the recursion `Σ_{n≤x} M(⌊x/n⌋) = 1`, memoised on
  the values `⌊X/k⌋`. A Möbius sieve covers `x ≤ X^{2/3} = 936,421`. It takes 3.65·10⁶ recursion
  steps, under a second in C. A direct sieve of 9·10⁸ values is not needed.
- **Lean work.**
  1. The identities `Σ_{n≤x} M(⌊x/n⌋) = 1`, from `ArithmeticFunction.moebius_mul_coe_zeta` and the
     usual divisor-to-floor swap, and `λ = Σ_{d²∣n} μ(n/d²)`, via multiplicativity
     (`isMultiplicative_liouville`). Mathlib's Liouville file has only five lemmas, so the
     square-indicator identity is new.
  2. An evaluator (sieve array plus memo table) proved equal to the Mathlib sums.
  3. One `native_decide`, with the robin-rh and weinberger-grh checkers as templates.
- **Lean prior art.** GitHub code search: `906150257` (only Perl, C, GAP and data files),
  `polya_conjecture` and `PolyaConjecture`. The only Lean hit is andyprevalsky/auto-math
  `inspiration/lean-verified/disproof-templates.lean`, whose `polya_conjecture_false` is a `sorry`
  over an `opaque` summatory function. Mathlib `Counterexamples/` has nothing on it. 1337: not
  listed.
- **Effort.** S–M (3–5 days with #4, since they share the checker).
- **Catch.** The label is *known*. One `native_decide` is documented. The statement is ours, so
  the auditor must check it against Pólya's wording (`n ≥ 2`, `λ(1) = 1`).

### 4. Von Sterneck's conjecture is false: `|M(7725038629)| > ½√7725038629` · S (after #3) · class 1 · *known*

- **Statement.** Von Sterneck conjectured `|M(x)| < ½√x` for `x > 200` (arXiv:2607.07566 and
  arXiv:1810.05244, both secondary). Neubauer (1963) disproved it near `7.76·10⁹`. arXiv:1810.05244
  gives `7725038629` as the least counterexample above 200 *(minimality unverified; not needed)*.
  There is no fc statement. In integers: `¬ ∀ x > 200, 4·M(x)² < x`.
- **Certificate (computed).** `M(7725038629) = 43947` and `M(7725038628) = 43946`.
  `4·43947² = 7,725,355,236 > 7,725,038,629`, while `4·43946² = 7,725,003,664 <` it, so the first
  value is a counterexample by a margin of only 0.00102 in `|M|/√x`. The run takes 1.54·10⁷
  recursion steps with a sieve to 3.9·10⁶. A sanity check also gave `M(1000) = 2`.
- **Lean work.** The same evaluator as #3, with no `λ` identity needed.
- **Prior art.** GitHub code search for `7725038629` and `sterneck`: no Lean. A `language:Lean`
  search was blocked by the rate limit.
- **Effort.** S once #3 exists. **Catch.** Von Sterneck is less famous than Mertens. The Mertens
  conjecture itself has no explicit counterexample (see Rejected), so this is the strongest
  Mertens-type refutation a finite certificate can give.

### 5. Euler's Graeco-Latin conjecture fails at order 10 · S · class 1 · *known*

- **Statement.** Euler (1782): no pair of orthogonal Latin squares of order `n ≡ 2 (mod 4)`.
  Parker (1959) gave an order-10 pair, and Bose–Shrikhande–Parker (1960) settled every `n ≠ 2, 6`.
  fc `Paper/LatinSquare.lean` defines `Orthogonal` and `HasCompleteMOLS` but has no Euler
  statement.
- **Certificate.** An explicit pair of 10×10 squares (copy from Parker's paper or a standard
  reference), checked by `decide` over 100 cells.
- **Prior art: not checked.** The GitHub code search was rate-limited before it ran. It is so
  short that it probably exists somewhere; search before starting.
- **Effort.** S (hours). **Catch.** Trivial once the squares are copied. Its only value is a
  catalogue entry.

### 6. Artin's original (1927) density is wrong for `a = 5`, given Hooley's hypothesis · M · class 2 (tier C at best) · RH-consequence (non-abelian GRH)

- **Statement.** Artin's first conjecture gave density `A = ∏(1 − 1/(p(p−1)))` for every
  non-power `a`. The Lehmers' counts (1957–62) disagreed, and the corrected density for squarefree
  `a ≡ 1 (mod 4)` is `A·(1 − μ(|a|)∏_{p∣a} 1/(p²−p−1))` *(history unverified; see Stevenhagen,
  J. Théor. Nombres Bordeaux 15 (2003), and Moree's survey, arXiv:1112.4816, which fc cites)*. For
  `a = 5`, fc's own `entanglementFactor 5 1 = 1 − 1/(1+5−25) = 20/19`. Target:
  `HooleyHypothesis 5 → ¬ (S 5).HasDensity ArtinConstant {p | p.Prime}`. Its value is in showing
  that fc's `artin_primitive_roots.parts.ii` hypothesis `¬a₀ ≡ 1 [ZMOD 4]` cannot be dropped.
- **Premise.** `HooleyHypothesis` (fc `Wikipedia/ArtinPrimitiveRootsConjecture.lean`) is GRH for
  `ζ` of `ℚ(ζ_k, a^{1/k})`, which is non-abelian. riemann-hypothesis cannot discharge it
  (NEXT_TARGETS, "Unconditional Artin"), so the result stays tier C permanently.
- **Reuse.** artin-grh already has `kummerDensity a` (`Artin/Kummer/Density.lean:225`),
  `moebius_div_kummerDegree_of_squarefree`, `exists_sq_cyclotomicField_iff` (`:393`, the
  `√a₀ ∈ ℚ(ζ_k)` entanglement) and a sorry-free Hooley route.
- **Missing.**
  1. Check that the density artin-grh obtains is exactly `kummerDensity a`. The headline only
     says `∃ x > 0`.
  2. Evaluate `kummerDensity 5 = (20/19)·A` as an Euler product. The degree is `kφ(k)/2` when
     `10 ∣ k`, and `kφ(k)` otherwise.
  3. Show `A > 0` and that densities are unique.
- **Prior art.** 1337 lists "Artin density" as unresolved (`newsfeed.md` §1(b)). fc has no such
  statement.
- **Effort.** M. **Catch.** Tier C forever, and it refutes a 1927 guess that Artin himself
  withdrew. Take it only as an extension of artin-grh.

### 7. (Not recommended) Maier's theorem refutes the Cramér-model short-interval asymptotic · L · *known, via GRH here*

- Maier (Michigan Math. J. 32 (1985)): for every `λ > 1`, `π(x + (log x)^λ) − π(x)` is not
  `~ (log x)^{λ−1}`. That asymptotic is what Cramér's model predicts. psi-grh's uniform
  `|π(x;q,a) − li x/φ(q)| ≤ C√x log(qx)` is exactly the equidistribution the matrix method
  needs, and it removes the exceptional-modulus bookkeeping. You would still need the oscillation
  of Buchstab's function `ω(u) − e^{−γ}`, a delay-differential-equation lemma not in Lean as far
  as I know *(not searched)*.
- It is excluded by the 2026-11-24 rule: Maier is unconditional, so the GRH route is the weaker
  proof. It is listed because it is the one place where a project of ours gives a large refutation
  a real shortcut.

## Rejected, with reasons

| Idea | Reason |
|---|---|
| Knapowski–Turán natural-density conjecture (Kaczorowski 1995, GRH) | Taken: NEXT_TARGETS rejected list, 1337 RH-transfer, fc `knapowski_turan_natural_density_false`. Also needs certified zeros of `L(s, χ₄)` |
| Pomerance 1974 nonexistence (Ford–Luca + GRH); BFLPS Carmichael λ; Riffaut; Jutila | 1337 RH-transfer list (do not repeat) |
| Rubinstein–Sarnak bias, Shanks–Rényi races | Need LI |
| Chebyshev's `π(x;4,3) ≥ π(x;4,1)` (first fails at 26861, Leech 1957) | No published "for all x" conjecture to refute; Chebyshev's actual claim is the Abel-weighted limit (1337). A trivial `decide` |
| `π(x;3,2) ≥ π(x;3,1)` (fails at 608981813029, Bays–Hudson 1978) | Same issue, and a 6·10¹¹ prime count is a large verified segmented sieve (L) |
| Mertens conjecture `|M(x)| < √x` | Odlyzko–te Riele is non-constructive; no explicit counterexample is known (least one is about `exp(5.15·10²³)`, arXiv:2502.21021). Needs zero data: XL |
| Turán's conjecture `Σ_{n≤x} λ(n)/n ≥ 0` | First failure at 72,185,376,951,205 (Borwein–Ferguson–Mossinghoff 2008 *(unverified)*). The same hyperbola identity works, but it needs about 2·10¹⁰ interval-arithmetic steps with a tiny sign margin: XL |
| Skewes / `π(x) < li(x)` | No explicit crossing; the best upper bound on the first crossing is about 1.4·10³¹⁶ |
| Euler's sum of powers (k = 4, 5) | Done: fc `eulers_sum_of_powers_conjecture.false_for_k4/k5` by `decide`; Mathlib `Counterexamples/EulerSumOfPowers.lean` |
| Borsuk | Done: fc `borsuk_conjecture` has a `formal_proof` (OpenAI 2026, dimension 9) |
| Jacobian conjecture, Dixmier, Poisson | Done in fc: `jacobian_conjecture` is proved in fc itself (Alpöge's map), and Dixmier/Poisson carry `formal_proof`. Isabelle AFP `Jacobian_Counterexample` too |
| Consequences of ¬JC: Gaussian moments, Zhao's vanishing conjecture, Mathieu, cubic-linear JC | Crowded. GMC: Long, arXiv:2607.18186, and LeanPool `GaussianMomentsCounterexamples.lean`. VC/HVC/cubic-linear JC(90): de Bondt, arXiv:2610.24889. Mathieu: active GitHub repos (`jacobian-anatomy/mathieu-su79`, `jacobian-cascade-lab`). None is in fc |
| Keller (dim 8), Hedetniemi (Shitov) | sneed-and-feed/lean-theorems-3 claims both (`keller_conjecture_eight_false_of_mackey_clique`, `not_hedetniemi_conjecture`); quality not audited. Hedetniemi's graphs are enormous anyway |
| Kaplansky unit conjecture (Gardam) | Lean 4 formalisation by Gadgil–Tadipatri exists *(from memory; unverified)* |
| Aharoni–Korman, Hilbert SOS (Motzkin), cyclotomic coefficients (105), Heawood | Mathlib `Counterexamples/` |
| Sidorenko / forcing | Lane `newsfeed` #4 |
| Hensley–Richards (k-tuples vs `π(x+y) ≤ π(x)+π(y)`) | Taken (lanes `atlas`, `fc-scan`) |
| Hirsch conjecture (Santos 2012) | Needs Santos's strong `d`-step theorem plus a prismatoid width computation; no fc statement; L–XL |
| Tait's conjecture (Tutte graph) | Mathlib has no planar-graph definition; no fc statement |
| Goldbach's other conjecture (5777), Fermat numbers (641 ∣ F₅), Polignac (127) | One-line `decide`/`norm_num` facts, low value; prior art likely, not searched (rate limit) |
| Imaginary quadratic fields with class group of exponent 3: list closed by GRH (Boyd–Kisilevsky 1972, Elsenhans–Klüners–Nicolae *(unverified)*) | A completeness proof, not a disproof. Sized with weinberger-grh's split-prime inequality and `x = (n/4)^{1/3}`: the analytic step only starts at `n ≈ 2·10¹²` (against `10⁸` for idoneal), so the finite check is about 2·10⁴ × weinberger's. Out |
| Euclidean quadratic fields (Weinberger), Ono–Soundararajan `x²+y²+10z²` | GRH for non-abelian Dedekind zeta / modular L-functions: not in riemann-hypothesis |
| Friedlander–Granville limitation of Elliott–Halberstam-type uniformity | Unconditional, and needs the Maier matrix method plus Siegel-zero handling: XL |
| Montgomery's `n_p ≫ log p log log p` infinitely often under GRH | Not a refutation of a named conjecture; XL |
| Cramér limsup vs Maier | Maier refutes the short-interval model, not the gap conjecture; see #7 |

## What I searched

- **fc.** Every file matching Pólya, Liouville, Mertens/Sterneck, sum of powers, Graeco/orthogonal
  Latin, Granville, Shanks, Chebyshev, Keller, Borsuk, Hirsch, Tait, Hajós, bunkbed, Goldbach
  other, Fermat number, Turán, Haselgrove, Firoozbakht and Artin. A grep of all fc for
  "contradict", "incompatib", "refutes", "false under", "conditional refutation" and similar
  phrases, with every hit read; that grep found the Jacobian/Poisson/Dixmier family.
- **Mathlib** (`fc4f59e5`, the workspace pin). `Counterexamples/` listing; `Liouville.lean`;
  `Fermat.lean`; Euler–Mascheroni and `log 2` bounds.
- **Erdős data** (atlas copy of `erdos.jsonl`). Entries mentioning GRH/RH together with
  "disproved/false/no": only #1138, already disproved in Lean.
- **GitHub code search.** `906150257`, `polya_conjecture`, `PolyaConjecture`, `7725038629`,
  `sterneck`, `hajos_conjecture`, `gaussian moments conjecture`, `mathieu conjecture`,
  `keller_conjecture`. After that the rate limit ran out, so the Graeco-Latin, "Catlin",
  `language:Lean` Pólya/Sterneck, Goldbach-other and Fermat searches did not run.
- **Workspace.** `AGENTS.md`, `NEXT_TARGETS.md`, all 2026-11-26 sweep reports, the 1337 inventory,
  `edges.jsonl` (no Granville, Pólya, Sterneck or Hajós edge), artin-grh and weinberger-grh
  sources.
- **Web.** Wikipedia and arXiv on Pólya and the Mertens function; MathWorld on the Catlin graph;
  arXiv abstracts 2610.24889 and 2607.18186; Isabelle AFP `Jacobian_Counterexample`.

## Proposed edges

```jsonl
{"premise": "Cramér limsup = 1 (cramer_conjecture.variants.limsup_eq_one)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT Cramér–Granville (granville at c = 1.1)", "consequence_ref": "FormalConjectures/Wikipedia/CramerConjecture.lean cramer_conjecture.variants.granville", "consequence_status": "open", "implication_source": "Granville 1995 (Scand. Actuar. J.), remark recorded in fc docstring; deduction: 1 < 2e^{-γ} from eulerMascheroniConstant_lt_two_thirds and log_two_gt_d9", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "refutation edge X => not Y; both open", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Cramér strict bound (cramer_conjecture.variants.strict_bound)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT Cramér–Granville (granville at c = 1)", "consequence_ref": "FormalConjectures/Wikipedia/CramerConjecture.lean cramer_conjecture.variants.granville", "consequence_status": "open", "implication_source": "fc docstring; trivial", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Shanks (MaximalPrimeGap.shanks_maximal_prime_gap_conjecture)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT Cramér–Granville", "consequence_ref": "FormalConjectures/Wikipedia/CramerConjecture.lean cramer_conjecture.variants.granville", "consequence_status": "open", "implication_source": "Granville 1995; fc MaximalPrimeGap docstring", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "primeGap n <= sup_primeGap (p_n + 1); log(p+1)/log p -> 1", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Firoozbakht (Firoozbakht.firoozbakht_conjecture) + PNT", "premise_status": "open", "premise_lean_source": "PNT: PrimeNumberTheoremAnd (Apache-2.0), declaration to be checked", "consequence": "NOT Cramér–Granville", "consequence_ref": "FormalConjectures/Wikipedia/CramerConjecture.lean cramer_conjecture.variants.granville", "consequence_status": "open", "implication_source": "Kourbatov arXiv:1503.01744 / Wikipedia (unverified); direct route: g_n < p_n(p_n^{1/(n+1)} - 1), needs pi(x) >= kappa x/log x with kappa > e^γ/2 = 0.8905", "effort": "S-M", "lean_exists": "", "in_1337": false, "class": 2, "notes": "avoids firoozbakht_conjecture_consequence (L)", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Finite certificate: C5[K3] has alpha = 2 and every 8-set of branch vertices needs >= 9 interior vertices (7 available)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Hajós conjecture is false (k = 8)", "consequence_ref": "FormalConjectures/Wikipedia/HajosConjecture.lean HajosConjecture.hajos_conjecture", "consequence_status": "solved", "implication_source": "Catlin, JCTB 26 (1979) 268-274; certificate computed in this sweep", "effort": "S-M", "lean_exists": "atlas-lean Chapter5/Hajos.lean is conditional on a probability hypothesis (Erdős–Fajtlowicz); no unconditional proof found", "in_1337": false, "class": 1, "notes": "label known: needs owner sign-off (open-problems-only rule); variants.catlin (all k >= 7) not covered", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Computation L(906150257) = 1 (hyperbola recursion, 3.65e6 steps, sieve to 936421)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Pólya's conjecture L(n) <= 0 for n >= 2 is false", "consequence_ref": "Pólya 1919; Haselgrove, Mathematika 5 (1958); Tanaka, Tokyo J. Math. 3 (1980); no fc statement", "consequence_status": "solved", "implication_source": "Tanaka 1980; recomputed in this sweep", "effort": "S-M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "label known; one native_decide with proved-sound checker; shares checker with von Sterneck", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Computation M(7725038629) = 43947 (1.54e7 steps); 4*43947^2 = 7725355236 > x", "premise_status": "theorem", "premise_lean_source": "", "consequence": "von Sterneck's conjecture |M(x)| < sqrt(x)/2 for x > 200 is false", "consequence_ref": "von Sterneck; Neubauer 1963; no fc statement", "consequence_status": "solved", "implication_source": "Neubauer 1963; least counterexample per arXiv:1810.05244 (unverified); recomputed in this sweep", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "label known; after the Pólya checker", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Parker's orthogonal Latin squares of order 10", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Euler's conjecture (no orthogonal pair for n = 2 mod 4) is false", "consequence_ref": "Euler 1782; Parker 1959; Bose–Shrikhande–Parker 1960; fc Paper/LatinSquare.lean has defs only", "consequence_status": "solved", "implication_source": "Parker 1959", "effort": "S", "lean_exists": "not searched (GitHub rate limit)", "in_1337": false, "class": 1, "notes": "label known; trivial decide; check prior art first", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "HooleyHypothesis 5 (GRH for zeta of Q(zeta_k, 5^{1/k}))", "premise_status": "open", "premise_lean_source": "fc Wikipedia/ArtinPrimitiveRootsConjecture.lean HooleyHypothesis; artin-grh Artin/Kummer/Density.lean kummerDensity", "consequence": "S(5) does not have density ArtinConstant (Artin's 1927 density is wrong; true density 20A/19)", "consequence_ref": "Lehmer–Lehmer 1962; Hooley 1967; Stevenhagen 2003 (unverified)", "consequence_status": "solved", "implication_source": "Hooley 1967 corrected density; fc entanglementFactor 5 1 = 20/19", "effort": "M", "lean_exists": "", "in_1337": false, "class": 2, "notes": "tier C forever: non-abelian GRH not in riemann-hypothesis; 1337 lists Artin density as unresolved", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "psi-grh uniform pi(x;q,a) bound (GRH, lean-proved tier U) + Buchstab oscillation", "premise_status": "lean-proved", "premise_lean_source": "psi-grh piAP_unconditional", "consequence": "Maier: pi(x+(log x)^lambda) - pi(x) not ~ (log x)^{lambda-1}", "consequence_ref": "Maier, Michigan Math. J. 32 (1985)", "consequence_status": "solved", "implication_source": "Maier 1985 matrix method", "effort": "L", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected by policy: known, via GRH here; Buchstab omega(u) oscillation lemma missing", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Kaczorowski 1995 (GRH)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Knapowski–Turán natural density conjecture false", "consequence_ref": "fc Wikipedia/ChebyshevBias.lean knapowski_turan_natural_density_false", "consequence_status": "solved", "implication_source": "Kaczorowski, Analysis 15 (1995)", "effort": "XL", "lean_exists": "", "in_1337": true, "class": 1, "notes": "rejected: taken (1337, NEXT_TARGETS); needs certified zeros", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Odlyzko–te Riele 1985", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Mertens conjecture false", "consequence_ref": "Mertens 1897", "consequence_status": "solved", "implication_source": "Odlyzko–te Riele 1985", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected: non-constructive, needs zero data, no explicit counterexample", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Computation at 72185376951205", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Turán's conjecture sum lambda(n)/n >= 0 false", "consequence_ref": "Haselgrove 1958; Borwein–Ferguson–Mossinghoff 2008 (unverified)", "consequence_status": "solved", "implication_source": "BFM 2008", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected: ~2e10 interval-arithmetic steps, tiny margin", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Jacobian conjecture false (fc jacobian_conjecture, Lean)", "premise_status": "lean-proved", "premise_lean_source": "FormalConjectures/Wikipedia/JacobianConjecture.lean jacobian_conjecture", "consequence": "Gaussian moments / Zhao vanishing / Mathieu conjectures false", "consequence_ref": "Long arXiv:2607.18186; de Bondt arXiv:2610.24889", "consequence_status": "solved", "implication_source": "Derksen–van den Essen–Zhao; Zhao; Mathieu 1997", "effort": "L", "lean_exists": "LeanPool GaussianMomentsCounterexamples.lean (GMC); others in active repos", "in_1337": false, "class": 1, "notes": "rejected: crowded since July 2026", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "GRH (Dirichlet) via weinberger-grh split-prime sieve", "premise_status": "lean-proved", "premise_lean_source": "weinberger-grh exists_split_prime_of_GRH", "consequence": "imaginary quadratic fields with class group exponent 3: list complete", "consequence_ref": "Boyd–Kisilevsky 1972; Elsenhans–Klüners–Nicolae (unverified)", "consequence_status": "open", "implication_source": "Boyd–Kisilevsky 1972", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected: analytic threshold ~2e12 with x=(n/4)^{1/3}; finite check ~2e4 x weinberger's; also needs class groups", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "Euler sum of powers counterexamples", "premise_status": "lean-proved", "premise_lean_source": "fc Wikipedia/EulerSumOfPowers.lean false_for_k4/k5; Mathlib Counterexamples/EulerSumOfPowers.lean", "consequence": "Euler sum of powers conjecture false for k = 4, 5", "consequence_ref": "fc eulers_sum_of_powers_conjecture", "consequence_status": "solved", "implication_source": "Lander–Parkin 1966; Elkies 1988; Frye", "effort": "S", "lean_exists": "fc, Mathlib", "in_1337": false, "class": 1, "notes": "rejected: done", "sweep": "2026-11-26", "lane": "disproof-literature"}
{"premise": "OpenAI 2026 dimension-9 set", "premise_status": "lean-proved", "premise_lean_source": "fc borsuk_conjecture formal_proof", "consequence": "Borsuk conjecture false", "consequence_ref": "fc Wikipedia/BorsukConjecture.lean borsuk_conjecture", "consequence_status": "solved", "implication_source": "Kahn–Kalai 1993; OAI 2026", "effort": "S", "lean_exists": "fc formal_proof", "in_1337": false, "class": 1, "notes": "rejected: done", "sweep": "2026-11-26", "lane": "disproof-literature"}
```
