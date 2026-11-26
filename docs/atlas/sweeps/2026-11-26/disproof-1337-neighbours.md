# Lane `disproof-1337-neighbours`: open neighbours of the 1337 refutations

Lane `disproof-1337-neighbours`, 2026-11-26. Research and computation only. No Lean and no
existing file was edited. The hint source is the 1337isnot1337/solved-conjectures repository
(shallow clone of `main` on 2026-11-26, read as data, none of its scripts run). Everything it
lists is already settled, so it was used only for **methods** and **neighbours**. Scripts are
in the session scratchpad: `work1337/` (shifted Lonely Runner), `nb-comb/` (Ulas, Carraher,
Benfield–Lippard, Fiscus), `rr-alex/` (real-rootedness). Claims I could not confirm from a primary
source are marked *(unverified)*.

## Main finding

Two published conjectures turned out false, each with a small explicit witness checked by three
independent implementations. Both are **cheap and shallow**: in each case the authors' own data,
or a classical theorem, already contradicts the statement. Neither is a famous conjecture.

1. **Gawron–Miska–Ulas, Conjecture 5.6** (arXiv:1703.01955, "Revision II" source; Monatsh. Math.
   185 (2018)). It fails at m = 1, k = 3, n = 1: `b(16) − b(4) = 36 − 4 = 32`, and the conjecture
   needs divisibility by `2^6 = 64`. It also fails for m = 3, 4, 5 and 6. Only m = 2 survives
   (checked through k = 25).
2. **Carraher–Galvin–Hartke–Radcliffe–Stolee, the `{1,8,k}` independence-ratio conjecture**
   (arXiv:1401.7183v1). It fails for every `k ≡ 5 (mod 9)` with `k ≥ 50` and every `k ≡ 3 (mod 9)`
   with `k ≥ 57`. The smallest witness is the 51-periodic set `{x : 22x mod 51 < 22}`, of density
   `22/51 > 201/466`. **Catch:** the conjecture appears only in the arXiv v1. The Discrete Math.
   339 (2016) version, as hosted by Galvin, states only Conjectures 26 and 29, so the authors
   dropped it at publication.

The main target, the **shifted Lonely Runner Conjecture at n = 58** (Zhang's Question 8.5, open
for `58 ≤ n ≤ 94`), produced no witness within budget. At least three groups are racing for it
(1337 issue #110, tomdif, and munimtechnologies/shifted-lonely-runner), so it is crowded.

## 1. Method catalogue of the 1337 refutations

The question is how each witness became findable. Entries rarely record the discovery, so the
column often gives the reduction the proof uses instead; reconstructions are marked (inferred).

| Entry | Conjecture refuted | Witness | Reduction that made it findable |
|---|---|---|---|
| coffey-smith | Smith 2005, Coffey–Smith conjunction | none (dichotomy) | Case split on RH: under RH the coefficient mass is `O(N^{-1/2} log³N)`; without RH the upper bound fails |
| merlini-sala-sala | arXiv:1903.06233 / 1907.01903, subpower bound for λ_tiny | `limsup |λ_tiny(n)|/n^{1/4} = ∞` | Proof by contradiction via an H² trace; asymptotic, not finite |
| chaudhary-khmiri-mazhouda | Li-coefficient monotonicity for automorphic L | `L(s+8i, χ₋₃)`, Re(λ₂−λ₁) < −3/2 | Unusual admissible member (imaginary twist) at the smallest index; rational interval arithmetic |
| csordas-vishnyakova | Conj. 3.6 (CEJM 2013) | `z⁴+z²+1`, `exp(−z⁴)` | Smallest genus past the proved case (inferred); exact inequalities |
| cardon-zero-sector | arXiv:1802.02641 Q. 6.1 | a cubic, α → 0⁺ | Small-parameter perturbation with an exact cubic certificate |
| wang-yang | Conj. 1.10 (Xi coefficients) | sign changes for every index | Asymptotic sign argument (Hardy 1914 zeros + Rolle) |
| wagner-laguerre-operator | arXiv:2108.01827 Conj. 4.3 | `e^z + 1 ↦ −e^z` | Simplest member of the class (inferred) |
| brown-mol | arXiv:1810.08655 Conj. 4.2 | diameter-4 trees, 1001-vertex T₂₀₀ | Reduction to an extremal family and an r → ∞ limit; Rouché disk |
| chappelon-ramírez-stamate | arXiv:2507.15006 Conj. 4.4 | semigroup from an additive basis | Reduction to additive bases of `[0,N)` |
| lópez-pouso–segura | J. Ineq. Appl. 2025, Conjs 3, 7 | 2-node Gauss–Legendre | Smallest degree, exact |
| fmp-cylindric | FMP Conj. 7.9 | 13-cell relaxed-seam diagram | Boundary-convention edge case |
| ćurgus–mascioni | Constr. Approx. 2007 uniqueness | a continuum at degree 2 | Smallest degree |
| alexandersson-parking-excedance | Alexandersson's list, real-rootedness | length-17 polynomial | Counting recurrence plus the Laguerre inequality at the rational point t = −1/5 (no roots computed) |
| benfield–lippard symmetry | arXiv:2404.08193 Conj. 10.1 | exponents 64, 128 | Exact numerical-semigroup truncation, Apéry set, 2-power gcd structure |
| burstein descent-top | DMTCS 2025 Conjs 16, 17 | Ferrers board (6,6,6,6,5,4) | Fiber decomposition; counts differ by one |
| caiolo–ferroni–hoster | arXiv:2605.28474 Conj. 7.3 | rank-5 matroids, q ≥ 17 | Transfer of a known coalescence family through a dual identity |
| chen–khare–sahi | arXiv:2509.19649 Conj. 5 | (4,2,0) vs (4,1,1) at q = 1/10 | Farkas-type separating functional over a finite reduction |
| coulangeon–lazzarini | JNT 2014 Conj. 21 | dim-10 integral lattice | Construction A from a tiny code |
| distance-graph-densities | arXiv:1401.7183 Conj. 39 | k = 50, 59, 68, … | Exhaustive periodic/transfer computation over a 1-D family of parameters |
| fiscus-grid-game | arXiv:2504.03448 Conj. 24 | P₂□P₇ | Smallest case, exhaustive minimax (16,384 positions) |
| gawron–miska–ulas valuation, sign density | Monatsh. 2018 Conjs 5.2, 5.8 | m = 17, m = 2^k+1 | Exact recursion mod 2^j from `T(x)^m = (1−x)^m T(x²)^m` |
| han–sabag–kostina–hassibi | arXiv:2406.17196 Conj. 1 | rational encoder | Exhaust the four sparse cases symbolically, then one dense point |
| hkm-ehrhart | arXiv:1612.07538 Conj. 4.10 | K_{2,2,2,2,2,2} | Interpolation formula over the complete-multipartite family |
| kovalev-hardy-duality | arXiv:2607.17373 Conj. 6.1 | order ≥ 500001 diagonals | Two-level extremal family, reduced to 1-D integrals |
| l-solitaire | OJAC 2020 Conj. 1 | n = 101 | Definitional loophole |
| li-coefficient-sign | arXiv:2503.09484 Problems 4.6, 4.9 | 31-vertex non-spider tree | Push past the authors' n ≤ 21 enumeration; DP over 2³⁰ cuts |
| mcnamara–steingrímsson | JCTA 2015 Conj. 9.4 | rank-67 interval | Direct sums of layered pieces turn counts into polynomial coefficients |
| meylender–thalmaier | arXiv:2603.12495 Conj. 6.1 | parallelogram, pentagon | Boundary regime b → 1 |
| nemeth–seberry–shu | 1979 V(p) = O(p) | Fourier-biased random circulants | Probabilistic construction |
| pham-denominator | arXiv:2208.14496 §6 | necklace 0001001011 | Degree bounds reduce to 26 coefficients |
| rowland–sistos barrón | arXiv:2501.14643 Conj. 5.3 | one rank-6 sequence | Square-dependent cancellation |
| separable-derangements | arXiv:2608.27583 Conj. 14 | asymptotic | Boltzmann/Schröder-tree asymptotics |
| steinerberger (three entries) | Open Problems §§20, 24, 43 | van der Corput; `exp(−x−x²/200)`; S³ coherent states | Identify with a classical object |
| zhu-jacobi-stirling | Adv. Math. 2024 §5.2 | 3×3 Hankel minor | Smallest minor, symbolic |
| erdős–gyárfás point degrees | Gyárfás 2002 Problems 2, 3 | upper bound (16n−13)/17 | Two-set degree comparison |
| sagan–wilson plactic mode | Semigroup Forum 2025 Conj. 7.3(d) | length 10 | Small-n exact check plus asymptotics |
| shifted Lonely Runner | Zhang arXiv:2608.13599 Q. 8.5 | certificates n = 18..57 | Annealing + LP polish; warm chain n−1 → n; smooth-speed sets; padding lemma |
| Knapowski–Turán, Fujii (1337 `research` branch, rh-transfer) | K–T 1962; Fujii 1988 | none (inherited) | Kaczorowski 1992 under GRH; Landau-type oscillation |

Patterns that transfer, in order of how often they produced a finite witness:
1. **Push the authors' own small-n check a little further**: Li, Alexandersson, Sagan–Wilson,
   Fiscus, Pham. This is the cheapest pattern and the one that found both hits below.
2. **One-parameter family**: a ∀ becomes a 1-D scan (distance graphs `{1,a,k}`, Thue–Morse
   exponents m, Benfield–Lippard exponents e).
3. **Rational-point certificates instead of root finding**: Laguerre/Newton inequality at a
   rational t, Farkas functional, interval arithmetic.
4. **Extremal or boundary family plus a limit**: Brown–Mol, Kovalev, Ferreira–Simon, Meylender–Thalmaier.
5. **Heuristic search with an exact check**: the Lonely Runner certificates only.

## 2. Neighbours generated, and their status

| Neighbour | Source | Status checked | Kept? |
|---|---|---|---|
| Shifted LRC, n = 58..94 (Zhang Q. 8.5) | arXiv:2608.13599 v3 | open: 1337 #110 (updated 03:40 today), munimtechnologies README "Open: 58 ≤ n ≤ 94 (checked 2026-11-26 10:00 UTC)", web search | yes, but crowded (3 groups) |
| GMU Conj. 5.5, 5.6 (colored binary partition congruences) | arXiv:1703.01955 | no follow-up found (web, GitHub code search on `1703.01955`, 1337 issues, OpenAlex citing works per the sub-agent) | yes → **hit** (5.6) |
| GMU Conj. 3.15, 5.9, 5.10 | same | open | searched, holds |
| Carraher et al. `{1,8,k}` and `{1,6,k}` conjectures | arXiv:1401.7183v1 | Liu–Robinson (arXiv:1611.03940) refute only 26 and 29; `{1,8,k}` is absent from the journal version | yes → **hit**, preprint-only |
| Benfield–Lippard Conjs 10.6, 10.18 | arXiv:2404.08193v2 | 10.1, 10.2, 10.4 settled by 1337; 10.5 elsewhere; 10.6 and 10.18 open | searched at k = 10, holds |
| Fiscus et al. remaining problems | arXiv:2504.03448v2 | no open conjecture besides 24; only "determine the winner" problems | data only |
| McNamara–Steingrímsson Q. 9.1, 9.5, Conj. 9.2 | JCTA 2015 | 9.5 answered; 9.2 (shellability) not computable; 9.1 too costly | dropped |
| Wild-number conjecture, 13 ≤ n ≤ 154 | arXiv:2610.22142 Conj. 6.1 | open, but proved for n ≥ 155 by 1337 and for n ≤ 12 by the source, so it is probably true | dropped: no plausibility for a counterexample |
| Alexandersson's real-rootedness list (other entries) | symmetricfunctions.com | see §5 | sub-agent |
| Mazák–Zrubák problems 6, 7; 1337 "Conjecture H′" | arXiv:2603.08822 | H′ is the 1337 repo's own conjecture, not a published one | dropped (ad hoc) |
| Hadamard order 2396 | — | an existence witness would prove, not refute | dropped |
| Fujii threshold 20.40443 | rh-transfer | analytic, no finite witness | dropped |

## 3. Hits

### Hit 1: Gawron–Miska–Ulas Conjecture 5.6 is false

- **Exact wording** (arXiv:1703.01955, source file `GMU_MOFM_Revision_II.tex`, `\label{cong:powerof2-1}`):
  "Let m be a fixed positive integer. Then for each n∈ℕ and k≥m+2 the following congruence holds:
  b_{2^m−1}(2^{k+1}n) ≡ b_{2^m−1}(2^{k−1}n) (mod 2^{4⌊(k+1)/2⌋−2})."
  Here `b_M(n)` is the coefficient of `x^n` in `∏_{i≥0}(1 − x^{2^i})^{−M}`, the number of
  M-coloured binary partitions; `b_1 = b` is Euler's binary partition function (A018819). The
  authors give no checked range. The source page reads `https://arxiv.org/abs/1703.01955`.
- **Witnesses** (n = 1 throughout; required exponent `4⌊(k+1)/2⌋−2`):

  | m | M = 2^m−1 | k | ν₂ of the difference | required |
  |---|---|---|---|---|
  | 1 | 1 | 3 | 5 (`b(16) − b(4) = 36 − 4 = 32`) | 6 |
  | 3 | 7 | 5 | 7 (`b₇(64) − b₇(16) = 346264414943104`) | 10 |
  | 4 | 15 | 6 | 8 | 10 |
  | 5 | 31 | 7 | 9 | 14 |
  | 6 | 63 | 8 | 10 | 14 |

  m = 2 holds through k = 25. The companion Conjecture 5.5 (`b_{2^m}`, modulus `2^k`) holds and
  is sharp for m = 1..5, k ≤ 25 (sub-agent run).
- **Verification.** There are three independent implementations: the sub-agent's `nb-comb/ulas/bcong.c`
  (mod 2⁶⁴ to n = 2²⁶) and `verify56.py` (big-integer series), and mine, an inline exact series
  product (`1/(1−x^p)` applied M times for each power of two), which reproduces every row above.
  All arithmetic is exact integer arithmetic.
- **Why it is shallow.** For m = 1 the statement says more than Churchhouse's congruence
  `b(2^{k+2}n) − b(2^k n) ≡ 0 (mod 2^{⌊(3k+4)/2⌋})`, proved by Rødseth and by Gupta (1970–72).
  That congruence is known to be sharp for odd n *(sharpness from memory, unverified)*, and
  `ν₂ = 5` at our point agrees with it. A reader of the 1975 literature could have refuted 5.6
  in one line, but nobody did. The m = 3..6 failures are not covered by a classical theorem.
- **Prior art.** I searched the web (several queries), GitHub code search for `1703.01955` (only
  1337's Conjectures 5.2 and 5.8 entries and OEIS mirrors), and 1337's issues and PRs (#434 and
  #435 concern Gawron–Ulas and Sobolewski–Ulas, different papers). The sub-agent checked the
  OpenAlex citing works (arXiv:2606.25825, 2609.16966, Ulas–Żmija 1809.04628) and the trureturing
  repository. None mentions 5.5 or 5.6. **Not checked:** the journal text in Monatsh. Math. 185
  (2018), which may have changed the statement (the source file says "Revision II", so it is
  probably the accepted version *(unverified)*); clopen.solutions and Hexagon were not
  searched directly.
- **Lean.** Route e, trivial. Define `b M n` by the recursion of the product, or as the
  convolution of M copies of A018819, and `decide` `¬ (64 ∣ b 1 16 − b 1 4)`. The m = 3 case
  needs `b 7 64`, a 15-digit number that `decide` or `norm_num` handles through a recursive
  evaluator. Effort S.
- **Label.** It is a refutation of a published conjecture, but a minor one (a congruence
  guess with the wrong exponent).

### Hit 2: the Carraher et al. `{1,8,k}` conjecture is false (arXiv v1 only)

- **Exact wording** (arXiv:1401.7183v1, `infinitecayley_arxiv.tex` l. 1966–1981; numbered
  Conjecture 34 in the author-hosted arXiv PDF according to the sub-agent): "For k > 8 with
  k ∉ {9, 10, 14, 16, 18, 23, 25, 32}, α({1,8,k}) = 4k/(9k+9) if k ≡ 0; 4/9 if k ≡ 1;
  (4k+1)/(9k+9) if k ≡ 2; (4k+24)/(9k+72) if k ≡ 3; (4k+2)/(9k+9) if k ≡ 4; (4k+1)/(9k+16) if
  k ≡ 5; (4k+3)/(9k+9) if k ≡ 6; (4k−1)/(9k+9) if k ≡ 7; 4/9 if k ≡ 8 (mod 9)." Here α(S) is
  the supremum of upper densities of independent sets in the distance graph on ℤ.
- **Witness.** Let P = k+1. The set `A = {x ∈ ℤ : h·x mod P < c}` is P-periodic, so it is
  independent in `G(ℤ, {1,8,k})` iff no `x ∈ A` has `x + d mod P ∈ A` for d ∈ {1, 8, k}. Its
  density is `c/P`.
  - k = 50, (h,c) = (22,22): density `22/51 = 0.431373 > 201/466 = 0.431330`.
  - k = 57, (25,25): density `25/58 > 28/65`.

  The pattern continues for all k ≡ 5 (mod 9) with k ≥ 50 and all k ≡ 3 (mod 9) with k ≥ 57.
  My scan over 9 ≤ k < 130 found exactly 50, 57, 59, 66, 68, 75, 77, 84, 86, 93, 95, 102, 104,
  111, 113, 120, 122, 129. The sub-agent's closed form says the excess is
  `(k−41)/((9k+9)(9k+16))` on the k ≡ 5 branch.
- **Verification.** There are three implementations: `nb-comb/distg/kappa.py`; `verify34.py`
  (brute force on ℤ/P plus Karp's maximum cycle mean for exact α; it reproduces α({1,3,4}) = 2/7
  and α({1,6,7}) = 4/13); and mine (an exhaustive scan over (h, c) with a cyclic independence
  check in exact `Fraction`s). The lower bound is enough to refute an equality claim, so no
  upper bound is needed. The sub-agent also reports that the formula overshoots at k = 11:
  exact α({1,8,11}) = 7/19 < 5/12 by Karp's algorithm. That needs an upper bound and has only
  the sub-agent's single implementation *(unverified by me)*.
- **Catch: publication status.** The Discrete Math. 339(12) (2016) 3058–3072 version, as hosted
  by Galvin (`infinitecayley_J.pdf`, 14 pp.), lists only Conjectures 26 (`{1,ℓ,2i}`) and 29
  (`{1,2k,2k+2ℓ}`). The `{1,8,k}` and `{1,6,k}` conjectures are gone. The authors' own data
  table prints `22/51` at k = 50 as an exact value (in black), according to the sub-agent, who
  rendered the PDF. So this is a preprint conjecture that the authors withdrew. A named author
  would recognise it, but it carries little weight.
- **Prior art.** Liu–Robinson (arXiv:1611.03940) refute Conjectures 26 and 29 only. The 1337
  entries cover Conjectures 38 and 39 (arXiv numbering) and Haralambis's three-difference
  result, which never mentions `{1,8,k}`. GitHub code search for `1401.7183` found only a
  bibliography line in kooshi/hadwiger-nelson. A web search for a refutation found none.
  Dumitrescu–Lángi (arXiv:2610.24803) is about planar distances, not this.
- **Lean.** Route e. A periodic set's density is elementary, but the fc-style `α` (a supremum
  of upper densities) needs a lemma saying that the upper density of a P-periodic set is
  `|A mod P|/P`. Effort S–M. No fc statement exists, so the statement would be ours.

## 4. Reduction chains and searches

### 4a. Shifted Lonely Runner, n = 58 (main target; no witness)

**Plausibility.** Counterexamples exist for 5 ≤ n ≤ 57 and n ≥ 95. The 1337 chain advanced n
by n whenever it had a strong (E ≳ 0.5) base at n−1. Here E := 1/γ − (n+1), and E > 0 is a
counterexample. Its stalls look like compute limits, not walls (PROOF.md: n = 57 came from the
first try after a strong n = 56 base appeared).

**Reduction chain.**

| Step | Property used | Space after |
|---|---|---|
| raw | n = 58 distinct positive speeds, shifts in [0,1)⁵⁸ | infinite |
| 1 | speeds ≤ 4n = 232 (largest certified speed so far 216; heuristic, not a theorem) | C(232,58) ≈ 10^55.4 speed sets × continuous shifts |
| 2 | speeds > n must be 19-smooth (every speed above n in the 41..57 certificates has largest prime factor ≤ 19, except isolated 59, 111, 123); universe 140 speeds | C(140,58) ≈ 10^40.1 |
| 3 | warm chain: keep the n = 57 certificate, add one speed (83 choices), and let annealing swap speeds | 83 × local moves |
| 4 | symmetries: time translation (fix the slowest runner's shift), reflection s ↦ −s | 57-dim shifts |
| 5 | every local maximum of `min_i ||s_i + v_i t||` is at a crossing `(v_i+v_j)t + s_i + s_j ∈ ℤ`. For a fixed combinatorial type, each peak height is linear in s, so the polish is an LP (SLP with trust region); 1,100 to 1,700 near-active rows | LP of 58 vars |
| 6 | padding lemma: an n = 57 state with E > 1 also suffices | — |

This chain does **not** end in an exhaustively searchable space: steps 1–3 are heuristic. So
the search is a bounded heuristic run with a stop condition, as the lane rules allow, and a
negative result proves nothing.

**Implementation** (all mine, `work1337/`). `sa.c` is a Metropolis grid annealer (cost:
uncovered grid cells at δ = 1/(n+1+E)) with targeted shift moves and speed swaps. `sa2.c` adds
exact pin detection: on a grid cover it computes the exact γ over crossings, and exposed peaks
become weighted special points. `sa3.c` uses a conservative grid, counting a cell only if an arc
contains it entirely, so a grid cover implies a true cover. `hb.c` is a heat-bath (Gibbs over
16,384 shift bins via phase folding) variant. `polish.py` is the crossing-LP SLP (HiGHS).
`exact.py` gives the exact γ by crossings (`Fraction`s) and an independent arc-cover check.
`exact.py` reproduces the published γ of the n = 41, 50, 55, 56 and 57 certificates exactly.

**Runs.** Wall time on a box at load 35–180.

| Run | Start | Grid | Steps × chains | CPU | Result |
|---|---|---|---|---|---|
| calibration (Metropolis, centre grid) | n=56 cert + 1 → n=57 | 2¹⁹ | 2M × 1 | 0.07 h | best 3 cells; polished γ pinned at exactly 1/58 |
| calibration | n=56 + 1 → 57 | 2¹⁸ | 4M × 8 | 0.7 h | one grid cover at E = 0.15, **exact E = −0.0001** (pinned) |
| heat-bath `hb` | n=56 + 1 → 57 | 2¹⁸, B = 16384 | ~60k × 12 (killed) | ~4 h | too slow under load; best 15–60 cells |
| `sa2` pin-aware | n=56 + 1 → 57 | 2¹⁸ | 6.9M × 12 (killed) | ~9 h | ten grid covers, exact E from −0.74 to −0.09 |
| `sa3` conservative | n=56 + 1 → 57 | 2¹⁸ | 6M × 2 | 0.3 h | best 16, 28 cells |
| `sa3` conservative | **n=57 + 1 → 58** | 2¹⁸ | 6M × 8 | 1.2 h | best 46–104 cells; no cover |

Total for this target: about 15 CPU-hours. **Stop condition reached** (CPU budget). The most
useful negative: a centre-sampled grid at 2¹⁸ cells is **not** a reliable cover test at
n ≈ 57. Pairs with v_i + v_j ≳ 200 leave holes narrower than a cell, so a grid "cover" was
exactly checked at E between −0.74 and 0 in every case. The conservative grid fixes this, but
it makes the anneal harder. Within the time spent, it did not even reproduce n = 57 from the
n = 56 base. That is a calibration failure of my pipeline, not evidence about n = 58.

### 4b–4e. Other neighbours (sub-agent `nb-comb`, about 0.5 CPU-hour on ≤ 6 cores)

| Target | Reduction chain | Range | Outcome |
|---|---|---|---|
| GMU Conj. 5.6 | one-parameter family in (m, k); exact recursion mod 2⁶⁴ | m ≤ 6, k ≤ 25, n ≤ 2²⁶ | **hit** (§3) |
| GMU Conj. 5.5 | same | m ≤ 5, k ≤ 25 | holds, sharp |
| GMU Conj. 3.15 (t_m(n) ≠ 0, m ≥ 4) | a zero needs `t_m(n) ≡ 0` modulo two primes near 2⁶¹ | m = 4..8 to 2²⁶; m = 9..40 to 2²⁴ | holds |
| GMU Conj. 5.9, 5.10 (signs, log-concavity) | exact big-integer coefficients | m ≤ 16 to 65536; m ≤ 128 to 3000 | holds (minimum log-concavity ratio ≥ 2.2) |
| Carraher `{1,8,k}` | periodic sets suffice (their theorem); a 1-D family in k; cyclic sets `{x: hx mod P < c}` | 9 ≤ k ≤ 1500 (κ), exact α to 600 | **hit** (§3) |
| Carraher `{1,6,k}` (arXiv v1) | same | κ to 1500, exact α for k ≤ 19 | consistent |
| Benfield–Lippard 10.6, 10.18 | 11 divides every generator except those with 11 ∣ m, which reduces to a much smaller semigroup T = ⟨(m¹⁰−1)/11⟩; DP to 4·10⁸ | k = 10 | g(1,10) = 1130 with a unique extremal element; both hold (beyond 4·10⁸ by window-max heuristic only) |
| Fiscus game, Problems 25, 29 | exhaustive minimax over 2^|V| ≤ 2³⁰ | ladders n ≤ 15; grids to 3×10, 5×6; small tori; K(6..8,2) | data, single implementation, unverified |

### 4f. Real-rootedness neighbours (Alexandersson's list)

See §5 (sub-agent `rr-alex`).

## 5. Real-rootedness neighbours

RR_SECTION_PLACEHOLDER

## 6. Best lead not finished

**Shifted LRC at n = 58.** Two things are needed. The first is a reliable cover test at grid
resolution: a conservative grid at 2²⁰ or more cells, or exact incremental arc bookkeeping. The
second is a pool of strong (E ≥ 0.5) n = 57 bases. The published n = 57 certificate has
E = 0.11, too thin for the warm chain by the 1337 notes' own account. Budget: tens of CPU-hours
on an unloaded box. **Crowding:** 1337 issue #110 (tomdif "search continues from the n = 57
certificate"), and munimtechnologies/shifted-lonely-runner (11 pre-registered routes; README
updated 2026-11-26 10:00 UTC with 58..94 still open). A new n is likely to be claimed by one of
them soon. If it is pursued, the untried idea in the 1337 notes is the "rigid time shift of a
subset" unpinning move, combined with the padding target (E > 1 at n = 57).

## Proposed edges

```jsonl
{"premise": "Computation: b(16) - b(4) = 32 (binary partitions, A018819); b_7(64) - b_7(16) = 346264414943104, nu_2 = 7", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Gawron–Miska–Ulas Conjecture 5.6 (b_{2^m-1}(2^{k+1}n) ≡ b_{2^m-1}(2^{k-1}n) mod 2^{4⌊(k+1)/2⌋-2}, all m ≥ 1, k ≥ m+2) is false", "consequence_ref": "arXiv:1703.01955 (Monatsh. Math. 185 (2018)), \\label{cong:powerof2-1}", "consequence_status": "open", "implication_source": "computed in this sweep (three implementations); m=1 also follows from the sharpness of Churchhouse's congruence (Rødseth, Gupta)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "fails for m = 1, 3, 4, 5, 6; m = 2 holds to k = 25; journal wording unchecked", "sweep": "2026-11-26", "lane": "disproof-1337-neighbours"}
{"premise": "Computation: the 51-periodic set {x : 22x mod 51 < 22} is independent in G(Z,{1,8,50}) with density 22/51", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Carraher–Galvin–Hartke–Radcliffe–Stolee {1,8,k} conjecture is false (k = 50, 57, 59, 66, ...)", "consequence_ref": "arXiv:1401.7183v1, conjecture on alpha({1,8,k}) (Conj. 34 in the arXiv PDF numbering, per sub-agent)", "consequence_status": "open", "implication_source": "computed in this sweep (three implementations); the authors' own data table lists 22/51 at k = 50", "effort": "S-M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "preprint-only: absent from the Discrete Math. 339 (2016) version; k = 11 overshoot (7/19) unverified", "sweep": "2026-11-26", "lane": "disproof-1337-neighbours"}
{"premise": "Heuristic search, about 15 CPU-h (warm chain from the n = 57 certificate, 19-smooth speed universe, crossing-LP polish)", "premise_status": "open", "premise_lean_source": "", "consequence": "shifted Lonely Runner counterexample for n = 58 (Zhang Q. 8.5)", "consequence_ref": "Zhang arXiv:2608.13599 v3 Question 8.5; 1337 issue #110", "consequence_status": "open", "implication_source": "", "effort": "L", "lean_exists": "1337 Lean for 18..57", "in_1337": true, "class": 1, "notes": "negative: no witness; centre-sampled grids at 2^18 give false covers (exact E -0.74..0); crowded (1337 #110, tomdif, munimtechnologies)", "sweep": "2026-11-26", "lane": "disproof-1337-neighbours"}
```
