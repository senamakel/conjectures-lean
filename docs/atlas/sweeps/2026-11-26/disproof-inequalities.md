# Lane `disproof-inequalities`: counterexample hunt in analysis, special functions, matrices and probability

Lane `disproof-inequalities`, 2026-11-26. Research and computation only. No Lean file and no
existing file was edited. Scripts and logs are in the session scratchpad
`/tmp/claude-1000/-home-ubuntu-work-personal-conjectures/e6c3a6a3-3702-43d3-8640-5f8f102b5329/scratchpad/hunt-ineq/`
(`src/` for the scripts, `dl/` for downloaded sources and logs). Downloaded arXiv sources were
read with `python3 -I`. The box was heavily loaded (load average 105–117 on 95 cores), so this
lane ran at most 16 processes.

## Main finding

**No hit.** None of the ten open conjectures I tested has a counterexample in the ranges below.
One witness I found is real but not new: the Gu–Sellke measure refutes the Wu–Yu–Guo Tsallis
conjecture at order α = 101/100. That conjecture was already settled in public on 2026-11-06
(Zenodo 10.5281/zenodo.24001602), so the witness is recorded below as **taken**, not as a hit.

The lane is heavily mined. In 2026 most conjectures of this kind that come with explicit
numerics have a public AI-assisted refutation or proof within weeks: the Gaussian completely
monotone conjecture (Gu–Sellke, arXiv:2605.11656), Cheng–Geng's log-convexity conjecture
(arXiv:2605.18081), the unrestricted Fasi–Higham conjecture (Scardino, arXiv:2610.39051),
Gautschi's fourth conjecture (arXiv:2609.19186), the Mahmoud–Qi degree conjectures
(arXiv:2610.33699), the Tsallis classification (Zenodo 24001602, evidencepress.org) and
partial results on the Rademacher endpoint (Barritz, Zenodo 22773903 and 22818774). Prior-art
checks have to cover Zenodo and evidencepress.org as well as arXiv.

The coordinator raised the bar mid-run: a hit must refute a conjecture the authors tested and
believed, with a witness beyond their range. Every candidate below meets that bar. Each one
has a reported verification range, and every search went past it.

## Candidates, sources and prior art

Each entry gives the source and its wording, what the authors checked, the prior-art check, the
reduction, the search, and the outcome. The word "Exa" means the Exa web search tool.

### 1. Fasi–Higham Conjecture 3.2, diagonal case k = m · open · no counterexample

- **Statement** (Fasi–Higham, SIAM J. Matrix Anal. Appl. 40 (2019), Conjecture 3.2, as restated
  in Scardino arXiv:2610.39051): "Let k ≥ 0 and m ≥ 1 be integers. If m is odd, then all the
  coefficients of the Taylor expansion of q_{k,m}^{-1}(z) at 0 are positive." Here
  q_{k,m}(z) = Σ_j (−1)^j C(m,j) (k+m−j)!/(k+m)! z^j.
- **Prior art.** Scardino refutes the unrestricted conjecture, for example with c_38(66,5) < 0,
  and proves it for k = 0 and for large k with m fixed. He states twice that "the diagonal case
  k = m, which is the case relevant in practice, remains open". The diagonal is the case the
  error bound needs.
- **Reduction.** The coefficients obey c_n = −Σ_{j=1}^{m} q_j c_{n−j}. Scardino's mechanism for
  failure is a nearly degenerate pair of minimal-modulus poles, which produces a transient
  oscillation on the scale n ≍ √k. On the diagonal the risky window is where the ratio
  c_n/c_{n−1} is smallest.
- **Search.**
  - Exact rational arithmetic for odd m ≤ 41 and n ≤ 600 (`src/fh.py`).
  - mpmath at 400 digits for m = 61, 101, 151 and n ≤ 8m (`src/fh2.py`).
  - Cost: about 0.3 CPU-h.
- **Result.** Every coefficient is positive. The smallest ratio sits at n ≈ 2.13m, and
  m·min_n(c_n/c_{n−1}) settles near a positive limit: 0.400 (m = 3), 0.3565 (m = 61),
  0.3549 (m = 101), 0.3539 (m = 151). The asymptotic ratio is m·c_n/c_{n−1} → 0.773. Nothing
  points to a failure on the diagonal. A proof would need the limiting profile at n ≈ 2.13m.

### 2. Wu–Yu–Guo Conjecture 1 (Tsallis entropy is completely monotone for α ∈ (1,2)) · **taken**

- **Statement** (Wu–Yu–Guo, arXiv:2312.01819 v4, IEEE Trans. Inf. Theory 2025, Conjecture 1):
  "The complete monotonicity holds for Tsallis entropy ĥ_α with α ∈ (1,2), i.e.
  (−1)^{k−1} ∂^k ĥ_α(p)/∂t^k ≥ 0 for all t > 0." The authors note: "This conjecture implies the
  completely monotone conjecture for differential entropy h."
- **What I computed.** I took the Gu–Sellke atomic measure μ = 0.002δ₀ + Σ_j c_j(δ_{1.8+j} +
  δ_{−1.8−j}) at t = 1/3, with heat semigroup e^{t∂²}. Then ∂_t⁵ ∫ g_t^α dx equals
  3.6567·10⁻⁷ at α = 1 + 10⁻⁶ (this reproduces Gu–Sellke's H⁽⁵⁾ ∈ (0.36, 0.37)) and
  8.49·10⁻⁴ > 0 at α = 101/100. That violates the k = 5 sign. At α = 1.1 and 1.2 the value is
  negative, so the sign holds there. Method: mpmath at 40 digits, quadrature on [0, 25] split
  into 50 pieces (`src/tsallis.py`). No interval certificate was made.
- **Prior art (decisive).** The conjecture is refuted publicly: "Complete monotonicity of
  Tsallis entropy under heat flow: a sharp order classification" (Zenodo 10.5281/zenodo.24001602,
  2026-11-06, anonymous, AI-assisted; also on evidencepress.org). It shows α = 2 is the only
  order that survives, gives a certified witness at α = 3/2 with derivative order 13, and
  credits the near-1 failure to Gu–Sellke by continuity. Not a hit.

### 3. Habib–Hildebrand Conjecture 7.2 (coefficients of the exponential-polynomial expansion are nonnegative) · open · no counterexample

- **Statement** (Habib–Hildebrand, arXiv:2606.21145, Experimental Math. 2026, Conjecture 7.2).
  Take the ODE u''u − (u')² = e^{−x}P(u) − 1 with u = Σ p_k(x+c)e^{−kx} and p₀ = x. Then:
  "Assume the conditions of Conjecture 7.1 [π₀ = 0, π₁ = π₂], and suppose in addition that
  π_j ≥ 0 for all j. Then the coefficients of all resulting polynomials p_k are nonnegative."
- **What the authors checked.** Floating point only: k ≲ 20 for d = 3 and k ≲ 10 for d = 6,
  where they report "numerical instabilities become significant".
- **Prior art.** Conjecture 7.1 is proved in Habib–Hildebrand, arXiv:2606.24182 (Theorem 2.5),
  whose outlook still lists nonnegativity as open. An Exa search found nothing else.
- **Reduction.**
  - Each p_s solves L_s p = R_s with L_s = x(D² − 2sD + s²) − 2(D − s), by exact back
    substitution (`src/hh.py`, `python-flint` `fmpq_poly`).
  - Validation: the script reproduces the paper's c_{3,0}(β) = 355/81 + (4903/972)β +
    (1313/648)β² + (11/36)β³ exactly for P = t³ + β(t² + t).
  - Scaling P by λ only multiplies p_k by λ^k (the shift x → x + log λ), so π_d = 1 is a valid
    normalisation.
  - Low coefficients are the ones at risk, because c_{3,0} is the first to go negative for
    β < 0.
- **Search.**
  - Exact arithmetic for t³, t⁴ and t⁶ up to k = 25, past the authors' range.
  - Eight extreme families up to k = 22 (degrees up to 177): t³ + ε(t² + t) and
    t⁵ + ε(t² + t) with ε ∈ {10⁻³, 10³}; t⁸ + t² + t; t⁸ + t³; t¹⁰; t¹⁰ + 10⁻²(t² + t).
  - A random scan of π_j ∈ {0, 1/100, 1/10, 1/2, 1, 2, 10, 100} with d ≤ 9 and k ≤ 12, for
    8 × 25 minutes (`src/hhscan.py`). Its only "hits" were invalid inputs π₁ ≠ π₂ produced by a
    generator bug, rejected correctly as having no polynomial solution.
  - Cost: about 5.5 CPU-h.
- **Result.** No negative coefficient. Every computed p_k was a polynomial, as Theorem 2.5
  requires.

### 4. Chien–Kirkland–Li–Nakazato Conjecture 1.1 (maximal numerical range of a cyclic shift) · open · no counterexample

- **Statement** (Chien–Kirkland–Li–Nakazato, arXiv:2304.06050, Conjecture 1.1): "Suppose that
  n ≥ 2, that 0 ≤ a₁ ≤ ⋯ ≤ a_n, and let A = S(a₁, a₃, a₅, …, a₆, a₄, a₂). Then
  W(A_σ) ⊆ W(A) holds for any σ ∈ S_n."
- **What the authors checked.** Proved for n ≤ 6. Nakazato verified n = 7, 8 symbolically.
- **Reduction.**
  - Inclusion means the support functions satisfy h_σ(θ) ≤ h(θ) with h(θ) = λ_max(Re e^{−iθ}A).
    By the 2π/n rotation symmetry, θ ∈ [0, π/n] suffices.
  - The characteristic polynomial of Re(e^{−iθ}A) is M_σ(x) − K cos(nθ), with K = 2∏(a_i/2)
    the same for every σ. So the question is a comparison of matching-type polynomials at the
    levels s ∈ [−K, K].
  - θ = 0 is the known numerical-radius theorem, so a failure would have to sit at θ > 0.
- **Search** (`src/cyc.py`, numpy `eigvalsh`).
  - n = 7: 30 weight vectors. n = 9: 80 vectors × all 20,160 arrangements. n = 10: 9 vectors ×
    all 181,440 arrangements.
  - Each case used 7 values of θ in [0, π/n]. Weights: uniform powers, small integers, and
    log-normal with σ = 1.5.
  - Cost: about 1.5 CPU-h.
- **Result.** No violation. The largest relative excess was 2.5·10⁻¹⁵, attained by the
  conjectured arrangement itself.

### 5. Kozma–Nitzan percolation inequalities (post-FKG, pre-FKG, monotone cluster property) · open · no counterexample

- **Statements** (Kozma–Nitzan, arXiv:2401.12397, "A reduction of the θ(p_c) = 0 problem to a
  conjectured inequality"):
  - Conjecture 1.1 (post-FKG): for a finite graph with arbitrary edge probabilities,
    P(0↔b) ≥ P(0↔A)·min_{a∈A} P(a↔b).
  - Conjecture 1.2 (pre-FKG): P(0↔b) ≥ min_{a∈A} P(0↔A, a↔b).
  - Conjecture 5.1 (mcp): E(f(0)·1{0↔A}) ≥ min_a E(f(a)·1{0↔A}) for every monotone cluster
    property f.
  - Questions 5.5–5.7: three "candidate minimiser" questions. The authors say they are "rather
    hesitant" about these; they are questions, not conjectures.
- **What the authors checked.** "Some (admittedly restricted) numerical evidence". They prove
  |A| = 2, some |A| = 3 cases, and the case where 0 is isolated in G∖A. They prove the mcp for
  1{|Cl| ≥ k} with k ≤ 4.
- **Prior art.** Exa found no refutation. The conjecture implies θ(p_c) = 0 in every dimension,
  so a refutation of post-FKG would be prominent.
- **Reduction.**
  - Exact enumeration of all 2^{|E|} configurations, aggregated by cluster bitmask (`src/perc.py`).
  - The tests cover every root 0, every target b, and every A with |A| ≥ 3 and 0 ∉ A. The mcp
    was tested for f = |Cl| and f = 1{|Cl| ≥ k} with k ≥ 5.
  - Per the authors' reduction, b may be taken non-adjacent to 0, and p = 1/2 suffices if
    graphs are allowed to grow.
- **Search.**
  - All connected graphs with n ≤ 7 vertices and at most 12 edges (geng): p = 1/2, p ∈ {0.1,
    0.3, 0.7, 0.9} for n = 6, and random per-edge probabilities from {0.05, 0.2, 0.5, 0.8, 0.95,
    1} (6 draws per graph for n = 7, 30 for n = 6).
  - Questions 5.6 and 5.7 (`src/percq.py`): all n ≤ 6, and n = 7 with 3 random draws.
  - n = 8, at most 11 edges: the first 240 of 1,648 graphs, 2 random draws each.
  - Continuous hill-climb over edge probabilities (`src/perc_opt.py`): 108 six-vertex graphs
    × 150 steps and 48 seven-vertex graphs × 60 steps, minimising the relative margin of
    pre-FKG, post-FKG and mcp|Cl|.
  - Cost: about 9 CPU-h.
- **Result.** No violation in any run. The hill-climb's most negative margins were about
  −6·10⁻¹⁶. These are floating-point equality cases (A separating 0 from b, or probabilities
  pinned at 0.001 and 0.999), not violations. A real violation needs a margin below about −10⁻¹².

### 6. Hollom–Portier Conjecture 6.2 (sup P(X > x) for Rademacher sums on [√2, 2]) · open · no counterexample

- **Statement** (Hollom–Portier, arXiv:2306.07811, Random Structures Algorithms 2025,
  Conjecture 6.2): with F(x) = sup_X P(X > x) over Rademacher sums of variance 1,
  "F(x) = 1/8 for x ∈ [√2, √3), F(x) = 1/16 for x ∈ [√3, 2), F(2) = 9/256".
- **Prior art.** Still open. Barritz (Zenodo 22773903 and 22818774, 2026-09-15) proves the √2
  endpoint under coefficient restrictions. mathdb.com lists it as open (2026-08).
- **Reduction.** The bound function is a nonincreasing step function, so the conjecture is
  equivalent to three inequalities: P(X > √2) ≤ 1/8, P(X > √3) ≤ 1/16 and P(X > 2) ≤ 9/256.
  The Gaussian limit is far below all three. Pinelis-type mixtures (one large weight plus n
  equal ones) are the natural competitors.
- **Search** (`src/rad.py`). Hill-climbing over weight vectors with n = 3–14, using exact
  enumeration of all 2^n sign patterns. Three seeds × 400 starts × 300 steps for each of the
  three inequalities. Cost: about 2 CPU-h.
- **Result.** The climbs reach an excess of exactly 0 (the equal-weight extremisers) and never
  go above it.

### 7. Mishura–Ralchenko–Schilling Conjecture (A) (fractional Gaussian noise predictor coefficients are positive for H > 1/2) · open · no counterexample

- **Statement** (arXiv:2209.02501, Fractal Fract. 6 (2022) 620, Conjecture (A)): "If H > 1/2,
  then the coefficients of the projection of any element of fractional Gaussian noise onto any
  finite number of its subsequent elements are strictly positive."
- **What the authors checked.** n ≤ 10 numerically. They prove the cases n = 3, 4 and
  Γ_n² > 0.
- **Prior art.** Bodnarchuk–Mishura–Ralchenko (Fractal Fract. 9 (2025) 428) still call it
  Conjecture 3, "numerically confirmed … for a wide range of n".
- **Search.** Levinson–Durbin recursion at 40 digits up to order 150, for H ∈ {0.501, 0.51,
  0.6, 0.75, 0.9, 0.99, 0.999, 0.9999} (`src/fgn.py`). Cost: about 0.1 CPU-h.
- **Result.** Every coefficient is positive. The minimum lies at j ≈ 0.75m and is about
  4–7·10⁻⁴ at m = 150. The last partial autocorrelation is close to (H − 1/2)/m. This is the
  ARFIMA(0,d,0) profile, whose Yule–Walker coefficients are known to be positive. Very likely
  true.

### 8. Kalmykov–Karp Conjecture 1 (Wright q-log-concavity of Σ f_n (a+μ)_n/(c+μ)_n xⁿ/n!) · open · no counterexample

- **Statement** (arXiv:1211.2882, J. Math. Anal. Appl. 406 (2013), Conjecture 1): "Under the
  hypotheses of Theorem 1 the family {f_{a,c}(μ;x)}_{μ≥0} is Wright q-log-concave for all
  c ≥ a > 0". The authors prove the case of integer shift.
- **Prior art.** The later papers by Kalmykov–Karp (arXiv:1611.06724 and 1808.05105) prove
  q-analogues and do not settle Conjecture 1. That is from an Exa search; I did not read them
  in full.
- **Search** (`src/kk.py`). 400 random choices of (a, c, μ, ν), non-integer shifts, and f_n
  equal to 1, qⁿ, binomial rows or qⁿ/n!. Coefficients up to x²⁵ at 30 digits. Cost: about
  0.2 CPU-h.
- **Result.** No negative coefficient.

### 9 and 10. Considered and not searched

- **Caragea–Lee–Malikiosis–Pfander / Cabrelli–Molter–Negreira** (arXiv:2409.09793,
  Conjecture 1.1(b)): for square-free N, every principal minor of F_N is nonzero. This is a
  non-vanishing statement about cyclotomic integers, not an inequality. The authors have
  searched it heavily (part (a) was disproved at N = 16), and it belongs to an
  algebraic/combinatorial lane. Not run.
- **Brevig–Ortega-Cerdà–Seip–Zhao** (arXiv:2210.13922): p ↦ 𝒞_p/p is strictly decreasing.
  Each 𝒞_p is an extremal problem with no finite certificate. Not run.

One-line rejects, not counted: the Krasniqi Alzer–Berg boundary-contact conjecture
(arXiv:2609.28707) is a uniqueness statement with no finite witness. Shemyakova–Khashin–Jeffrey's
a_c ≈ 2.2997 is an estimate, not a conjecture. Gautschi, Mahmoud–Qi, GCM and Fasi–Higham
(unrestricted) are already refuted, so they belong to route c and to the sibling lanes.

## Searches run (do not repeat)

| Conjecture | Range | Precision | CPU-h | Outcome |
|---|---|---|---|---|
| Fasi–Higham, k = m | odd m ≤ 41 with n ≤ 600; m = 61, 101, 151 with n ≤ 8m | exact; 400 digits | 0.3 | positive; m·min ratio → 0.354 |
| Wu–Yu–Guo Tsallis | Gu–Sellke μ, t = 1/3, k = 5, α ∈ {1+10⁻⁶, 1.01, 1.1, 1.2} | 40 digits | 0.2 | violated at α = 1.01; **taken** (Zenodo 24001602) |
| Habib–Hildebrand 7.2 | t³, t⁴, t⁶ to k = 25; 8 families to k = 22; random d ≤ 9, k ≤ 12 | exact rationals | 5.5 | all coefficients ≥ 0 |
| Chien–Kirkland–Li–Nakazato 1.1 | n = 7 (30), 9 (80), 10 (9 weight vectors), every arrangement, 7 θ | double | 1.5 | no violation |
| Kozma–Nitzan 1.1, 1.2, 5.1; Questions 5.5–5.7 | all connected n ≤ 7, ≤ 12 edges; n = 8 (240 graphs); hill-climb | double, tolerance 10⁻¹² | 9 | no violation |
| Hollom–Portier 6.2 | n ≤ 14, hill-climb, 3 × 400 starts | exact sign enumeration | 2 | excess ≤ 0 |
| Mishura–Ralchenko–Schilling (A) | order ≤ 150, 8 values of H | 40 digits | 0.1 | positive |
| Kalmykov–Karp 1 | 400 random parameter sets, up to x²⁵ | 30 digits | 0.2 | positive |

Total: about 19 CPU-h, at most 16 processes at a time.

## Best unfinished lead

**Kozma–Nitzan pre-FKG and mcp at p = 1/2 on larger graphs.** It is the only target whose
authors say their own evidence is thin ("admittedly restricted"). The mcp conjecture is a
"far-reaching generalisation" that the authors only say "might be true". My exhaustive range
stops at 7 vertices (plus a slice of 8). Their reductions (p = 1/2, degree 3, b not adjacent
to 0) point to sparse cubic graphs with 10–16 vertices, where 2^{|E|} is still feasible in C.
Next steps:

1. Port `src/perc.py` to C.
2. Enumerate cubic and subcubic graphs with n ≤ 14.
3. Test pre-FKG and the mcp with f = |Cl| and with up-set indicators 1{S ⊆ Cl}.

Estimated cost: 10–20 CPU-h. The first check is the mcp with general up-set indicators, which
my runs did not cover (only |Cl| and 1{|Cl| ≥ k}). An LP over conic combinations of up-set
indicators decides that check exactly for a given graph.

A second, cheaper lead: **Habib–Hildebrand with mixed signs.** The authors suggest the
nonnegativity region is larger than π ≥ 0 (β ≥ β̂ ≈ −1.9272 for t³ + β(t² + t)). Their
"suggests" is not a conjecture, but mapping the true region exactly is a natural follow-up.

## Proposed edges

```jsonl
{"premise": "Gu-Sellke atomic measure mu (arXiv:2605.11656), heat semigroup e^{t d^2}, t = 1/3: d^5/dt^5 int g_t^alpha = 8.49e-4 > 0 at alpha = 101/100 (mpmath 40 digits, not interval-certified)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Wu-Yu-Guo Conjecture 1 (Tsallis entropy completely monotone along the heat flow for alpha in (1,2)) is false at alpha = 101/100, k = 5", "consequence_ref": "Wu, Yu, Guo, arXiv:2312.01819 v4, Conjecture 1", "consequence_status": "solved", "implication_source": "this sweep (src/tsallis.py); already public: Zenodo 10.5281/zenodo.24001602 (2026-11-06; witness alpha = 3/2, k = 13, plus full classification)", "effort": "M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "taken; rediscovered by continuity from Gu-Sellke as the conjecture's own remark predicts", "novelty": "published", "novelty_searched": "Exa web search (Tsallis complete monotonicity counterexample), arXiv sources of 2605.11656, 2608.30275, 2605.18081; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
{"premise": "Computation: exact rational c_n(m,m) for odd m <= 41, n <= 600; 400-digit for m = 61, 101, 151, n <= 8m", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to the diagonal case k = m of Fasi-Higham Conjecture 3.2 in this range; m * min_n c_n/c_{n-1} -> about 0.354", "consequence_ref": "Fasi-Higham, SIMAX 40 (2019), Conjecture 3.2; diagonal case open per Scardino arXiv:2610.39051", "consequence_status": "open", "implication_source": "this sweep (src/fh.py, src/fh2.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, 0.3 CPU-h", "novelty": "unknown", "novelty_searched": "arXiv source of 2610.39051; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
{"premise": "Exact computation of p_k for P in {t^3, t^4, t^6} (k <= 25), eight extreme families (k <= 22), random nonnegative P with d <= 9 (k <= 12)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Habib-Hildebrand Conjecture 7.2 (nonnegative coefficients of p_k when pi_j >= 0) in this range", "consequence_ref": "Habib-Hildebrand, arXiv:2606.21145, Conjecture 7.2 (Conjecture 7.1 proved in arXiv:2606.24182)", "consequence_status": "open", "implication_source": "this sweep (src/hh.py, src/hhscan.py; validated against the paper's c_{3,0}(beta))", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, 5.5 CPU-h; extends the authors' floating-point range (k ~ 20 for d = 3, k ~ 10 for d = 6) with exact arithmetic", "novelty": "unknown", "novelty_searched": "Exa web search; arXiv 2606.24182; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
{"premise": "Numerical check of support functions at 7 angles in [0, pi/n] over all arrangements: n = 7 (30), n = 9 (80), n = 10 (9 weight vectors)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Chien-Kirkland-Li-Nakazato Conjecture 1.1 (alternating arrangement gives the largest numerical range) for n = 9, 10 in this sample", "consequence_ref": "Chien, Kirkland, Li, Nakazato, arXiv:2304.06050, Conjecture 1.1 (proved n <= 6; verified n = 7, 8)", "consequence_status": "open", "implication_source": "this sweep (src/cyc.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, 1.5 CPU-h, floating point; theta = 0 is a known theorem", "novelty": "unknown", "novelty_searched": "", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
{"premise": "Exact enumeration over all connected graphs with n <= 7 vertices and <= 12 edges (p = 1/2, p grid, random per-edge p), 240 graphs with 8 vertices, and hill-climbing over edge probabilities", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Kozma-Nitzan post-FKG, pre-FKG, monotone-cluster-property (f = |Cl|, 1{|Cl| >= k}) conjectures or Questions 5.5-5.7 in this range", "consequence_ref": "Kozma-Nitzan, arXiv:2401.12397, Conjectures 1.1, 1.2, 5.1", "consequence_status": "open", "implication_source": "this sweep (src/perc.py, src/percq.py, src/perc_opt.py)", "effort": "M", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, about 9 CPU-h; best lead for a larger C search on cubic graphs with p = 1/2", "novelty": "unknown", "novelty_searched": "Exa web search; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
{"premise": "Hill-climbing over Rademacher weight vectors, n <= 14, exact sign enumeration", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Hollom-Portier Conjecture 6.2 (F = 1/8, 1/16, 9/256 on [sqrt2, 2])", "consequence_ref": "Hollom-Portier, arXiv:2306.07811, Conjecture 6.2", "consequence_status": "open", "implication_source": "this sweep (src/rad.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, 2 CPU-h; partial proofs by Barritz (Zenodo 22773903, 22818774)", "novelty": "unknown", "novelty_searched": "Exa web search; mathdb.com; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
{"premise": "Levinson-Durbin at 40 digits, orders <= 150, H in {0.501, 0.51, 0.6, 0.75, 0.9, 0.99, 0.999, 0.9999}", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Mishura-Ralchenko-Schilling Conjecture (A) (positive fGn predictor coefficients for H > 1/2)", "consequence_ref": "Mishura, Ralchenko, Schilling, arXiv:2209.02501, Conjecture (A); open per Bodnarchuk-Mishura-Ralchenko 2025", "consequence_status": "open", "implication_source": "this sweep (src/fgn.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, 0.1 CPU-h; profile matches ARFIMA(0,d,0); very likely true", "novelty": "unknown", "novelty_searched": "Exa web search; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
{"premise": "400 random parameter sets, non-integer shifts, coefficients up to x^25 at 30 digits", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Kalmykov-Karp Conjecture 1 (Wright q-log-concavity for c >= a > 0)", "consequence_ref": "Kalmykov-Karp, arXiv:1211.2882, Conjecture 1", "consequence_status": "open", "implication_source": "this sweep (src/kk.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, 0.2 CPU-h", "novelty": "unknown", "novelty_searched": "Exa web search; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-inequalities"}
```
