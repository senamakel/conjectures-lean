# Lane `disproof-oai-neighbours`: open neighbours of openai/math's counterexamples

Lane `disproof-oai-neighbours`, 2026-11-26. Research and computation only. No Lean and no
existing file was edited. Input: openai/math at `3344da599` (2026-11-24), read through a sparse
checkout of `CONTENTS.md`, `preprints/`, `lean/docs/` and `lean/ComparatorChallenges/`. A full
checkout has about 181k files and used up the scratch tmpfs inodes, so `lean/OAI/**` was not
checked out. Scripts and outputs are in the session scratchpad (`oai-work/`, with subfolders
`brannen/` and `ryser/`). Claims I could not confirm from a primary source are marked
*(unverified)*.

## In one line

**No hit.** The best target turned out to be Brannen's simplex conjecture in dimensions 4–8. It is a
named conjecture (Brannen 1996, MathWorld), it is open there by the explicit statement of Feng–Hu–Liu–Xu
(arXiv:2610.13953, 16 Aug 2026), and nobody has claimed it. It has an exact finite-dimensional
reduction, built from FHLX Prop. 4.1–4.2 plus one observation of mine. Under that reduction, every
polytope with n+2 facets in dimensions 4 ≤ n ≤ 8 stays at or below the simplex value, and so do the
n+3 and n+4 facet runs that finished. Both a global search and an exact first-order
analysis say so. The search reproduces the known n = 9 violation and improves its margin. The
second lead was an explicit small-rank counterexample to Ryser's intersecting conjecture, built from
OpenAI's merge-and-split construction. It cannot be instantiated for q ≤ 31: the geometric data do
not exist there, even with every condition the cover proof needs dropped.

## 1. Method and lemma catalogue

`CONTENTS.md` lists 375 result families (the brief's "246" is out of date). A grep for
counterexample, disprove, refute, fails and similar words gives 70 disproof families
(`oai-work/disproof_families.tsv`), plus 378 (ETH). Most are infinite objects in algebraic
geometry, operator algebras, topology or PDE, with no finite witness to transform: 046–059, 095,
098, 151, 195–209, 247–249, 285–330, 340–361. The table keeps the families whose witness is
finite or explicitly parametrised, plus the lemma in each that pins down the structure.

| Family | Outcome | How the witness was found / what it is | Structural lemma a neighbour can use |
|---|---|---|---|
| 161 Sidorenko + forcing | H = incidence graph of 22 triples on 13 points (35 v, 66 e); host G only proved to exist (matrix model over F_q, q → ∞) | Kernel construction: rank-r symmetric-matrix differences, determinant signs, colour-refinement type scores | Prop. 2.1: every pair is in exactly two faces, 3-bit face labels with spanning "exposure orders", every a_e ≥ 1/3, colour refinement discrete. **Checked here:** the triple system is a triangulated 2-sphere (all 33 pairs in 2 faces, every vertex link one cycle, χ = 2, degrees 4³5⁶6⁴), `oai-work/sidsphere.py` |
| 162 Ryser (intersecting) | τ = r = q+1 for every **sufficiently large** prime q; the threshold is not numerical (doc 162, "the prime threshold is existential") | Affine plane F_q², merge two parallel lines and split two lines into opposite-pair blocks in every direction; random independent transversal plus the local lemma | Deterministic reduction Prop. 2.1 (occupancy, concentration of core covers, local condition); intersection needs only validity (1) and compatibility (1) |
| 088 Brannen | Δ₁₀ × Δ₁₀ in R²⁰, ratio 22355476/22020096 | Product identity R_{r+s}(A×B) = R_r(A)R_s(B) | Products help only once c_r c_s > c_{r+s}, i.e. at r = s = 10. Feng–Hu–Liu–Xu: fails for n ≥ 9 with ≤ n+2 facets; true for n = 2, 3; **open for 4 ≤ n ≤ 8** |
| 156 Borsuk | Rank-one projectors on R⁴ (in R⁹), b > 10 | Degree / topological argument | Dimension k(k+1)/2 − 1. k = 3 gives R⁵, but RP² can be split into ≤ 6 parts without an orthogonal pair (cap covers), so it fails |
| 157 Hadwiger | α ≤ 2 graphs with h < 26m/75 + 2/3 < m/2 | Tensor/unit construction, random sampling | Also kills Seymour's K_{⌈m/2⌉} form and Füredi–Gyárfás–Simonyi connected matchings (paper §1, lines 170–192): saturated |
| 155 periodic tiling Z³ | One explicit tile | Encoding of a substitution/Wang system | Dimension 3 is shown minimal: saturated |
| 190 ordered matrix removal | One 66×66 pattern | Explicit sequence of host matrices | Smaller patterns open (unverified), no finite route |
| 132 sensitivity | bs/s² ≥ 2^d/(4(d+2)²) | Iterated composition | Every quadratic-type neighbour dies with it |
| 192 Gopalan–Servedio | Σ f̂(i) > C√deg f for every C; dimensions finite but not bounded | Gaussian "observation" amplification | Kudin–Pašalić already refuted the majority version at d = 4. No explicit √deg witness is known. The neighbour is "an explicit witness", not an open statement |
| 172 Euclidean Ramsey | 12-point circle set, 50-colour obstruction; 9-point algebraically independent set | Tensor-field classification | Every ≤ 5-point circle set is Ramsey; 6–8 points open (unverified) |
| 100 / 118 / 191 / 266 / 076 | Explicit ε-families or existence | Perturbation / LP gap / probabilistic | No finite neighbour found |

## 2. Neighbours checked for open and unclaimed

| Neighbour | Status | Prior-art check (2026-11-26) |
|---|---|---|
| Brannen's bound P_n(K) ≤ (n+1)nⁿ/n! for **4 ≤ n ≤ 8** | Open: FHLX p. 3, "The remaining cases 4 ≤ n ≤ 8 are still unresolved" | Web/arXiv/GitHub searches for Brannen plus dimension 4–8, clopen.solutions/zenodo/github: nothing. fc has no Brannen statement; fc issue #7146 (open) proposes only the n = 20 product witness. The 1337 snapshot has none. OpenAI 088 is silent on n < 20 |
| Ryser intersecting at an **explicit** rank r (smallest open r = 6; Tuza r ≤ 5) | OpenAI's thresholds are existential. The companion paper (r = pⁿ+1) is existential too | Web search found no explicit τ = r intersecting example. Francetić–Herke–McKay–Wanless (linear, r ≤ 9) and Bustamante–Stein (Aharoni's strengthening, r = 13) are different statements |
| Smaller Sidorenko counterexample (fewer than 66 edges) via another sphere triangulation satisfying Prop. 2.1 | No named conjecture. "Sidorenko for all bipartite H with ≤ N edges" is a natural frontier, not a published conjecture | Not searched further: it fails the "named conjecture" test from the coordinator's note |
| Gyárfás tree cover | Refuted together with Ryser (OpenAI Cor. 1.2) | Saturated |
| Seymour α = 2, FGS connected matching | Refuted in OpenAI 157 itself | Saturated |
| Forcing conjecture | OpenAI Cor. 1.3 | Saturated (and in `newsfeed`) |

## 3. Reduction chains

### 3a. Brannen, 4 ≤ n ≤ 8 (run)

1. **Raw space:** all convex bodies in Rⁿ, an infinite-dimensional space.
2. **Polytopes are dense**, and P_n is continuous in the Hausdorff metric, so a strict violation
   is attained by a polytope with some number m of facets.
3. **Exact reduction for m facets (FHLX Prop. 4.1, plus the exactness observation below).**
   Every polytope Q with m facets is, up to a linear map, the Minkowski body whose facet vectors are
   −P_F e_i for an n-dimensional F ⊂ 1^⊥ ⊂ R^m. FHLX prove
   P_n(Q) ≥ nⁿ V(P_F C_m) V((λ+F) ∩ Δ_{m−1}) for every λ. Equality holds when the section is
   homothetic to Q: in Minkowski's inequality the right-hand side is the support-number polytope
   P(h_Q), which is such a section. So
   `P_n(Q)/c_n = Γ(F) := n!/(n+1) · V(P_F C_m) · max_λ V((λ+F) ∩ Δ_{m−1})`,
   and a counterexample with m facets exists iff max_F Γ > 1. That is a k(m) + m parameter problem,
   with k = m − n − 1.
4. **m = n+2 (k = 1).** By FHLX Prop. 4.2, Γ = D(a) f_a(t)/(n+1)². Here f_a is the B-spline density
   of ⟨a, s⟩ for s uniform on Δ_{n+1}, and D(a) = Σ|a_i − a_j|. This leaves n+1 real parameters
   after affine normalisation.
5. **First-order test at the simplex-degenerate family** a = (−1, 0ⁿ, 1), t = 0, which gives
   Γ = 1. The gain in direction (b, τ) is D(b)/(2(n+1)) − n·E_p|⟨b,p⟩ − τ| for p uniform on
   Δ_{n−1}, a convex problem. It reduces to an LP over 4000 Dirichlet samples. On that sample the
   LP is biased toward a gain, so a negative value is conservative.

### 3b. Ryser explicit (run, stopped at the data stage)

Raw space: intersecting r-partite hypergraphs, infinite. OpenAI §2 reduces a counterexample at
r = q+1 to finite data in F_q²: two constituents per direction, and two valid split tuples per
direction that are pairwise compatible. τ is then a set-cover number over (q+1)² blocks and about
e^{−2}q² + 8(q+1) points, which an ILP can settle. The bottleneck comes before τ. Each split line
needs 4 designated points that lie on no other split line. About q·e^{−2(q+1)/q} points per line
qualify: 1.4 at q = 11, 3.9 at q = 29, 5 at q = 37. So data are expected only for q ≳ 50–100. At
that size the ILP has about 10⁴ variables and an integrality gap of at least 1 (Füredi: τ* ≤ r − 1
for r-partite intersecting hypergraphs), beyond the budget.

### 3c. Sidorenko, smaller H (not run)

Template: a 3-uniform complex in which every pair lies in two faces (a closed surface), with
Prop. 2.1 (2)–(4). The class sizes V − 2 match for every V, so the template is formally
dimension-free. Section 7 uses the specific degree sequence (Σ C(2deg i, 2) = 618), but only
inside D-dependent slack, so the proof looks generic *(unverified: needs a full read of §§3–7)*.
The chain would be: plantri triangulations with V ≤ 12 (49,566 at V = 13, fewer below), then
trivial automorphism group and discrete WL, then a SAT search for a 3-bit labelling with exposure
orders. A hit gives an H with 3V − 6 < 66 edges, with no explicit host. Not run: plantri is not
installed, and the target is not a named conjecture.

## 4. Searches run (range, cost, result)

Times are wall-clock on a box at load 120–160 (95 cores); about 8–13 processes at a time.

| # | Target | Plausibility written beforehand | Space searched | Stop | Result | Cost |
|---|---|---|---|---|---|---|
| S1 | Validation | – | FHLX a_ε = (−1, εb, 1), n = 9 | – | Γ = 1.000094 (ε = 0.001), 1.000489 (0.01), 0.99902 (0.03): **reproduces FHLX** at 60 digits (mpmath) and in the general-k code (1.000488926) | seconds |
| S2 | Brannen m = n+2, n = 2,3,4,9 | n = 9 must exceed 1, n = 2, 3 must not (proved) | Nelder–Mead on (a, t), 60 starts each, three start families | 60 starts | n = 2, 3, 4: max Γ = 1 − O(10⁻⁸), attained at the degenerate simplex family. **n = 9: Γ = 1.000708** at a ≈ (0, 0.472, 0.482, 0.489, 0.495, 0.5, 0.505, 0.511, 0.518, 0.528, 1), t = ½. That beats FHLX's ε-family (max about 1.0005); the improvement is ours | ~2 CPU-min |
| S3 | Brannen m = n+2, n = 5–8 | FHLX's perturbative mechanism needs a dimension-8 cube moment; a global optimum could go lower | 300 starts per n (two seeds × 150) | 300 starts | **max Γ = 1** (to within 4·10⁻⁸) for every n = 5, 6, 7, 8; every optimum is the simplex-degenerate family | ~25 CPU-min |
| S4 | First order at the degenerate family, n = 4–10 | Decides 2-split perturbations exactly up to sampling | LP, 4000 samples | – | gain −0.059, −0.032, −0.016, −0.0069, −0.0039 (n = 4–8); **+0.00075 (n = 9)**, +0.0037 (n = 10). The threshold is exactly between 8 and 9 | ~1 CPU-min |
| S5 | Brannen m = n+3 (k = 2), n = 4–8, first pass | A 3-way facet split is a first-order mechanism that m = n+2 lacks | Nelder–Mead over (A, λ) with qhull section volumes centred at λ; starts: 226, 90, 29, 8, 2 for n = 4…8 | 1200 s wall | Reported best 1, **1.0000979**, 1, 1, 0.99999735. The n = 5 value is an **artifact**: recomputed with the robust evaluator it is 0.9999999999999 (a simplex in disguise; five equal columns). qhull's halfspace intersection centred at λ is off by about 10⁻⁴ relative, while the Chebyshev-centred evaluator returns 1 to 10⁻¹³ there and reproduces FHLX to 9 digits | ~1.7 CPU-h |
| S6 | Brannen m = n+4 (k = 3), n = 4–6, first pass | as S5 | as S5; 67, 27, 8 starts | 1200 s wall | best 1, **1.00000076** (artifact: robust 0.9999999999998), 0.99777 | ~1 CPU-h |
| S7 | 3-split first-order φ at the simplex, n = 4, 6 (8–10 never started) | as S5, local | NM over split directions, ε = 10⁻⁴ | killed | Two "positive" φ at n = 4 (0.087, 129) were qhull artifacts: λ had drifted to a simplex vertex (coordinates ~10⁻¹²). Robust recheck: Γ = 0.9999941, 0.9999651. Otherwise φ < 0 (best −0.013 at n = 4, −0.23 at n = 6). The run was stopped because its evaluator is unreliable | ~0.5 CPU-h |
| S5′ | Brannen m = n+3 and n+4, robust evaluator | as S5; the first pass was not trustworthy above 1 − 10⁻⁴ | m points in R^k (columns of A) plus a section point t; Chebyshev-centre LP and qhull; three start families (simplex-degenerate cluster, random, FHLX-like spread). Starts: k = 2: n = 5: 35, n = 6: 25, n = 7: 26, n = 8: 11; k = 3: n = 7: 4, n = 8: 0 | 2400 s, then killed | **Every value ≤ 1.** Best: 1 (n = 5, simplex), 0.99999967 (6), 0.99984 (7), 0.99969 (8); k = 3, n = 7: 0.976. Coverage at n = 8 is thin (11 starts) | ~5 CPU-h |
| S8 | Ryser data, strict (all §2 conditions) | Construction may already work at moderate q | q = 19, 23, 29; full tuple enumeration; 200 greedy transversal restarts | full slot fill | best partial fill 7/40, 10/48, 13/60 slots: **no data** | seconds |
| S9 | Ryser data, relaxed (only what intersection needs) | Cover proof conditions are not needed when τ is checked by ILP | q = 11, 13, 17, 19, 23, 29, 31; 2000 restarts | full slot fill | best partial 7/24, 9/28, 11/36, 13/40, 16/48, 19/60, 20/64: **no data**; a third of the slots fills, matching the e^{−2} heuristic | ~1 CPU-min |

Total compute is about 10 CPU-hours, under the 20-hour budget. The n = 9 improvement in S2 was
checked exactly: with the rounded a above and t = 1/2, rational arithmetic (`fractions`) gives
Γ = 1.0007084752541… > 1, and mpmath at 60 digits agrees. **Lesson recorded:** never trust a qhull
`HalfspaceIntersection` volume near 1 ± 10⁻⁴ unless it is centred at the Chebyshev centre. All
three apparent exceedances in this sweep came from that.

Prior art for every target was searched before compute: web, arXiv, GitHub, clopen.solutions, Zenodo,
fc and the 1337 snapshot. Under the owner's bar, Brannen 4 ≤ n ≤ 8 qualifies. It is a named
conjecture, proved for n = 2, 3 (Chen–Feng–Li–Xi–Xu) and listed as open by FHLX, so any witness
would have needed structure to find. The Ryser target qualifies too, since Tuza proved r ≤ 5.

## 5. Hits

None. Nothing here is a counterexample, and nothing needs Lean checking.

## 6. Best unfinished lead

**Brannen in dimensions 4–8 with many facets, or a non-perturbative witness at n = 8.** The exact
reduction in 3a(3) turns any m into a finite optimisation. That holds for every m, so the lead can
be continued at more facets. What it needs:
(i) a faster evaluator for Γ at k ≥ 2: the bivariate simplex-spline density in closed form instead
of qhull section volumes, and the |det| sum computed once per F;
(ii) gradient-based optimisation with many more restarts in n = 7, 8, where S5 and S6 managed only a
handful of starts;
(iii) since m = n+2 sits exactly at Γ = 1 for n ≤ 8, a second-order analysis at the simplex for
m ≥ n+3, together with the 3-split first-order test (S7).
A hit would have exact rational data: rational a or A, and rational λ. Γ is then rational for k = 1
(B-spline divided differences), so it can be checked exactly, and in Lean by `norm_num` on a closed
form. The second, independent check is the direct formula
P_n(Q) = Σ_I |det(s_F ν_F)| / V(Q)^{n−1}, with Q reconstructed from its H-representation.

## 7. Proposed edges

```jsonl
{"premise": "Computation: max of FHLX Gamma over polytopes with n+2 facets equals 1 for n = 4..8 (numerical, 300 starts each)", "premise_status": "numerical", "premise_lean_source": "", "consequence": "no counterexample to Brannen's simplex bound among polytopes with at most n+2 facets in dimensions 4-8 (evidence, not proof)", "consequence_ref": "Brannen 1996 (Mathematika), P_n(K) <= (n+1)n^n/n!; FHLX arXiv:2610.13953 p.3 lists 4<=n<=8 open", "consequence_status": "open", "implication_source": "FHLX Prop 4.1-4.2 + exactness of the Minkowski step at the optimal section (this sweep)", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search; the n+2 family is critical at the simplex, first-order gain negative for n<=8 and positive for n>=9", "sweep": "2026-11-26", "lane": "disproof-oai-neighbours"}
{"premise": "Computation: n = 9 polytope with 11 facets, Gamma = 1.000708", "premise_status": "numerical", "premise_lean_source": "", "consequence": "Brannen's simplex bound fails in dimension 9 with a larger margin than FHLX's", "consequence_ref": "FHLX arXiv:2610.13953 Thm 1.3", "consequence_status": "solved", "implication_source": "FHLX Prop 4.2", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected as a target: n >= 9 already disproved (FHLX); only the margin is new", "sweep": "2026-11-26", "lane": "disproof-oai-neighbours"}
{"premise": "OpenAI 088: R_20(T10 x T10)/c_20 = 22355476/22020096", "premise_status": "lean-proved", "premise_lean_source": "openai/math lean/docs/088.md", "consequence": "Brannen's simplex maximum fails in dimension 20", "consequence_ref": "fc issue #7146 (open)", "consequence_status": "solved", "implication_source": "OpenAI 088 Thm 1", "effort": "S", "lean_exists": "openai/math; fc #7146 proposes the statement", "in_1337": false, "class": 1, "notes": "rejected: taken; FHLX already had n >= 9", "sweep": "2026-11-26", "lane": "disproof-oai-neighbours"}
{"premise": "OpenAI 162 merge-and-split construction at explicit prime q", "premise_status": "theorem", "premise_lean_source": "openai/math ComparatorChallenges/BalancedRyser.lean (existential q)", "consequence": "explicit intersecting (q+1)-partite hypergraph with tau = q+1 (Ryser fails at an explicit rank)", "consequence_ref": "Ryser's conjecture, intersecting case; Tuza r <= 5", "consequence_status": "open", "implication_source": "OpenAI Balanced Ryser Prop 2.1 (deterministic); direct ILP for tau", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 1, "notes": "negative: no compatible split data for q <= 31 even relaxed; heuristic needs q >~ 50-100; then a 1e4-variable ILP with integrality gap", "sweep": "2026-11-26", "lane": "disproof-oai-neighbours"}
{"premise": "OpenAI 161 triple system is a 13-vertex triangulated 2-sphere (checked)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "candidate smaller Sidorenko counterexamples from other sphere triangulations satisfying Prop 2.1", "consequence_ref": "Sidorenko's conjecture (disproved); smallest counterexample unknown", "consequence_status": "open", "implication_source": "OpenAI 161 §2-§7, generality unverified", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 2, "notes": "not run; not a named conjecture", "sweep": "2026-11-26", "lane": "disproof-oai-neighbours"}
```
