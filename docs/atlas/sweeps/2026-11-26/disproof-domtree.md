# Lane `disproof-domtree`: Alikhani–Peng unimodality for trees

Lane `disproof-domtree`, 2026-11-26. Research and computation only. No Lean file and no existing
file was edited. Scripts, logs and raw outputs are in the session scratchpad under
`hunt-domtree/` (`src/`, `runs/`, `bin/`). Downloads went to their own subdirectories
(`hunt-domtree/dl/`), and nothing downloaded was executed. This lane continues
`disproof-hunt.md` §3, which checked every tree with at most 28 vertices for a valley. Claims I could
not confirm from a primary source are marked *(unverified)*.

## Main finding

**No hit.** I found no tree with a non-unimodal domination polynomial. The tree case is still open
in the literature as of 26 Nov 2026 (§0).

What this lane adds:

1. **A structural obstruction (heuristic, not a proof).** Every general counterexample works the
   same way: two "phases" of dominating sets with matched total counts and far-apart typical sizes,
   kept from mixing by many cycles. A tree has no such mechanism.
   - At any vertex `v` of a tree, the "v in S" phase outweighs the "v out of S" phase.
   - Each pendant branch shifts the mass ratio by a factor of at most 2.
   - A Cauchy–Schwarz bound then shows a hub cannot produce a second peak unless one of its branches
     is already "lumpy".
   - Lumpiness, measured as `ρ`, is at most 0.475 over all 53,271 rooted trees with up to 14 vertices.
     It falls roughly like 3/n: annealing reached at most 0.014 at 60–200 vertices.
   - So a hub cannot amplify lumpiness (§2).
2. **A new exhaustive fact (D, computational).** Every free tree with `n ≤ 28` vertices has a domination
   polynomial that is **log-concave from its first strict descent onward**. That property implies
   unimodality. It covers 3,221,658,129 trees with 20 ≤ n ≤ 28; smaller n were checked in Python.
   The normalised post-descent curvature stays at or below −0.83, against −1 for a Gaussian.
   All known non-log-concave trees fail only before the mode: Hong's `U` (n = 27) and the three at
   n = 28, which this run recounted as 1 and 3. So the smallest counterexample to the
   "post-descent log-concavity" strengthening, if one exists, has n ≥ 29.
3. **Negative scans** (§4) found no valley and no near-miss:
   - seven parametrised families up to 3,000 vertices, about 2.6·10⁶ trees in all;
   - 32 annealing chains of 4,000–150,000 steps each, at n from 40 to 3,000.

   Every margin stayed in the Gaussian regime. On Hong's jump `c_{j+1} − c_j` past the first
   descent, a valley needs a value above 2. The best seen outside degenerate stars was 0.13.

**Calibration.** This is a negative result. It is useful mainly as evidence that the tree case is
probably *true*, and as a cheap-to-test strengthening, post-descent log-concavity. It is not a
refutation.

## 0. Prior art (step 0, before any compute)

**The conjecture as published.** Alikhani and Peng, *Introduction to domination polynomial of a
graph*, arXiv:0905.2251 (2009), published in Ars Combin. 114 (2014): "**Conjecture.** The domination
polynomial of any graph is unimodal." There is no separately published tree conjecture. The tree
restriction is the open case, named in these words:
- Du–Heilman–Panova, arXiv:2605.02193 (May 2026), §1: "This conjecture remains widely open even for
  trees."
- Beaton–Brown, arXiv:2012.11813, §4: "the conjecture remains elusive for graphs with low minimum
  degree, and in particular for trees."
- Heilman, Substack, 10 Aug 2026 ("Another Counterexample to Add to the Pile"): "the original
  conjecture could still be true for trees, much like the related independent set problem for trees,
  also known as Erdős problem 993."
- Chanu Hong, *Unimodality of domination polynomials of forests with upper domination gap at most
  four* (2026, under review; `github.com/ARTHONG1/domination-polynomial-verification`, created
  13 Nov 2026): "this is open even for trees."
- `github.com/ipitchford/domination-polynomial-unimodality-counterexamples` (Evidence Press,
  24 Nov 2026), README "Limits": "Trees remain open."

**The refutations of the general conjecture, and why they are not trees:**

| Source | Construction | Why it is not a tree |
|---|---|---|
| Anonymous note on X, 24–25 Jul 2026 *(unverified; known only through Silverman's citation [8] and Heilman)* | derandomised split graph on about 2.8·10¹⁴ vertices | a split graph contains a clique |
| S. J. Silverman, *Domination polynomials need not be unimodal*, Zenodo 10.5281/zenodo.21587251 (26 Jul 2026) | two 37-vertex rooted gadgets with **exactly matched** boundary masses (2·9⁹) but different state means, attached in m = 774,840,977 copies to each of 2q **clique** centres, plus a quadratic layer of degree-2 penalty vertices | cliques, and penalty vertices joining distinct centres |
| Zilin Wang, Zenodo 10.5281/zenodo.21701336 (30 Jul 2026) | explicit connected **split** graph, 134,366 vertices, valley d₆₇₆₇₀ > d₆₇₆₇₁ < d₆₇₆₇₂, CRT/NTT and Arb certificate | clique |
| Heilman, Substack (10 Aug 2026) | bipartite: hub h joined to every vertex of L and R; 2b leaves on h; 2 leaves on each r ∈ R; each ℓ ∈ L has d private z-vertices, each z joined to a random r = f(ℓ, z) | cycles h–ℓ–z–r–h; the random map f is what couples "all of L" against "all of R" |
| L. R. Chalmers, ResearchGate 10.13140/rg.2.2.34268.76163 (2 Oct 2026); Lean archive Zenodo 10.5281/zenodo.23092985 | connected bipartite graphs of **bounded maximum degree**, with arbitrarily many deep peaks | rooted-tree gadgets whose roots are tied by "external clauses" with **expander** bounds (Lean files `ExpanderTails.lean` and `PackingFibres.lean`; doc comment: "External clauses touch roots only; interiors retain the chosen rooted-tree adjacency") |
| ipitchford, Evidence Press, Zenodo 10.5281/zenodo.24511988 (Nov 2026) | split and bipartite graphs on 317,440 vertices, d₁₆₀₀₈₀ > d₁₆₀₃₂₀ < d₁₆₀₅₆₀ | Bhattacharyya–Kahn style two-family construction with clique or bipartite coupling |

The common mechanism: two large families of dominating sets ("L forced, R free" against "R forced,
L free") with equal total counts but different typical sizes. Mixed configurations are suppressed by
vertices that need a dominator from L *or* R, and these vertices are wired so that every ℓ is tied to
many r's. That wiring needs many disjoint ℓ–r paths, which is exactly what a tree lacks.

**Results on trees.** All are positive or partial, and none settles the case:
- Beaton–Schoonhoven (arXiv:2411.02288): monotone segments `d_γ ≤ … ≤ d_{⌊(n+2γ+1)/3⌋}` and
  `d_{⌈(n+2Γ−2)/3⌉} ≥ … ≥ d_n`. Unimodal when Γ − γ < 3.
- Burcroff–O'Brien (Disc. Math. 2023): spiders with at most 400 legs.
- Du–Heilman–Panova: legged caterpillars are log-concave; W_{m,t} fails log-concavity at m indices
  near γ, which "does not provide a path toward disproving Conjecture 1.1".
- Hong (2026, unrefereed):
  - forests with Γ − γ ≤ 4 are unimodal;
  - a non-unimodal forest with gap h has `n − γ < 3K_h − 7`, where K_h = ⌈(h+1)²/4⌉;
  - log-concave for n ≤ 26, with exactly one non-log-concave tree `U` at n = 27;
  - criterion: unimodal if `c_{j+1} − c_j ≤ 2` for all j, where c_j is the mean number of critical
    vertices. His Question asks whether this holds for `(n+2γ+1)/3 < j < n`.
- Goyal (Nov 2026, Lean-checked): leaf deletion can move the unique mode by 2 (7,284-vertex tree).
  This is a different question.
- Omar (arXiv:2601.14494): threshold graphs are log-concave.

I found no claimed tree counterexample on arXiv, Zenodo, GitHub (`gh search repos/code`) or the web
(Exa and web search, 26 Nov 2026). **The tree case is open, so the search went ahead.**

## 1. Why the general mechanism does not transfer to trees

Root T at v. Each pendant branch c of v has DP states:
- A: c ∈ S;
- B: c ∉ S, dominated inside its branch;
- C: c ∉ S and not dominated inside its branch.

Write `f_c = A+B+C` for the factor when v ∈ S and `g_c = A+B` for the factor when v ∉ S. Then

  D(T) = x·Πf_c + (Πg_c − ΠB_c).

1. **The in-phase always wins.** The map S ↦ S ∪ {v} is injective from "v ∉ S" sets to "v ∈ S"
   sets, so the "v out" phase is never heavier than the "v in" phase. The same holds per branch,
   f_c ≥ g_c coefficientwise, so a tree cannot mass-match two phases the way Silverman's gadgets
   are matched. Silverman's two phases attach to *different* hubs and can be compared freely; a tree
   offers only one ordered pair (in, out) per vertex.
2. **Each branch shifts the ratio by at most 2.** The map C → A (add c to S) is injective, so
   `w_c := C_c(1)/g_c(1) ≤ 1`. Any constraint carried along a single path costs at most a factor of
   2 at λ = 1, whereas the general constructions multiply penalties over many parallel paths (the
   z-vertices). In particular the vertex-cover / clause encoding that the general graphs use becomes,
   in a tree, a softened tree independence polynomial (family F5 below).
3. **A hub cannot amplify (Gaussian heuristic).** Let P = Πf_c (in-phase) and Q = Πg_c (out-phase),
   with mass ratio R = e^L. Let q_c = w_c/(1+w_c) and Δ_c = mean(C_c) − mean(g_c). Then:
   - the shift between the phases is S = Σ q_c Δ_c;
   - the mixing variance satisfies V_mix = Σ q_c(1−q_c)Δ_c² ≤ var(P);
   - by Cauchy–Schwarz, S² ≤ (Σ w_c)·V_mix, and with w_c ≤ 1, Σ w_c ≤ L/ln 2.

   For the lighter phase (weight 1/(R+1)) to stand above P's Gaussian tail at distance S, we need
   S²/(2σ_P²) > L − ln(σ_P/σ_Q). Combined with the bound above, that requires
   σ_Q < σ_P·e^{−0.28L}. In other words, V_mix must dominate the intrinsic variance, so some branch
   must be **lumpy**: its own ρ_c := q_c(1−q_c)Δ_c²/var(g_c) must be large. If every branch has
   ρ ≤ 1/2, the requirement becomes 0.72 L > 2L − ln√1.5. That forces L < 0.16, which in turn gives
   S < 0.35σ. Two components that close cannot form two peaks.
4. **Branches are never lumpy (computed).** `src/lumpy.py` computes ρ for every rooted tree with
   n ≤ 14 (53,271 rooted trees). The maximum is **0.475**, at n = 5 (root–a–b with two leaves on b);
   the maxima for n = 5, 10 and 14 are 0.475, 0.291 and 0.213. The shift stays near −1.33 while
   var(g) grows, so ρ_max ≈ 3/n. Annealing on rooted trees (`src/anneal_rho.py`, 18 chains) reached
   only 0.19 at n = 15, 0.014 at 60–200 vertices and 0.005 at 200–500. **The state of a vertex
   moves the size of a dominating set by O(1).** That is the tree analogue of "no long-range order".
   The O(1) shift is also why the known non-log-concave trees fail only next to γ, at λ → 0, and
   never near the mode, where λ = 1 and a valley would have to sit.

The argument is heuristic in two places: the Gaussian tails, and the assumption that ρ stays below
1/2 for every rooted tree, which was checked only by enumeration to 14 vertices and by annealing.
Turning it into a proof would need a local-CLT version of step 3 and a proof that ρ ≤ 1/2. Either
gap could hide a counterexample at small scale, where nothing is Gaussian, but that scale is the
range §3 checks exhaustively.

## 2. Plausibility estimate, written before the scans

- **Valley window.** By Beaton–Schoonhoven a valley lies in `((n+2γ)/3, (n+2Γ)/3)`. By Hong,
  `n − γ < 3⌈(h+1)²/4⌉ − 7`, so h = Γ − γ ≳ 1.15√(n−γ). Any tree with long legs or hub-of-gadget
  structure meets this, so these bounds exclude no family of interest.
- **What is needed.** Two phases with mass ratio O(1), separated by more than about 2 standard
  deviations, that is by about √n vertices.
- **What trees deliver.** Shift ≤ 0.35σ per hub (§1, step 3), with lumpiness that does not grow up
  the tree. Prior odds of a witness at n ≤ 3,000: **very low**. The scans therefore served as a check
  of the heuristic as much as a search. The stop condition was one pass over each family plus the
  annealing budget, or the first valley.

## 3. Implementations and validation

- **DP-1** (`src/dt.py`): python-flint `fmpz_poly`, exact. It uses the subtraction-free merge
  `A ← A(A_c+B_c+C_c)`, `B ← B(A_c+B_c) + C·A_c`, `C ← C·B_c`, with `D = A+B` at the root, plus a
  closed form for k identical branches: `B' = B g^k + C(g^k − b^k)`.
- **DP-2**: the sibling's C code (`hunt/src/treepoly.c`), which uses the subtraction formulation
  `B = Π(A+B) − ΠB`, in 64-bit integers.
- **DP-3** (`src/postlc.c`): a new C OUTPROC for gentreeg using the subtraction-free merge in 128-bit
  integers.
- **Brute force** (`dt.brute`): every subset, testing whether its closed neighbourhoods cover V.

Cross-checks:
- DP-1 rooted at vertex 0 equals DP-1 rerooted at a random vertex, and equals brute force, for
  **every tree with n ≤ 14** (5,446 trees).
- The multiset of DP-1 polynomials equals the multiset from DP-2 for every n ≤ 20 (1.34·10⁶ trees).
- DP-3's maximum curvature agrees with DP-1's at n = 10, 15 and 19.
- DP-3 recounts the non-log-concave trees as 1 at n = 27 and 3 at n = 28, as Hong and the sibling
  found.
- The tree counts match OEIS A000055 (n = 28: 2,023,443,032).
- DP-1 reproduces Hong's printed `D(U, x)` exactly, from 2x⁹ to x²⁷.

**Margins recorded for every tree.** For each tree I recorded:
- `M = max_{j<k} min(log d_j/d_{j+1}, log d_{k+1}/d_k)`, which is positive exactly when there is a
  valley;
- `K` = var × the largest post-descent second difference of log d_j, which is about −1 for a
  Gaussian and positive for a post-mode log-concavity failure;
- `J_core` = Hong's jump `c_{j+1} − c_j = 1 + e_j − e_{j+1}`, with `e_j = (n−j+1)d_{j−1}/d_j`,
  taken after the first descent and excluding the last three indices. A valley needs a jump above 2
  somewhere after the first descent.

## 4. Searches

| # | Family | Range | Trees | Valleys | Best K (n ≥ 40) | Best J_core (n ≥ 40) | CPU |
|---|---|---|---|---|---|---|---|
| E | all free trees: post-descent log-concavity (new property) | 20 ≤ n ≤ 28 exhaustive (smaller n in Python) | 3.22·10⁹ | 0 | −0.8309 (n = 28; −0.810 to −0.831 for n = 20 to 28) | — | ≤ 5.3 h |
| F1 | hub + k₁·G₁ + k₂·G₂ + ℓ leaves; G₁, G₂ any rooted trees with ≤ 7 vertices (85); k ∈ {1,2,3,4,6,8,12,16,24,32,48,64,96}, ℓ ∈ {0,1,4} | n ≤ 1,349 | 1,813,305 | 0 | −0.847 | 0.10 | 0.9 h |
| F2 | hub of hubs: k_a·U_a + k_b·U_b, U = root + k·g (g ≤ 5 vertices, k ≤ 32), k_a, k_b ≤ 16 | n ≤ 2,977 | 128,437 | 0 | −0.852 | 0.13 | 0.3 h |
| F3 | Hong–Beaton–Schoonhoven T(k₁..k_r) + m pendant P₂ (r = 3, 4; k ≤ 5; m ≤ 2; ≤ 60 vertices; 139 of the 305 are non-log-concave) as seeds: hubs of k ≤ 32 seeds under three rootings; pairs joined by paths of 0–5 inner vertices; products of 2–3 non-log-concave seeds (forests) | n ≤ 1,924 | 521,987 | 0 | −0.878 (hub), −0.877 (path), −0.907 (products) | −0.33 | 0.5 h |
| F5 | clause trees: H subdivided at every edge, with a ∈ {0..3} leaves and b ∈ {0..2} pendant P₂ on each H-vertex and c ∈ {0,1} P₂ on each subdivision vertex; H = the sibling's 21 non-log-concave independence trees (n = 26, 28), random trees, stars, paths, binary trees | n ≤ 877 | 1,776 | 0 | −0.866 | −0.05 | s |
| A1 | annealing on K or J_core (leaf moves, subtree prune-and-regraft, add or delete leaf, branch duplication), seeds random, T(k..) and spiders | 18 chains × 150,000 steps, 40 ≤ n ≤ 120 | 2.7·10⁶ evaluations | 0 | −0.894 | −0.032 | 0.5 h |
| A2 | the same | 6 chains × 40,000 steps at 100–300; 3 chains × 8,000 at 300–700; 9 chains × 4,000 at 1,000–3,000 (the 3 spider-seeded chains reached K −0.955/−0.956 and J_core −0.49 to −0.51; no hits) | 3.3·10⁵ evaluations | 0 | −0.923 (100–300), −0.943 (300–700), −0.955 (1,000–3,000) | −0.49 to −0.70 | 1.6 h |
| R | annealing on unit lumpiness ρ (rooted) | 15–500 vertices, 18 chains | — | — | max ρ 0.19 / 0.014 / 0.005 by size class | — | 0.3 h |

All margins sit at their Gaussian values: K between −0.83 and −0.96, approaching −1 as n grows, and
no M above −0.002. The best J_core values come from double stars and stars, near the top end, and are
far below 2. **Least negative valley margin per family:** E −0.831; F1 −0.847; F2 −0.852;
F3 −0.877; F5 −0.866; A1 −0.894; A2 −0.923. These are values of K, where a valley needs a value
above 0. M at large n is −0.002 to −0.003 only because M scales like 1/var.

**Total compute: about 9 CPU-h.** That is an upper bound from wall time × processes, at most 16
processes at a time, on a box at load ~110 on 95 cores. It is under the 20 CPU-h budget.

## 5. What it would take to go further

1. **Prove the obstruction.** A local-CLT version of §1, step 3, together with a proof that every
   rooted tree has `ρ ≤ 1/2`, would prove the conjecture for trees whose phases are near-Gaussian.
   Combined with an exhaustive search for small n, that is a plausible route to a *proof* of the tree
   case. That is research, not a bounded search.
2. **Test the strengthening.** "D(T) is log-concave after its first strict descent" is cheap to test
   and implies unimodality. Extending E to n = 29–30 would take about 3·10⁹ + 1.4·10¹⁰ trees, roughly
   10–30 CPU-h with `bin/postlc`. Hong's Question (jumps ≤ 2 in the window) is the same kind of
   statement, and the margins here are far from 2.
3. **For a refutation.** A tree would need a branch whose root state moves the size by order σ with
   bounded weight loss. §1 says no branch does. Larger random search is unlikely to change that, so I
   do not recommend more annealing.
4. **Lean.** Only relevant for a future hit. The witness would be checked by a certified DP: the
   three-state recurrence proved sound once against `Finset` dominating sets, about 1–2k lines,
   then `native_decide` on the three big coefficients. Polynomials of degree n with n-bit
   coefficients cost about n² GMP operations, which is seconds for n ≈ 2,000. Size M.

## Proposed edges

```jsonl
{"premise": "Exhaustive computation: every free tree on n <= 28 vertices has a domination polynomial that is log-concave from its first strict descent onward (3,221,658,129 trees for 20 <= n <= 28 by a 128-bit C DP; n <= 19 in exact Python); normalised post-descent curvature <= -0.8309", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Alikhani-Peng unimodality for trees below 29 vertices (independent re-check of disproof-hunt), and none to the stronger post-descent log-concavity property", "consequence_ref": "Alikhani-Peng, arXiv:0905.2251 / Ars Combin. 114 (2014), restricted to trees (open: Du-Heilman-Panova arXiv:2605.02193; Hong 2026, github.com/ARTHONG1/domination-polynomial-verification)", "consequence_status": "open", "implication_source": "this sweep (src/postlc.c; cross-checked against brute force for n <= 14, against the sibling's subtraction DP for n <= 20, and against the non-log-concave counts 1 at n = 27 and 3 at n = 28)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative; post-descent log-concavity implies unimodality and is a candidate strengthening for trees; at most 5.3 CPU-h", "novelty": "not-found", "novelty_searched": "Exa and web search; gh search repos/code 'domination polynomial'; Hong, Beaton-Schoonhoven, Du-Heilman-Panova, Omar; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-domtree"}
{"premise": "Parametrised scans (hub + two rooted gadgets <= 7 vertices; hubs of hubs; T(k1..kr) seeds as hubs, paths and products; clause trees from subdivided H) and simulated annealing, 40 <= n <= 3000, exact flint DP", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no tree with a non-unimodal domination polynomial among about 2.6e6 structured trees with n <= 3000 and about 3e6 annealing evaluations; every margin in the Gaussian regime (best K -0.85, best Hong jump 0.13 against a needed 2)", "consequence_ref": "Alikhani-Peng conjecture restricted to trees", "consequence_status": "open", "implication_source": "this sweep (src/scan_hub.py, src/scan_misc.py, src/anneal.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, about 3.5 CPU-h", "novelty": "unknown", "novelty_searched": "", "sweep": "2026-11-26", "lane": "disproof-domtree"}
{"premise": "Heuristic: in a tree, mass(v in S) >= mass(v not in S) (injection); each pendant branch changes the hub mass ratio by a factor in [1,2] (injection C -> A); Cauchy-Schwarz gives shift^2 <= (sum w_c) * mixing variance; computed unit lumpiness rho <= 0.475 for all 53,271 rooted trees with <= 14 vertices, decaying like 3/n", "premise_status": "conjecture", "premise_lean_source": "", "consequence": "the two-phase mass-matched mechanism behind the July-October 2026 refutations (cliques, z-vertices on cycles, expander clauses) cannot be realised in trees; a tree counterexample would need a lumpy rooted branch, which none of the computed ones is", "consequence_ref": "Silverman Zenodo 10.5281/zenodo.21587251; Heilman Substack 10 Aug 2026; Chalmers 10.13140/rg.2.2.34268.76163; Wang Zenodo 10.5281/zenodo.21701336", "consequence_status": "open", "implication_source": "this sweep, section 1 (heuristic, not a proof: Gaussian tails, and rho <= 1/2 unproved)", "effort": "L", "lean_exists": "", "in_1337": false, "class": 3, "notes": "a proof of rho <= 1/2 plus a local CLT would be a route to proving the tree case; research, not a bounded search", "novelty": "unknown", "novelty_searched": "", "sweep": "2026-11-26", "lane": "disproof-domtree"}
```
