# Lane `disproof-hunt`: bounded counterexample searches outside the mined sources

Lane `disproof-hunt`, 2026-11-26. Research and computation only. No Lean file and no existing file
was edited. Scripts, logs and raw outputs are in the session scratchpad under `hunt/`
(`src/`, `runs/`). Downloads went to their own subdirectories (`hunt/dl/`), and nothing downloaded
was executed. Claims I could not confirm from a primary source are marked *(unverified)*.

The sources the brief calls saturated were not searched except to check a candidate against
them. These are formal-conjectures, Epoch's OEIS Open, `tadamcz/fc-review-results`,
`s66lem/conjectures`, 1337 and `openai/math`.

## Main finding

**One hit, and it is already taken.** Conjecture 2 of Cazenave, *Lemmas and Conjectures in
Spectral Graph Theory* (arXiv:2611.03879 v1, 2 Nov 2026) states `λ₂ ≤ μ₁ − 2` for every connected
graph. It is false. The search found an 11-vertex counterexample, two diamonds joined by a path
with three inner vertices, and an infinite family. Both were checked by a second, exact
implementation. But Sulaymon Sadullo refuted the same conjecture with the same 11-vertex graph in
Lean 4 on 19 Nov 2026 (`github.com/Sulayman22S/gap-is-one`), and also proved that the best constant
is 1. **The only new fact from this lane is minimality.** All 11,716,571 connected graphs on 10
vertices satisfy the inequality, so the smallest counterexample has exactly 11 vertices. Sadullo
left order 10 open.

Every other search was negative:

- **Alikhani–Peng unimodality for trees.** Every tree with at most 28 vertices has a unimodal
  domination polynomial, 2.97·10⁹ trees in all. As far as I found, no exhaustive tree range had
  been published. The general conjecture fell in July 2026, but only to astronomically large
  graphs.
- **Forest variant of the Alavi–Malde–Schwenk–Erdős question.** Every product of two or three
  non-log-concave tree polynomials on at most 28 vertices is unimodal.
- **The other curated conjectures of arXiv:2611.03879** (C1, its two strengthenings, C3, C6(i),
  C6(iii), C6(iv) and C7): annealing at 4 ≤ n ≤ 60 found nothing.
- **The 14,150 open and 3,798 conditional items of the same corpus:** see §5.

**Main lesson.** In late 2026 even a three-week-old machine-generated list is being mined within
days, by `gap-is-one`, by the Omega Institute's `trureturing` (which proves C4 and C5) and by
Hexagon notes (Kramer proves C6(ii)). A refutation lane has to check GitHub, Hexagon and
`trureturing` before it calls anything new. Here that check came after the search, not before.

## 1. Shortlist with plausibility notes

The ranking is (chance of a small witness) × (credibility and visibility). The odds are
rough priors written down before each search.

| # | Conjecture (source) | Why a witness seemed plausible | Prior odds | Status before the search |
|---|---|---|---|---|
| 1 | Cazenave 2026, Conj. 2: `λ₂ ≤ μ₁ − 2` (arXiv:2611.03879 §7) | Machine-generated. Tested only on all connected graphs with n ≤ 9 and on parametrised families, with no optimisation. It is "asymptotically tight on paths", and two cliques joined by an edge come within O(1/k) of it. A two-blob graph puts λ₂ near the blob's λ₁ while μ₁ stays near Δ + 1 | medium | listed open; refuted 19 Nov by Sadullo, found only afterwards |
| 2 | Same paper, Conj. 1 `R ≥ λ₂ + 1`, its strengthenings `2m ≥ λ₁² + (λ₂+1)²` and `m ≥ λ₁(λ₂+1)`, Conj. 3 `2R ≤ rk(A)·λ₁`, Conj. 6(i), (iii), (iv), Conj. 7 `R ≥ rad + √2 − 3/2` | Same testing gap. Conj. 1 is tight to 0.012 on `K_80 – K_80`. 6(iii) is tight on paths, and near-cubic two-blob graphs approach it | low–medium | open |
| 3 | The corpus's 14,150 `ouverte` and 3,798 `conditionnelle` items (`preuves_spectrales.zip`, `index_conjectures.csv`) | 2,480 of 16,630 items the prover left open later failed on large graphs. The test base has no local search | medium per item, low visibility | open |
| 4 | Alikhani–Peng 2014, restricted to trees: the domination polynomial of every tree is unimodal | The general conjecture is false (Silverman, Zenodo 10.5281/zenodo.21587251, July 2026; Chalmers, Oct 2026; Heilman's Substack). Trees are named open by Heilman and by Chalmers ("Unimodality for trees remains open"). Non-log-concave trees exist (Beaton–Schoonhoven, arXiv:2411.02288; Du–Heilman–Panova, arXiv:2605.02193). Du–Heilman–Panova call exhaustive search beyond about 20 vertices intractable, so no exhaustive range was published | low (Beaton–Schoonhoven's bounds confine any valley to a window that is narrow for small trees) | open |
| 5 | Alavi–Malde–Schwenk–Erdős 1987, Problem 3, forest form: "for trees (or perhaps forests)" | For forests unimodality does not follow from the tree case (Galvin, arXiv:2502.10654, §1). Since 2023 non-log-concave trees exist (n = 26, 28), and only a product of at least two such factors can fail | very low, seconds of CPU | open |
| 6 | AMSE for trees, beyond n = 29 | Reynolds (`BrettRey/erdos-problem-993`, Zenodo 10.5281/zenodo.19100781) has verified n ≤ 29 | very low | **not run**; n ≤ 28 was rerun only as validation |
| 7 | Chollet's permanent inequality `per(A∘B) ≤ per A per B` | Its relative Bapat–Sunder fell to Drury at n = 7 | low | **not run**: proved for n ≤ 6 (Li–Zhao–Luo, Preprints.org 202608.2196 *(unverified)*) and actively attacked (clopen.solutions OP-00073; yair-lavi.com) |
| 8 | Domination unimodality, general graphs | none | n/a | **dropped**: refuted July 2026 |
| 9 | Graffiti spectral conjectures (Written on the Wall) | The list is old, with few searches | low | **dropped**: Roucairol–Cazenave (arXiv:2409.18626) ran 15-minute MCTS on every computable open item, and WOW-284 was refuted in 2026 (arXiv:2607.27452) |
| 10 | Brouwer's Laplacian sum, Erdős–Gyárfás power-of-two cycles, Lieb's permanental dominance | Famous | very low at a 2 CPU-h cap | **not run** |

## 2. Hit: Cazenave's Conjecture 2 is false (already taken)

**As published** (arXiv:2611.03879 v1, §1 and §7; https://arxiv.org/abs/2611.03879):

> All graphs are simple, undirected and connected, with n ≥ 2 vertices and m edges. … A is the
> adjacency matrix, with eigenvalues λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ (counted with multiplicity) … 𝓛 = D − A
> is the Laplacian, with eigenvalues μ₁ ≥ μ₂ ≥ ⋯ ≥ μₙ = 0.
>
> **Conjecture 2 (#20829).** λ₂ ≤ μ₁ − 2. It is asymptotically tight on paths (λ₂ → 2, μ₁ → 4).

The range the authors checked: "on all connected graphs with at most 9 vertices; on structured
families up to n = 2000 …; on closed-form families … up to n = 10¹⁵". The corpus row is
`20829,ouverte,…,λ2 ≤ (μ1 - 2)`.

**Witness.** Let `G(k, p)` be two copies of `K_k` minus an edge, with an endpoint of one missing
edge joined to an endpoint of the other by a path with `p` inner vertices. Then:
- `G(4, 3)`: n = 11, m = 14. λ₂ = 2.64119, μ₁ − 2 = 2.61803 (μ₁ = (7+√5)/2), margin +0.0232.
- `G(5, 2)`: n = 12, m = 21. This is the graph the search found first, margin +0.0746.
- The family (float scan, `runs/` log in the session): the margin is positive for k = 4 with
  p ≥ 3, for k = 5 with p ≥ 2 and for k ≥ 6 with p ≥ 1. It grows with k, to +0.233 at
  k = 9, p = 6, so the failure is robust, not a rounding artefact.

**Verification 1 (search).** `src/deep_curated.py`, simulated annealing on the relative slack
over connected graphs, seeded from a structured pool, with numpy/LAPACK eigenvalues. It hit
`G(5,2)` and `G(4,3)` within 8,000 steps (347 CPU-s for all 13 curated statements).

**Verification 2 (independent, exact).** `src/verify_exact.py` rebuilds `G(k,p)` from the
description above, not from the search output. It computes `det(xI − A)` and `det(xI − L)` over
ℚ (Faddeev–LeVerrier) and counts roots by Sturm sequences at rational points, with no floating
point:
- `G(4,3)`: 2 roots of `det(xI−A)` above 263/100 and none of `det(xI−L)` at or above 37/8. So
  λ₂ > 2.63 > 2.625 > μ₁ − 2.
- `G(5,2)`: 2 roots above 367/100 and none at or above 281/50. So λ₂ > 3.67 > 3.62 > μ₁ − 2.

**Minimality (new).** `src/exh_c2.py` decoded every connected graph on 10 vertices from nauty
`geng -c 10`: 11,716,571 graphs, matching OEIS A001349. Batched LAPACK gives a maximum
`λ₂ − μ₁ + 2` of −0.0374 there, attained by `G(4,2)`, so no 10-vertex counterexample exists. The
margin is large against float error (about 10⁻¹³ at this size). With the authors' n ≤ 9 test,
**the least order of a counterexample is 11**. It took 133 s wall on 16 cores (about 6 CPU-min).
I did not check whether `G(4,3)` is the only 11-vertex counterexample.

**Prior art: taken.**
- `github.com/Sulayman22S/gap-is-one` (created 19 Nov 2026). In Lean 4 and Mathlib it proves
  `Conj2.conjecture_two_false` with the same graph `G₁₁`, `Conj2.Family.exists_counterexample`
  for every n ≥ 11 (diamonds joined by longer paths), and `Conj2.best_constant`
  (`λ₂ ≤ μ₁ − c` for all connected graphs iff `c ≤ 1`). Its README says "a smallest
  counterexample has 10 or 11 vertices; the case of 10 vertices is not settled here." Its
  `applications/refuted_open_rows.csv` lists 125 open corpus rows that its graphs violate in
  floating point.
- The Omega Institute's `trureturing` issue 26790 (5 Nov 2026) records an unsuccessful attempt
  *(as quoted in the gap-is-one README; not opened)*.
- arXiv lists only v1. I found no erratum.
- I found Sadullo's repository after the hit, by searching the conjecture's wording.

**Lean feasibility.** Already done, by Sadullo, with Rayleigh-quotient certificates: 17 squares for
`μ₁ ≤ 37/8` and two test vectors for `λ₂ ≥ 293/111`. For us the only open item is the minimality
statement ("no connected graph on 10 vertices violates it"). In Lean that is a `native_decide`
over 11.7M graphs with certified eigenvalue bounds per graph: an XL checker for a fact of little
value. **Not recommended.**

**Calibration.** This is a genuine refutation of a published conjecture, with a robust margin,
not a typo-level slip. But it is a three-week-old machine-generated conjecture, and someone else
refuted it first. Credit for it here: nil beyond minimality.

## 3. Alikhani–Peng for trees: exhaustive to n = 28 (negative)

- **Statement.** Alikhani–Peng (Ars Combin. 114 (2014), p. 263, per arXiv:2012.11813 and
  Chalmers 2026) conjectured that the domination polynomial `D(G,x) = Σ d_k x^k` of every graph
  is unimodal. That is now false for general graphs (§1, item 8). Chalmers (ResearchGate, Oct
  2026, p. 1) writes "Unimodality for trees remains open". Heilman (Substack, 10 Aug 2026) writes
  "the original conjecture could still be true for trees".
- **Why a witness was plausible.** The general counterexamples interfere two "phases" of
  dominating sets through gadgets attached at hubs, and such gadgets can be trees. Non-log-concave
  tree sequences exist. The only prior tree search was PatternBoost (Du–Heilman–Panova), which
  looked for log-concavity failures, not valleys.
- **Search space.** Every free tree on 23 ≤ n ≤ 28 vertices, from nauty `gentreeg` with an
  in-process `OUTPROC`. A three-state rooted DP computes `D(T,x)` and `I(T,x)` exactly in 64-bit
  integers. For each tree I computed the valley score and the log-concavity.
- **Stop condition.** n = 28 done (cost estimate about 1.6 CPU-h) or the first violation.
- **Validation.**
  - The DP equals brute-force subset enumeration (`src/brute_tree.py`) on every tree for
    n = 9, 11 and 13.
  - The tree counts match OEIS A000055 (n = 28: 2,023,443,032).
  - The independence polynomials reproduce the known log-concavity failures exactly: 2 trees at
    n = 26, none at n = 27 and 19 at n = 28, matching Kadrawi–Levit (arXiv:2305.01784) and
    Reynolds.
- **Result.** No tree with at most 28 vertices has a non-unimodal domination polynomial, out of
  2,972,066,803 trees for 23 ≤ n ≤ 28. Smaller n were done in seconds and are also clean. A
  by-product: the first trees with non-log-concave domination polynomials have 27 vertices (1
  tree), and there are 3 at n = 28. Beaton–Schoonhoven's example may be larger; I did not compare.
- **Cost.** 7,941 CPU-s (2.2 CPU-h) on 16 cores, 556 s wall. That is slightly over the 2 CPU-h
  cap, as estimated before the start.
- **Caveat.** As far as I found, this exhaustive range is new: Du–Heilman–Panova, Beaton–Schoonhoven
  and Chalmers do not report one, and I did not search beyond those papers. It is a negative
  result only.

## 4. Forests from non-log-concave trees (negative)

- **Question.** AMSE 1987, Problem 3 ("For trees (or perhaps forests), is the vertex independence
  sequence unimodal?", quoted by Galvin, arXiv:2502.10654). By Ibragimov's theorem, a product with
  a log-concave factor keeps unimodality, so a forest counterexample needs at least two
  non-log-concave components.
- **Search.** The 21 non-log-concave trees with at most 28 vertices from §3, and every product of
  2 or 3 of them, repetition allowed: 2,002 forests on 52 to 84 vertices. That covers every forest
  on at most 56 vertices whose non-log-concave components have at most 28 vertices each. All are
  unimodal. Cost: seconds.

## 5. The Duhamel–Cazenave corpus: screen and annealing

ANNEAL_PLACEHOLDER

## 6. Negative searches (do not repeat)

| Conjecture | Why plausible | Range covered | Result | CPU |
|---|---|---|---|---|
| Alikhani–Peng, trees | general case false; trees named open; no exhaustive range published | all trees, n ≤ 28 (2.97·10⁹ for 23 ≤ n ≤ 28) | no valley; first non-LC domination trees at n = 27 | 2.2 h |
| AMSE forests | unimodality does not pass to forests; non-LC trees exist from n = 26 | all products of 2–3 of the 21 non-LC trees with n ≤ 28 | all unimodal | s |
| Cazenave Conj. 1 `R ≥ λ₂+1` and both strengthenings | tight on `K_k – K_k` | annealing, 16 seeds × 8,000 steps, 4 ≤ n ≤ 60, structured and random seeds | best slack −2.6·10⁻³ (C1), −1.2·10⁻³ and −3.4·10⁻³ (strengthenings); exhaustive n = 10 for the strengthenings: −0.74, −0.55 | part of 6 min |
| Cazenave Conj. 3 `2R ≤ rk(A) λ₁` | equality on `K_{a,b}` | as above | only the equality cases (slack 10⁻¹⁶) | — |
| Cazenave Conj. 6(i), 6(iii), 6(iv) a and b | 6(iii) tight on paths | as above, plus exhaustive n = 10 for 6(iii) (−0.50) | best −3.2·10⁻², −2.6·10⁻³, −6.8·10⁻³, −3.2·10⁻³ | — |
| Cazenave Conj. 7 `R ≥ rad + √2 − 3/2` | the literature's hard one (Caporossi–Hansen) | annealing as above | equality on even paths only | — |
| Cazenave Conj. 4, 5, 6(ii) | — | annealing negative | proved since by others: C4 and C5 in `trureturing` (`CazenaveRandicSpectralBound`, `CazenaveLaplacianRankBound`), C6(ii) by Kramer (Hexagon 2611.00232) *(not audited)* | — |
| Corpus open and conditional items | see §5 | see §5 | see §5 | see §5 |

## 7. What I would try next with more budget

1. **Before any search**, grep GitHub, Hexagon (`hexagonmath.org`), `trureturing` issues and
   clopen.solutions for the conjecture's wording. That would have saved the Conjecture-2 effort.
2. **Corpus items whose extremal graphs are big:** two cluster-blobs with long connectors, and
   complete-split clusters as in Sadullo's `T m t`. A stronger annealer with vertex
   insertion and deletion at n = 60–200 and the eigensolver in C would reach the corpus's
   "large-graph" regime, where 2,480 earlier items fell.
3. **Alikhani–Peng for trees at n = 29–30:** about 5.5·10⁹ and 1.5·10¹⁰ trees, so 6 and
   17 CPU-h. Better: a guided search (beam or PatternBoost style) on trees built from the
   two-phase gadgets of the general refutations, scaled down to trees of 40–200 vertices.
4. **The domination analogue of Levit–Mandrescu** (unimodality for well-dominated or
   very-well-covered classes), now that Silverman's interference mechanism exists. That is
   research, not a bounded search.

## Proposed edges

EDGES_PLACEHOLDER
