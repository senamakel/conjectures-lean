# Lane `disproof-combinatorics`: finite counterexamples in discrete structures

Lane `disproof-combinatorics`, 2026-11-26. This lane did research and computation only: no Lean
file and no existing file was edited. Scripts, logs and downloads are in the session scratchpad
under `hunt-comb/` (`src/`, `runs/`, `dl/`). Downloaded data went into `dl/`, nothing downloaded
was executed, and Python that read downloads ran with `-I`. Claims I could not confirm from a
primary source are marked *(unverified)*.

The bar for a hit, as set by the owner: the conjecture must be open, stated by named authors who
report evidence for it, and refuted by a witness beyond the range they tested that took structure
to find.

## Main finding

**One hit. Bóna and Cory's Conjecture 5.1 (DMTCS 21:2, 2019, #8) is false at n = 29.** Let
`C_n(q)` be the number of cyclic permutations (single n-cycles) of `[n]` that avoid the
pattern `q`. Then

```
C_29(312) = 9,465,101,461,702   >   C_29(321) = 9,388,443,765,578
```

The difference is 76,657,696,124 (0.82 %). This breaks the link `C_n(321) ≥ C_n(231) = C_n(312)` in
their chain. For n ≤ 28 the inequality holds. The authors checked n ≤ 12. Published values reach
n ≤ 24 (OEIS A309506, A309508, Andrew Howroyd). At n = 24 the ratio `C_n(312)/C_n(321)` was 0.833.
No exhaustive search can reach n = 29: there are Catalan(29) ≈ 1.0·10¹⁵ 312-avoiders. The counts
come from transfer-matrix DPs that track how partial cycles connect, described in §2.

Status of the verification:
- **Verification 1:** the counts above.
- **Verification 2:** a second, independently derived algorithm for each count.
  - The algorithms agree on every value they share: n ≤ 28 for C_n(321) and n ≤ 28 for
    C_n(312) (see §2.4).
  - The second program at n = 29 is reported in §2.4.
- **Prior art:** I found no prior refutation or extension (§2.5).

**Negative searches** (§3), each one recorded so it is not repeated:
- Costa–Luu–Wood's CDM conjecture: verified for every connected graph with α = 2 on at most
  18 vertices. The authors checked up to 11.
- Jamison's caterpillar question: verified for every tree up to 27 vertices. Mol–Oellermann
  checked up to 24.
- Akbari–Kumar–Mohar–Pragada–Zhang's Conj. 1.2 (`s⁺ ≥ n`): verified on every connected graph on
  10 vertices. The authors checked up to 9.

**Lesson, as in the sibling lanes.** Graph-invariant and spectral conjectures from 2025–26 are
being mined within weeks. `graffiti-verification-ae088f.gitlab.io` alone claims 481 refutations,
including the Akbari et al. inertia conjecture. Enumerative inequality conjectures in permutation
patterns are much less crowded. The witness here is a number, not an object, and it needs a
clever count, not a search.

## 1. Shortlist

The ranking is (chance of a reachable witness) × (the authors would recognise it), estimated
before any compute.

| # | Conjecture (source) | Authors' range | Why plausible | Prior-art status before compute | Outcome |
|---|---|---|---|---|---|
| 1 | Bóna–Cory Conj. 5.1, `C_n(321) ≥ C_n(312)` (DMTCS 2019) | n ≤ 12 (theirs); n ≤ 24 (OEIS) | The ratio grows by a steady factor of ×1.039 per step, which extrapolates to a crossing at n ≈ 29. Archer–Graves–Laudone (arXiv:2505.04456 §7) say it "may even be the case that c_n(312) > c_n(321) for some n close to 28" | open; nobody had computed beyond n = 24 | **HIT, n = 29** |
| 2 | Costa–Luu–Wood Conj. 10 (CDM), arXiv:2512.17114 | all graphs ≤ 11 vertices | It implies Seymour's strengthening of HC for α = 2. A reduction to maximal triangle-free complements reaches n = 18 cheaply | open | negative, n ≤ 18 |
| 3 | Jamison 1983 caterpillar question (Mol–Oellermann JGT 2019; Cambie–Wagner–Wang EJC 2021) | n ≤ 24 | Optimal trees change shape with n (stars, then double stars, then batons) | open; an LLM-verified "solution" by Ansatz (2026) *(unverified)* | negative, n ≤ 27 |
| 4 | Akbari–Kumar–Mohar–Pragada–Zhang Conj. 1.2: connected, m ≥ n+1 ⇒ s⁺ ≥ n (arXiv:2506.07264) | n ≤ 9 | Exhaustive n = 10 is cheap | open; not in the graffiti-verification list | negative, n = 10 (min slack 0.594) |
| 5 | Akbari–Elphick–Kumar–Pragada–Tang inertia conjecture `2n⁺ ≤ n⁻(n⁻+1)` (Disc. Math. 2026) | n ≤ 9 | — | **refuted**: Chen–Li arXiv:2605.07196 (W_k, n = 15); graffiti-verification §7cw | dropped |
| 6 | Same paper, Conj. 4.12 `n⁺(L(G)) ≤ n⁻(L(G)) + 1` | n ≤ 9 | — | **refuted**: Paone (Zenodo 10.5281/zenodo.21499790), Francis–Uptain arXiv:2607.22874 | dropped |
| 7 | Mkrtchyan's S₁₀ and S₁₂ conjectures (cubic graphs) | — | — | **refuted**: Wolf arXiv:2509.14184 | dropped |
| 8 | Hoffmann-Ostenhof 3-decomposition conjecture | n ≤ 28 (SAT, Zhang–Szeider CP 2025) | — | extending it costs about 4 CPU-years per order | not run |
| 9 | Full Brouwer conjecture with its equality cases (Li–Guo; Chen–Zi arXiv:2503.11165) | n ≤ 9 | — | taken: graffiti-verification §7rn covers n = 11, equality included | dropped |
| 10 | Klostermeyer–Mynhardt γ–θ conjecture (eternal domination) | n ≤ 11 (85 CPU-days) | — | n = 12 is far beyond the budget | not run |
| 11 | Bóna–Cory Conj. 5.2, `C_{n+1} ≤ 4C_n` | n ≤ 12 | — | the ratios are 3.4–3.6 and no trend reaches 4 | checked in passing to n = 29: holds |

Searched and rejected without compute: Gallai path decomposition (n ≤ 11, Botler–Cunha–Sambinelli
2019; replicated by `mathlab.drummerduck.com`), the Fajtlowicz energy conjecture (Graffiti; the
graffiti-verification corpus), graceful trees (n ≤ 35), and graph reconstruction (n ≤ 13).

## 2. Hit: Bóna–Cory Conjecture 5.1 fails at n = 29

### 2.1 Statement as published

Bóna, Cory, *Cyclic permutations avoiding pairs of patterns of length three*, Discrete Math.
Theor. Comput. Sci. 21:2 (2019) #8 (Permutation Patterns 2018), arXiv:1805.05196 v5, §5:

> Let C_n(q) be the number of cyclic permutations of length n that avoid the pattern q. …
> Numerical evidence shown in Table 1 enabled us to formulate the following conjectures.
>
> **Conjecture 5.1** For all positive integers n, the chain of inequalities
> C_n(123) ≥ C_n(132) = C_n(213) ≥ C_n(321) ≥ C_n(231) = C_n(312) holds.

"Cyclic" means a single n-cycle in the cycle decomposition (§1 of the paper; also AGL §2). The
authors' Table 1 covers 3 ≤ n ≤ 12. Archer–Graves–Laudone (arXiv:2505.04456, §7) restate the
chain, extend the table to n = 13, cite OEIS for n ≤ 24, and remark that the last link "becomes
closer and closer". The two equalities are trivial: they come from inverse and
reverse-complement. The other links (123 ≥ 132 ≥ 321) have ratios that move away from 1 (0.74 and
0.69 at n = 24) and are not in danger.

### 2.2 The witness

| n | C_n(312) | C_n(321) | ratio |
|---|---|---|---|
| 24 | 16,245,866,825 | 19,506,240,462 | 0.8329 |
| 25 | 57,578,591,494 | 66,519,726,924 | 0.8656 |
| 26 | 204,968,426,678 | 227,878,322,518 | 0.8995 |
| 27 | 732,625,336,887 | 783,979,716,374 | 0.9345 |
| 28 | 2,628,648,068,210 | 2,707,924,923,904 | 0.9707 |
| **29** | **9,465,101,461,702** | **9,388,443,765,578** | **1.0082** |

The rows n = 25–29 are new; n ≤ 24 reproduces OEIS exactly. The ratio grew by a factor between
1.0389 and 1.0395 at every step from n = 19 to n = 29. So the failure persists for n ≥ 29, and
there is no sign of a reversal (extrapolation, not proof). Only n = 29 is computed exactly.

### 2.3 How the counts were made (verification 1)

There are too many objects to enumerate (Catalan(29) ≈ 1.0·10¹⁵ 312-avoiders), so both counts
come from exact transfer-matrix DPs with u64 counts. Each DP builds the permutation left to
right. It records the partial functional graph `i → π(i)` as a bijection between path starts
(elements whose in-edge is unknown) and path ends (elements whose out-edge is unknown). A branch
is discarded as soon as a cycle closes before the last step.

- **`src/cyc312t.cpp` (312).** 312-avoiders are exactly the permutations a stack can produce
  from the input 1, 2, …, n. The DP runs over the push/pop word. Its state is (pushes v, pops p,
  bijection from stack positions to end ranks).
  - Pushes add a fixed point on top. A pop joins the top start with the smallest end.
  - States with v ≥ n − 1 are not stored. The remaining suffix is (j pops, push n, pop all), and
    each choice of j is decided by whether `s ↦ (h−1) − g(s)` is a single h-cycle.
  - With this trick the stored layer at n = 29 is the size of the full layer at n = 27: peak
    1.7·10⁸ states, 6.8 GB, 958 s wall.
- **`src/cyc321t.cpp` (321).** π avoids 321 iff every entry is a left-to-right maximum or the
  smallest unused value (proved in two lines, and checked by brute force).
  - The sweep is over positions. The state is (mask of used values above the current position,
    bijection from unused values ≤ p to used values > p).
  - Once the value n is used, every later step is forced, so those states are completed on the
    spot.
  - At n = 29: peak 5.4·10⁷ states, 6.6 GB, 832 s.

Validation: both programs reproduce all 25 OEIS terms n = 0..24 of A309506 and A309508, which
Howroyd computed independently. Both also agree with brute force over S_n for n ≤ 7, using the
literal definitions (cycle check plus pattern-occurrence check).

### 2.4 Second verification: independent algorithms

- **321.** `src/cyc321.cpp` is a separate implementation: the same characterisation, no tail
  shortcut, a different hash table. It gives C_28(321) = 2,707,924,923,904, identical. At n = 29,
  `src/cyc321p.cpp` (a re-implementation with 64-bit keys) gives: SEE-321P.
- **312.** Two programs use different characterisations, not the stack.
  - `src/cyc231.cpp` counts the inverse class Av(231) with its own rule, derived from the
    definition of 231: π(i) must lie in the lowest run of consecutive unused values. Its state
    is different (run separators, mask, bijection). It gives 4,605,569,378 at n = 23 and
    16,245,866,825 at n = 24, identical. It needs too much memory beyond that.
  - `src/cyc312p.cpp` / `cyc312p2.cpp` use a position sweep from the 312 definition: π(i) is
    either the largest unused value below the current maximum, or any unused value above it.
    It completes forced tails once n is used, and shares no transition code with `cyc312t`. It
    gives C_26 = 204,968,426,678, C_27 = 732,625,336,887 and C_28 = SEE-312P28, identical.
    At n = 29: SEE-312P29.
- `src/cyc312s.cpp` (the stack DP without the tail shortcut, sorted-array layers) agrees for
  n ≤ 22.

### 2.5 Prior-art check (before and after compute)

- **OEIS.** A309506 and A309508 list data only to n = 24. Their comments and links point only to
  AGL 2025 and Bóna–Cory 2018.
- **Later papers.**
  - Archer–Graves–Laudone (May 2025) leave the inequality open.
  - Laudone, arXiv:2505.05651 (321 cycles, growth ≥ 3.141; no new terms).
  - Laudone, arXiv:2607.21466 (only the (132, 213) class).
  - Archer et al., AJC 94 (2026) (cycle-form avoidance, a different problem).
  - None computes C_n(312) or C_n(321) beyond 24 or settles Conjecture 5.1.
- **Web and code search.**
  - Exa and web search for the conjecture's wording plus "counterexample" found nothing.
  - GitHub code and repo search for "A309506", "A309508", "cyclic permutations avoiding 312" and
    "Bona Cory conjecture" found no relevant hits.
  - `graffiti-verification` README grep for "Bóna" or "cyclic permutation": none.
  - formal-conjectures has no pattern-avoidance cycle statement.
- **Repeated after the hit:** same result, 2026-11-26.

**Calibration.** This is a real refutation of a published, named conjecture.
- The authors tested it (Table 1, n ≤ 12), and OEIS data supported it to n = 24.
- The witness lies far beyond both ranges, and only a non-trivial counting method reaches it.
- AGL had predicted a crossing "close to 28", so the result is anticipated, but no one had shown
  it.
- Scope: only the last link of the chain fails. The links 123 ≥ 132 ≥ 321 hold on all data and
  are not touched.

### 2.6 Lean feasibility

The statement is `(Finset.univ.filter (fun σ : Equiv.Perm (Fin 29) => σ.IsCycle ∧ support = univ
∧ avoids σ 312)).card > (… 321).card`.
- Direct `decide` over 29! permutations is impossible.
- A route is `native_decide` on the two DPs together with a Lean proof that each DP counts the
  set. That means formalising the stack (or position-sweep) characterisation of Av(312) and
  Av(321) and the path-bijection invariant.
- The DPs take about 15 minutes each in C++. A Lean `native_decide` would take hours, with tens
  of GB.
- Effort **XL**. A cheaper intermediate result: prove the characterisations in Lean, then
  certify n = 29 by a verified DP extracted to compiled code. The counts themselves are
  reproducible from `src/` in about 30 minutes on 2 cores.

## 3. Negative searches (do not repeat)

| Conjecture | Why plausible | Range covered | Result | CPU |
|---|---|---|---|---|
| Costa–Luu–Wood Conj. 10 (CDM): every connected G with α(G) = 2 has a non-empty connected dominating matching (arXiv:2512.17114) | the authors checked ≤ 11 only; it implies Seymour's strengthening of HC for α = 2 | **every connected graph with α = 2 on ≤ 18 vertices** (see the reduction below) | no counterexample | < 1 min |
| Jamison 1983 caterpillar question (maximum mean subtree order attained by a caterpillar) | Mol–Oellermann verified n ≤ 24; optimal shapes shift with n | **all trees 24 ≤ n ≤ 27** (gentreeg, 1.17·10⁹ trees; counts match A000055); maximiser unique and a caterpillar at each n: n = 25: 162661/9683, n = 26: 173758/9855, n = 27: 692596/37509 | holds | ≈ 1.5 h |
| Akbari–Kumar–Mohar–Pragada–Zhang Conj. 1.2: connected, m ≥ n+1 ⇒ s⁺(G) ≥ n | authors checked n ≤ 9 | all 11,715,808 connected graphs on 10 vertices with m ≥ 11 (geng; float eigenvalues) | min s⁺ − n = 0.594 (n = 8, 9: 0.71, 0.70); not close | ≈ 0.3 h |
| Bóna–Cory Conj. 5.2 (upper bound `C_{n+1} ≤ 4C_n`) for 312 and 321 | — | n ≤ 29 from §2 | holds (ratios ≤ 3.61) | 0 |

**The CDM reduction.**
- Write H for the complement of G, so H is triangle-free.
- An edge xy of G is dominating iff x and y have no common neighbour in H. So if H is not
  maximal triangle-free, some single edge is a connected dominating matching.
- Hence a counterexample must be the complement of a maximal triangle-free graph that is not
  complete bipartite (if H is complete bipartite, G is disconnected).
- House of Graphs lists all maximal triangle-free graphs up to n = 18 (1,337,848 of them at
  n = 18). An exact backtracking search found a connected dominating matching for every one
  (`src/cdm.c`). It branches on the least vertex the current matching still has to cover, so it
  is complete.

## 4. Best unfinished lead

1. **Make §2 Lean-checkable.** This is the obvious next step for this hit.
2. **Bóna–Cory beyond n = 29.** The ratio trend predicts `C_n(312) > C_n(321)` for every n ≥ 29.
   Proving that needs growth rates: gr(312) > gr(321). Neither is known. The bounds so far are
   ≥ 3.04 and ≥ 3.17 (AGL), and ≤ 4. The data suggest about 3.7 against 3.56. A rigorous
   separation would turn the single counterexample into "false for all large n". That is a
   research problem, not a search.
3. **The same technique.** The path-bijection DP with forced-tail elimination counts cyclic
   permutations in any class with a one-pass generating rule (stack-sortable classes, Av(4321),
   Av(132, 4321), …). Other "c_n(σ) ≥ c_n(τ)" observations in the cyclic-avoidance literature
   are candidates. None was stated as a conjecture in what I read.

## Proposed edges

Total compute for the lane: about 6 CPU-h (DPs ≈ 2.5 h including cross-checks; trees ≈ 1.5 h;
graphs ≈ 0.5 h; the rest is validation), never more than about 16 processes at once, peak RAM
about 8 GB per job.

```jsonl
{"premise": "Exact counts: C_29(312) = 9465101461702 and C_29(321) = 9388443765578 (cyclic permutations of [29] avoiding 312, resp. 321), by transfer-matrix DPs over partial-cycle bijections, cross-checked by independent algorithms", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Bona-Cory Conjecture 5.1 (C_n(321) >= C_n(312) for all n) is false; n = 29 is the least counterexample", "consequence_ref": "Bona, Cory, DMTCS 21:2 (2019) #8, arXiv:1805.05196 v5, Conjecture 5.1", "consequence_status": "solved", "implication_source": "this sweep (hunt-comb/src/cyc312t.cpp, cyc321t.cpp; checks cyc312p2.cpp, cyc231.cpp, cyc321.cpp, cyc321p.cpp)", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route e. Inequality holds for n <= 28 (new values n = 25..29 in section 2.2). AGL arXiv:2505.04456 anticipated a crossing near 28. Lean needs a verified DP (stack/position-sweep characterisation of Av(312), Av(321) plus path-bijection invariant)", "novelty": "not-found", "novelty_searched": "OEIS A309506/A309508; arXiv citing papers (AGL 2505.04456, Laudone 2505.05651, 2607.21466, Archer et al. AJC 94); Exa and web search; GitHub code/repo search; graffiti-verification README; formal-conjectures; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-combinatorics"}
{"premise": "Exhaustive computation: every complement of a maximal triangle-free graph on <= 18 vertices (House of Graphs lists) that is connected has a non-empty connected dominating matching; non-maximal triangle-free complements have a dominating edge", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Costa-Luu-Wood Conjecture 10 (CDM) holds for all connected graphs with independence number 2 on at most 18 vertices", "consequence_ref": "Costa, Luu, Wood, arXiv:2512.17114, Conjecture 10 (checked by the authors to 11 vertices)", "consequence_status": "open", "implication_source": "this sweep (hunt-comb/src/cdm.c)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, under a CPU-minute", "novelty": "not-found", "novelty_searched": "arXiv listing and Exa search for CDM follow-ups; 2026-11-26", "sweep": "2026-11-26", "lane": "disproof-combinatorics"}
{"premise": "Exhaustive computation over all trees with 24 <= n <= 27 vertices (gentreeg): the maximum mean subtree order is attained uniquely, by a caterpillar", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Jamison's caterpillar question below 28 vertices", "consequence_ref": "Jamison 1983 Q1; Mol-Oellermann JGT 2019 (n <= 24); Cambie-Wagner-Wang EJC 2021", "consequence_status": "open", "implication_source": "this sweep (hunt-comb/src/mso.c)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, about 1.5 CPU-h; an LLM-verified 'solution' by Ansatz (2026) is listed on papex.org, unverified", "novelty": "not-found", "novelty_searched": "Exa search; Uppsala thesis 2026 (W. Ruoyu) states the question open", "sweep": "2026-11-26", "lane": "disproof-combinatorics"}
{"premise": "Exhaustive computation over all 11,715,808 connected graphs on 10 vertices with m >= 11: min s+(G) - n = 0.594", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Akbari-Kumar-Mohar-Pragada-Zhang Conjecture 1.2 on 10 vertices", "consequence_ref": "arXiv:2506.07264, Conjecture 1.2 (checked by the authors to 9 vertices)", "consequence_status": "open", "implication_source": "this sweep (hunt-comb/src/exh_splus.py)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search, floating-point eigenvalues with a margin of 0.59", "novelty": "unknown", "novelty_searched": "", "sweep": "2026-11-26", "lane": "disproof-combinatorics"}
```
