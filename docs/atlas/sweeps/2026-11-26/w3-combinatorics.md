# Lane `w3-combinatorics` (wave 3): statements outside number theory · **paused, incomplete**

**Paused, incomplete.** The owner paused the lane on 2026-11-26. Every script was stopped before
this report was written; one run, the C4-free check of WOWII 133 at n = 13, did not finish.

Research and computation only: no Lean, and no edits outside this file and
`w3-combinatorics.edges.jsonl`. Scripts and logs are in the session scratchpad
`/tmp/claude-1000/-home-ubuntu-work-personal-conjectures/80f083f8-5ab0-487d-92fb-ea9d3923a16c/scratchpad/w3c/`:

- `src/wow.c`: four WOWII conjectures, all invariants.
- `src/wow2.c`: traceability first, then the 189 and 199 hypotheses.
- `src/brute.py`: brute-force cross-check.
- `src/fam133.py` and `src/lip.c`: structured C4-free families and longest induced paths.
- `src/tm.py`: transfer-matrix check.

The `geng` binary was copied from an earlier session's nauty build.

## Summary

**No strong class-A candidate.** What the lane found:

- **Exhaustive negatives beyond the published range.** WOWII 189 and 199 hold on every connected
  graph with 11 vertices. DeLaViña's own range stops at 10 vertices.
- **One routine class-A item.** OEIS A184557, Hardin's empirical recurrence, is proved here by a
  transfer matrix. The ground is crowded: other groups are mass-proving Hardin recurrences in
  Lean.

The WOWII ground is saturated. Many groups have posted AI-assisted proofs and refutations
since July 2026 (see the novelty list). For the four WOWII statements still open in
formal-conjectures (40, 133, 189, 199), the computations below found no counterexample, and
none of the four has a proof.

## Candidates

### B/C-level. WOWII 189 and 199 (Hamiltonian-path sufficient conditions) · open · no counterexample through n = 11
- **Statements.** `FormalConjectures/WrittenOnTheWallII/GraphConjecture189.lean`, `conjecture189`:
  connected, `max_v distEven v ≤ 1 + secondSmallestDegree G` ⇒ `∃ a b, ∃ p : G.Walk a b,
  p.IsHamiltonian`. `GraphConjecture199.lean`, `conjecture199`: connected,
  `largestInducedTreeSize G - 2 ≤ vertexConnectivity G` (ℕ subtraction) ⇒ Hamiltonian path.
  Both are tagged research open, status O on DeLaViña's list.
- **Computation.**
  - Every connected graph on at most 11 vertices was tested.
    - n = 11 covers 1,006,700,565 graphs, which equals A001349(11).
    - Of these, 6,469,055 are non-traceable. The hypotheses were evaluated literally on each
      non-traceable graph, using the fc definitions: `vertexConnectivity` with the complete-graph
      convention, and the second entry of the sorted degree list.
  - **No counterexample to either conjecture.** n ≤ 10 was also run with the full-invariant
    program.
  - Invariants were cross-checked against a Python brute force for n ≤ 6 (exact match).
  - Cost: about 1 CPU-h with 48 processes.
- **Partial proof (189).** The diameter-2 case follows from Ore's theorem.
  - If diam = 2, then distEven(v) = n − deg v.
  - So the hypothesis gives d₁ + d₂ ≥ n − 1.
  - Every non-adjacent pair then has degree sum ≥ n − 1, and Ore's condition for traceability
    applies.
  - The general case is open.
- **Partial analysis (199).**
  - Chvátal–Erdős settles it whenever t(G) ≥ α(G) + 1.
  - That bound fails in general. Example: independent x₁..x_k with a clique of connectors y_ij,
    each joined to x_i and x_j. There α = k and t ≤ 6, but that graph is traceable.
  - A counting argument rules out the obvious non-traceable shape: a clique cut S with
    |S| + 2 isolated components.
  - West's REGS page notes the conjecture is sharp at K_{r,r+1} / K_{r,r+2}.
- **Novelty.**
  - gustavobernardo1/conjectura has a scouting note (CJ-0005) only.
  - txmy/ultra-mathematician has a task "solve-wowii-199" with sources only.
  - No proof or refutation was found for 189.
  - The graffiti-verification README covers original-WOW 189, which is a different
    conjecture.
  - Searches run on 2026-11-26: Exa, GitHub code and repo search ("wowii"), fc PRs.
  - The n = 11 range does not appear elsewhere that I found.
- **Class.** Open, and a proof would be class A. What I have is a negative search. A proof of 199
  looks like a Chvátal–Erdős fan argument and is M–L effort. It is not sketched here.

### WOWII 40, `⌈(pc + b + 1)/2⌉ ≤ f` · open · taken for computation
- `GraphConjecture40.lean` `conjecture40`.
- It holds on all connected graphs with n ≤ 10, and on all C4-free connected graphs with
  n ≤ 12. Minimum slack is 0, so it is tight. Tight families include K_n, K_{m,m} and K_{m,m,m}.
- **Taken:** `cozuya/wowii-conjecture-40` (2026-09-21) has a deficiency form, a bipartite
  reduction, partial proofs and exhaustive verification to n = 11. Do not repeat it.

### WOWII 133, `rad + l^{cC4} ≤ path` · open · partial results public
- `GraphConjecture133.lean` `conjecture133`. fc PR #5727 (merged 2026-09-11) dropped the floor on
  `l G`, so fc's version is the stronger one, with `l` real-valued.
- **The C4 branch is trivial.** If G has a C4, cC4 = 0 and the claim is path ≥ rad + 1.
  path ≥ diam + 1 ≥ rad + 1 always holds, because a diametral geodesic is an induced path.
- **Computation.**
  - All connected graphs with n ≤ 10 were checked.
  - All C4-free connected graphs were checked with n ≤ 12 (18,502 and 120,221 graphs; minimum
    slack 0.18 and 0.17). The n = 13 run was stopped at the pause.
  - Structured C4-free families, longest induced path found by randomized DFS and verified:
    - Petersen: needs 5, holds.
    - Hoffman–Singleton: needs 9, found 20.
    - Erdős–Rényi polarity graphs ER_q, q = 2, 3, 5, 7, 11, 13: for ER_13, needs 10, found 48.
    - Levi graphs of PG(2,q), same q: for q = 13, needs 17, found 86.
  - The margins are huge, so dense C4-free algebraic graphs do not threaten the conjecture.
- **Novelty.** Zenodo 10.5281/zenodo.22054834 (Haoyu Chen, 2026-08-22, AI-generated) proves
  three things:
  - the C4 branch;
  - the case ⌊l⌋ ≤ 2;
  - in the band ⌊l⌋ = 3, that a minimal counterexample has radius ≥ 4.

  It works with the floored statement. Still open. A counterexample would have to be C4-free with
  rad ≥ 4 and l ≥ 3; none was found.

### A (routine, crowded). OEIS A184557: Hardin's empirical order-12 recurrence is true
- **Source.** OEIS A184557, "Number of (n+1)X3 0..2 arrays with no 2X2 subblock summing to less
  than 4". Formula field: "Empirical: a(n)=15*a(n-1)+43*a(n-2)-381*a(n-3)-42*a(n-4)+1696*a(n-5)
  -590*a(n-6)-2216*a(n-7)+1085*a(n-8)+858*a(n-9)-456*a(n-10)-88*a(n-11)+48*a(n-12)"
  (R. H. Hardin, 2011).
- **Proof.**
  - a(n) = 1ᵀTⁿ1, with T the 27×27 row-transfer matrix.
  - The residual u_n = a(n) − Σcᵢa(n−i) equals 1ᵀT^{n−12}P(T)1.
  - By Cayley–Hamilton it vanishes for all n ≥ 12 iff it vanishes for n = 12..38. Checked
    exactly in `src/tm.py`. It holds for every n ≥ 12, counting from a(0) = 27.
  - The script reproduces all 15 OEIS terms.
- **Lean.** A generic "row-local constraint ⇒ card = 1ᵀTⁿ1" lemma, then `decide` or
  `native_decide` on 27×27 integer matrices. Effort M for the framework, S per sequence.
- **Catch: crowded and low value.** The-omega-institute/trureturing has a Lean
  `TransferMatrix.cardMatrix` framework, and has proved A185761–A185768 (std3 axioms).
  Further prior art:
  - Ma–Zhang (Zenodo 10.5281/zenodo.24411969, 2026-11-21; zenodo.24486987, 2026-11-24);
  - Dougherty-Bliss–Spahn (ACM CCA 2025, Hardinian arrays);
  - Song (arXiv 2610.00279).

  A184557 itself was not found proved: Exa search only, not a full search. Any single Hardin
  recurrence is likely to be swept up by those pipelines soon.

### Not reached / not run
- The finite fc statements outside WOWII were listed but not computed:
  - LatinSquare `latinSquareOrder11Transversal` and `molsOrder12`: out of reach.
  - MonochromaticQuantumGraph `eqSystem8_no_solution_d3`, … (polynomial systems; N = 6 is taken
    by fc #8283).
  - Dean's conjecture, k = 5 (infinite).
  - Catch-Up (infinite).
- Ramsey and Turán small cases, Kourovka finite questions, and Erdős combinatorics small cases
  were not reached. The Erdős refutation side is in `disproof-erdos.md`.
- AutoGraphiX and GraPHedron lists were not reached.
- The C4-free WOWII 133 run at n = 13 was stopped.
- No proof attempt beyond the partial arguments above.

## Novelty searches (2026-11-26)
- Exa: Graffiti.pc / WOWII 40, 133, 189, 199; Hardin empirical recurrence proofs.
- The graffiti-verification README, 5.5 MB, was grepped. Its Graffiti.pc entries are 340, 364,
  399a, 427, 434c, 442 and 448b, and none of 40, 133, 189, 199. Its "189" and "133" refer to the
  original WOW.
- GitHub repo search "wowii": 30 repos. Relevant: cozuya/wowii-conjecture-40,
  openmikasa/wowii-conjecture-200, and others on 59, 61, 72, 84, 85, 91, 109, 138, 144, 160, 198a,
  213, 291, 322, 372, 399b.
- GitHub code search "conjecture199".
- fc PRs: `gh pr list -R google-deepmind/formal-conjectures --search` on those file names.
  Results: #3796, #3820, #3821, #5727.
- DeLaViña's WOWII page (last updated 2026-11-19) lists 133 as O.
- Not searched: arXiv full text for 189 and 199, MathOverflow, the solved-conjectures clone,
  openai/math.
