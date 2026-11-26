# Implication atlas

Edges between results: "from `X`, `Y` follows". The atlas is how targets are found. An open `Y`
whose `X` is proved in Lean is a theorem waiting to be written; an open `Y` whose `X` is itself
open gives `theorem Y_of_X`, which becomes unconditional the day `X` is proved.

It complements the [Conjecture Atlas](https://github.com/senamakel/tiny-cortexdb-mathagent),
which scores problems one at a time. This one records the links between them, with the source of
each deduction and, for edges we rejected, the reason.

## Files

| File | Content |
| :--- | :--- |
| `edges.jsonl` | one JSON object per implication edge, kept or rejected |
| `sweeps/2026-11-26/toolkit-reuse.md` | opens with the premise inventory: our theorems with their constants and thresholds |
| `constructions.jsonl` | one JSON object per counterexample construction or structural lemma, with the conjectures it refutes and the neighbours not yet tested |
| `sweeps/` | the report of each discovery sweep, by date and lane |

## Edge schema

| Key | Meaning |
| :--- | :--- |
| `premise` | the result `X` |
| `premise_status` | `lean-proved`, `theorem` (published, not in Lean), `claimed`, `open` |
| `premise_lean_source` | repository, path and declaration when `X` is in Lean |
| `consequence` | the result `Y` |
| `consequence_ref` | formal-conjectures path and declaration, Erdős number, Atlas id, or a citation |
| `consequence_status` | `open`, `partially`, `solved` |
| `implication_source` | where the deduction is published |
| `effort` | `S`, `M`, `L`, `XL` |
| `lean_exists` | where a Lean proof of `Y` or of `X ⇒ Y` already exists; empty if none was found |
| `in_1337` | whether 1337isnot1337/solved-conjectures lists `Y` as settled |
| `class` | `1`: `X` is proved in Lean, so `Y` can be unconditional. `2`: `X` is open |
| `notes` | the catch, the finite range, the reason for a rejection |
| `novelty` | is the deduction itself in the public literature? `published` (a paper, preprint, problem page or public Lean repository proves it), `asserted-unproved` (stated somewhere without a proof), `not-found` (searched and not found; `novelty_searched` says where and when), `unknown` (not yet searched) |
| `novelty_searched` | the places searched and the date |
| `sweep`, `lane` | the sweep date and the lane that found the edge; the same edge can appear from two lanes |

## Constructions: witnesses and where else they might apply

`edges.jsonl` links statements. `constructions.jsonl` links a **witness** to statements: one
JSON object per counterexample construction or structural lemma, with the conjecture it
refuted and the neighbouring conjectures it has and has not been tried against. A proof is
extrapolated by following these links: a construction that refutes `X` is evaluated on each
untested neighbour of `X`, and a lemma that pins down where a counterexample to `X` must sit
is reused as the search filter for the variants of `X`.

| Key | Meaning |
| :--- | :--- |
| `construction` | the object or family, with its parameters |
| `source` | paper, repository and path where it is defined or verified |
| `computable` | what the construction gives in closed form (flag counts, spectrum, exact values), which decides which invariants can be evaluated on it without enumeration |
| `refutes` | the conjectures it settles, with reference and status of the Lean proof |
| `method` | how it was found: `transplant`, `residue-class scan`, `parametrised family`, `annealing`, `warm start`, `analytic location`, `exhaustive` |
| `neighbours_tested` | conjecture, outcome (`holds on the family`, `refuted`, `not computable`), and the sweep report |
| `neighbours_untested` | conjectures of the same shape the construction has not been evaluated on: the to-do list |
| `sweep`, `lane` | as for edges |

An edge whose premise is a construction uses `"premise_status": "construction"` and names the
`constructions.jsonl` line in `premise_lean_source`.

## Priority: not yet in the public literature

Since 2026-11-26 a prover is started only on an edge whose `novelty` is `not-found` or
`asserted-unproved`: a statement that is open in the literature and that we can settle, a
statement that becomes a theorem through the Lean proof of RH and GRH by a deduction nobody
wrote down, a result stronger than the published one, or an implication that was only asserted.
Edges whose deduction is `published` are kept for the record and are not worked on. Edges from
the first sweep were collected before this rule and have `novelty: unknown` unless a later
audit set it; the lanes `novel-via-rh` and `novelty-audit` are filling that in.

## Sweeps

| Date | Lanes | Status |
| :--- | :--- | :--- |
| 2026-11-26 | [formal-conjectures conditional scan](sweeps/2026-11-26/fc-scan.md); [solved-conjectures newsfeed](sweeps/2026-11-26/newsfeed.md) (with an [inventory of 1337isnot1337/solved-conjectures](sweeps/2026-11-26/newsfeed-1337-inventory.md)); [Conjecture Atlas](sweeps/2026-11-26/atlas.md); [reuse of our theorems](sweeps/2026-11-26/toolkit-reuse.md); [implications between open conjectures](sweeps/2026-11-26/implications.md); [Erdős status feed](sweeps/2026-11-26/erdos-feed.md); [lemma mining of big proofs](sweeps/2026-11-26/lemma-mining.md) (inventories: [external](sweeps/2026-11-26/lemma-mining-external-inventory.md), [local](sweeps/2026-11-26/lemma-mining-local-inventory.md)) | 268 edges |
| 2026-11-26, second pass | [wave 2: uncovered premises and areas](sweeps/2026-11-26/wave2.md); refutation lanes ([Erdős](sweeps/2026-11-26/disproof-erdos.md), [other formal-conjectures](sweeps/2026-11-26/disproof-fc-other.md), [literature](sweeps/2026-11-26/disproof-literature.md)) | one candidate passes the novelty test so far: Sun's conjecture on `π(n^k)/n^k` (OEIS A038098) for `k ≥ 4`, from RH; a prover is on it |
| 2026-11-26 | refutation lane: [literature](sweeps/2026-11-26/disproof-literature.md); [Erdős formal-conjectures](sweeps/2026-11-26/disproof-erdos.md); [other formal-conjectures directories](sweeps/2026-11-26/disproof-fc-other.md). The two formal-conjectures lanes found no unclaimed cheap disproof (Erdős: 850 open declarations read; other directories: 1,102), and the literature lane's candidates are tracked in AGENTS.md. | 37 edges |

The sweep reports are research notes: nothing in them was built, and claims marked
*(unverified)* were not checked against a primary source. An edge is confirmed only when its
Lean proof is merged.

## Edges proved so far

Merged into [`conjectures/implications`](../../conjectures/implications/), each rebuilt and its
axioms read before the merge (standard three only).

| Edge | Kind | PR |
| :--- | :--- | :--- |
| infinitely many squarefree `2^n − 1` ⇒ infinitely many non-Wieferich primes (Rotkiewicz), with `sq_dvd_mersenne_iff_isWieferichPrime` | theorem; both were `sorry` in formal-conjectures | #1 |
| Cramér, its strict form, Firoozbakht, or any `p^ε` gap bound ⇒ Erdős 382 (i); Firoozbakht ⇒ Cramér | premise open | #2 |
| Butson `H(4, 2m)` ⇒ Hadamard conjecture | premise open | #3 |
| four exponentials ⇒ `2^t` or `3^t` transcendental for irrational `t` | premise open | #3 |
| abc ⇒ Erdős 936 (four variants) and Erdős 977 (factorial variant) | premise open | #4 |
| quantitative density bound for `k`-term progressions ⇒ Erdős 142 (lower variant) and all-`k` Erdős 140 | premise proved in Lean by openai/math, taken here as a hypothesis | #5 |
| abc ⇒ infinitely many non-Wieferich primes; finitely many consecutive powerful triples; Brocard finiteness; Erdős 366 finiteness forms; equivalence of the three abc forms | premise open | #11 |
| Dickson ⇒ every admissible pattern at consecutive primes; Erdős 141 and variants, Erdős 218 equal gaps, balanced primes | premise open | #13 |
| Firoozbakht ⇒ Oppermann, Andrica, Legendre, Brocard; Oppermann ⇒ Andrica; Andrica ⇒ Legendre | premise open | #14 |

Corollaries of our own theorems, each in its own project folder: prime-powers-rh (#7),
bach-corollaries-grh (#8), legendre-exceptions-rh (#9), ramanujan-rh (#10).

## Candidates not found in the literature (scouts of 2026-11-26)

Reports: [`novel-via-rh.md`](sweeps/2026-11-26/novel-via-rh.md), [`novel-oeis-lists.md`](sweeps/2026-11-26/novel-oeis-lists.md), [`wave2.md`](sweeps/2026-11-26/wave2.md). Nothing here is proved until its project is merged.

| Candidate | Premise | State |
| :--- | :--- | :--- |
| Sun, OEIS A038098: `π(n^k)/n^k` strictly decreasing, `k ≥ 4` | Schoenfeld's bound (RH) + exact counts to `2.8·10⁶` | **proved**, PR #20 (`k = 3` open for `141 ≤ n < 10⁷`) |
| A prime primitive root `q < p` modulo `p²`, every odd prime `p` | erdos-985's argument + one character sum (GRH) | **proved**, PR #21; Martin 1997 has it for large `p` without an explicit constant |
| Sharp generator constant `2/log² 3` for `(ℤ/m)ˣ`, every `m ≥ 3` | lls-grh's analysis (GRH) + finite check | **proved in part**, PR #24 (`m < 2^17` and `m ≥ 5·2^49`, optimality; `2^17 ≤ m < 5·2^49` open) |
| Erdős 770 (iii) with a single-digit constant | LLS Theorem 1.1 (GRH) | **proved** (tier H; constant 5), PR #26 |
| Sun, arXiv:1402.6641 Conj 2.7(i): `π(kn)^{1/k} > π((k+1)n)^{1/(k+1)}` | elementary, no RH | **proved**, PR #23 (tier D) |
| Sun, Conj 2.14(ii): `π(n²)^{1/n}` strictly decreasing, `n ≥ 3` | elementary, no RH | **proved**, PR #23 (tier D) |
| Sun, Conj 3.25 / OEIS A243164: a prime `q < n` with `q·n` a primitive root mod `p_n` | erdos-985's argument with a shorter range (GRH) | feasibility study running |
| Grosswald's conjecture modulo `p²` (Kerr–McGown–Trudgian) | grosswald-grh's sieve + one term (GRH) | not started: about 1000 CPU-hours of checks |
| Hassani 2013: `A_n/G_n` decreasing for `n ≥ 226` | RH bound from about `3·10¹³` | not started: the range below is beyond a Lean checker |
| Axler's Conjecture 3.4 (arXiv:1609.07934) | RH beyond Axler's `10¹⁹` | not started: finite range would be a cited hypothesis; a preprint of 2026-11-24 studies the same quantity |

## Novelty verdicts (audit of 2026-11-26)

Is the mathematical statement in the public literature? Full report:
[`sweeps/2026-11-26/novelty-audit.md`](sweeps/2026-11-26/novelty-audit.md).

| Result | Verdict |
| :--- | :--- |
| Erdős 770 (iii), explicit for every `n ≥ 2` | not found in explicit form; **proved** (tier H; constant 5), PR #26 |
| `O(log³ N)` exceptions for Oppermann, Andrica, Brocard under RH | not found |
| Erdős 647 "infinitely many" variant from Dickson | asserted without proof (Erdős 1979) |
| Sun's `π(n^k)/n^k` conjecture for `k ≥ 4` (in progress) | not found |
| A prime primitive root `q < p` modulo `p²` (in progress) | not found |
| Cookson Hills from Flint Hills | not found written down; short |
| Units `≤ 2 log² m` generate `(ℤ/m)ˣ` | published (Lamzouri–Li–Soundararajan; Bellotti 2026) |
| Ramanujan's inequality under RH | published (Dudek–Platt 2015), with a lower threshold than ours |
| Prime between `x^α` and `(x+1)^α`, `α ≥ 3` | published and stronger (Chamberland–Straub reach `9/4`) |
| Firoozbakht ⇒ Oppermann, Andrica, Legendre, Brocard, Cramér | published (Ferreira–Mariano, arXiv:1604.03496) |
| Dickson ⇒ Erdős 141, 218 | published (Schinzel–Sierpiński 1958); balanced primes folklore |
| abc ⇒ Erdős 366 forms, powerful triples | published |
| Erdős 142 lower variant, Erdős 140 for all `k` | published (erdosproblems.com/3) |
| Solé–Planat, extremely abundant, extraordinary numbers | published RH-equivalences |

Stronger statements the audit proposes, none in the literature: the sharp generator constant
`2/log² 3 ≈ 1.657` for every `m ≥ 3` (left open by Bach in 1990); Erdős 770 (iii) with a
single-digit constant; explicit per-block exception bounds for the four Legendre-type conjectures.
The audit also notes that Bazzanella's Theorem 2 may give `log³ N` when summed over `[1, N]`,
the same as ours; this needs checking against the journal version.
