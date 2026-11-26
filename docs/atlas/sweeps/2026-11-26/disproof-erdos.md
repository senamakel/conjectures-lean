# Lane `disproof-erdos`: open Erdős statements whose negation we could prove

Date 2026-11-26. Research only: no repo was edited and nothing was built. Input: every declaration
tagged `category research open` in formal-conjectures (FC) `FormalConjectures/ErdosProblems/*.lean`
at commit 9097e2f. That is **850 declarations in 544 files**, extracted by script and read in four
slices of about 212 entries each. Every slice was read literally, with the local definitions opened.
Also used: the teorth/erdosproblems `problems.yaml` copy from the `erdos-feed` lane (2026-11-24),
erdosproblems.com pages and threads read through Exa, and FC PR search with `gh`. Scripts and
outputs are in the session scratchpad (`derdos/`, `derdos/w0`–`w3/`). Claims not confirmed from a
primary source are marked *(unverified)*.

One fact about this FC commit matters for the whole lane: **there are no `answer(sorry)` wrappers
in `ErdosProblems/`** (grep count 0). Each statement fixes a truth value. Statements that end in
an `….answer` def are `sorry` defs: they fix no target and cannot be refuted (about 50 of them).

**In one line:** nothing in the Erdős corpus has a cheap disproof that is both open and
unclaimed. Every route came up empty:
- (a) RH/GRH: RH-strength upper bounds don't contradict any of the open existence or density
  claims.
- (d) Misformalisation: none of the 850 statements is false as written.
- (e) Finite search: every bounded search was negative, recorded in §4 so nobody repeats it.
- (c) Published disproofs: they exist for #96, #97 and #108. Each already has a Lean disproof
  and an open FC status-fix PR.
- (b) Conditional: what is left is #855 from prime k-tuples, which is effort L, plus heuristics
  with no proof route.

## 1. Ranked candidates (easiest first)

| # | FC declaration | Route | Witness or deduction | Effort | Catch |
|---|---|---|---|---|---|
| 1 | `Erdos97.erdos_97`, `erdos_97.variants.k_equidistant`, `Erdos96.erdos_96`, `Erdos108.erdos_108` | (c) | Lean disproofs exist: lkruer/erdos-96-97-proof `Proof.erdos_97_false`, `Proof.erdos_97_general_false`, `Proof.erdos_96_false` (Lean v4.33.1); Kohlmeyer–Kruer, "A counterexample to Erdős problem 108 via arc graphs" (aiXiv:2611.02216), whose abstract says it negates "the pinned Formal Conjectures statement" in Lean; Nguyen–Walczak arXiv:2609.40192 improves 6 to 3 | none for us | Already taken. FC PRs #8219 (96), #8228 (97) and #8227 (108) are open to record this. Nothing to build |
| 2 | `Erdos855.erdos_855` | (b) | `PrimeTuplesConjecture.prime_tuples_conjecture` (FC `Paper/PrimeTuples.lean`) + Hensley–Richards ρ*(y) − π(y) ≥ (log 2 − ε) y/log²y ⇒ ¬855 | L | Class 2. Needs the full HR midpoint sieve; one 447-tuple is not enough (§2) |
| 3 | `Erdos676.erdos_676` | heuristic only | Exceptions to `n = a p² + b, b < p` follow ∏(1−1/p) ≈ 2e^{−γ}/log n: 160,034 up to 2·10⁶ against 154,795 predicted; thread exceptions near 10¹⁶ | XL / no route | The negation says "infinitely many exceptions". Sieve methods only give density 0 (≪ x/(log x)^c). No finite or conditional proof is known |
| 4 | `Erdos852.erdos_852.parts.ii` (h(x) = o(log x)) | heuristic only | A Cramér-model birthday estimate suggests h(x) ≍ log x | XL | No conditional statement in the literature that I found; Brun only gives h → ∞ |
| 5 | `Erdos782.erdos_782.parts.ii` | (b) | Bombieri–Lang ⇒ negation (Cilleruelo–Granville), as the FC docstring already says *(not checked against the paper)* | L–XL | Bombieri–Lang is not in FC as a statement; the deduction is Diophantine-geometric |

Nothing ranks at S or M. Item 1 is listed so that nobody restarts it.

## 2. Erdős 855 sized

FC text: `∀ᶠ (xy : ℕ × ℕ) in atTop ×ˢ atTop, π (xy.1 + xy.2) ≤ π xy.1 + π xy.2`. The negation needs
x, y ≥ N for every N. Swapping roles doesn't help: with y fixed and x → ∞, the inequality becomes
"no interval of length y has more than π(y) primes", so a single admissible tuple of width 3159
(the "taken" HL1 ⇒ ¬HL2 edge) gives only one y. So admissible sets in [0, L] with more than
π(L) elements are needed for **unbounded** L.

Hensley–Richards (Acta Arith. 25 (1973/74) 375–391; Richards, Bull. AMS 80 (1974) 419–438), as
summarised in Richards §4 and the erdosproblems.ai library page, work in three steps:
1. Sieve [−L/2, L/2] at class 0 by every prime p ≤ L/(N log L), for a fixed N > 2/log 2.
2. Lemma 1: the residual set is 2π(L/2) − 2π(L/(N log L)) + O(1), which exceeds π(L) by
   (log 2 − 2/N) L/log²L.
3. Lemma 2 (admissibility for the large primes), through Lemmas 3–5: the primes up to (log L)/N
   cover some progression of length ≥ N log L. This is a Westzynthius–Erdős–Rankin-type statement.

Lean inputs:
- Lemma 1 is the second-order gain 2π(L/2) − π(L) ≫ L/log²L. At tier U it follows from
  schoenfeld-rh's explicit |π − li| bound, since li(L) − 2 li(L/2) ~ −(log 2) L/log²L.
- A Chebyshev upper bound for π(L/(N log L)), which Mathlib has.
- The Rankin-type covering lemma, the expensive part: about 2–4 weeks *(estimate)*.
- `prime_tuples_conjecture` for k = |H| with b = H shifted to ℕ. Its hypothesis `hab` is
  admissibility, which is exactly what HR prove.

So this is effort L, class 2, and it agrees with the atlas and erdos-feed lanes' edges. Nobody has
posted it *(GitHub code search not run for this lane; erdos-feed searched `Erdos855`, no hit)*.

## 3. Stale FC tags (route c), checked and dropped

The database marks these problems as disproved or solved while FC still tags a main statement
`research open`:
- **#96, #97, #108**: Lean disproofs exist and FC status PRs are open (table above).
- **#910 (parts i and ii)**: Rudin's counterexamples assume CH. The FC docstring already says that
  a CH counterexample does not refute the ZFC statement, so this is correctly open.
- **#1082**: part (ii) is already `research solved` with a formal proof (Harborth's 8 points);
  part (i) is genuinely open.
- **#488**: the published counterexamples are for the typo'd `a ∤ n` reading. FC formalises the
  `a ∣ n` reading, and that one survived our search (§4).
- **#133, #664 block design, #125, #147 Janzer, #189 parallelogram, #205 odd, #270 monotone,
  #649 Tong, #692 ii, #897 variants, #967 finite and {2,3,5}, #59 c4 and big_o, #74 sqrt**: these
  are the open *variants* of problems whose main statement was disproved, and the main disproof
  does not reach any of them.

## 4. Negative searches (do not repeat)

Each search had a stated reason, a bounded range and a stop rule (`w0/PLAUSIBILITY.txt`).
Every one found nothing.

| Declaration | Why a witness seemed plausible | Range covered | CPU |
|---|---|---|---|
| `erdos_151`, `.variants.cliqueFree_four` (τ ≤ n − H(n)) | n − H(n) stays at 5 for n = 8, 9 | all graphs n ≤ 10 (12,005,168 at n = 10, nauty geng); equality at every n | ~10 min |
| `erdos_65.parts.ii` | equality cases at n ≤ 7 | all graphs n ≤ 10 with a(n−a) edges | < 5 min |
| `erdos_317.variants.claim2` | 3ⁿ sign patterns vs lcm(1..n) ≈ eⁿ | exact hit only for n ≤ 4 (already in FC); none for 5 ≤ n ≤ 28, meet in the middle | minutes |
| `erdos_49.variants.primes_maximal` | edge cases | N ≤ 2·10⁵ | s |
| `erdos_11.variants.all_odd`, `not_four_dvd` | edge cases | n ≤ 2·10⁶ | s |
| `erdos_288` and interval variants | overlapping intervals allowed | endpoints ≤ 150 | s |
| `erdos_282.variants.sq` | greedy stall | denominators ≤ 12 | s |
| `erdos_458` | two prime squares in one gap | all prime powers ≤ 10¹²; worst ratio 6/7 | < 40 s |
| `erdos_542.variants.only_two` | small n | exact, n ≤ 60 | < 40 s |
| `erdos_488` | known extremal ratio near 2 | A ⊆ [2,40], \|A\| ≤ 3, and A ⊆ [2,22], \|A\| ≤ 4; m ≤ 3000; best 1.975 | < 40 s |
| `erdos_406.variants.one_two` | small exponents | e < 200 | s |
| `erdos_883.parts.i` | small n | 6 ≤ n ≤ 22, all A of the threshold size | minutes |
| `erdos_699` | known Erdős–Szekeres exceptions | n ≤ 250: none for `i ≤ p`; the strict `i < p` form has exactly (10,3,5), (16,2,6), (28,3,14), (28,5,14), (244,3,122), which fits the finite-exception sibling | minutes |
| `erdos_677` | Erdős's l = 2 solutions | k ≤ 12, n, m < 2·10⁵ | minutes |
| `erdos_779` | small n | n < 200 (probable-prime tests) | s |
| `erdos_931.variants.exists_prime` | both blocks must sit in one prime gap and be gap-smooth | n₁ < 10⁸, 3 ≤ k₂ ≤ k₁ ≤ 12 (18 smooth blocks); unfiltered n₁ < 2·10⁵ | 3 s |
| `erdos_676` (for §1 item 3) | heuristic density | n ≤ 2·10⁶ | ~1 min |

## 5. Rejected ideas, with reasons

- **Misformalisation (d), all 850:** no statement is false as written. Edge cases that looked
  dangerous but are guarded:
  - `primeFactors 0 = primeFactors 1 = ∅` gives #850 no witness.
  - #382 requires 1 ≤ u; #373 requires a > 1; #853 and #854 require 0 < t; #820 requires k ≥ 2.
  - In #897 the first disjunct at k = 0 forces f ≡ 0, which only makes it vacuous.
  - In #317 the coercion `(k+1)` elaborates in ℚ, not `Fin n`.
  - #364.strong at k = 0 reads 4 > 0^c, which is true.
  - #695.upperBound at k = 0 is rescued by o 0 = −1.
  - #312: `a i = 0` makes it vacuous, a smell but not falsity.
  - The `tsum`, `sSup` and `sInf` statements (#68, #247, #251, #257, #267, #1049, #1050, #195,
    #329, #647, #757, #770, #1038, #33, #569) are summable, bounded or nonempty where it matters.
- **RH/GRH (a):** the open prime statements (#141, #200, #218, #234, #238, #386, #430, #663,
  #950, #1137, …) are existence or lower-bound claims. An RH upper bound can't contradict them.
  For #663 the CRT heuristic gives q ≈ (1 + log k/log log n) log n, which is consistent with the
  conjecture.
- **#1210 er80 correction via prime tuples:** it reduces to whether admissible H ⊂ [1, L] can
  have Σ 1/h − Σ_{p ≤ L} 1/p unbounded. That is an open combinatorial question, not a known lemma.
- **#386.variants.forall** (fixed k ≥ 3): Erdős–Graham expect "never", but blocks of consecutive
  primes near √n can't be excluded cheaply (C(14,4) = 7·11·13).
- **#850, #364, #938, #137:** the negations are Erdős–Woods-type or abc-strength research.
- **#409 sigma_termination:** σ(n) − 1 is strictly increasing until it reaches a prime, so a
  disproof needs an infinite orbit. Not finitely checkable.
- **#501, #739, #595, #918, #1154, #1168–#1176** (the database's "not disprovable" or
  "independent" problems): not refutable in ZFC.
- **#269 (rational vs irrational), #125 variants:** deliberate contradictory pairs or case
  splits; one of each is false, but deciding which is the open problem.

## 6. What was searched and what was not

- **Searched:**
  - FC 9097e2f, every `research open` declaration in `ErdosProblems/`, read literally.
  - The teorth database status crossed with FC (`derdos/cross.py`).
  - erdosproblems.com pages for 96, 97, 108, 488, 458, 676 (with its thread), 677, 852, 910,
    938, 1082, 1110, 1160 and 951.
  - FC PRs for 96, 97 and 108.
  - The arXiv and aiXiv pages for #108, and the GitHub README of lkruer/erdos-96-97-proof.
- **Not checked:**
  - Whether the lkruer and Kohlmeyer–Kruer Lean files build at our pin.
  - 1337isnot1337/solved-conjectures for this lane: nothing here is a target, so I didn't check.
  - GitHub code search for Erdos855 (erdos-feed did that on 2026-11-26 and found no hit).

## Proposed edges

```json
{"premise": "qualitative prime k-tuples conjecture (FC PrimeTuplesConjecture.prime_tuples_conjecture) + Hensley-Richards midpoint sieve", "premise_status": "open", "premise_lean_source": "formal-conjectures FormalConjectures/Paper/PrimeTuples.lean prime_tuples_conjecture (statement only)", "consequence": "not erdos_855 (eventual Segal / second HL in both x and y)", "consequence_ref": "FC ErdosProblems/855.lean Erdos855.erdos_855", "consequence_status": "open", "implication_source": "Hensley-Richards, Acta Arith. 25 (1973/74) 375-391, Thm + Cor; Richards, Bull. AMS 80 (1974) Thm 4.1", "effort": "L", "lean_exists": "", "in_1337": false, "class": 2, "notes": "Same edge as atlas/erdos-feed lanes. Inputs: 2pi(L/2)-pi(L) >> L/log^2 L (tier U from schoenfeld-rh), Chebyshev bound, Rankin-type covering lemma (primes <= log L/N cover an AP of length N log L) - the expensive part. A single 447-tuple of width 3159 does not reach the atTop x atTop filter.", "sweep": "2026-11-26", "lane": "disproof-erdos"}
{"premise": "lkruer/erdos-96-97-proof Proof.erdos_97_false, Proof.erdos_97_general_false (Lean v4.33.1, standard axioms per README)", "premise_status": "claimed", "premise_lean_source": "github.com/lkruer/erdos-96-97-proof Erdos9697Complete.lean", "consequence": "not erdos_97 and not erdos_97.variants.k_equidistant", "consequence_ref": "FC ErdosProblems/97.lean", "consequence_status": "solved", "implication_source": "Kruer-Kohlmeyer-Price, Unit distances in convex polygons (2026, unrefereed)", "effort": "S", "lean_exists": "github.com/lkruer/erdos-96-97-proof; FC PR #8228 open", "in_1337": false, "class": 1, "notes": "rejected: already done, FC status PR open; not built at our pin", "sweep": "2026-11-26", "lane": "disproof-erdos"}
{"premise": "lkruer/erdos-96-97-proof Proof.erdos_96_false", "premise_status": "claimed", "premise_lean_source": "github.com/lkruer/erdos-96-97-proof Erdos9697Complete.lean", "consequence": "not erdos_96 (convex unit distances O(n))", "consequence_ref": "FC ErdosProblems/96.lean Erdos96.erdos_96", "consequence_status": "solved", "implication_source": "Kruer-Kohlmeyer-Price 2026: Omega(n log log n) unit distances in convex position", "effort": "S", "lean_exists": "github.com/lkruer/erdos-96-97-proof; FC PR #8219 open", "in_1337": false, "class": 1, "notes": "rejected: already done", "sweep": "2026-11-26", "lane": "disproof-erdos"}
{"premise": "Kohlmeyer-Kruer arc-graph construction (triangle-free, chi >= M, C4-free subgraphs 6-colourable); Nguyen-Walczak improve to 3", "premise_status": "claimed", "premise_lean_source": "Kohlmeyer-Kruer Lean (per aiXiv:2611.02216 abstract: negation of the pinned FC statement)", "consequence": "not erdos_108", "consequence_ref": "FC ErdosProblems/108.lean Erdos108.erdos_108", "consequence_status": "solved", "implication_source": "jenwin.io/papers/erdos108-arc-graphs.pdf; arXiv:2609.40192", "effort": "S", "lean_exists": "Kohlmeyer-Kruer Lean (URL not located); FC PR #8227 open", "in_1337": false, "class": 1, "notes": "rejected: already done", "sweep": "2026-11-26", "lane": "disproof-erdos"}
{"premise": "sieve heuristic: n fails iff n mod p^2 >= p for all p <= sqrt n, probability ~ prod(1-1/p)", "premise_status": "open", "premise_lean_source": "", "consequence": "not erdos_676 (infinitely many n not of the form a p^2 + b, b < p)", "consequence_ref": "FC ErdosProblems/676.lean Erdos676.erdos_676", "consequence_status": "open", "implication_source": "none; Erdos [Er79] 'rather unlikely'; Selfridge-Wagstaff search", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 2, "notes": "rejected: counts to 2e6 (160034 exceptions) match 2e^-gamma x/log x; thread has exceptions near 1e16; no proof route beyond density 0 (Brun-Selberg)", "sweep": "2026-11-26", "lane": "disproof-erdos"}
{"premise": "Bombieri-Lang conjecture", "premise_status": "open", "premise_lean_source": "", "consequence": "not erdos_782.parts.ii", "consequence_ref": "FC ErdosProblems/782.lean erdos_782.parts.ii", "consequence_status": "open", "implication_source": "Cilleruelo-Granville, per FC docstring (unverified)", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 2, "notes": "rejected: premise not stated in FC; Diophantine-geometric deduction", "sweep": "2026-11-26", "lane": "disproof-erdos"}
{"premise": "finite search", "premise_status": "theorem", "premise_lean_source": "", "consequence": "counterexample to erdos_151 / erdos_65.parts.ii / erdos_458 / erdos_488 / erdos_699 / erdos_677 / erdos_931.variants.exists_prime / erdos_317.variants.claim2", "consequence_ref": "FC ErdosProblems/{151,65,458,488,699,677,931,317}.lean", "consequence_status": "open", "implication_source": "", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected: all searches negative, ranges in disproof-erdos.md section 4", "sweep": "2026-11-26", "lane": "disproof-erdos"}
```
