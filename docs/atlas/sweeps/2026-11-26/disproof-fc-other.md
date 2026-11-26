# Lane `disproof-fc-other`: refuting formal-conjectures statements outside `ErdosProblems/`

Lane `disproof-fc-other`, 2026-11-26. Research only. Nothing was built and no repository was
edited. "fc" means formal-conjectures at `9097e2f` (2026-11-24, still its `HEAD` when checked);
paths are relative to `FormalConjectures/`. Numbers come from C and `python3 -I` scripts in the
session scratchpad (`scratchpad/disproof/`). Claims I could not confirm from a primary source are
marked *(unverified)*.

## Method and coverage

- `disproof/extract.py` pulled every declaration tagged `category research open` outside
  `ErdosProblems/`: **1,102 declarations in 601 files** (OEIS 394, Wikipedia 336, Green 128,
  Paper 93, Arxiv 43, OpenQuantumProblems 28, Other 17, Millennium 12, WOWII 11,
  OptimizationConstants 11, Books 11, Mathoverflow 9, Kourovka 5, Litt 2, Hilbert 2). None of
  them uses `answer(sorry)`.
- I read every statement, and the definitions behind about 80 of them, asking of each whether its
  negation follows from (a) RH/GRH or our theorems, (b) another open statement, (c) a published
  disproof, (d) a misformalisation, or (e) a small search.
- Prior art was checked in five places: fc's 554 open non-Erdős PRs (all touched files were
  listed; 163 of the 601 lane files are touched), the fc issues "Open statements with known
  solutions" #4927, #6448 and #6591, the Epoch AI OEIS Open results
  (`epoch-research/LeanOpenProblems-results`, sparse clone of every `scores.json` and
  `metadata.json`), the Epoch fc misformalisation audit (`tadamcz/fc-review-results`, 5 runs),
  and GitHub code search on each fc namespace I considered. The 1337 `CONTENTS.md` has none of the
  candidates below.

## Main finding

**Three groups have already worked over this lane, and every refutation I found or confirmed is
already claimed.**

1. **Epoch AI, OEIS Open** (Adamczewski, arXiv:2608.11941). It covers the 492 OEIS conjectures
   that Tsoukalas et al. formalised. Across the 19 OEIS run directories, 170 conjectures were
   resolved with checked Lean proofs: **61 disproved and 109 proved**. Their statements are
   Tsoukalas's, not fc's. Of their 61 disproofs, 17 land on A-numbers that still have open fc
   declarations. I checked each witness against the literal fc text. Most of them refute a defect
   in Tsoukalas's wording that fc does not share: A7406, A17666, A60841, A179524, A179537,
   A191004, A229969, A232616, A234360 and A262403. Two are genuine refutations of the fc text (A189409, A238281). A261876 refutes the
   characterisation that fc already marks solved as `conjecture_2`, and fc PR #8070 refutes
   `conjecture_3` at a different `n`. Two are incompatibility results (A92243, A120424). A46969 and
   A241898 already have open fc PRs. Details are under Candidates and Rejected.
2. **Epoch AI, fc-review audit** (`tadamcz/fc-review-results`). A language model reviewed every fc
   file against its source for misformalisations, with a "trivial proof" phase that writes Lean
   proofs or refutations of the defective statements. It flagged 76 lane files at some commit,
   and issues were filed. The false-as-written cases I re-read have already been fixed by
   `9097e2f`. Green 21 `fox_kleitman_modular` now has `0 < k`, Green 133 no longer has the floor,
   and A153330 `conjecture4` now has an occurrence hypothesis. Route (d) is therefore saturated.
3. **fc's own pipeline.** fc has 554 open non-Erdős PRs, many of which settle lane statements:
   TxGraffiti 3 (#7661), A238281 (#8225), A261876 `conjecture_3` (#8070), A108569 (#7644),
   A105720 (#8312), A114216 (#8068), A108864 (#8067, #8072), A114137 (#8071), A120424 (#8210),
   A60841 (#7885), A46969 (#7982), A241898 (#7936), WOWII 61/72/96/372, Kaplansky idempotent
   (#8213), Atiyah–Sutcliffe (#6966), Barker (#7759), Kakeya (#7741), Flint Hills (#7757),
   Green 36/44/35, and others. The known-solutions issues list more.

What is left unclaimed is a handful of **class-2 "X ⇒ ¬Y" edges between fc statements** (S, a
few lines each). Each holds because the two statements contradict each other outright, not
because of any new mathematics. The Cramér–Granville family belongs to the same kind, but it is
already in `disproof-literature`.

## Candidates, easiest first

### 1. `EllipticCurveRank.finite_twentyone_lt_finrank` ⇒ ¬`unbounded_rank_conjecture` (S, unclaimed)
- **Statements** (`Wikipedia/EllipticCurveRank.lean`, both research open):
  `{E : RatEllipticCurve | 21 < E.rank}.Finite` (the PPVW 2016 heuristic, §8.2) and
  `∀ n, ∃ E : RatEllipticCurve, n ≤ E.rank`.
- **Deduction.** If ranks are unbounded, then for each `n > 21` there is some `E_n` with
  `rank ≥ n`. These curves are pairwise distinct for distinct rank values, so infinitely many
  curves have rank above 21. `RatEllipticCurve` is a reduced-model structure, so distinct ranks
  give distinct elements. The docstring itself says the heuristic "contradicts" the classical
  belief.
- **Lean.** None found (no fc PR touches the file's open declarations for this, and GitHub search
  found nothing).
- **Catch.** This is a refutation edge between two open conjectures, so the theorem is
  `¬ unbounded_rank_conjecture` under the PPVW hypothesis, and the reverse. It has no
  mathematical content beyond the pigeonhole step.

### 2. `isMirimanoffPrime_iff` ⇒ ¬`exists_isWieferichPrime_and_isMirimanoffPrime` (S, unclaimed)
- **Statements** (`Wikipedia/WieferichMirimanoffPrime.lean`): `∀ p, IsMirimanoffPrime p ↔ p = 11 ∨
  p = 1006003` and `∃ p, IsWieferichPrime p ∧ IsMirimanoffPrime p`.
- **Deduction.** The same file already proves, as `category test`, that 11 and 1006003 are not
  Wieferich (`isMirimanoffPrime_and_not_isWieferichPrime_11/_1006003`). Recomputed here:
  `2^10 mod 121 = 56` and `2^1006002 mod 1006003² = 58755605216`, both `≠ 1`. The symmetric
  check, `isWieferichPrime_iff` ⇒ ¬both, also holds: `3^1092 mod 1093² = 341017` and
  `3^3510 mod 3511² = 24578`.
- **Catch.** It is a one-line corollary of tests already in the file, so its value is low.

### 3. Other contradictory pairs inside fc (S each, unclaimed, trivial)
- `Wikipedia/WieferichPrime.isWieferichPrime_iff` (only 1093 and 3511) ⇒ ¬`infinite_isWieferichPrime`.
- `Wikipedia/Fermat.fermat_number_are_composite` (`∀ n > 4`) ⇒ ¬`infinite_fermat_primes`.
- `OptimizationConstants/6a.c6a_eq_half` ⇒ ¬`c6a_upper_bound_improved` (`C6a < 1/2`).
- These are bookkeeping edges. Record them, but don't spend a project on them.

### 4. A92243: `conjecture2` ⇒ ¬`conjecture3` (Lean exists elsewhere, porting M)
- **Statements** (`OEIS/92243.lean`): the prime-gap "score" `a n = Σ_{k=2}^n sign(g_k − g_{k−1})`
  is bounded below (`conjecture2`) and bounded above (`conjecture3`).
- **Premise.** Epoch's accepted GPT-6 Astra submission `oeis_92243_conjecture`
  (`runs/oeis-open-lite-gpt6astra-…`, `Spec.lean`, 12,470 lines) refutes "bounded below and above".
  It uses Maynard's prime-tuples theorem, CRT covering congruences and the shifts `k!·3^j` to
  produce arbitrarily long runs of strictly increasing gaps. *(The summary is from their
  `metadata.json`; I did not read the 12k lines.)*
- **Catch.** It rules out the conjunction only, so neither fc statement is refuted on its own.
  Porting means matching their definitions of `primeGap` and the score to fc's, and the licence
  of the results repository was not checked.

### 5. A189409 `conjecture_1` is false: `29² ∣ a 9` (S, **taken**)
- **Statement.** `OEIS/189409.lean`: `∀ n, Squarefree (a n)` with
  `a n = (Nat.kthPrimorial n)^2 + 1` and `kthPrimorial k = ∏_{i<k} nth Prime i`.
- **Witness.** `kthPrimorial 9 = 223092870`, and
  `a 9 = 49770428644836901 = 29² · 59180057841661` (recomputed here). No `n ≤ 8` works.
- **Status.** It is still research open in fc, and no fc PR or issue touches the file. It is
  **already disproved in Lean** in two places. `s66lem/conjectures`
  (`results/campbell-oeis-a189409/`) cites `OeisA189409.conjecture_1` by name, proves the
  disproof, and proves minimality with Lucas certificates for `a(0..8)`. Epoch's
  `oeis_a189409_conjectures` disproves Tsoukalas's conjunction. My heuristic dismissal of this
  item earlier in the sweep was wrong: `Σ 2/(q log q)` is small, but `q = 29` is small too.
- **Catch.** Nothing is left for us beyond pointing fc at the existing proof.

### 6. A238281 `conjecture_2` is false at `n = 14` and `n = 286` (S, **taken**)
- **Statement.** `OEIS/238281.lean`: for `n > 1`, `n ≠ 8`, there is `0 < k < n` with `2k+1` prime and
  `π(kn) − π((k−1)n) = π((k+1)n) − π(kn)`.
- **Check.** For `n = 14`, `k` ranges over `{1, 2, 3, 5, 6, 8, 9, 11}` and the count pairs are
  `(6,3), (3,4), (4,3), (3,4), (4,2), (4,1), (1,4), (2,3)`, so no `k` works. The search for `n < 400`
  finds exactly `{14, 286}`. Because `kn` is composite there, open and half-open intervals give the
  same counts, so Sun's own OEIS wording fails too.
- **Status.** Taken: fc issue #8191, fc PR #8225, and Epoch `oeis_238281_conjecture_0`.

### 7. TxGraffiti Conjecture 3, `i(G) ≤ μ*(G)` for regular `G` (**taken**)
- `Arxiv/2507.17780/3.lean`. A 48-vertex cubic counterexample with `i = 16 > 15 ≥ μ*` is proved in
  Lean (fc PR #7661, issue #6737). Before I found that PR, my own random search covered about
  1.1M random `r`-regular graphs with `r = 3..7` and `n ≤ 22` and found nothing. That is consistent
  with the smallest known counterexample having 48 vertices.

## Negative searches (ranges covered, so nobody repeats them)

Every search below had a stated reason beforehand, a bounded range, and a cap of 2 CPU-hours. The
time is wall-clock on a box with load about 160.

| fc declaration | Why a counterexample was plausible | Range covered | Result | Time |
|---|---|---|---|---|
| `OeisA231830.conjecture` (`a(n)` squarefree, `a(n+1) = (a(n)−1)a(n)²+1`) | random-map heuristic for orbits mod `p²` | every prime `p ≡ 1 (4)`, `p ≤ 10⁸`: orbit mod `p` to find `p ∣ a(n)`, then test `p² ∣ a(n)` | 1,134 primes divide some term; **no `p²`** | ~4 min, `a231830.c` |
| `Arxiv.«2507.17780».tx_graffiti_conjecture_3` | tight on cycles and `K_{r,r}`, AI-generated | about 1.1M random `r`-regular graphs, `r = 3..7`, `n ≤ 22`, exact `i` and `μ*` | none (known counterexample has 48 vertices) | ~10 min, `txg3.c` |
| `OeisA224.conjecture` | composite pseudoprimes for `n² ≡ 1 mod a(a−1)` | `2 ≤ n ≤ 20000` | no mismatch | `misc1.py` |
| `OeisA135508.conjecture` | Rowland-type recurrence | primes `p < 20000` with `p−2` not prime | holds | `misc1.py` |
| `OeisA72200.conjecture` (`a 24 = 0`) | the claim rests on "no `k! < 10000!` has 24 sixes" | `k ≤ 3000` (beyond that the digit count makes 24 sixes impossible in practice) | no `k!` has exactly 24 sixes | `six.py` |
| `OeisA17666.conjecture` | Epoch's disproof of a neighbouring statement at `n = 18` | `n ≤ 2·10⁷`, Stewart's practicality test | none | `a17666.c` |
| `OeisA7406.conjecture` | Epoch witness `n = 4` (their wording) | `4 ≤ n < 3000` | holds | `ep_checks.py` |
| `OeisA2426.conjecture` (`n` prime ↔ `T(n) ≡ 1 mod n²`) | Wolstenholme-type pseudoprimes | `3 < n ≤ 6000`, exact `T(n)` | no mismatch | `t2426.py` |
| `OeisA229969` (all six variants) | Epoch witness `n = 7` (their wording) | `n < 3000` | all hold | `sun_checks.py` |
| `OeisA191004.conjecture_2/3` | Epoch witness `m = 10` (their wording) | `m < 4000` | both hold | `sun_checks.py` |
| `OeisA241898.conjecture_2` | Epoch witness `n = 736` (their wording) | `n < 20000` | holds (an fc PR also exists) | `sun_checks.py` |
| Seven "a(n) = 1 ↔ n ∈ singletons" Sun statements (A238568, A262781, A261627, A237720, A237578, A234246, A232194) | iff statements, boundary at `n = 0` | killed after 40 min with no output (sympy `primepi` too slow) | **not completed** | `iffcheck.py` |

## Rejected (also in the edges block)

- **Taken by an open fc PR, issue, or external Lean:** A189409, A238281, TxGraffiti 3, A261876
  `conjecture_3` (#8070), A108569, A105720, A114216, A108864, A114137, A120424 (#8210, and Epoch's
  "conj1 ⇒ ¬conj2"), A60841, A46969, A241898, A86766 `conjecture2` (s66lem, `n = 1010`), WOWII 61,
  72, 96 and 372, WOWII 84 (proved true by `lightninnng/graffiti84`), Kaplansky idempotent (#8213),
  Atiyah–Sutcliffe (#6966), Green 14 `W_3_29/30` (CCH23 colourings; #6754), Green 44 (#8125),
  Green 35, Monochromatic quantum graphs `N = 6` (#8283), and Barker, Kakeya and Flint Hills marked
  solved.
- **Epoch disproofs of Tsoukalas-only defects, which do not transfer to fc:** A7406 (`n = 4`),
  A17666 (`n = 18`; 18 is practical), A60841 (`n = 1807` gives a denominator that is not a power
  of 2; fc asks for denominator 1), A117545 (`n = 0`, excluded in fc), A1223 (no fc open
  statement), A179524 (free `x`), A179537 (`(7/p)` against `(p/7)`; fc uses `legendreSym 7 p`,
  which is `(p/7)`), A191004 (`q ≤ m/4`), A229969 (`x ≤ y ≤ z`), A232616 (a different
  sub-conjecture), A234360 (`(k+1)^{φ/2} − k`, a different statement), A262403 (index 0).
- **Route (d):** every lane file with a misformalisation flagged in the Epoch audit is either
  fixed by `9097e2f` (for the cases I checked) or concerns a declaration that is not research open.
  The re-reads that found no literal defect: Sierpiński (`n = 0` harmless for odd `k`),
  Firoozbakht (`1/(n+1)`), Cramér ratio (`n ≥ 4`), Skewes (principal-value `li` with `li(2)`),
  A41 (`¬IsPerfectPower 1`), Hyperperfect (`1 < n`), Agoh–Giuga (the Bernoulli form is equivalent
  to Agoh's congruence), A78680 (open because of the five unresolved Sierpiński `k < 65536`), and
  A108129 (open because of the unresolved Riesel `k`).
- **Route (a):** no lane statement contradicts RH or Dirichlet GRH. The RH-flavoured ones (Skewes
  no-crossover, Montgomery, Chebyshev bias) are consistent with RH.
- **Not attempted, with reason:** Equational 677 ⇒ 255 on finite magmas (the ETP has searched
  extensively, no SAT solver is installed, and the gain over their range is unknown);
  `W 3 21..28` (CCH23's local search improved only `t = 29, 30`, and no stronger solver is
  available here); WOWII 189 and 199 (Ham-path conclusions; no structured family found by hand,
  and `gustavobernardo1/conjectura` is scouting 199); McCranie's odd-`k` hyperperfect conjecture
  (would need search past McCranie's range, which I did not verify); Kourovka 20.51 (an existence
  question whose expected answer is yes); BMO 1, 5 and 8 (bbchallenge "cryptids", where
  simulation can only prove the statement, not refute it).
- **Cramér–Granville, Shanks, `limsup_eq_one`, `strict_bound` and Firoozbakht:** genuine X ⇒ ¬Y
  edges, but already recorded by lane `disproof-literature`. Not duplicated here.

## Not checked

- I did not read the Lean of Epoch's 12,470-line A92243 proof, the licence of
  `epoch-research/LeanOpenProblems-results`, or that of `s66lem/conjectures`.
- GitHub code search was run on about 20 namespaces only, not on all 601 files.
- The iff-singleton batch did not finish.

## Proposed edges

```jsonl
{"premise": "PPVW finiteness: {E : RatEllipticCurve | 21 < E.rank}.Finite", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT unbounded_rank_conjecture", "consequence_ref": "FormalConjectures/Wikipedia/EllipticCurveRank.lean unbounded_rank_conjecture (vs finite_twentyone_lt_finrank)", "consequence_status": "open", "implication_source": "evident: unbounded ranks give infinitely many distinct curves of rank > 21; docstring of finite_twentyone_lt_finrank notes the contradiction (PPVW 2016 §8.2)", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "refutation edge between two open fc statements; no new mathematics", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "isMirimanoffPrime_iff (only 11, 1006003)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT exists_isWieferichPrime_and_isMirimanoffPrime", "consequence_ref": "FormalConjectures/Wikipedia/WieferichMirimanoffPrime.lean", "consequence_status": "open", "implication_source": "file's own tests isMirimanoffPrime_and_not_isWieferichPrime_11/_1006003; recomputed 2^10 mod 121 = 56, 2^1006002 mod 1006003^2 = 58755605216", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "trivial corollary; symmetric edge via isWieferichPrime_iff: 3^1092 mod 1093^2 = 341017, 3^3510 mod 3511^2 = 24578", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "WieferichPrime.isWieferichPrime_iff (only 1093, 3511)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT infinite_isWieferichPrime", "consequence_ref": "FormalConjectures/Wikipedia/WieferichPrime.lean", "consequence_status": "open", "implication_source": "evident", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "bookkeeping edge", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "Fermat.fermat_number_are_composite (all n > 4)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT infinite_fermat_primes", "consequence_ref": "FormalConjectures/Wikipedia/Fermat.lean", "consequence_status": "open", "implication_source": "evident", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "bookkeeping edge", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "Frankl union-closed: C6a = 1/2 (c6a_eq_half)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT c6a_upper_bound_improved (C6a < 1/2)", "consequence_ref": "FormalConjectures/OptimizationConstants/6a.lean", "consequence_status": "open", "implication_source": "evident", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "bookkeeping edge", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "Maynard prime tuples (Lean, Epoch OEIS Open submission oeis_92243_conjecture)", "premise_status": "lean-proved", "premise_lean_source": "epoch-research/LeanOpenProblems-results runs/oeis-open-lite-gpt6astra-37ly1phzfwj2ech4/oeis_92243_conjecture/Submission/Spec.lean", "consequence": "NOT (OeisA92243.conjecture2 AND conjecture3): prime-gap score not bounded on both sides", "consequence_ref": "FormalConjectures/OEIS/92243.lean conjecture2, conjecture3", "consequence_status": "partially", "implication_source": "Epoch OEIS Open (Adamczewski 2026, arXiv:2608.11941) accepted proof; summary from metadata.json (unverified beyond summary)", "effort": "M", "lean_exists": "Epoch results repo (Tsoukalas statement, not fc's)", "in_1337": false, "class": 1, "notes": "refutes the conjunction only; porting needs matching definitions; licence unchecked", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "Computation: 29^2 divides 223092870^2 + 1", "premise_status": "lean-proved", "premise_lean_source": "s66lem/conjectures results/campbell-oeis-a189409 (Lean, with minimality)", "consequence": "OeisA189409.conjecture_1 (all a(n) squarefree) is false at n = 9", "consequence_ref": "FormalConjectures/OEIS/189409.lean conjecture_1", "consequence_status": "solved", "implication_source": "direct computation, recomputed in this sweep", "effort": "S", "lean_exists": "s66lem/conjectures; Epoch oeis_a189409_conjectures", "in_1337": false, "class": 1, "notes": "rejected: taken; fc still says research open, no fc PR or issue", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "Computation: no k works for n = 14 (and n = 286)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "OeisA238281.conjecture_2 is false", "consequence_ref": "FormalConjectures/OEIS/238281.lean conjecture_2", "consequence_status": "solved", "implication_source": "direct computation, recomputed in this sweep", "effort": "S", "lean_exists": "Epoch oeis_238281_conjecture_0", "in_1337": false, "class": 1, "notes": "rejected: taken (fc issue #8191, PR #8225)", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "48-vertex cubic graph with i = 16, mu* <= 15", "premise_status": "lean-proved", "premise_lean_source": "danielpuri1901/erdos-lean-formalization Solution.lean txgraffiti3_false", "consequence": "TxGraffiti conjecture 3 is false", "consequence_ref": "FormalConjectures/Arxiv/2507.17780/3.lean tx_graffiti_conjecture_3", "consequence_status": "solved", "implication_source": "ipitchford/txgraffiti-order48-successor", "effort": "S", "lean_exists": "fc PR #7661", "in_1337": false, "class": 1, "notes": "rejected: taken; own random search to n <= 22 found nothing", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "OeisA120424.conjecture1 (even-term density 1/2)", "premise_status": "open", "premise_lean_source": "", "consequence": "NOT OeisA120424.conjecture2", "consequence_ref": "FormalConjectures/OEIS/120424.lean", "consequence_status": "open", "implication_source": "Epoch OEIS Open accepted proof oeis_a120424_conjecture_0", "effort": "M", "lean_exists": "Epoch; fc PR #8210", "in_1337": false, "class": 2, "notes": "rejected: taken", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "Algebraic factorisation 10^(2(kr+1)) - 1 = (10^(kr+1) - 1)(10^(kr+1) + 1)", "premise_status": "lean-proved", "premise_lean_source": "s66lem/conjectures lean/Conjectures/FiroozbakhtA086766.lean", "consequence": "OeisA86766.conjecture2 is false (n = 1010)", "consequence_ref": "FormalConjectures/OEIS/86766.lean conjecture2", "consequence_status": "solved", "implication_source": "s66lem/conjectures results/firoozbakht-oeis-a086766", "effort": "S", "lean_exists": "s66lem/conjectures", "in_1337": false, "class": 1, "notes": "rejected: taken", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
{"premise": "Prime orbit computation mod p^2 for p <= 10^8", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to OeisA231830.conjecture (squarefree) from p <= 10^8", "consequence_ref": "FormalConjectures/OEIS/231830.lean conjecture", "consequence_status": "open", "implication_source": "this sweep, a231830.c", "effort": "XL", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search; heuristic expected count beyond 10^8 is tiny (sum p^-1.5)", "sweep": "2026-11-26", "lane": "disproof-fc-other"}
```
