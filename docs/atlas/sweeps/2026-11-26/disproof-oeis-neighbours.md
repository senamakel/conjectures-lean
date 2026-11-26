# Lane `disproof-oeis-neighbours`: counterexamples to open OEIS conjectures next to solved ones

Lane `disproof-oeis-neighbours`, 2026-11-26. Research and computation only. No Lean was written
and no existing file was edited. The inputs were two repositories, both cloned as untrusted data
into the session scratchpad (`hints-epoch/epoch`, `hints-epoch/s66`) and read with `python3 -I`:

- `epoch-research/LeanOpenProblems-results`, the "OEIS Open" runs (Adamczewski, arXiv:2608.11941):
  492 OEIS conjectures, 170 of them solved with accepted Lean;
- `s66lem/conjectures`: 32 result folders, six of them on OEIS (A189409, A086766, A108569, A308355,
  A400974, A402341).

The scripts are in `scratchpad/hints-epoch/{scripts,src}`. OEIS entries were fetched in text
format on 2026-11-26. Claims I could not confirm from a primary source are marked *(unverified)*.
The negative searches already recorded in `disproof-fc-other.md` (A231830, A224, A135508, A72200,
A17666, A7406, A2426, A229969, A191004, A241898) were not repeated.

## Result in one paragraph

**I found no counterexample that is both new and unclaimed.** The search found a genuine
counterexample to an open OEIS conjecture: A308656, Conjecture 2 (Zhi-Wei Sun, 2019), fails at
**n = 235644514** for f(x) = x(4x+1), and fails again at **n = 9974943843**. The first of these
is already published. `joeyhlu/sun-representation-counterexamples` was created on GitHub at
02:25 UTC on 2026-11-26, a few hours before this lane ran, and it contains the same witness,
the claim that it is the smallest, and a verifier. The second witness is not in that
repository, which scanned only to 3·10⁸, but it refutes a statement that is already refuted.
Everything else this lane ran came back negative. That covers 13 sibling statements in the same
Sun family that nobody has reported on, the A212496 normalised-sum inequalities to 10¹¹,
Ordowski's A000224 criterion to 10¹⁰, and others. Each range is listed in §5 so nobody repeats
it. The process lesson is in §6: **check prior art before spending compute, every time.**

## 1. The 61 Epoch disproofs: what found them

My regex (an accepted `Spec.lean` containing a proved `<id>.disproof`) gives 67 of the
170 accepted ids. The paper says 61. The gap comes from conjunctions such as A120424 and A92243
that are refuted only in part. Read through, the witnesses fall into seven recurring patterns:

| Pattern | Examples (Epoch id → witness) | Reduction that found it |
|---|---|---|
| P1 "a(n) = … iff n is prime", pseudoprime failure | A309391 and A64169 → 16843² (Wolstenholme prime squared); A340079 → 3·37·43·42307·116341 (squarefree, ∏(2p−1)+1 = 26n); A335023 → 1194648; A296075 → 2¹⁴·4409·458009 | Factorisation shape: squares of the special primes (Wolstenholme, Wieferich), or a product of primes with p−1 dividing a fixed number (a Carmichael/Lehmer-type construction) |
| P2 Sun "a(n) > 0 / a(n) = 1 iff n in a finite list" over sparse sets | A157225 → 716993899; A306477 (2-4-6-8) → beyond Baruch's 2·10¹², found by a modular sieve; A261876 → 69383; A263001 → 51156; A232616 → 550172; A238281 → 14, 286; A241898 → 736; A234360 → 1408 | The author checked only to N (often 10⁶ to 1.5·10⁸) and the representation count grows only like log n or a power of log n. Exhaustive bitset scans 10 to 100 times past N |
| P3 local obstruction | A303639 (a prime p ≡ 3 mod 4 divides exactly once); A363102 (3 ∤ n²−2); A070823 (13² ∣ a(20)); A189409 (29² ∣ a(9)); A078590 (19) | Congruence or valuation argument on a fixed small prime |
| P4 algebraic factorisation / structural family | A084046 (j²⁷ − 27 = (j⁹−3)(…)); A093456, A374265, A010846 (infinite families by construction) | Polynomial identity or a digit-sum or prime-block argument |
| P5 p-adic supercongruence at small p or large r | A357958 (p = 3), A361713 (p = 7, r = 6), A129365 (p = 2), A179537, A179524, A336982 (small p) | Direct evaluation at the smallest admissible primes |
| P6 recurrence or closed form fails late | A190363 → n = 144 (161·√(5/4) just above an integer, a convergent of √5); A355898; A284852; A049473; A248802 → n = 51 | Continued-fraction convergents of the irrational that defines the Beatty-type sequence |
| P7 edge index or misformalisation | A7406 (n = 4), A72780 (n = 0), A262403 (index 0), A383327, `a_n_is_defined_for_all_n` (n = 0), A17666, A60841 | Tsoukalas-wording defects; the scout lane showed that most do not transfer to fc |

P1, P2 and P6 are the only patterns that produce "a counterexample a named author would
recognise". P2 is the richest. Its failures cluster in Sun's 2009 and 2018–2019 families, where
the verification bound printed in the OEIS is 10⁶ to 1.5·10⁸.

## 2. Target pool

There are 322 unsolved Epoch conjectures: Sun 144, Bala 30 (supercongruences), Ordowski 15,
Ratushnyak 7, Hasler 6, then a long tail. To them I added the OEIS "Conjecture" comments in the
same entries and in the cross-referenced entries outside the 492. The OEIS text of all 444
A-numbers in the 492 was fetched and grepped for "verified" bounds and for later refutations.

Already refuted, so dropped (OEIS comments, not counted as ours):
- A071532: positivity is false at a(331523) (Schlesinger, 2026-09-09, with Lean).
- A067857: Schlesinger's counterexample repository.
- A308656, Conjecture 1: a(2109982225) = 0 (Jiao-Min Lin, 2022).
- A352286, Conjecture 2: a(8710) = 1 and others (Scott Moore, 2026-05-21).
- A308640, Conjecture 1: a(1764630) = 0 (Moore, 2026-05-21).
- A308403, Conjecture 2: Resta's 4551086841.
- A157225: Adamczewski at 716993899. Sun's 2009 post already credits McNeil with 1433987797,
  as joeyhlu's README points out.

## 3. Shortlist and reduction chains

Each entry gives the plausibility argument, the space, and the stop condition, written before
the run. "Remainder" is what the code actually tests.

1. **A308656 Conj. 2–4, A308640 Conj. 2–3, A308641 Conj. 1–3, A308644 Conj. 1–2, A308662
   Conj. 1–2 (Sun, June 2019).** Statement: every n > 0 is s + F(c) + G(d), where
   s = (p^a q^b)² and F, G are binary quadratic polynomials.
   - *Plausibility (pattern P2):* the same entry's Conjecture 1 failed at 2.1·10⁹ when it had been
     verified to 10⁸, and siblings failed at 1.76·10⁶ and 7.65·10⁶. The OEIS verification for
     Conjectures 2–4 is only 10⁶.
   - *Heuristic:* about 0.33·log²n values of s. 48m+5 = 3X² + 2Y² is a one-class genus, so each
     m = n − s is represented iff no prime with (−6/q) = −1 divides it to an odd power, which has
     probability about c/√log m. The draws are strongly correlated through n mod small primes, so
     zeros occur at a rate of roughly one per 10⁹.
   - *Chain:* the raw space is n ∈ [1, X]. The s-terms with s ≤ 2²⁶ are covered by bitset
     shift-OR on a table of F(c)+G(d) built per 2²⁸ block. The survivors (about 0) get the full
     s list with an exact quadratic-residue test.
   - *Stop:* 10¹⁰ per form, or about 0.3 CPU-h per form.
2. **A157237 (Sun 2009) and A157218 (outside the 492).** Odd N = p + 2^x + c·2^y with p in a
   class mod 6. Pattern P2, sibling of A157225, which failed at 7.2·10⁸ after verification to
   1.5·10⁸. Chain: odd N, then a bitset of primes in the class, shifted by s/2 for
   s = 2^x + c·2^y ≤ 2²⁶, then Miller–Rabin for the rest. Stop at N = 10¹¹.
3. **A212496 (Sun 2012).** b(n) = Σ_{k≤n} (−1)^{k−Ω(k)}/k. Sun conjectured b(n) < −1/√n for
   n > 1 and b(n) > −log log n/√n for n > 2008 (the pool item), and, in the same entry,
   a(n) > √n for n > 324 and a(n) < √n·log log n for n > 5892.
   - *Plausibility (a Pólya/Turán first-sign-change shape):* the Dirichlet series is
     −(1 + 2^{1−s})ζ(2s)/ζ(s). Its pole at s = 1/2 gives √n·b(n) ≈ −(1+√2)/ζ(1/2) ≈ −1.653 plus
     oscillating zero terms, and a(n)/√n ≈ +1.653 plus oscillation. Both bounds sit at distance
     0.653 from the mean, comparable to Turán's 0.684, which first failed at 7·10¹⁰. Below 10⁸
     the extremes were already −1.024 and 1.053.
   - *Chain:* segmented Ω sieve over n ≤ X with Kahan-summed long double, in two passes: block
     totals, then per-block bounds, exact where a block is ambiguous.
   - *Stop:* X = 10¹¹, about 1.5 CPU-h.
4. **A000224 (Ordowski 2025).** n² ≡ 1 (mod a(n)(a(n)−1)) iff n is an odd prime. Marcus checked
   to 10⁸. Plausibility is weak: for composite n the condition becomes a Diophantine equation
   in the prime factors, with k = (n²−1)/(a(a−1)) bounded by about 4^ω. Chain: a multiplicative
   sieve for a(n), a u128 test, and a comparison with primality. Stop at 10¹⁰.
5. **A245211 / A245212 (Krizek).** Σ_{d|n} dτ(d) = n(τ(n)+1) only for n = 21, and
   2nτ(n) − Σ dτ(d) = σ(n) only for powers of 2. Both are multiplicative-ratio Diophantine
   equations; for squarefree n the first reads ∏(1 + 1/(2p)) = 1 + 2^{−k}. Chain: a
   multiplicative sieve to 10¹⁰. *(A DFS over factorisation shapes was started and abandoned:
   too slow in Python.)*
6. **A321576 (Ordowski).** a(n) = 2 iff n is prime, where a(n) = 2 means every divisor of 2ⁿ−1 is
   ≡ 1 (mod n).
   - *Reduction:* the product of the factors of M_p is M_p, so 2^p ≡ 2 (mod n) for every prime
     p ∣ n. Then ord_r(2) ∣ p − 1 for all r, p ∣ n, so n is a base-2 pseudoprime.
   - For n = p² this needs a Wieferich prime, but 43721 ∣ M₁₀₉₃ with 43721 ≢ 1 (mod 1093²), and
     35111 ∣ M₃₅₁₁ with 35111 ≢ 1 (mod 3511²). Both prime-square candidates die.
   - The squarefree case needs every prime factor of M_p to be ≡ 1 (mod n) for each p ∣ n. A
     pair p < r forces r ∣ q − 1 for every q ∣ M_p.
   - *Dropped:* the remainder is a search over base-2 pseudoprimes (Feitsma's list), which was
     not downloaded. Plausibility is low.

Dropped without a run, with the reason:
- A331343 and A108866 (Ordowski/Eldar): Epoch's own failed agents reduce both to "no
  super-Wolstenholme prime" (v_p ≥ 6, resp. ≥ 5), which is unreachable.
- A2326 (needs 2^{p−1} ≡ 1 mod p³).
- A51903 (reduces to Lehmer's totient problem).
- A7918 c1 and A40 c5 (Cramér-strength gap bounds; the largest known g/log²p is 0.92).
- A34694 and A53000 (least prime in a progression, or after n², against n² or φ(n): off by
  orders of magnitude).
- A38098 (fluctuations can win only for n < 30).
- A308950: Resta verified it to 10¹¹, and its expected count is about 45 at 10¹⁰.
- A157242: McNeil 10¹³, and joeyhlu found 107576474238337 (taken).
- The Bala supercongruences (30): each needs its own sequence code, Epoch agents had them with
  computation, and the two that failed (P5) failed at the smallest p. Not attempted.

## 4. Hits

### A308656, Conjecture 2 with f(x) = x(4x+1): false at n = 235644514 — **taken, not ours**

- **OEIS wording** (A308656, Zhi-Wei Sun, entry of 2019-06-14 per Epoch metadata): "Conjecture 2:
  If f(x) is one of the polynomials x*(4x+1), x*(5x+2), x*(5x+4), x*(7x+3)/2 and x(7x+5)/2, then
  any positive integer n can be written as (2^a*9^b)^2 + f(c) + d*(3d+1)/2, where a and b are
  nonnegative integers, and c and d are integers." The verification printed is 10⁶.
- **Witness.** n = 235644514 = 2·7·17·101·9803. There are 40 values s = (2^a 9^b)² ≤ n and
  |c| ≤ 7676; for every pair, n − s − c(4c+1) is not a generalised pentagonal number.
  A second counterexample, **9974943843**, is the only other one in (3·10⁸, 10¹⁰).
- **Verification 1.** `src/sun3.c` (bitset table of F(c)+G(d), shift-OR over s ≤ 2²⁶, exact
  test for the rest) reports exactly these two in [1, 10¹⁰). The same program reproduces Lin's
  A308656 Conj. 1 counterexample 2109982225, Moore's A308640 Conj. 1 counterexample 1764630 and
  joeyhlu's A308644 counterexamples 7654105 and 108011768, which validates it.
- **Verification 2.** `scripts/verify308656.py`: pure Python with exact integers, enumerating
  every (s, c) and testing 24r+1 = z², z ≡ ±1 (mod 6). It gives 0 representations for both
  witnesses and positive counts for the other four polynomials (25, 69, 36, 41 at 235644514).
  `src/brute2a.c` (direct per-n enumeration, a different code path) rechecks minimality over
  [1, 235644514]: PENDING.
- **Prior art: TAKEN.**
  - `joeyhlu/sun-representation-counterexamples` (created 2026-11-26 02:25 UTC, pushed
    09:18 UTC) lists A308656 Conj. 2 (f = x(4x+1)) → 235644514 as the smallest, from an
    exhaustive `direct_scan` to 3·10⁸, with `verify.py`.
  - The same repository also has A157242 → 107576474238337 and A157237 exhaustive to 10¹³
    (targeted to 4.5·10¹⁸), A308644 Conj. 1 and 2 (r = 3), A302982, A302984 and A303932.
  - The OEIS entry, the Epoch runs (4 failed attempts on `oeis_308656_conjecture_2`), s66lem,
    fc (no `OEIS/308656.lean` on `main`), GitHub code search and web search show nothing else.
- **Formalisation note.** Epoch's Lean statement `oeis_308656_conjecture_2` is
  `∀ n > 0, ∃ f ∈ F, ∃ a b c d, n = …`: "some f" instead of Sun's "each f". It is weaker than
  the OEIS conjecture, and the witness does **not** refute it, since the other four polynomials
  represent both witnesses. This is a route-(d) wording defect worth reporting to Epoch, not a
  disproof.
- **Lean route (if wanted).** It is a finite check: 40 × 15353 pairs, each "24r+1 is not a
  square ≡ ±1 mod 6" via `Nat.sqrt`. Use `native_decide` with a soundness lemma for the
  pentagonal test, or kernel `decide` on chunks as joeyhlu did for A157242.

## 5. Every search, with range and cost

CPU time is wall time × processes on a box with load 160–200. All ranges are inclusive of
their start and exclusive of their end.

| Statement | Why plausible | Range covered | Result | Cost |
|---|---|---|---|---|
| A157237 (Sun 2009; k = 11, p ≡ 1 mod 6) | sibling of A157225 | odd N < 10¹¹ | only Sun's 22 small exceptions. Subsumed by joeyhlu (10¹³) | ~0.4 CPU-h, `p2c.c` |
| A157218 (k = 7, p ≡ 1 mod 6; outside the 492) | as above | odd N < 10¹¹ | only Sun's 13. Subsumed: joeyhlu cites McNeil's 445466268731 | ~0.4 CPU-h |
| A157225 (validation) | Epoch witness | odd N < 2·10⁸ and [1.3·10⁹, 1.6·10⁹) | Sun's list, plus 1433987797 (= Epoch's n = 716993899) | 10 CPU-s |
| A308656 Conj. 2, f = x(4x+1) | P2, 10⁶ verified | n < 10¹⁰ | **235644514, 9974943843** (taken) | ~0.25 CPU-h |
| A308656 Conj. 2, f = x(5x+2), x(5x+4), x(7x+3)/2, x(7x+5)/2 | same | n < 10¹⁰ each | none | ~1 CPU-h |
| A308656 Conj. 3 (q = 7; c(2c+1) + d(3d+r), r = 1, 2) | same | n < 4·10⁹ each | none | ~0.2 CPU-h |
| A308656 Conj. 4 (q = 7; five g(c) + d(3d+1)/2) | same | n < 4·10⁹ each | none | ~0.5 CPU-h |
| A308640 Conj. 2 (k = 1, 2; c ≥ 0) | same entry's Conj. 1 failed at 1.76·10⁶ | n ≤ 10¹⁰ each | none | ~0.5 CPU-h, `sun4.c` |
| A308640 Conj. 3 (k = ±1; c ≥ 0) | same | n ≤ 10¹⁰ each | none | ~0.5 CPU-h |
| A308641 Conj. 1, Conj. 2 (five f), Conj. 3 | sibling, no verification bound printed | n ≤ 10¹⁰ each (7 forms) | none | ~1.8 CPU-h |
| A308644 Conj. 1 first assertion, Conj. 2 r = 1 | siblings of joeyhlu's two | n ≤ 10¹⁰ each | none (joeyhlu: first assertion none to 3·10⁸) | ~0.5 CPU-h |
| A308662 Conj. 1, Conj. 2 (r = 1, 2) | sibling, 10⁸ verified | n ≤ 10¹⁰ each | none | ~0.8 CPU-h |
| A212496 b-inequalities (pool) and the a-inequalities (same entry) | Turán-type bias 0.653 | n ≤ 10¹¹ | all hold. Closest: √n·b(n) = −1.0237 at 17593752 (exact); a(n)/√n ≥ 1.046 (block bound, ~1.2·10⁸); min (√n b + log log n) = 0.003 at n = 2009; max a/(√n log log n) = 0.995 at n = 5893 | ~1.5 CPU-h, `liou.c`, `liouex.c` |
| A000224 (Ordowski) | Diophantine, extend Marcus's 10⁸ | 2 ≤ n < 10¹⁰ | no composite n satisfies it; every odd prime does | ~0.4 CPU-h, `sq224.c` |
| A245211 / A245212 (Krizek) | multiplicative Diophantine | 2 ≤ n ≤ 10¹⁰ | only n = 21; no non-power of 2 for A245212 | ~0.3 CPU-h, `kriz.c` |
| A321576 (Ordowski) at n = 1093², 3511² | Wieferich reduction | the two known Wieferich primes | both fail (43721, 35111) | seconds |

The A212496 extremes look stationary on a log scale over 10⁵–10¹¹: max √n·b oscillates between
−1.02 and −1.26, and min a/√n between 1.04 and 1.20. A crossing needs a rarer alignment of
zeros, plausibly far beyond 10¹² *(heuristic)*. I stopped at the cap.

## 5a. Against the owner's bar (a "real" hit)

A hit counts only if the author tested the statement, reported a range, and the witness lies
beyond that range and needed structure to find.

- A308656 Conj. 2 meets that bar. Sun verified it to 10⁶; the witness is at 2.4·10⁸ and needed
  an exhaustive bitset scan. It is **taken**.
- The 15 sibling statements and A157237/A157218 are the same kind of real target, and all are
  negative to the ranges in §5.
- A212496, A000224 and A245211/2 are author-tested too, and negative.
- Nothing in this lane was a typo-level or first-small-case failure. The Epoch P7 class
  (edge-index defects) was not pursued.

## 6. Process lesson

The A308656 witness came from a search started on the strength of the OEIS text alone. The
prior-art search came afterwards and found joeyhlu's repository from the same morning, which
had worked over exactly this family (Sun's 2018–2019 sparse-sum conjectures). Lanes mining OEIS
"verified to 10⁶" conjectures should run `gh search repos/code <A-number>` and read the
repository's README *before* the first CPU-hour. Families mined within days: Sun's sparse
representation conjectures (joeyhlu, Scott Moore 2026-05, Lin 2022), and Epoch OEIS Open
(De Vlieger annotates the OEIS entries).

## 7. Best unfinished lead

The 15 sibling statements nobody had reported on all hold to 10¹⁰ (A308656 Conj. 3 and 4 hold
to 4·10⁹): A308640 Conj. 2–3, A308641 Conj. 1–3, A308644 Conj. 1 (first assertion) and Conj. 2
(r = 1), and A308662 Conj. 1–2. Counterexamples in this family have so far appeared between
1.7·10⁶ and 10¹⁰: 1764630, 7654105, 108011768, 235644514, 2109982225 and 9974943843. Going
further with exhaustive scans costs about 0.1 CPU-h per form per 10⁹.

The better next step is joeyhlu's targeted method, ported to these forms. Rank the classes of
n modulo a product of small primes by how many n − s are locally obstructed. For the
d(3d+1)/2 forms, the obstruction is 48m+5 or 24m+1 having a prime q with (−6/q) = −1 to an odd
power. Then scan only the best classes, from 10¹⁰ to 10¹⁴. Effort: M, about one day of code
plus 5 CPU-h. joeyhlu is evidently active on this family, so look at their repository again
before starting.

## Proposed edges

```jsonl
{"premise": "Computation: 235644514 not of the form (2^a 9^b)^2 + c(4c+1) + d(3d+1)/2", "premise_status": "theorem", "premise_lean_source": "", "consequence": "OEIS A308656 Conjecture 2 (f = x(4x+1)) is false", "consequence_ref": "OEIS A308656 (Sun 2019); Epoch oeis_308656_conjecture_2 is weaker (exists f) and NOT refuted", "consequence_status": "solved", "implication_source": "this lane (sun3.c + verify308656.py); first published by joeyhlu/sun-representation-counterexamples 2026-11-26", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "rejected: taken (joeyhlu, smallest, verify.py); second witness 9974943843 found here; Epoch statement misformalised as exists-f", "sweep": "2026-11-26", "lane": "disproof-oeis-neighbours"}
{"premise": "Exhaustive scan odd N < 1e11", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no new exception to A157237 / A157218 below 1e11", "consequence_ref": "OEIS A157237 (Epoch oeis_A157237_sun_conjecture), A157218", "consequence_status": "open", "implication_source": "this lane, p2c.c", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative; subsumed by joeyhlu exhaustive 1e13 and targeted 4.5e18", "sweep": "2026-11-26", "lane": "disproof-oeis-neighbours"}
{"premise": "Segmented Liouville-type sieve n <= 1e11", "premise_status": "theorem", "premise_lean_source": "", "consequence": "A212496 b(n) < -1/sqrt n, b(n) > -loglog n/sqrt n, sqrt n < a(n) < sqrt n loglog n hold for n <= 1e11", "consequence_ref": "OEIS A212496 (Epoch oeis_212496_conjecture_1)", "consequence_status": "open", "implication_source": "this lane, liou.c/liouex.c; mean -(1+sqrt2)/zeta(1/2) = -1.653", "effort": "M", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative; near misses -1.0237 at 17593752 and a/sqrt n 1.046", "sweep": "2026-11-26", "lane": "disproof-oeis-neighbours"}
```
