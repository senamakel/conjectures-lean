# Lane `disproof-sun-family`: Sun's sparse-term representation conjectures

Lane `disproof-sun-family`, 2026-11-26. Research and computation only. No Lean was written and
no existing file was edited. Downloaded data (OEIS text, the joeyhlu and other GitHub
repositories) went into their own directories under the session scratchpad
`scratchpad/hunt-sun/dl/` and was read only with `python3 -I`. The programs are in
`scratchpad/hunt-sun/{src,py}`, the run logs in `scratchpad/hunt-sun/runs`. This lane continues
[`disproof-oeis-neighbours.md`](disproof-oeis-neighbours.md) and does not repeat its ranges.

## Result in one paragraph

**Hit: OEIS A301534 (Zhi-Wei Sun, 16 April 2018) is false.** Sun conjectured that every prime
p > 7 with p ≡ 7 (mod 12) is x² + 3y² + 15·2^z with x, y, z ≥ 0, and verified it for
7 < p < 8·10⁹. **The prime p = 28662666283 has no such representation.** It is the smallest
counterexample: every prime p ≡ 7 (mod 12) below it was tested. There are six counterexamples
below 10¹¹: 28662666283, 34777306483, 43394007823, 44172408919, 46796931343, 61044565927.
The model predicted this before the scan: A301534 was the only statement in the pool whose
near-miss counts grow from octave to octave, and the predicted rate was about one exception
per octave just above Sun's bound. **Prior art, as of 12:28 UTC on 2026-11-26: none found.**
The OEIS entry is unchanged since its creation (revision #22, 16 April 2018). joeyhlu's
repository does not mention A301534. A search of GitHub code, repositories and issues, of
OEIS full text and of the web for "A301534" and "28662666283" finds nothing. A second check
was made just before this report was written (see §6.4). The witness has not been checked in
Lean (this lane writes no Lean). Under AGENTS.md it is therefore a script-verified witness, and
it becomes a result only once Lean has checked it (§6.5). Every other statement in the pool is
negative over the ranges in §5.

## 0. Prior art, checked before any computation (step 0)

Checked 11:53–12:05 UTC and again at 12:28 UTC.

- **joeyhlu/sun-representation-counterexamples**, cloned at 11:53 UTC. The last commit is
  `22d8e9e` (04:18 −0500 = 09:18 UTC). It claims eight statements:
  - A157242 → 107576474238337;
  - A302984 → 4375339279 (18 counterexamples below 10¹¹, all ≡ 79 mod 80);
  - A302982 → 558556427;
  - A303932 Conj. 1 → 257558146370 and Conj. 2 → 68211369278;
  - A308644 Conj. 2 (r = 3) → 7654105, and Conj. 1 second assertion → 108011768;
  - A308656 Conj. 2 (f = x(4x+1)) → 235644514.

  Its exhaustive ranges are A157242 and A157237 to 10¹³ (A157237 targeted to 4.5·10¹⁸),
  A302984 to 10¹¹, A302982 to 10⁹, A303932 to 10¹², and the 2019 forms to 3·10⁸. Its targeted
  method (`suntarget2.c`, for p + 2^x + k·2^y) ranks the classes mod 9699690 by surviving
  candidates and tests the best N exactly. It says nothing on A301534, A302983, A3033xx,
  A3085xx–A3086xx other than A308644/A308656, or A308661.
- **Other public work on this family** (found by `gh search repos/code` and web search):
  - DCLXAI/a303639-counterexample: A303639, binomial terms, n = 800322180, Aug 2026.
  - Samsen879/a303656: A303656, a² + b² + 3^c + 5^d, verified to 2.416·10¹¹, open.
  - darkness-38/counter-hunter: CRT "sniper" streams on prime + sparse statements, no hits.
  - yotam1001/sun-a157218-counterexample: McNeil's 445466268731.
  - EgorcaA/sun-conjectures-counterexamples: the π(x) statements A263107, A263020, A262995.
  - F8Labs-ai/sun_conjectures: prime conjectures.
  - derekblair/math-proofs: lists A308621/A308623 as "deep open", with no computation.
  - The OEIS comments themselves: Lin (A303338 at 12558941213, A303637 at 18836421387,
    A308656 Conj. 1 at 2109982225, A303656 verified to 2.4·10¹¹, A303540 to 10¹¹, A308734 to
    1.6·10¹¹); Moore (A308640 Conj. 1 at 1764630, May 2026); Resta (A308621, A308623 to 10¹⁰,
    A308661 Conj. 1 to n < 8.33·10⁹, A308411 and A308403 to 10¹⁰, A308950 to 10¹¹);
    McCranie (A303821 to 2.5·10¹²); Hou (A280356 and A300510 to 10⁹).

  None of these covers A301534. A301534 is not in google-deepmind/formal-conjectures
  (`FormalConjectures/OEIS` has 300997, 303639, 303656, 306424, 306477, 307865, 308734 and
  309132 in this range), nor in the Epoch OEIS Open index.
- **Decision.** The pool excludes every statement listed above as refuted or scanned, and adds
  statements nobody lists: Sun's other 2018–2019 entries with one or two sparse terms.

## 1. Pool

For each statement: the sparse set S, the base form Q, and the range Sun or the OEIS states.
The variables are as in the OEIS. "r(n)" is the number of distinct sparse values s ≤ n with
n − s ∈ Q. The conjecture says r(n) > 0.

| Statement | n = s + q with | Base form Q, exact membership test | Stated range |
|---|---|---|---|
| **A301534** | p prime ≡ 7 (12), s = 15·2^z | x² + 3y² (x, y ≥ 0): every prime ≡ 2 (mod 3), 2 included, to even power | p < 8·10⁹ (Sun) |
| A302983 (= A302985) | 2^z + 3·2^w | x² + 2y²: primes ≡ 5, 7 (8) to even power | 6·10⁹ |
| A303233 / A303363 | 2^c + 2^d (c ≤ d; A303363: c even) | T(a) + T(b): 4m+1 is a sum of two squares | 10⁹ |
| A303389 (= A303399) | 5^c + 5^d | T + T | 10¹⁰ |
| A303401 | 3^c + 3^d | a(3a−1)/2 + b(3b−1)/2, a, b ≥ 0 (generic test) | 7·10⁶ |
| A303428 and its "Moreover" | 3^u + 3^v | x(3x−2) + y(3y−2), x, y ∈ Z; x(3x+2) + y(3y+2), y ≥ 0 | 3·10⁸ |
| A303432 Conj. 1, 2, 3 | 2^c + 2^d | hexagonal a(2a∓1) + b(2b∓1), a, b ≥ 0 | 2·10⁶ |
| A303543 | C(k) + C(m), Catalan, 0 < k ≤ m | a² + b² | 10⁹ |
| A303601 | Bell(k) + Bell(m), 0 < k ≤ m | T + T | 7·10⁸ |
| A308566 | 4^y·5^z | w² + x(x+1) (= T + T) | 5·10⁸ |
| A308584 | 5^c·8^d | T + T | 4·10⁸ |
| A308621 | 2^c·5^(3d) | T + T | 10¹⁰ (Resta) |
| A308623 | 2^c·10^(2d) | T + T | 10¹⁰ (Resta) |
| A308661 Conj. 1 | 3n+1 = T + T + (2^c 5^d)² | T + T on the class 1 (mod 3) | n < 8.33·10⁹ (Resta) |
| A308661 Conj. 2 | 24n+10 = a² + b² + (2^c 3^d)², d > 0 | a² + b² on the class 10 (mod 24) | n ≤ 10⁸ |
| *Calibration only* | A302984, A303338, A303637 (refuted); A308621 with 250^d (Resta: 7272774228), T + T + 2^c 3^d (Resta: 729546026), two octagonal + 2^c + 2^d (Sun: 76683391 least), a² + b² + two Bell (Sun: 111277) | | |

Considered and dropped without a scan:
- A308934 Conj. 1–2 (two squared sparse terms, about 5000 pairs below 10¹⁰): far too many
  representations.
- A302920 (p² = x² + 2y² + 3·2^z for primes p): plausible, since A301471 fails at the
  composite 5884015571, but each test factors a number near 10²⁰ (§7).
- A300510 and A301452 (n² as 4^k·m + a binary form, Hou to 10⁹ and Sun to 5·10⁷): the same
  factoring cost.
- A280356 and A280153 (cubes and fourth powers, so not a binary form).
- The prime-term statements (A303702, A303821, A304081 and others): not this family.

## 2. Model and calibration

**Program.** `src/hs.c` and `hs2.c`/`hs3.c` are generic exhaustive scanners. For a block of n,
they build a bitset of Q over [L − 2^24, L + 2^26) by enumerating (c, d). They OR-shift it by
every s ≤ 2^24 into bit-sliced saturating counters, which hold r_small(n) up to K. For every n
with r_small < K they add the larger s, using the exact test (factor-based for the class-number
one forms, or a direct loop for the generic ones). They write a per-octave histogram of r ∈
{0, …, K−1} and every n with r ≤ 1 or 2. Validation: the scanner reproduces every published
failure it was pointed at:
- 4375339279 (A302984), 12558941213 (A303338) and 18836421387 (A303637);
- Resta's 7272774228 (250^d) and 729546026 (2^c 3^d);
- Sun's 76683391 (least, octagonal) and 111277 (least, Bell);
- for A301534, the r value of every prime ≡ 7 (12) below 2·10⁵, compared with a brute-force
  enumeration (0 mismatches).

**Near-miss estimator (the model used for ranking).** N_k(o) is the number of n in
[2^o, 2^(o+1)) with r(n) = k. In every statement here the low tail is close to geometric:
N_(k+1)/N_k ≈ q, constant for k = 1, 2, 3. The base level N_2 + N_3 is fitted log-linearly in
o, and the prediction is N_0(o) = (N_2 + N_3)(o) / (q² + q³). This is the empirical form of
X·E[exp(−R(n)·w(n))]: the factor q carries the local (class) variation, and the octave growth
carries how R grows with n. Calibration against the known failures:

| Calibration statement | Predicted N₀ | Observed |
|---|---|---|
| A302984 | 6.4 in octaves 22–31; 12 per octave at 2³³, growing ×1.9 per octave | 0 below 2³²; then 3, 2, 4, 4 in octaves 32–35 (joeyhlu's list) |
| A303338 | 4.2 in octaves 22–31; 4.8 per octave at 2³³ | 0 below 2³²; Lin's first at 1.26·10¹⁰ (octave 33) |
| A303637 | 0.03 per octave at 2³³ | Lin's first at 1.88·10¹⁰ (octave 34) |
| 250^d variant | 0.3 per octave at 2³² | 1 in octave 32 (7272774228) |
| 2^c 3^d variant | 0.5 in octaves 22–31 | 1 (729546026, octave 29) |

The estimator is good to a factor of about 3–10 in either direction. It overestimates growing
families and underestimates the flat ones. That is enough to rank, not to promise.

**Local census (the reduction chain).** `src/model.c` enumerates the classes a mod M, with M a
product of prime powers q^e (e ≥ 2 for odd q, so that a single factor q is visible). For each
class it counts U(a), the number of s that are not locally blocked. Blocked means
v_q(Am + B) is odd and below e, or the odd part is in a forbidden class mod 4 or 8. It then
fits r ~ NegBin(κU/√ln X, θ) to the near-miss histogram. For A308621 and A308623 (T + T, so the
test is on 4m+1), with M = 3³·7²·11²·31² ≈ 1.5·10⁸, the predicted exceptions concentrate only
weakly: 2.7% of the classes carry 89% of the mass for A308621, and 7% carry 88% for A308623.
A per-class sieve costs about 10 ns for each pair (n, unblocked s), against 21 ns per n for
the exhaustive bitset. With U ≈ 55 unblocked s per class, the targeted scan saves at most a
factor of about 4 and covers about 89%. **So for these statements I used the exhaustive
bitset, not a targeted scan.** The class census is recorded here so the comparison need not
be repeated. For A301534 the exhaustive scan restricted to primes costs only
0.42 CPU-s per 10⁹, so no targeting was needed either.

## 3. Expected exceptions in (2^33, 2^44) ≈ (8.6·10⁹, 1.8·10¹³)

From the near-miss estimator (fit window: octaves 22–31; for A301534, 24–32). N₁–N₃ are the
counts of n with r = 1, 2, 3 in the window. "None" means that no n above 2^22 has r ≤ 3,
which puts the expectation far below 0.1.

| Statement | N₁ / N₂ / N₃ in window | Growth per octave | Expected exceptions in (2³³, 2⁴⁴) | Decision |
|---|---|---|---|---|
| **A301534** | 12 / 226 / 2210 | ×1.58 | **≈ 300 (1.2 per octave at 2³³)** | scan first; **hit** |
| A308623 | 5 / 51 / 547 | ×0.99 | 0.45 (0.04 per octave) | exhaustive scan |
| A308621 | 3 / 26 / 239 | ×1.01 | 0.39 (0.035 per octave) | exhaustive scan |
| A303543 | 0 / 1 / 4 | ×0.94 | 0.07 | dropped (≪ 0.1 once the bias is allowed for) |
| A308661 Conj. 1 | 1 / 9 / 130 | ×0.99 | 0.05 | dropped |
| A308584 | 0 / 31 / 228 | ×0.82 | 0.05 | dropped (scanned to 10¹⁰ anyway) |
| A308661 Conj. 2 | 0 / 0 / 2 | ×0.95 | 0.03 | dropped |
| A303428 "Moreover" | 0 / 8 / 94 | ×0.89 | 0.02 | dropped |
| A308566 | 0 / 0 / 4 | ×0.91 | 0.003 | dropped |
| A302983 | none above 2³ | – | ≪ 0.1 | dropped. Unlike 5·2^w in A302984, 3·2^w meets no bad prime of x² + 2y² (3 is good), so no class loses its sparse terms |
| A303233, A303363, A303601, A303432 Conj. 3 | none above 2³ | – | ≪ 0.1 | dropped |
| A303432 Conj. 1, 2 | none above 2¹² | – | ≪ 0.1 | dropped |
| A303389, A303401 | none above 2¹⁸ | – | ≪ 0.1 | dropped |
| A303428 | none above 2²¹ | – | ≪ 0.1 | dropped |

The structural reason A301534 stands out: it has **one** sparse term, 15·2^z, so R(p) is about
log₂ p · c/√(ln p), which grows like √(ln p). Exceptions then thin out only like
exp(−c√(ln X)), and their count grows with X. The other single-term statements (A308566,
A308584, A308621, A308623, A308661) have a two-parameter sparse set with about (ln n)²/c
elements, and their near-miss rate per octave is flat. The pair statements (2^c + 2^d,
3^c + 3^d, …) have no near misses at all past small n.

## 4. Reduction chains

**A301534.** Q = x² + 3y² is a one-class form: m ∈ Q iff every prime ≡ 2 (mod 3), including 2,
divides m to an even power (checked against enumeration for m < 2·10⁵). For p ≡ 7 (12) and
m = p − 15·2^z:
- z ≥ 1 gives m odd and m ≡ 1 (mod 3), so 2 and 3 never block. z = 0 gives m even, and it
  needs v₂ even.
- 5 never divides m, since 15·2^z ≡ 0 and p ≢ 0 (mod 5).
- A bad prime q blocks the z in one class modulo ord_q(2), namely the class where
  15·2^z ≡ p (mod q). The q with small orders are 11 (order 10), 17 (8), 23 (11), 41 (20),
  47 (23), 89 (11), 29 (28) and so on. They fix arithmetic progressions of z.

So the exceptions sit in classes of p mod 11·17·23·89… where these progressions cover many of
the about 31 values of z, and the rest must die for "random" reasons. The six witnesses show
exactly this: 28662666283 has z = 4, 14, 24 blocked by 11, z = 12, 20, 28 by 17, z = 5, 16, 27
by 23, z = 8, 19, 30 by 89, and 6 of its 31 z blocked only by a prime above 1000 (§6.3). The
scan itself is exhaustive: a bitset of Q, shifts 15·2^z ≤ 2^24, the exact test for larger z,
and a Miller–Rabin primality filter on the survivors with p ≡ 7 (12).

**A308621, A308623.** m ∈ T + T iff 4m+1 is a sum of two squares. For N ≡ 1 (mod 4) this
holds iff every prime q ≡ 3 (mod 4) with q ≤ √N divides N to an even power. A bad prime above
√N would force a second bad prime below √N to an odd power, since N ≡ 1 (mod 4). This is what
a progression sieve would use. Local blocking comes from 3, 7, 11, 19, 23, 31, 43, … through
the group ⟨2, 125⟩ (resp. ⟨2, 25⟩) mod q. The census in §2 shows only weak concentration, so
the scan was exhaustive.

## 5. Every search, with range and cost

CPU is user time on a box with load 60–160. Ranges include their start and exclude their end.
"Calibration" means a range already exhausted by someone else, rerun only to measure
near misses (cheap, and not counted as new coverage).

| Statement | Range | Kind | Result | CPU |
|---|---|---|---|---|
| A301534 | primes p ≡ 7 (12), p < 2³³ | calibration (Sun: 8·10⁹) | only p = 7 | 0.11 h |
| **A301534** | **primes p ≡ 7 (12), 2³³ ≤ p < 10¹¹** | **new, exhaustive** | **6 counterexamples** (§6) | 1.17 h |
| A308623 | [1, 10¹⁰) | calibration (Resta) | none | 0.06 h |
| A308623 | [10¹⁰, RANGE623) | new, exhaustive | COUNT623 | CPU623 |
| A308621 | [1, 10¹⁰) | calibration (Resta) | none | 0.06 h |
| A308621 | [10¹⁰, RANGE621) | new, exhaustive | COUNT621 | CPU621 |
| A308584 | [1, 10¹⁰) | new above Sun's 4·10⁸ | none; 24 n with r = 1 | 0.06 h |
| A308566 | [1, 2³²) | new above Sun's 5·10⁸ | none | 0.11 h |
| A303401 | [1, 2³²) | new above 7·10⁶ | none (r ≥ 4 for all n > 2¹⁹) | 0.05 h |
| A303428, "Moreover" | [1, 2³²) each | new above 3·10⁸ | none | 0.14 h |
| A303432 Conj. 1, 2, 3 | [1, 2³²) each | new above 2·10⁶ | none | 0.24 h |
| A303543 | [1, 2³²) | new above 10⁹ | none | 0.11 h |
| A303601 | [1, 2³²) | new above 7·10⁸ | none | 0.08 h |
| A303233, A303363 | [1, 2³²) | new above 10⁹ | none | 0.26 h |
| A302983 | [1, 2³²) | calibration (Sun: 6·10⁹) | none | 0.19 h |
| A303389 | [1, 2³²) | calibration (Sun: 10¹⁰) | none | 0.08 h |
| A308661 Conj. 1 | 3n+1 < 2³³ | calibration (Resta) | none | 0.20 h |
| A308661 Conj. 2 | 24n+10 < 2³³, i.e. n < 3.58·10⁸ | new above n ≤ 10⁸ | none | 0.22 h |
| A302984, A303338, A303637 | [1, 2³²) | calibration (refuted statements) | as published (none below 2³²) | 0.48 h |
| Validation and benchmarks | windows around 8 known witnesses | | all reproduced | ≈ 0.4 h |

Total: TOTALCPU CPU-hours, against a 30 CPU-h budget. Stop conditions, written before each
run:
- A301534: stop at the first hit or at 10¹¹ (cap 2 CPU-h). I ran on to 10¹¹ to count the
  exceptions.
- A308621 and A308623: exhaustive to 10¹² each, with a cap of 8 CPU-h each.
- Calibration runs: 2³² (2³³ for A308661 and A301534).

## 6. The hit: A301534 is false

### 6.1 The statement as Sun wrote it

OEIS [A301534](https://oeis.org/A301534), "Number of ways to write the n-th prime congruent to
7 modulo 12 as x^2 + 3*y^2 + 15*2^z with x,y,z nonnegative integers", by _Zhi-Wei Sun_, Apr 16
2018 (revision #22, unchanged since). The comments read:

> Conjecture: a(n) > 0 for all n > 1. In other words, any prime p > 7 with p == 7 (mod 12) can
> be written as x^2 + 3*y^2 + 15*2^z with x,y,z nonnegative integers.
>
> We have verified the conjecture for all primes p == 7 (mod 12) with 7 < p < 8*10^9.

Conventions: x, y, z ≥ 0 are integers. Taking x, y ∈ Z instead gives the same set, since only
x² and y² occur.

### 6.2 Witness

**p = 28662666283**, which is prime (so its factorisation is p itself), with
p ≡ 7 (mod 12) and p mod 8 = 3. The admissible z are 0 ≤ z ≤ 30, since 15·2³⁰ ≈ 1.6·10¹⁰ ≤ p
< 15·2³¹. For each z, m = p − 15·2^z has an odd power of a prime ≡ 2 (mod 3), so
m ≠ x² + 3y². It is the least counterexample: every prime ≡ 7 (mod 12) below it was tested,
by `hs3` over [1, 2³³) and [2³³, 3.4·10¹⁰).

All counterexamples below 10¹¹, all prime and ≡ 7 (mod 12), each with 0 representations:
28662666283, 34777306483, 43394007823, 44172408919, 46796931343, 61044565927. That is 1 in
[2³⁴, 2³⁵) and 5 in [2³⁵, 2³⁶), against the estimator's 1–3 per octave.

### 6.3 Two independent exact verifications

1. **`src/hs3.c` (C).** A bitset of {x² + 3y²} built by enumeration, shifted by 15·2^z ≤ 2^24,
   with the factor criterion for larger z (trial division to the cube root, then Pollard rho
   and Miller–Rabin) and a deterministic Miller–Rabin filter for primality. It reports
   r(p) = 0.
2. **`py/verify534.py` (Python, standard library only, no shared code).** Deterministic
   Miller–Rabin (13 bases) checks that p is prime. Then the script enumerates **every** z with
   15·2^z ≤ p and **every** y with 3y² ≤ m, and tests m − 3y² for a perfect square with
   `math.isqrt`, so it does not rely on the class-number criterion. It finds **0**
   representations for each of the six witnesses (3 s each).

   Controls: the three primes ≡ 7 (mod 12) below 28662666283 have 35, 30 and 40
   representations, and the three above have 19, 29 and 58. The script reproduces the first OEIS terms a(1..8) =
   0, 2, 3, 4, 5, 5, 2, 6 (p = 7, 19, 31, 43, 67, 79, 103, 127).
3. **Obstruction certificate** (`work/cert534.txt`). For each z, a prime q ≡ 2 (mod 3) with
   q ∥ m:

   | z | q | z | q | z | q | z | q |
   |---|---|---|---|---|---|---|---|
   | 0 | 641 | 8 | 89 | 16 | 23 | 24 | 11 |
   | 1 | 467 | 9 | 389 | 17 | 29 | 25 | 911 |
   | 2 | 1823 | 10 | 101 | 18 | 67409 | 26 | 104549 |
   | 3 | 149 | 11 | 150779 | 19 | 89 | 27 | 23 |
   | 4 | 11 | 12 | 17 | 20 | 17 | 28 | 17 |
   | 5 | 23 | 13 | 47 | 21 | 113 | 29 | 71 |
   | 6 | 233 | 14 | 11 | 22 | 383 | 30 | 89 |
   | 7 | 51839 | 15 | 167 | 23 | 1637 | | |

   No covering congruence explains it. Fifteen z are killed by primes below 100, lying on
   progressions mod ord_q(2). The other 16 are killed by larger primes, up to 150779.

### 6.4 Prior art at the moment of the hit

Checked at 12:28 UTC and again at RECHECK UTC, 2026-11-26:
- the OEIS entry, re-fetched: still #22 of 16 April 2018, with no comment after Sun's;
- an OEIS full-text search for 28662666283: no results;
- joeyhlu's repository at `22d8e9e`, re-fetched: no mention of A301534 or the number;
- `gh search code/repos/issues` for "A301534" and for "28662666283": nothing relevant;
- web search for the number and for "A301534" with "x^2 + 3*y^2 + 15*2^z": only the OEIS
  page;
- google-deepmind/formal-conjectures and the Epoch OEIS index: no entry.

Mathematical Reviews, zbMATH, Chinese-language sources and Sun's own web pages were not
searched *(unverified)*.

### 6.5 How Lean could check it

Literal statement (no existing Lean statement was found, so this is proposed):

```lean
def SunA301534 : Prop :=
  ∀ p : ℕ, p.Prime → p % 12 = 7 → 7 < p → ∃ x y z : ℕ, p = x^2 + 3*y^2 + 15*2^z
theorem sunA301534_false : ¬ SunA301534 := -- witness p = 28662666283
```

Proof shape:
- Primality: `Nat.Prime 28662666283` by `norm_num`, or by a Pratt or Pocklington certificate
  under `decide`.
- Bound z ≤ 30, since 15·2³¹ > p.
- For each z, bound y ≤ ⌊√((p − 15·2^z)/3)⌋ and test `Nat.sqrt` of the rest: 2,968,144 pairs
  (y, z) in all.
- With `native_decide` this takes seconds. It needs a soundness lemma for the bounded search:
  the decidable instance over `Finset.range` together with `Nat.sqrt_eq'`/`Nat.exists_mul_self`.
- Kernel-only alternative (no `native_decide`): use the certificate in §6.3. Each z needs the
  lemma "q prime, q ≡ 2 (mod 3), q ∣ x² + 3y² ⇒ q ∣ x ∧ q ∣ y", from −3 being a non-residue
  (quadratic reciprocity in Mathlib), applied with q ∥ m. Alternatively, for q ≤ 23 (9 of the
  31 z), a residue check of x² + 3y² mod q² by `decide`.
- The rest are kernel-checkable divisions.

## 7. Misses, and what going further needs

- **A308621 and A308623** hold on [1, RANGEBOTH) (Resta to 10¹⁰, this lane beyond). The
  near-miss rate is flat, at about 0.04 expected exceptions per octave. Going further: the
  exhaustive scan costs about 4.5·10⁻⁸ CPU-s per n on this loaded box, so 10¹² → 10¹³ is about
  110 CPU-h per statement. A targeted progression sieve on the worst 3% of classes mod
  3³·7²·11²·31² would cut that about 4× at about 89% coverage (by the model). About 0.15
  expected exceptions per statement per decade make this a poor bet.
- **A302920** (primes p, p² = x² + 2y² + 3·2^z) is the natural next single-term target. Sun
  found that A301471 (all n) fails at the composite 5884015571. With about 2 log₂ p sparse
  terms, R grows like √(ln p), as in A301534. Each test needs the exponent parity of
  primes ≡ 5, 7 (mod 8) in a number near p², which is 10²⁰ at p = 10¹⁰. That needs a
  polynomial sieve over n² − 3·2^z or 128-bit Pollard rho, at about 100 µs per test.
  Effort: M.
- **A301452 and A300510** (n² = m·4^k + a binary form) are the same type, with the same cost.
- More A301534-type entries (a prime in a fixed class, a class-number-one binary form, and one
  term c·2^z): this lane fetched A301490–A301600 and found only A301534. A full-text OEIS
  search for "prime congruent to" "2^z" "x^2" turned up nothing else. A wider pull of Sun's
  2017–2018 entries may find more.
- Everything else in the pool: see §3 (dropped) and §5 (scanned negative).

## Proposed edges

```jsonl
{"premise": "Computation: 28662666283 is prime, = 7 mod 12, and not x^2+3y^2+15*2^z (x,y,z>=0); least such prime > 7", "premise_status": "theorem", "premise_lean_source": "", "consequence": "OEIS A301534 conjecture (every prime p > 7, p = 7 mod 12, is x^2+3y^2+15*2^z) is false", "consequence_ref": "OEIS A301534 (Z.-W. Sun, 2018-04-16; verified by Sun for p < 8e9)", "consequence_status": "open", "implication_source": "this lane: hs3.c exhaustive scan of primes = 7 mod 12 below 1e11 (6 counterexamples) + verify534.py full enumeration; prior art none found 2026-11-26 12:28 UTC", "effort": "S", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route (e); script-verified only, Lean check pending (native_decide over 2,968,144 (y,z) pairs, or per-z certificate q = 2 mod 3, q || m); other counterexamples 34777306483, 43394007823, 44172408919, 46796931343, 61044565927", "sweep": "2026-11-26", "lane": "disproof-sun-family"}
{"premise": "Exhaustive bitset scan, n in [1e10, RANGE623)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to A308623 (T_a + T_b + 2^c*10^(2d)) below RANGE623", "consequence_ref": "OEIS A308623 (Sun 2019; Resta 1e10)", "consequence_status": "open", "implication_source": "this lane, hs2.c", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative; flat near-miss rate ~0.04 expected exceptions per octave", "sweep": "2026-11-26", "lane": "disproof-sun-family"}
{"premise": "Exhaustive bitset scan, n in [1e10, RANGE621)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to A308621 (T_a + T_b + 2^c*5^(3d)) below RANGE621", "consequence_ref": "OEIS A308621 (Sun 2019; Resta 1e10)", "consequence_status": "open", "implication_source": "this lane, hs2.c", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative; flat near-miss rate ~0.035 expected exceptions per octave", "sweep": "2026-11-26", "lane": "disproof-sun-family"}
{"premise": "Exhaustive scans to 2^32 (A308584 to 1e10; A308661 Conj. 2 to n < 3.58e8)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to A303401, A303428 (both), A303432 Conj. 1-3, A303543, A303601, A303233, A303363, A308566, A308584, A308661 Conj. 2 in those ranges", "consequence_ref": "OEIS (Sun 2018-2019)", "consequence_status": "open", "implication_source": "this lane, hs.c/hs2.c", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative; near-miss model gives << 0.1 expected exceptions in (8.6e9, 1.8e13) for each", "sweep": "2026-11-26", "lane": "disproof-sun-family"}
```
