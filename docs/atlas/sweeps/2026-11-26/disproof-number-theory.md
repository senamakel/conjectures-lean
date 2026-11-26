# Lane `disproof-number-theory`: integer counterexamples to named, tested conjectures

Lane `disproof-number-theory`, 2026-11-26. Research and computation only. No Lean file and no
existing file was edited. Scripts, lists and logs are in the session scratchpad under `hunt-nt/`
(`phirep.c`, `verify.py`, `c326.py`, `lists/`, `runs/`). Anything I could not confirm from a
primary source is marked *(unverified)*.

## Main finding

**Two parts of a published conjecture, both tested by its author, are false. The witnesses lie
beyond the range he checked.**

Zhi-Wei Sun, *Conjectures on representations involving primes*, in M. Nathanson (ed.),
Combinatorial and Additive Number Theory II, Springer Proc. Math. Stat. 220 (2017), 279–310
(arXiv:1211.1588 v29, 1 Dec 2017), **Conjecture 3.27**, dated 2013-12-26. The text below is from
the arXiv v29 PDF:

> (ii) Any integer n > 25 can be written as k + m (k, m ∈ Z⁺) with 3·2^{φ(k)/2+φ(m)/8} + 1
> prime. Also, any integer n > 15 can be written as k + m (k, m ∈ Z⁺) with 3·2^{φ(k)/2+φ(m)/12} − 1 prime.
> …
> (iv) Any integer n > 10 can be written as k + m (k, m ∈ Z⁺) with 2^{φ(k)+φ(m)/4} − 5 prime.
>
> Remark 3.27. This implies that there are infinitely many primes in any of the following seven
> forms … **We have verified Conjecture 3.27 for n up to 50,000.** See [16, A234451, A236358 and
> A234504] for related data.

The same statements are on OEIS A234451 (part (ii), with the same "verified for n up to 50000")
and A234504 (part (iv), "verified this for n up to 50000"). A value 3·2^x + 1 or 2^x − 5 with x
not an integer is not an integer, so it is not prime. Sun's Mathematica code in both entries
(`PrimeQ[...]` of a power with a rational exponent) has the same convention.

| Part | Witness (least) | Further exceptions found | Certificate |
|---|---|---|---|
| 3.27(ii), first sentence, `3·2^{φ(k)/2+φ(m)/8}+1` | **n = 62191** | 128 exceptions with `n > 25`, all in `[62191, 129145]`; none in `(129145, 2·10⁶]` | **complete**: all 17,161 attainable integer exponents `e ∈ [1743, 31086]` give a composite (15,111 with a prime factor below 2²⁰, 2,050 by a failed Fermat test base 3) |
| 3.27(iv), `2^{φ(k)+φ(m)/4}−5` | **n = 167665** | 106 exceptions in `[167665, 574191]`; search stopped at `6·10⁵` | **checked against the list only** (program 1): no attainable exponent is in A059608. A full compositeness certificate was not run. There are 61,838 exponents in [9136, 167642]; 9,145 of them have no prime factor below 2²⁰ and need a Fermat test. One such test takes 63 s at 10⁵ bits on this box, and Σe² = 6.8·10¹³, so the total is about 50–120 CPU-hours *(estimate)*, beyond this lane's budget |
| OEIS A234451 only (not in the paper): `3·2^{φ(k)/2+φ(m)/12}+1` for `n > 38` | n = 83843 | 10 exceptions in `[83843, 130801]`, none to `2·10⁶` | **complete**: 21,452 exponents in `[1538, 41897]`, 18,843 by a small factor, 2,609 by Fermat |

**Prior art.** I found none. The OEIS A234451 history has had no edit since 23 Jan 2014, and the
entry still states the conjecture. arXiv v29 (2017, the published version) still states 3.27 as
quoted. Exa web searches for the witnesses "62191" and "167665" together with Sun, phi or
3·2^n+1 found nothing relevant. GitHub code search for A234451, A234504 and A236358 finds only
the jOEIS implementations. None of the A-numbers is in formal-conjectures `9097e2f`
(`FormalConjectures/OEIS/`) or in Epoch's OEIS Open id list (`allids.txt`, 443 ids). The
other parts of 3.27, which survive (below), are not refuted anywhere I found either.

**Why the witnesses exist (the structure that found them).** For a fixed n, the exponent
e = φ(k)/a + φ(m)/b runs over a window [αn, βn]: here about [n/36, n/2] for (ii). The
exponents x for which 3·2^x + 1 is prime (A002253) thin out like c·log x. So the window holds
only O(1) "good" exponents, whatever the size of n, and a(n) does not grow. Sun's 50,000 sits just
below a large gap in A002253: 3912 is followed by 20909, a ratio of 5.3. For n = 62191 the
window is [1743, 31086]. It contains exactly six good exponents (2208, 2816, 3168, 3189, 3912,
20909), and 17161 of its 29344 integers are attained (58%). All six are missed. With an attain
rate of about 0.58, the chance of missing six is about 0.42⁶ ≈ 0.5% per n, which matches 128
exceptions across a window of about 40,000 n. Part (iv) is the same story at the gap 48212 →
120440 in A059608. This is a heuristic. The witnesses themselves are checked exactly (next section).

## Verification

Two programs, written separately, one of them straight from the paper's definitions:

1. **`phirep.c`** (C, OpenMP). It computes φ by sieve. For each n and each 1 ≤ k < n, it forms
   L·e = φ(k)·(L/a) + φ(n−k)·(L/b), keeps the integer e, and tests e against the OEIS list of
   prime exponents (`lists/*.txt`, copied from the OEIS entries). It reproduces A234451's first
   30 terms and its listed single-representation cases a(769) = a(787) = a(867) = a(869) =
   a(913) = a(1085) = 1. For each n with a(n) = 0 it also confirms that the largest attainable
   exponent lies below the largest list entry, so the list covers the window.
2. **`verify.py`** (Python, exact). φ comes from `sympy.totient`, and the exponent is a
   `fractions.Fraction`, so no sieve and no OEIS list are used. Every attainable integer
   exponent gets a **compositeness certificate**: either a prime factor below 2²⁰ (found
   modularly, then checked by exact division), or a failed Fermat test 3^{N−1} ≢ 1 (mod N) in
   GMP (gmpy2 2.3.2), which proves N composite. The script stops with an error if any value is a
   probable prime.

Results:
- **n = 62191, 3.27(ii):** 62,190 pairs (k, m), 17,161 distinct integer exponents, range
  [1743, 31086], the same range `phirep` reports. All 17,161 values 3·2^e + 1 are composite:
  15,111 by a factor below 2²⁰ and 2,050 by Fermat base 3. No PRP appeared. 209 s wall on 10
  workers, about 35 CPU-min. Certificate `runs/cert_3x2p1_8_62191.txt`, sha256 `11993eaf…8b4b1d`.
- **n = 83843, A234451 /12 variant:** 21,452 exponents in [1538, 41897], all composite (18,843
  by small factor, 2,609 by Fermat). Certificate `runs/cert_3x2p1_12_83843.txt`, sha256
  `1a61534c…83e055`.
- **n = 167665, 3.27(iv):** program 1 only. Every attainable exponent (at most 167,642) misses
  A059608: 3, 4, 6, 8, 10, 12, 18, 20, 26, 32, 36, 56, 66, 118, 130, 150, 166, 206, 226, 550, 706,
  810, 1136, 1228, 1818, 2368, 2400, 3128, 4532, 5112, 8492, 16028, 16386, 17392, 18582, 21986,
  24292, 27618, 30918, 32762, 48212, 120440, … So this witness is exactly as reliable as the
  list's completeness below 167,642, which rests on the PRP searches credited in the OEIS
  entry (Lifchitz, Underwood, Grantham). **Mark it unverified until certified.**
- Sanity checks of program 2: for n = 1000 and n = 167 it finds a probable prime
  (e = 41, 3·2⁴¹ + 1 = 6597069766657; e = 26, 2²⁶ − 5), and for n = 25 it finds no
  representation, which is consistent with Sun's threshold n > 25.

**Minimality** of 62191 needs only that the listed exponents below 3913 give primes. Those values
are Proth numbers, proved prime long ago (Golomb 1976, Table I, and the Ballinger–Keller lists), so
every n with 25 < n < 62191 has a representation that `phirep` exhibits. Minimality of 167665
rests in the same way on the A059608 entries ≤ 48212 being primes. Some of the larger ones may be
recorded only as PRPs *(unverified which)*. This affects only the minimality claim, not the
witness.

**Lean.** The negation is `∃ n > 25, ∀ k m, k + m = n → 0 < k → 0 < m → ¬ (3·2^{e}+1).Prime`,
stated with a rational exponent or with "e integral ∧ …". A checker would do three things:
- compute φ(k) for k < 62191 by a sieve, proved equal to `Nat.totient` (or prove it from
  per-k factorisations with `Nat.totient_mul` and the prime-power formula);
- enumerate the integer exponents;
- for each exponent, check a stored certificate: `(3*2^e+1) % p = 0` with `p < 3*2^e+1`, or
  `Nat.powMod 3 (N-1) N ≠ 1`. Soundness is Fermat's little theorem
  (`ZMod.pow_card_sub_one_eq_one`).

That is 17,161 exponents, 2,050 of which need a Fermat test on numbers of at most 31,088
bits. Under `native_decide` with GMP-backed `Nat` this is minutes. The proof of the φ sieve is
the only real engineering: effort **M**. Part (iv) at 167665 is about 3× larger (numbers up to
167,642 bits).

## Candidate pool and ranking

Sources read: Sun, arXiv:1211.1588 v29 (all 100 conjectures, skimmed for verification ranges),
Sun's talk slides `Representation.pdf` and `RepresentationRiddle.pdf`, and the OEIS entries the
paper cites. Excluded as already mined: formal-conjectures (which includes Sun's 2^k + m
conjecture, `OEIS/231201.lean`, and A231577) and Epoch's OEIS set (which includes A234360 =
Conjecture 3.28(ii)). Sibling lane `hints-epoch` is running Sun's polygonal-number forms (its
`sun3/`, `sun4/`), so I left those alone.

Heuristic used to rank: **how the expected number of representations grows with n.**
- Representations counted by n/log^c n (Goldbach-type: Conjectures 2.x, 3.33–3.43, verified to
  10⁸–10⁹) or by √n/log n give an expected number of exceptions beyond the checked range that is
  far below 1. Dropped.
- Representations counted by log n (Conjectures 3.6, 3.7, 3.9 and 3.10: 2^k + m, F_k + m,
  k!m ± 1, verified to 10⁶–10¹⁰) need about e^{−c log n} = n^{−c}. With c around 20–30 at
  n = 10⁷ this is negligible, and the checks are expensive. Dropped.
- **O(1) representations: the φ-exponent families** (Conjectures 3.26 and 3.27, verified to
  about 5·10⁴ or only to the b-file ranges). The count does not grow at all, so exceptions are
  expected infinitely often, clustered just above gaps in the prime-exponent lists. **Shortlisted.**

| # | Statement | Author's range | Expected exceptions in reach | Outcome |
|---|---|---|---|---|
| 1 | 3.27(ii) first: `3·2^{φ(k)/2+φ(m)/8}+1`, n > 25 | 50,000 | high: A002253 gap 3912 → 20909 | **false, n = 62191** |
| 2 | 3.27(iv): `2^{φ(k)+φ(m)/4}−5`, n > 10 | 50,000 | high: A059608 gap 48212 → 120440 | **false, n = 167665** |
| 3 | A234451 variant `3·2^{φ(k)/2+φ(m)/12}+1`, n > 38 (OEIS only) | 50,000 | high | false, n = 83843 (OEIS comment, not the paper) |
| 4 | 3.27(i) `2^{φ(k)/2+φ(m)/6}+3`, n ≥ 10 | 50,000 | medium: gap 58312 → 122550 | holds for n ≤ 2·10⁶ (list complete to 2.2·10⁶) |
| 5 | 3.27(i) `…−3`, n > 13 | 50,000 | medium | holds for n ≤ 2·10⁶ |
| 6 | 3.27(ii) second `3·2^{φ(k)/2+φ(m)/12}−1`, n > 15 (paper; OEIS n > 14) | 50,000 | medium | holds for n ≤ 469,000 (list as fetched ends at 234760) |
| 7 | 3.27(iii) `2·3^{…}+1`, n > 27 | 50,000 | medium | holds for n ≤ 2·10⁶ |
| 8 | 3.27(iii) `2·3^{…}−1`, n > 37 | 50,000 | medium | holds for n ≤ 2·10⁶ (list to 1,360,104) |
| 9 | 3.26(i) `2^{φ(k)}+2^{φ(m)}−1`, k, m ≥ 3, n > 5 | b-file to 8000 (no range in paper) | O(1) count, λ ≈ 6 | TODO |
| 10 | 3.26(ii) `a^{φ(k)}+a^{φ(m)/2}−1`, N(a) = 5 (a = 2..6, 8), N(7) = 17 | b-file to 2500 for a = 5 | O(1) count | TODO |

## Searches (range, cost)

| Search | Range | Result | Cost |
|---|---|---|---|
| `phirep`, 8 forms of 3.27 / A234451 / A236358 / A234504 | n ≤ 2·10⁵ | exceptions only in forms 1, 2, 3 | under 1 CPU-min |
| `phirep`, forms 4, 5, 7, 8 | 2·10⁵ < n ≤ 2·10⁶ | none | ~15 CPU-min |
| `phirep`, form 6 | 2·10⁵ < n ≤ 4.69·10⁵ | none | ~1 CPU-min |
| `phirep`, forms 1 and 3 | 2·10⁵ < n ≤ 2·10⁶ | none | ~10 CPU-min |
| `phirep`, form 2 | 2·10⁵ < n ≤ 6·10⁵ | 104 more exceptions (largest 574191) | ~2 CPU-min |
| `verify.py`, three witnesses | n = 62191, 83843, 167665 | TODO | TODO |
| `c326.py`, 3.26(i) | TODO | TODO | TODO |
| `c326.py`, 3.26(ii), a = 2..8 | 6 ≤ n ≤ 10⁴ | TODO (a = 7: zeros exactly at 6, 7, 10, 17, matching N(7) = 17) | TODO |

## Not done / leads

- Part (iv) beyond 6·10⁵: A059608 is a PRP list whose completeness I did not check above 595122.
- Sun's OEIS-only siblings from Dec 2013–Jan 2014 (A234503 `3^{…}+2`, A234337, A234344,
  A234346, A234361) have the same O(1) structure and are probably false too. They count as OEIS
  conjectures, not paper conjectures, and they are in the sibling lane's territory (Epoch
  neighbours), so I did not run them.

## Proposed edges

```jsonl
{"premise": "Computation: for n = 62191 every k in [1, 62190] gives e = phi(k)/2 + phi(62191-k)/8 non-integral or 3*2^e+1 composite (17161 exponents; 15111 small-factor and 2050 Fermat-base-3 certificates)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "Sun's Conjecture 3.27(ii) (first sentence: every n > 25 is k+m with 3*2^(phi(k)/2+phi(m)/8)+1 prime) is false; least witness n = 62191", "consequence_ref": "Z.-W. Sun, Conjectures on representations involving primes, CANT II, Springer PROMS 220 (2017) 279-310, arXiv:1211.1588 v29, Conj. 3.27(ii); OEIS A234451 comment (ii)", "consequence_status": "open", "implication_source": "this sweep: phirep.c (list-based, minimality) and verify.py (exact, list-free certificate)", "effort": "M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route (e). Author verified n <= 50000; witness beyond. 128 exceptions in [62191,129145], none in (129145, 2e6]. Lean: totient sieve proved equal to Nat.totient + certificate checker (factor or Fermat) under native_decide; 2050 Fermat tests on <= 31088-bit numbers", "sweep": "2026-11-26", "lane": "disproof-number-theory"}
{"premise": "Computation against OEIS A059608 (k with 2^k-5 prime): no attainable e = phi(k)+phi(167665-k)/4 lies in the list", "premise_status": "claimed", "premise_lean_source": "", "consequence": "Sun's Conjecture 3.27(iv) (every n > 10 is k+m with 2^(phi(k)+phi(m)/4)-5 prime) is false; least witness n = 167665", "consequence_ref": "arXiv:1211.1588 v29 Conj. 3.27(iv); OEIS A234504", "consequence_status": "open", "implication_source": "this sweep: phirep.c; full compositeness certificate not run (61838 exponents, 9145 Fermat tests up to 167642 bits, ~50-120 CPU-h)", "effort": "M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route (e), unverified until certified: relies on completeness of A059608 below 167642. 106 exceptions in [167665, 574191]", "sweep": "2026-11-26", "lane": "disproof-number-theory"}
{"premise": "Computation: for n = 83843 every e = phi(k)/2 + phi(n-k)/12 gives 3*2^e+1 composite (21452 exponents certified)", "premise_status": "theorem", "premise_lean_source": "", "consequence": "OEIS A234451 conjecture (ii), variant '3*2^(phi(k)/2+phi(m)/12)+1 prime for n > 38', is false; least witness n = 83843", "consequence_ref": "OEIS A234451 comment (ii) (Sun, Dec 2013); not in the arXiv paper", "consequence_status": "open", "implication_source": "this sweep: phirep.c and verify.py", "effort": "M", "lean_exists": "", "in_1337": false, "class": 1, "notes": "route (e); OEIS-only statement, lower value than the paper conjecture", "sweep": "2026-11-26", "lane": "disproof-number-theory"}
{"premise": "Computation with OEIS prime-exponent lists", "premise_status": "theorem", "premise_lean_source": "", "consequence": "no counterexample to Sun Conj. 3.27(i) both parts and (iii) both parts for n <= 2e6, nor to 3.27(ii) second sentence for n <= 469000", "consequence_ref": "arXiv:1211.1588 Conj. 3.27(i),(ii),(iii)", "consequence_status": "open", "implication_source": "this sweep, phirep.c", "effort": "S", "lean_exists": "", "in_1337": false, "class": 2, "notes": "negative search; O(1) representation count, so exceptions are expected eventually at gaps in A057732/A050414/A002235/A003306/A003307", "sweep": "2026-11-26", "lane": "disproof-number-theory"}
```
