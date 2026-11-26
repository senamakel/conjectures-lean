# Independent verification: Sun, Conjecture 3.27(ii), claimed counterexample n = 62191

Date: 2026-11-26. Status: **stopped early on the owner's instruction.** The job was wound down
before the main computation finished, so this report covers only what was established up to
that point.

## Verdict

**PARTIALLY CONFIRMED, NOT VERIFIED.** No disagreement with the claim was found, but the
independent check is incomplete:

- The statement wording and the exponent reading were checked fully (see §1). The claimant's
  reading is the right one.
- Of the claimant's 17,161 attainable exponents for n = 62191, I independently classified the
  **1,385 with e ≤ 5000 (8.1%)**. All 1,385 are composite in my run as well. Each has the same
  proof type as the claimant's (prime factor or Fermat-3 failure), and where both give a
  factor, it is the same factor. None of them is prime.
- **Not done:** my own enumeration of the attainable-exponent set for n = 62191. The 1,385
  figure only checks the claimant's list at its own entries; it does not show that the list is
  complete. Also not done: the exponents 5000 < e ≤ 31086 (15,776 of them), minimality over
  26..62190, the φ(m)/12 variant at n = 83843, and 3.27(iv).

## 1. Statement fidelity

**arXiv:1211.1588 v29** (1 Dec 2017, "33 pages, final published version"). This is verbatim
from the v29 TeX source (`176r.tex`, lines 747–762):

> {\rm (ii)} Any integer $n>25$ can be written as $k+m\ (k,m\in\Z^+)$ with
> $3\cdot2^{\varphi(k)/2+\varphi(m)/8}+1$ prime. Also, any integer $n\gs15$ can be written as
> $k+m\ (k,m\in\Z^+)$ with $3\cdot2^{\varphi(k)/2+\varphi(m)/12}-1$ prime.
>
> {\rm (iv)} Any integer $n>10$ can be written as $k+m\ (k,m\in\Z^+)$ with
> $2^{\varphi(k)+\varphi(m)/4}-5$ prime.
>
> Remark 3.27: "We have verified Conjecture \ref{Conj3.27} for $n$ up to 50,000. See
> \cite[A234451, A236358 and A234504]{S} for related data."

The conjecture is dated 2013-12-26. n = 62191 is above Sun's stated verification bound of
50,000, so the claim does not contradict it.

**OEIS A234451.** Its NAME and DATA are for part **(i)**, 2^(φ(k)/2+φ(m)/6)+3, not for
part (ii). Part (ii) appears only in a COMMENT:

> (ii) Each integer n > 25 can be written as k + m with k > 0 and m > 0 such that
> 3*2^(phi(k)/2 + phi(m)/8) + 1 (or 3*2^(phi(k)/2 + phi(m)/12) + 1 when n > 38) is prime.
> Also, any integer n > 14 can be written as k + m with k > 0 and m > 0 such that
> 3*2^(phi(k)/2 + phi(m)/12) - 1 is prime.

This comment is the only source for the φ(m)/12 "+1" variant (n > 38). It also gives n > 14 for
the "−1" form, where the paper has n ≥ 15; the two bounds are the same. The program in the
entry is Mathematica:
`f[n_,k_]:=2^(EulerPhi[k]/2+EulerPhi[n-k]/6)+3; a[n_]:=Sum[If[PrimeQ[f[n,k]],1,0],{k,1,n-1}]`.

**OEIS A234504.** NAME: "Number of ways to write n = k + m with k > 0 and m > 0 such that
2^(phi(k) + phi(m)/4) - 5 is prime". COMMENT: "Conjecture: a(n) > 0 for all n > 10. We have
verified this for n up to 50000." The program is the same kind of Mathematica code.

**Exponent reading.** Mathematica evaluates 2^(r) for a non-integer rational r to a non-integer,
so PrimeQ returns False. When the sum is an integer (for example 1/2 + 1/2), it evaluates to an
integer. So "the sum must be an integer" and "a non-integer exponent is not prime" are the same
reading (**sum**). The alternative is **strict**: φ(k)/2 and φ(m)/8 must each be integers. My
script `reading_check.py` (pure Python, exact) gives:

- The DATA of A234451 (n ≤ 84) and A234504 (n ≤ 80) match under both readings, so the data
  alone does not decide.
- The **thresholds** do decide. For 3·2^(φ(k)/2+φ(m)/8)+1, the n < 400 with no representation
  are {2,3,4,5,8,16,17,25} under the sum reading, so the largest is 25. That matches "n > 25"
  exactly. Under the strict reading the list also contains **29** (and 6–15), so the conjecture
  as stated would already fail at n = 29. Sun therefore meant the sum reading.
- For the φ(m)/12 variant, both readings give 38 as the largest failure below 400 (sum:
  {2..7,12,13,14,18,22,23,26,38}). That matches "n > 38".

The sum reading allows more representations than the strict one. A counterexample under the
sum reading is therefore also a counterexample under the strict reading. The least
counterexample under the strict reading, however, is 29, which is not 62191.

## 2. Independent recomputation for n = 62191 (partial)

**Tooling.** I wrote my own C code against the system `libgmp.so.10`, declaring the few GMP
prototypes by hand because no `gmp.h` is installed. It does not use Python, sympy or gmpy2.
PARI/GP, PFGW and LLR are not installed.

**`scan.c`** classifies N(e) = c·2^e + s for every e ≤ Emax:
- sieve by every prime up to B, giving a proved factor;
- otherwise a Fermat test to base 3 (`fermat3-fail` proves N composite);
- otherwise, for s = 1, Proth's theorem with a quadratic non-residue a, proved by
  a^((N−1)/2) ≡ −1 (mod N).

**Completed run: c=3, s=1, e = 1..5000, B = 10^6** (file
`disproof-scripts/sun-3-27-verify/partial_status_3x2e+1_e1-5000.txt`):
- 4,483 exponents have a factor, 493 fail Fermat-3, and 24 are Proth-proved prime.
- The 24 primes are e = 1, 2, 5, 6, 8, 12, 18, 30, 36, 41, 66, 189, 201, 209, 276, 353, 408,
  438, 534, 2208, 2816, 3168, 3189, 3912. This matches OEIS A002253 up to 5000 exactly, found
  independently.
- e = 1 is N = 7, which is prime trivially. Proth's condition k < 2^e fails there.

**Abandoned run.** The run to e ≤ 49000 with B = 2·10^6 had sieved down to 4,745 candidates
and completed 200 of their power tests when it was killed. Its output was lost, because the
program writes only at the end.

**Diff against the claimant's certificate.** The claimant's `cert_3x2p1_8_62191.txt` lists
17,161 exponents, with e from 1743 to 31086: 15,111 with a factor and 2,050 Fermat-3 failures.
For its 1,385 entries with e ≤ 5000:
- my run proves none of them prime;
- the F/C type agrees on all 1,385;
- every factor agrees.

The known prime exponents 2208, 2816, 3168, 3189, 3912, 20909 and 34350 do not occur in the
claimant's set.

`reps.c` enumerates the attainable exponents, under either reading, and searches for
minimality. It was written but never compiled or run. So the attainable-exponent set itself,
including whether 17,161 is complete, has **not** been checked independently.

## 3. Minimality

Not done. The plan: classify every e ≤ 49000 with `scan`, then run
`reps 2 8 status 26 62191 sum witnesses.txt`, which gives a Proth-certified (k, m, e, a) for
each n.

## 4. φ(m)/12 variant (n = 83843) and 3.27(iv) (n = 167665)

Not done.

The claimant's `cert_3x2p1_12_83843.txt` is in `claimant/runs/`. Its `cert_2m5_167665.txt` is
**empty (0 bytes)**, so no certificate exists for (iv).

Feasibility of (iv): the exponents reach about 2.1·10^5 bits, and only Fermat-type
compositeness proofs are possible. With the generic `mpz_powm` I estimate tens of CPU-hours for
about 9,000 tests. A special reduction modulo 2^e − 5 would roughly halve that. Proving the
primes needed for minimality would require ECPP, which is not available.

## 5. Prior art (searches run before the stop)

- **Web searches** for "62191" together with Sun/φ/3·2^, for a refutation of "Conjectures on
  representations involving primes", and for the A234451 form found no refutation. The OEIS
  page for A234451 (fetched 2026-11-26) has no counterexample note. A related entry, A234503,
  does note one, a(43905) = 0.
- **Epoch, "OEIS Open"** (arXiv:2608.11941): it lists A234360 among Sun's conjectures, but
  neither A234451 nor A234504.
- **GitHub code search**:
  - "A234451": nothing relevant.
  - "A234504": the only relevant hit is this project's own `disproof-number-theory.md`, which is
    the claimant, not prior art.
  - "62191 phi": nothing.
- **Shallow clones** of 1337isnot1337/solved-conjectures, quietofwinter/solved-conjectures,
  redlazerrobot/solved-conjectures and epoch-research/LeanOpenProblems:
  - filename-level hits for the loose pattern were unrelated (numeric data);
  - the word-bounded grep for `A234451|A234504|A236358` and for `62191` returned no matches in
    any of the four repos.
- **Not searched:** MathOverflow, Sun's homepage conjecture lists, evidencepress.org, Zenodo,
  and the OEIS history and b-files of A234451 and A234504. OEIS blocks curl with Cloudflare,
  and WebFetch got HTTP 403; the pages were read through a different fetcher.

## Files

`docs/atlas/sweeps/2026-11-26/disproof-scripts/sun-3-27-verify/`:
- `scan.c`, `reps.c`, `reading_check.py`: my code.
- Build: `gcc -O2 -fopenmp scan.c -o scan /usr/lib/x86_64-linux-gnu/libgmp.so.10`.
- `partial_status_3x2e+1_e1-5000.txt`: one line per e ≤ 5000, either `e F p`,
  `e C fermat3-fail` or `e P a`.
- `scan49000.log`: log of the killed run.
- `claimant/`: `phirep.c`, `verify.py`, `c326.py` and `runs/cert_*.txt`, copied after my
  partial result. I did not read the claimant's code.

To resume, rerun `scan 3 1 49000 2000000` (about 4,700 power tests), then `reps`.
