# Lane `disproof-large-witnesses`: constructed counterexamples beyond any scan

**Result: no hit.** The lane was wound down by the owner before the most promising construction
finished. Nothing below is a verified counterexample. Four targets were examined in depth. Two of
them have structural reasons why the obvious construction fails, recorded here so nobody repeats
them. One more has a live construction route, which is the best unfinished lead (§3).

Budget used: about 1.5 CPU-hours, all cheap exact computation. Scripts are in
`disproof-scripts/disproof-large-witnesses/`. Two research subagents (an OEIS scan for
Pell-type "finite" claims and a literature scan) were stopped before they reported.

## 1. Targets examined, with outcome

| # | Conjecture (source) | Route tried | Outcome |
|---|---|---|---|
| 1 | Sun, OEIS A304331 / A304522 ($1000 prize) / A304333: every n > 1 is a Fibonacci (Lucas) number plus a positive (odd) squarefree number. Verified to 10^10 (A304333 to 5·10^9) | Covering by prime squares: n ≡ F_k (mod q²) for every k ≤ log_φ n | **Dropped, structural.** For most q the solution set of F_k ≡ r (mod q²) has period q·π(q), and its q-adic part is a single lift, so different primes act independently (CRT). The only q-fold ("fixed") classes are k ≡ π(q)/2 or π(q)/4 (mod π(q)), and they never contain k = 3p for large primes p. Budgeted greedy: 7–16% of the k ≤ K left uncovered at 100–1000 digits (`greedy_sq.py`). Each patch prime adds about 9.6·log10 q new indices, so the finite patch-up diverges. Evidence *for* the conjecture against this attack |
| 2 | Sun, OEIS A308950: 6n ± 1 = p + 2^k·3^m (k, m ≥ 1). Resta verified to 10^11 | 2D covering of (a, b) by the fibres {2^a 3^b ≡ c (mod q)} | **Dropped, structural.** The fibres behave independently. With every prime whose orders of 2 and 3 divide 720, the greedy leaves 34% uncovered (≈ ∏(1 − 1/g_q)). Σ 1/\|⟨2,3⟩ mod q\| is only 0.89 (orders dividing 720), 1.02 (5040) and 1.16 (55440). The single-λ reduction (3 ≡ 2^λ mod every q) needs CRT-compatible discrete logs, and these conflict already for q = 5 and q = 13 |
| 3 | Sun, OEIS A303932 Conj. 2 (and family A303233…A303821): 2n = p + 2^k + 3^m with 11 a QNR mod p. Verified to 5·10^8 | QR condition mod 44, plus covering | **Dropped.** The mod-44 condition kills about 55% of (k mod 10, m mod 10) pairs for every choice of 2n mod 44 (`qr11.py`). The remaining 45% runs into the same 2D-independence obstruction as #2 |
| 4 | Eldar–Ordowski, OEIS A309268 (2019): no Carmichael m has A326690(m) prime. Checked below 2^64 | Algebraic reduction | **Dropped, heuristic.** A326690(m) = q prime means m = qM with M \| qT − 1 (T = Σ_{p\|M} M/p). Korselt for q forces q − 1 \| M − 1, so q < M, and q is then the unique residue T⁻¹ mod M. That leaves a ~1/q coincidence for each M, so the expected number of hits converges and is dominated by small m, which are already checked |
| 5 | **Ordowski, OEIS A122045 comment (2020-02-06): odd composites m with m \| E(m−1) are exactly the Carmichael numbers whose prime factors are all ≡ 1 (mod 4) (A265237).** Eldar checked only the first 13 terms of A265237 | Carmichael-type subset-product construction with one "Euler-irregular" prime | **Best lead, unfinished** (§3) |
| — | Ordowski/Eldar OEIS claims A321790, A307767, A322120/1 | — | All three are theorems by short arguments: Fermat plus a subgroup/interval argument, 2-adic valuations, and the strong-liar count formula. Not targets |
| — | A309397, A330718, A331343, A332786 (n² \| harmonic-type numerators ⇒ n prime) | Transplant of 16843², 2124679² | Not run. They reduce to v_p ≥ 4…6 conditions at Wolstenholme/Wieferich primes, the same unreachable reduction as in `disproof-oeis-neighbours` §3 |
| — | A158914 (Noe: "Is this finite?"), Dąbrowski 2012 (28 prime-complete y² − 1), A217277 | — | A question, not a conjecture. Or two independent primality events. Or already covered by Luca–Najman (k ≤ 25) |

## 2. Lemmas established (exact, checked numerically)

- **Euler numbers mod any odd N.** E_n ≡ Σ_{a=0}^{N−1} (−1)^a (2a+1)^n (mod N).
  Proof: E_n(y) + E_n(y+1) = 2y^n telescopes to E_n(x) + E_n(x+N) = 2Σ(−1)^a(x+a)^n. Euler
  polynomials have coefficients in Z[1/2], so E_n(x+N) ≡ E_n(x) (mod N). Put x = 1/2 and
  E_n = 2^n E_n(1/2). The formula agrees with sympy's exact E_n for N ≤ 45 and n < 40
  (`euler_check.py`). Consequences: E_n mod p depends only on n mod (p − 1) for n ≥ 1, and
  p \| E_{p−1} ⇔ p ≡ 1 (mod 4) (asserted for every p < 1500).
- **Irregular Euler pairs** (p, r), r < p − 1, p \| E_r, for p < 1500 (`euler_R.py`):
  84 primes. Small ones: (19,10), (31,22), (43,12), (47,14), (61,6), (67,26), (71,28),
  (79,18), (101,62), (277,8), (349,256), (509,140), (577,208), (677,528).
- **Exhaustive small search (squarefree, prime factors < 1500).** No two-prime m. Thirty-three
  three-prime m: 1105, 2465, 10585, 29341, … 116682721. All of them looked like Carmichael
  numbers with every prime factor ≡ 1 (mod 4); that was checked by eye for the first dozen, not
  by program. No counterexample in this range.

## 3. Best unfinished lead: Ordowski's Euler-number criterion (A122045)

The condition is m \| E_{m−1}. For squarefree m it holds iff, for every p \| m,
r_p := (m − 1) mod (p − 1) (read 0 as p − 1) satisfies p \| E_{r_p}. A Carmichael number with all
prime factors ≡ 1 (mod 4) satisfies it, since r_p = p − 1. A counterexample needs at least one
prime in an irregular pair, with every other prime p ≡ 1 (mod 4) and p − 1 \| m − 1.

**Construction.** Take m = p0·∏_{p∈S} p, where (p0, r0) is an irregular pair, S is a set of primes
p ≡ 1 (mod 4) with p − 1 \| L, and m ≡ 1 (mod L), m ≡ 1 + r0 (mod p0 − 1). This is a subset-product
problem modulo lcm(L, p0 − 1), solved by meet in the middle (`euler_construct2.py`).

**Constraints found:**
- A single 3-mod-4 defect prime is impossible. 4 \| p − 1 \| L forces m ≡ 1 (mod 4), but the product
  is ≡ 3 (mod 4). This kills p0 = 19, 31, 43, …
- A 1-mod-4 defect needs r0 ≡ 0 (mod 4), gcd(L, p0 − 1) \| r0, and 1 + r0 not divisible by
  a small prime p with p ∤ E_even (3 in particular). That rules out (277,8), (541,464) and
  (761,104), and leaves **(509,140)**, (349,256), (577,208) and (677,528).
- Alternatively, use two 3-mod-4 defects. (19,10) with (31,22) is consistent (m ≡ 2 mod 9,
  m ≡ 3 mod 5), but then 3 ∤ L and 5 ∤ L.

**State at stop.** The (509, 140) run with L = 2^6·3^3·5^2·7·11·13 and 36 pool primes ≤ 10^5 was
killed before it printed. If a solution exists, the witness has roughly 40–80 digits. That is far
beyond any exhaustive scan, and each factor is ≤ 10^5, so primality is trivial.

**Verification plan.**
1. For each p \| m, evaluate Σ_{a<p}(−1)^a(2a+1)^{m−1} mod p directly.
2. Independently, compute E_{r_p} mod p with PARI's sec series, together with Kummer
   periodicity.
3. Confirm squarefreeness and that 509 ≡ 1 (mod 4) with 508 ∤ m − 1, so m is not Carmichael.

**Prior art (2026-11-26, exa search).** I found no proof or refutation. The OEIS entry was last
edited 2026-08-16 and does not mention one. Repeat the search before reporting. Ordowski
conjectures are actively mined (Zenodo 10.5281/zenodo.24380486 refutes a different one).

**Lean.** Prove the alternating-sum congruence for Euler numbers once. Then each prime is a
`decide`/`native_decide` over at most 10^5 terms.

## Proposed lines (do not apply without a verified witness)

```jsonl
{"source": "OEIS A122045 (Ordowski 2020-02-06)", "target": "odd composite m | E(m-1) => m Carmichael with all p == 1 mod 4", "status": "open; construction route identified, no witness", "lane": "disproof-large-witnesses"}
```

```jsonl
{"construction": "Carmichael-type subset product with one Euler-irregular prime p0 (p0 | E_r0, r0 < p0-1): m = p0*prod S, p == 1 mod 4, p-1 | L, m == 1 mod L, m == 1+r0 mod p0-1", "source": "docs/atlas/sweeps/2026-11-26/disproof-large-witnesses.md", "computable": "m | E_{m-1} via E_n == sum_{a<N} (-1)^a (2a+1)^n mod N", "refutes": [], "method": "subset product", "neighbours_tested": [], "neighbours_untested": ["Ordowski A122045 (needs a solved instance, (509,140) first)", "analogous Ordowski criteria for other Euler/Bernoulli-type sequences"], "sweep": "2026-11-26", "lane": "disproof-large-witnesses"}
```
