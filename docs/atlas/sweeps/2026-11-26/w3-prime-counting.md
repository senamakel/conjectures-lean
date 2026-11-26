# Lane `w3-prime-counting` (wave 3): π(x), p_n, sums over primes at sparse arguments

**PAUSED, INCOMPLETE** (owner's instruction, 2026-11-26). The searching stopped part-way. Nothing
here was built, and no Lean file was touched. Numbers come from Python `-I` and small C sieves in
the scratchpad, which were not kept. Edges are in `w3-prime-counting.edges.jsonl`.

## Summary

| # | Statement | Class | Route | Finite range | Effort |
|---|---|---|---|---|---|
| D1 | Sun, arXiv:1208.2683 Conj. 2.1 (all α > 0) is **false**: α = 0.001, n = 9 | counterexample | exact decimal check | one evaluation | S |
| D2 | Sun, arXiv:1210.1562 Remark 1.1, part 1 (`N_n(q)^{1/n}` increasing from n = 2) is **false** for every prime power q ≥ 27, at n = 2 | counterexample | closed form | none | S |
| A1 | Sun, Ramanujan J. 42 (2017) Conj. 4.1(ii): `S(m)^{1/m}` strictly increasing, where `S(m) = max_k (km − p_k)` | A | RH (Schoenfeld) for m ≥ 17, exact for m ≤ 17 | π up to 8.5·10⁷ | S–M |
| A2 | Sun, arXiv:1208.2683 Remark 2.1: the sharp thresholds 9, 15, 31, 47, 62, 92, 92, 122, 122 for α = 2..10 in `(1/n)Σ p_k^α < p_n^α/(α+1)` | A | RH (Schoenfeld) for p_n ≥ 1.4·10⁷, sieve below | sieve to 1.4·10⁷ | S–M |
| A3 | Sun, arXiv:1208.2683 Conj. 2.17 (i)–(iii): monotonicity of `M_q(n)`, the number of monic irreducibles of degree ≤ n over F_q | A | elementary (Gauss's formula plus explicit error bounds) | q ≤ 32, n ≤ 25 | M |
| A4 | Sun, 1210.1562 Remark 1.1, part 2 (ratio of n-th roots decreasing for n ≥ n₀(q)), and part 1 corrected to n ≥ 3 | A | elementary | q ≤ 16, n ≤ 19 | M |
| I1 | Sun, BAustMS 88 (2013) Remark 2.4 (for every α > 0 and every n, `(S_n^{(α)}/n)^{1/n}` decreases) implies Firoozbakht's conjecture | new implication (premise open) | limit α → ∞ | none | S |

A1–A4 have no proof anywhere I looked. A3 and A4 are the F_q analogue of π at exponential
arguments, not π itself.

## Counterexamples (flag)

### D1. Sun's Conjecture 2.1 of arXiv:1208.2683 is false for small α

- **Statement (Sun, 2012-09-12).** "For any α > 0 we have (1/n) Σ_{k=1}^n p_k^α < p_n^α/(α+1)
  for all n ⩾ 2⌈α⌉² + ⌈α⌉ + 6." For 0 < α ≤ 1 the threshold is n ≥ 9.
- **Why it fails.** As α → 0+, the inequality at a fixed n becomes `log p_n − θ(p_n)/n ≥ 1`. At
  n = 9 (p₉ = 23) this quantity is 0.999594 < 1.
- **Witness (60-digit Decimal).** α = 0.001, n = 9: the inequality fails. At α = 0.01, n = 9 it
  still holds (LHS 1.0216219648…, RHS 1.0216353332…). For α ∈ {0.5, 0.2, 0.1, 0.05, 0.01} there
  is no failure for 9 ≤ n < 200. The failure set is a small interval of α near 0 at n = 9; its
  exact endpoint was not computed. Sun checked only α = 2..700.
- **Lean.** The proof is a finite real-number computation: nine terms `p^α` with α = 1/1000,
  bounded by rational intervals. Effort S. Novelty: no refutation found (searches below).

### D2. Remark 1.1 of Sun, arXiv:1210.1562, part 1, is false for q ≥ 27

- **Statement.** "Our computation suggests that (N_n(q)^{1/n})_{n⩾2} is strictly increasing",
  for every prime power q. It is a remark, not a numbered conjecture.
- **Disproof.** `N₂ = (q²−q)/2` and `N₃ = (q³−q)/3`, so `N₂³/N₃² = 9q(q−1)/(8(q+1)²)`. This
  exceeds 1 for q ≥ 27 (at q = 27 it is 1.0073; at q = 25 it is 0.9985). Hence
  `N₂^{1/2} > N₃^{1/3}` for every prime power q ≥ 27. Check: q = 27 gives N₂ = 351 and
  N₃ = 6552, with 18.735 > 18.712. A scan of q ≤ 300, n ≤ 150 finds no other failure, so the
  statement is true from n = 3 on (A4).

## Class A candidates

### A1. `S(m)^{1/m}` strictly increasing (Sun, Ramanujan J. 42 (2017) 59–67, arXiv:1409.5685 v6, Conj. 4.1(ii))

- **Source wording.** "(ii) The sequence ᵐ√S(m) (m = 1, 2, 3, . . . ) is strictly increasing."
  Here `S(m) := max{km − p_k : k ∈ Z⁺}`. Sun proves `(m−1)S(m+1) ⩾ mS(m)` and
  `e^{m−1}/(m−1) < S(m) < (m−1)e^{m+1}`. Note `S(1) = −1`. A Lean statement must use the real
  m-th root with its sign: the integer form `S(m+1)^m > S(m)^{m+1}` fails at m = 1, since
  (−1)² = 1.
- **Deduction (mine).** `S(m) = max_{x≥2} (mπ(x) − x)`, which is attained at a prime. The smooth
  model `m·li(x) − x` peaks at x = eᵐ with value `m·li(eᵐ) − eᵐ ≈ (eᵐ/m)(1 + 2/m + …)`. So
  `log S(m)/m = 1 − (log m − c)/m + …`, with an increasing gap of about `(log m − 1)/m²`.
  Schoenfeld's bound changes S(m) by a relative amount of at most about `m³e^{−m/2}/(8π)`.
- **Threshold (computed).** A log-grid scan of the upper bound `sup_x (m li x − x + m ε(x))` and
  the lower bound at x = e^{m+1} separates the two values for every m ≥ 16 with Schoenfeld's
  constant, and for every m ≥ 17 with an extra slack factor of 1.1, checked up to m = 120. Beyond
  that the margin only widens (an asymptotic argument is still needed). Sieve windows where RH
  does not bound F(x) < S(m): m = 17 needs [1.8·10⁷, 3.3·10⁷], and m = 18 needs
  [5.1·10⁷, 8.5·10⁷].
- **Numerics (exact sieve to 1.4·10⁹).** S(1..20) = −1, 1, 5, 13, 37, 83, 194, 469, 1111, 2743,
  6698, 16379, 40543, 101251, 254053, 640483, 1622840, 4133371, 10578367, 27130829. The
  conjecture holds for m ≤ 20. Its smallest relative step is
  `log S(m+1)/(m+1) − log S(m)/m = 0.0052` at m = 17.
- **Lean.** Use schoenfeld-rh's π bound, the monotonicity of li, and a proved-sound π checker up
  to 8.5·10⁷ (the erdos-985 scale). Tier U. **Catch:** the asymptotic tail (m > 120) needs a
  clean analytic inequality, and the li convention must match schoenfeld-rh.

### A2. Sun's sharp thresholds for α = 2..10 (arXiv:1208.2683, Remark 2.1)

- **Source wording.** "Our numerical computation suggests that for α = 2, 3, . . . , 10 we may
  replace ⌈α⌉² + ⌈α⌉ + 6 in the inequality by 9, 15, 31, 47, 62, 92, 92, 122, 122
  respectively."
- **Check (exact sieve to 10⁸, n ≤ 5,761,455).** The last failure is at n = N_α − 1 in each
  case, exactly as Sun says. The normalised margin `(1 − r)(α+1)log p_n/α` is at least 0.686 for
  n > 1000. Its asymptotic value is 1.
- **Deduction.** By partial summation the inequality is equivalent to
  `∫₂ˣ t^{α−1}π(t)dt > x^α π(x)/(α+1)` at x = p_n. The main term's margin is about
  `x^{α+1}/((α+1)(α+2) log² x)`. With `|π − li| ≤ 1.1·√t log t/(8π)` for t ≥ 2657 (and ≤ 17
  below), the inequality holds for every real x ≥ x₀(α). The computed x₀ values are:
  1.08·10⁵, 3.86·10⁵, 9.2·10⁵, 1.8·10⁶, 3.1·10⁶, 4.9·10⁶, 7.2·10⁶, 1.0·10⁷ and 1.37·10⁷ for
  α = 2, …, 10. The finite check is a sieve to 1.4·10⁷.
- **Catch.** Dusart-type unconditional bounds probably suffice too, so the RH content is weak
  and a referee could call it routine. The general-α conjecture is out of reach (see D1 and the
  rejected list).

### A3. Sun's Conjecture 2.17 of arXiv:1208.2683 (monic irreducibles of degree ≤ n over F_q)

- **Source wording.** (i) "M_q(n+1)/M_q(n) < M_q(n+2)/M_q(n+1) unless q < 5 and
  n ∈ {2,4,6,8,10,12}." (ii) "If n > 2, then ⁿ√M_q(n) < ⁿ⁺¹√M_q(n+1) unless q < 7 and
  n ∈ {3,5}." (iii) For n > 3, "ⁿ⁺¹√M_q(n+1)/ⁿ√M_q(n) > ⁿ⁺²√M_q(n+2)/ⁿ⁺¹√M_q(n+1) unless
  (q < 8 & n ∈ {5,7,9,11,13}) or (9 < q < 14 & n = 4)."
- **Exact check** (Gauss's formula, prime powers q ≤ 300, n ≤ 150). The exceptions found are
  subsets of Sun's lists. (i): (2, 2–12 even), (3, 2), (3, 4), (4, 2). (ii): (2,3), (2,5), (3,3),
  (4,3), (5,3). (iii): (2, 5–13 odd), (3,5), (3,7), (4,5), (5,5), (7,5), (11,4), (13,4). There
  are no counterexamples.
- **Deduction.** Use `|dN_d − q^d| < q^{d/2+1}/(q−1)` (Sun 1210.1562, Lemma 2.1) to get two-sided
  bounds `A_n ± B_n` for M_q(n). These bounds prove (i)–(iii) at every pair with q ≤ 3000 and
  n ≤ 400, except q ≤ 32 and n ≤ 25. Those remaining pairs are checked exactly. The region beyond
  needs an asymptotic argument; the errors decrease in q and n.
- **Lean.** Mathlib at `fc4f59e5` has `irreducible_iff_dvd_X_pow_card_pow_sub_X_and_isCoprime`
  and `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` (`FieldTheory/Finite/Extension.lean`), but no
  Gauss counting formula. That formula is most of the work. Tier D. Effort M.
- **Near prior art.** Chebolu–Mináč–Nguyen–Tân, arXiv:2605.11445 (May 2026), prove
  log-convexity of `N_n(q)` (degree exactly n) for q > 8. They do not treat M_q(n), n-th roots or
  Sun (checked by fetching the paper). Sun 1210.1562 proves the N_n analogues for large n only.

### A4. Sun 1210.1562 Remark 1.1: the true part

- **Statement.** `N_n(q)^{1/n}` is strictly increasing for n ≥ 3 (the corrected part 1). The
  ratio of consecutive n-th roots is strictly decreasing for n ≥ n₀(q), where n₀(2) = 14,
  n₀(3) = 8, n₀(4) = n₀(5) = 6, and n₀(q) = 4 for q > 5.
- **Prior result.** Sun proves the ratio part only for n ≥ 5.835·10¹⁴, and part 1 for
  n > e^{3+7/(q−1)²}.
- **Check.** Exact for q ≤ 300, n ≤ 150, with no failure of either part. The crude bound fails
  only at q ≤ 16, n ≤ 19 (ratio part) and q ≤ 8, n ≤ 9 (part 1), so the finite range is tiny.
  Tier D. Effort M, sharing the Gauss formula with A3.

## New implication

**I1.** Sun (BAustMS 88 (2013), Remark 2.4) conjectures that `(S_n^{(α)}/n)^{1/n}` is strictly
decreasing for every α > 0 and every n. Let `f(α) = (n+1)log(S_n/n) − n log(S_{n+1}/(n+1))`.
Then `f(α)/α → (n+1)log p_n − n log p_{n+1}` as α → ∞ (checked numerically: n = 30 gives 1.2232
against the limit 1.2234 at α = 10⁴). So the conjecture implies `p_n^{1/n} ≥ p_{n+1}^{1/(n+1)}`,
and equality is impossible, so it implies Firoozbakht's conjecture. The case 0 < α ≤ 1 looks
provable from crude bounds (f/α ≥ 0.077 over the tested grid), but it is only a partial result.
I did not find the implication written down.

## Class B or C, and rejected

- **Sun 1208.2683 Conj. 2.1 for all α:** false (D1). Even restricted to large α it is out of
  reach. At n ≈ 2α² it needs prime counts in windows of length about x/α ≈ √(2x log x) at
  relative precision 1/log x, which is beyond RH.
- **1402.6641 §2:** every conjecture other than 2.7(i) and 2.14(ii) (already proved, PR #23) asks
  for primality, squares or additive structure of π-values. These are 2.1–2.6, 2.7(ii), 2.8, 2.9,
  2.11–2.13 and 2.15–2.25; rejected.
  - Remark 2.7's `π(kn) < π((k+1)n)` for n ≥ k contains Oppermann's inequality at k = n−1:
    rejected, Legendre strength.
  - Conj. 2.10 needs at least √n − 1 distinct values of `π((k+1)n) − π(kn)`. RH resolution gives
    only about n^{1/3} (consecutive k) or √n/log³ n (sparse k): rejected.
  - Conj. 2.14(iii) needs gaps below √y: rejected.
  - Section 1 holds no conjectures.
- **1402.6641 §3** (p_n): all arithmetic or additive; rejected.
- **OEIS A038098 (ii)** (k = 2): needs the prime count in intervals of length 2√x at relative
  error 1/log x; rejected (agrees with wave2).
- **OEIS comments read:** A000720, A038107, A038098, A238165, A237578, A237615, A237710, A237712,
  A238570, A238902, A239328, A241568, A007053, A006880. Apart from the known ones, the only
  further conjectures are arithmetic (primality, squares, perfect powers); rejected.
- **1208.2683 Conj. 2.2–2.11:** Firoozbakht-type gap statements or Schinzel; rejected. The
  squarefree and two-squares Conj. 2.12/2.13 are out of lane. Their n-th-root halves need gaps
  below log, but their "ratio of roots increasing" halves look provable from crude counts (not
  checked numerically, so not listed).
- **Primes between consecutive n^α for α < 9/4:** using 22/25 together with the maximal-gap tables
  to 2⁶⁴ needs α ≳ 2.29, which is worse than the published 9/4; rejected. Sums of primes S_n,
  triangular numbers, n·p_n and p_n p_{n+1} all have gaps below √x log x; rejected.
- **Panaitopol 2000 (Acta Arith. 94):** π(ax) < aπ(x), π(x+y) ≤ 2π(x/2) + π(y) and the related
  inequalities are proved; nothing open found.

## Novelty search (2026-11-26)

| Where | Queries | Found |
|---|---|---|
| arXiv full texts | 1402.6641 v12, 1208.2683 v9, 1211.1588 v29 (skimmed), 1210.1562 v2, 1409.5685 v6, BAustMS 142s.pdf (= 1207.7059), 1303.5595 (Wang–Zhu), Graz slides of 2026-05-05 | statements as quoted; Wang–Zhu does not treat Conj. 2.1, 2.17 or 4.1 |
| Exa / WebSearch | Sun Conj. 2.1 power sums; Conj. 2.17 / irreducible polynomials n-th root; S(m) = max(km − p_k); Remark 2.4 and Firoozbakht; generalised Mandl inequality for p_k² and p_k^α; Panaitopol and related open inequalities | Chebolu et al. arXiv:2605.11445 (N_n only); Sinha arXiv:1011.1667 and Axler (α = 1 only); Gerard–Washington (asymptotic only); nothing on A1–A4, D1, D2 or I1 |
| OEIS (via Exa fetch) | entries listed above, plus a search for S(m)'s terms | no OEIS entry for S(m); A247895 and A038606 are related but have no claim |
| formal-conjectures | clone `9097e2f`: grep for the arXiv ids, "monic irreducible", Mandl; `gh pr list --state all --search` for 1208.2683, 1210.1562, 1409.5685, Mandl, "sum of the first n primes", Firoozbakht | none relevant (only the Firoozbakht statement and closed "solve" PRs) |
| solved-conjectures, openai-math, grh-lean, atlas-repo clones | grep for the ids, Mandl, "monic irreducible" | no relevant hit |
| GitHub code search | "1210.1562", "1409.5685" | noise only (an OEIS spider mirror of A247895) |
| MathOverflow | not searched separately | — |

## Not reached (paused)

- Sun's OEIS comments on A000040 (the page is too large to read in one fetch); the neighbours of
  A238165 and A238902; A007097; π(n!), π(F_n), π(n^n).
- Hassani's lists, Karanikolov, Vrba, Mandl-type refinements beyond α = 1, Kourbatov.
- A rigorous asymptotic tail for A1 (m > 120) and A3/A4 (q > 3000 or n > 400); the exact
  α-interval of failure in D1.
- The second Hardy–Littlewood conjecture for y ≥ C√x log² x under RH (probably published; not
  searched).
- The "ratio of roots increasing" halves of 1208.2683 Conj. 2.12/2.13 (squarefree numbers, sums of
  two squares).
