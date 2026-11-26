# Lane `novel-oeis-lists`: Sun's lists, OEIS conjectures, Axler/Hassani/Kotnik inequalities

Date 2026-11-26. Research only: nothing built, no Lean file edited. All numbers were computed
in this session (Python `-I` and small C sieves in the scratchpad; not kept). Claims not checked
against a primary source are marked *(unverified)*. Edges: `novel-oeis-lists.edges.jsonl`.
Candidates of `novel-via-rh` (primitive roots mod `p²`, Cohen–Trudgian) and `wave2` (A038098,
`k ≥ 4`) are not repeated.

## Summary

Five class-A candidates, all verified numerically over a meaningful range. Be clear about what
they are worth:

- **Two are elementary.** Sun's `π(kn)^{1/k}` and `π(n²)^{1/n}` monotonicity conjectures follow
  from `π(X) ≥ X/log X` and a trivial count of odd numbers. No RH is involved. They are open only
  because nobody wrote the ten lines down.
- **One is a real GRH result with a feasible check.** Sun's Conjecture 3.25 (OEIS A243164) is
  erdos-985's argument with search length `n ≈ p/log p`.
- **Two are RH consequences whose finite range is out of reach in Lean.** Hassani's conjecture
  that `A_n/G_n` decreases, and Axler's Conjecture 3.4. The RH bound only bites from about
  `3·10¹³`–`5·10¹³`, so the range below has to be a cited computation (tier H).

The Sun/OEIS hunting ground is mostly barren for RH. Out of roughly 150 prime-related Sun
conjectures read, almost all are additive (Goldbach type), concern values of polynomials or
special sequences, or are Firoozbakht-type gap statements. The one exception is A038098
(already taken).

## Class A, easiest first

### A1. Sun: `π(kn)^{1/k} > π((k+1)n)^{1/(k+1)}` for `n > 4`, `1 ≤ k ≤ n` · S · no RH needed

- **Source.** Sun, arXiv:1402.6641 Conj. 2.7(i) (2014-02-17). OEIS A238165, comment "(ii) For any
  integer n > 4, the sequence pi(k*n)^(1/k) (k = 1, ..., n) is strictly decreasing". Not in
  formal-conjectures.
- **Deduction (mine).** The inequality is `k·log(π((k+1)n)/π(kn)) < log π(kn)`. Since
  `log(1+u) ≤ u`, it suffices that `k·Δ < π(X)·log π(X)`, where `X = kn` and `Δ = π((k+1)n) − π(kn)`.
  The interval `(kn, (k+1)n]` holds at most `(n+1)/2` odd numbers, so
  `kΔ ≤ X/2 + k/2 ≤ X/2 + √X/2` (because `k ≤ n` gives `k ≤ √X`). For `X ≥ 17`,
  `π(X) ≥ X/log X` (Rosser–Schoenfeld), so `π(X) log π(X) ≥ X(1 − log log X/log X) ≥ 0.632·X`.
  That exceeds `X/2 + √X/2` for every `X ≥ 17`. The cases `kn < 17` are a handful.
- **Check (exact, done).** Every `5 ≤ n ≤ 19999` and every `k ≤ n` with `(k+1)n ≤ 4·10⁸` passes
  (sieve to `4·10⁸`). The smallest margin is `(k+1)log π(kn) − k log π((k+1)n) = 0.575`, at
  `n = 5, k = 2`. The sufficient condition `kΔ < π log π` also holds in every case checked.
- **Lean.** It needs `π(x) ≥ x/log x` for `x ≥ 17`. schoenfeld-rh's bound (valid from 2657) plus a
  `decide` below 2657 would do, but a Chebyshev-type bound would avoid RH altogether. Effort S.
- **Catch.** It is trivial. Its only value is that a stated conjecture gets closed.

### A2. Sun: `π(n²)^{1/n}` strictly decreasing for `n ≥ 3` · S · no RH needed

- **Source.** arXiv:1402.6641 Conj. 2.14(ii); OEIS A038107, Sun's comment of Feb 17 2014, part (i).
- **Deduction (mine).** It suffices that `n·Δ < π(n²) log π(n²)`, where
  `Δ = π((n+1)²) − π(n²)` is at most the number of integers coprime to 6 in `(n², n²+2n+1]`, so
  `Δ ≤ (2n+1)/3 + 2`. With `π(X) log π(X) ≥ X(1 − log log X/log X)` and `X = n²`, the condition
  holds for `n ≥ 14`. Python: the sufficient condition fails only for `n ≤ 13`.
- **Check (exact, done).** Every `3 ≤ n ≤ 19999` passes. The smallest margin is 0.170, at `n = 3`.
- **Lean.** As A1. Effort S. Part (ii) of the same comment, a prime in `[π(n²), π((n+1)²)]`, is
  rejected below.

### A3. Sun Conjecture 3.25: for `n > 6` there is a prime `q < n` with `q·n` a primitive root mod `p_n` · M–L · RH-consequence (new deduction)

- **Source.** arXiv:1402.6641 Conj. 3.25 (first part), which the abstract singles out. OEIS A243164
  ("Conjecture: (i) a(n) > 0 for all n > 6"). Sun verified it for `n ≤ 2·10⁵`. Not in
  formal-conjectures.
- **Premise.** GRH bounds in Lean: erdos-985 `bach_nonprincipal_of_GRH`,
  `bach_principal_of_GRH`, and the indicator bound of `Erdos985/Indicator.lean`.
- **Deduction (mine).** Let `P = p_n`. Then `q·n ∈ G` (the primitive roots) iff `q ∈ n⁻¹G`, and
  `1_G(qn) = θ Σ_{d | P−1} μ(d)/φ(d) Σ_{ord χ = d} χ(q)χ(n)`. Since `|χ(n)| = 1`, erdos-985's
  inequality goes through unchanged with search length `x = n` (`≈ P/log P`) in place of `x = P`.
  A counterexample forces
  `x/2 − √x/20 − 3 − 1.5√x ≤ (2^ω − 1)·bachC(P, x)·√x·log P`. The term `1.5√x` (from
  `ψ − θ ≤ 1.43√x`) removes prime powers: here `q^k n ∈ G` does not imply `q n ∈ G`, unlike in
  erdos-985.
- **Threshold (sieve-free model, Lean's `bachC`).** For each `ω = ω(P−1)`, the analytic bound
  holds from these values of `P` on:

  | ω | ≤ 6 | 7 | 8 | 9 | 10 | ≥ 11 |
  |---|---|---|---|---|---|---|
  | holds from | 4.7·10⁷ | 2.5·10⁸ | 1.25·10⁹ | 6.2·10⁹ | 3.0·10¹⁰ | every `P` with that ω |

  The finite check is every prime below `4.7·10⁷` (2.8·10⁶ primes), plus the primes below
  `3·10¹⁰` with `ω(P−1) ≥ 7`. That is a few percent of `1.3·10⁹` primes, which have to be
  enumerated. Adding the McGown–Treviño–Trudgian sieve that grosswald-grh already runs should
  bring this down to about erdos-985's `10⁸` *(not computed)*.
- **Check (done).** No counterexample for any `n ≥ 7` with `p_n ≤ 10⁸` (5.76·10⁶ primes). The least
  admissible `q` never exceeds 211.
- **Missing Lean.** Reuse erdos-985's indicator with a twist `χ(n)`, the prime-power correction
  `ψ − θ ≤ c√x`, the per-ω numerics, and the `n = π(P)` bookkeeping (`n ≥ P/log P`). The checker is
  erdos-985's with `g = q·n mod P`. Effort M with the sieve-free range, L to bring it down to `10⁸`.
- **Catch.** The second half of Conj. 3.25 (`q(n − q)` a primitive root) is binary and is rejected.

### A4. Hassani 2013: `A_n/G_n` strictly decreasing for `n ≥ 226` · deduction S, Lean L (tier H) · RH-consequence (new deduction)

- **Source.** M. Hassani, IJNT 9 (2013) 1593–1603. Here `A_n` and `G_n` are the arithmetic and
  geometric means of `p_1, …, p_n`. Axler (Mediterr. J. Math. 15 (2018), arXiv:1609.07934, final
  remark) writes: "One of the conjectures … stated by Hassani is still open, namely that the
  sequence (A_n/G_n) is strictly decreasing for every n ≥ 226."
- **Deduction (mine).** Write `x = p_n`, `L = log x`, `p = p_{n+1}`. The step condition is
  `(n+1)·log(1 + u/(n+1)) < v`, with `u = p/A_n − 1` and `v = log p − log G_n`. The expansions
  (`π ≈ li`, `Σ_{p ≤ x} p ≈ li(x²)`, `θ ≈ x`) give `u = 1 + 1/L + 2.5/L² + 8.75/L³ + …` and
  `v = D(n) = 1 + 1/L + 3/L² + 13/L³ + …`. So the margin is about `0.5/L² + 4.25/L³`, which
  matches the computed margins. A gap `g` costs `g/x`, and under RH `g ≤ (22/25)√x L` (cramer-rh).
  The Schoenfeld errors in `θ`, `π` and `Σp` move the margin by at most about
  `(2L³ + 6.7L²)/(8π√x)`, so RH closes the inequality for `x ≳ 3·10¹³` (crude, with no
  cancellation used).
- **Check (done).** No failure for `226 ≤ n`, `p_n ≤ 10⁹`. The smallest `margin·L³` is 0.64, at
  `p = 1429`; at `10⁸`, `margin·L² = 0.88`.
- **Why RH.** An unconditional route needs `|θ(x) − x| ≲ 0.1·x/L³`. The known explicit bounds of
  that strength hold only for astronomically large `x`, which is the same obstruction that leaves
  Axler's Conj. 3.4 open.
- **Lean.** The range to about `3·10¹³` is an external sieve computation (`Σp` and `Σ log p` to
  `3·10¹³`, CPU-hours), so it enters as a `VerifiedUpTo` hypothesis, as in robin-rh. A sharper
  error analysis would lower the threshold *(not attempted)*.

### A5. Axler Conjecture 3.4: `log p_n − θ(p_n)/n > 1 + 1/log p_n + 3/log² p_n` for every `n ≥ 264` · deduction S, Lean XL/tier H · RH-consequence

- **Source.** Axler, arXiv:1609.07934, Conj. 3.4. His Corollary 3.3 proves it unconditionally for
  `264 ≤ n ≤ π(10¹⁹)` (using Büthe's `θ(x) < x` for `x ≤ 10¹⁹`) and for `n > π(e^{89243})`.
- **Deduction (mine).** The slack is `13/L³`, while the RH error in `D` is at most about
  `2L³/(8π√x)`, so RH settles every `p_n ≥ 5·10¹³`, and in particular everything beyond `10¹⁹`. With
  Axler's Corollary 3.3, RH implies the conjecture.
- **Check (done).** No failure for `n ≥ 264`, `p_n ≤ 4·10⁸`. The smallest `(D − rhs)·L³` is 1.31, at
  `p = 1699`.
- **Lean.** The finite range is not replayable, so it enters as Axler's computation, a cited
  hypothesis. **Novelty caveat:** arXiv:2611.32537 (posted 2026-11-24) studies exactly
  `D(p_n) = log(p_n/G_n)` under RH. It cites Axler but not Conj. 3.4 (grep of the full text). This
  corner is active; search again before any announcement.

## Class B (the conditional result is published, or the statement is a one-line corollary of a published RH theorem)

- **Kotnik 2008, Conjectures 2 and 3.** These are `−(2/5)x^{3/2} < ∫₂^x(π − li) < 0`,
  `|∫(π − li + ½li(√u))| < x^{3/2}/5` and `|∫(π − R)| < x^{3/2}/5` for all `x ≥ 2`, together with
  the absolute comparisons of Conj. 2 *(the absolute-value bars are lost in the text extraction;
  unverified)*. The upper half of 3(a) is Johnston's RH-equivalence (arXiv:2201.06184). Axler,
  arXiv:2203.09290 Cor. 1.3, gives explicit two-sided RH bounds
  `−(2/3 + 0.046)x^{3/2}/log x < ∫ < −(2/3 − 0.046)x^{3/2}/log x` beyond explicit ranges. The lower
  bound of 3(a) follows in one line (with Kotnik's computation to `10¹⁴`), and so do 3(b), 3(c)
  and Conj. 2. These statements are RH-equivalent (Landau). Nobody states them as proved. In Lean,
  erdos-985's `bach_principal_of_GRH` already gives `|∫₀^x(ψ − t)| ≤ x^{3/2}/20 + 3x`; partial
  summation would then give the bounds from `x` around `10²`–`10⁴` *(estimate)*. Effort M. This is
  low novelty.
- **OEIS A223942** ("least prime `q` with `Φ_p` irreducible mod `q` is `≤ √(7p)`"): that `q` is the
  least prime primitive root, so the bound follows from MTT 2016 (`ĝ < √p − 2` for `p > 2791`) plus
  a check. This is the same gap as `novel-via-rh` B1: Lean has `g`, not `ĝ`.
- **Second Hardy–Littlewood for `y ≥ c√x log² x`:** published under RH (arXiv:2503.02766 Cor. 1.2;
  Axler arXiv:1909.12625 Thm 1.5).
- **Sondow–Nicholson–Noe Conj. 1** (Ramanujan primes, OEIS A190413): settled by Axler, Funct.
  Approx. 63 (2020), except `(38, 9)`.

## Rejected (in the edges file)

Firoozbakht-type `n`-th-root monotonicity for `p_{p_n}` (A006450), twin primes, practical and
squarefree numbers, primes in progressions, and Sun 1208.2683 Conj. 2.2–2.6 and 2.12 all need gaps
below `log² p`. So does Ordowski's `log log p_{n+1} − log log p_n < 1/n` (fc `OEIS/40.lean`).
Sun's prime in `[π(n²), π((n+1)²)]` needs a prime in an interval of length about `2√X/√log X`. A
prime in `(S_n, S_{n+1})` needs one in an interval shorter than `√x log x` by a factor of
`√log n`. Ordowski's `a(n) < n²` for A034694 would need `p < n²`, while Bach–Sorenson gives
`2(φ(n) log n)²`. Sun's primitive roots of special shapes (`k²+1`, `k(k+1)`, triangular,
partition, Fibonacci and Lucas numbers, sums of primes, `2^q − 1`, `q!`, `B_{q−1}`, Bell, `5^k+10^m`)
are Weil-type or worse. The Artin-type ones (A242748, A243755, A291615) need GRH for Kummer fields.
A243847 and A291690 (one root for two moduli) are GRH-reachable in principle, but
`2^{ω₁+ω₂}` pushes the sieve-free threshold to `10¹⁴` or more. Sun's power-sum Conj. 2.1
(arXiv:1208.2683) is open but is not an RH question: Dusart-type bounds suffice for each fixed
`α`, and the obstacle is uniformity in real `α`. Kotnik's `|π − li| < √x` is not decided by RH.
Axler 2024's lower bound (1.5) for `N_k/φ(N_k)` is not posed as a conjecture; its RH form is his
Theorem 1.3.

## Novelty search, line by line (2026-11-26)

| Where | Queries | Found |
|---|---|---|
| OEIS (JSON API) | Sun + "strictly decreasing" + pi; Sun + `pi(` + "for all n >"; Sun + `prime(n)`; Sun + "primitive root" (64 entries); Sun + "quadratic (non)residue" (53); entries A002233, A001918, A223942, A243164, A243847, A053760, A034693/4, A038107, A238165, A007053, A007504 | the conjectures as quoted; no comment claims a proof of A238165(ii), A038107(i) or A243164 |
| arXiv / web (Exa ×8, WebSearch ×2) | Sun Conj 2.1; Sun 2.7/2.14 monotonicity; A243164; Ramanujan-prime conjectures; Hassani `A_n/G_n`; Axler Conj 3.4; Kotnik Conj 3 | Sun–Zhao arXiv:2004.01080 (concerns Conj 2.1 on `π(kn)` prime, not 2.7); Axler 2018/2022; Johnston 2022; arXiv:2611.32537 (`D(p_n)` under RH, no mention of 3.4 or Hassani); nothing proving A1–A5 |
| Sun's papers (full text) | arXiv:1208.2683, 1402.6641, 1405.0290, 1209.3729; NMBRTHRY post of 2015-10-19 | read for prime conjectures; statements as above |
| Zenodo (via Exa) | quasi-RH corollaries of Sun/Hassani/Axler conjectures | only the dr vengy notes (Vinogradov, `g*(p)`); nothing on A1–A5 |
| formal-conjectures | clone `9097e2f` grep `Hassani`, `Kotnik`, `Axler`, `238165`, `243164`; `gh pr list --state all --search` for 238165, 38107, 243164, Kotnik, Axler, "arithmetic and geometric means", "pi(k*n)" | no statement and no PR for any candidate (`OEIS/38107.lean` exists but carries Legendre, not Sun's (i)) |
| 1337isnot1337/solved-conjectures | clone `43152d5` grep Hassani/Axler/Kotnik/OEIS numbers | nothing relevant |
| GitHub code search (incl. openai/math) | `A243164`, `A238165`, "Hassani A_n/G_n", "pi(k*n)^(1/k)", "primitive root modulo prime(n)" | OEIS mirrors and an unrelated OEIS-counterexample hunt (Kuberwastaken/c5-k4, touches A239957 only) |
| MathOverflow | not searched separately (Exa results include MO; none relevant) | — |

## Not searched or not checked

- **Guy, UPINT sections A, B, F:** I had no machine-readable text. Only entries reachable through
  OEIS cross-references (F9 via A002233) were covered. This is the biggest gap.
- **Sun's 2021 book (820 conjectures)** and the May 2026 Graz slides: not accessible or not read.
  Only the arXiv lists and the OEIS were swept.
- **A3:** the sieve-refined threshold (I only ran the sieve-free model) and whether the MTT sieve
  carries over with the twist `χ(n)`.
- **A4:** a sharp error analysis. `3·10¹³` is an upper estimate, and an exact RH threshold might be
  one or two orders lower.
- **Kotnik:** the exact form of Conjecture 2. The PDF text lost the absolute-value bars, and the
  Springer copy was not fetched.
- **A1/A2:** whether Mathlib at our pin has `π(x) ≥ x/log x` (not searched).
