# Lane `w3-small-prime-mod-p` (wave 3): small primes with a multiplicative property mod p

**Status: paused, incomplete** (stopped on the owner's instruction, 2026-11-26). Research only. Nothing
was built and no Lean file was edited. Numbers come from Python `-I` scripts kept in the session
scratchpad (`w3scripts/`), not in the repo. Edges are in `w3-small-prime-mod-p.edges.jsonl`.

## Summary

- **One class-A candidate: Sun's "Bertrand with Legendre symbols" conjecture** (arXiv:1211.1588
  Conj. 3.33 in v29, Conj. 2.9 in v27, 2012; MathOverflow 332147, 2019, no answers; OEIS A185150
  comment (3)). The condition is one quadratic character of conductor at most `8n`, and the search
  range is `(n, 2n)`. So the search length is about the modulus: the erdos-985 regime, with ratio 1
  instead of `2^ω`. A tent-weighted combination of three erdos-985 `bachSum`s closes the
  inequality from about `n ≈ 8·10⁴` (or `3·10⁵` with a crude bound on prime powers). I checked it
  numerically for every `n ≤ 10⁷`: the exceptions are exactly Sun's.
- One class-B item: Knapp–Köcher–Schmid 2012, least odd prime QR `ϱ_p < √p` except for 8 primes.
  ERH ⇒ no further exception is in their paper. Our GRH closes it with a check below about `3·10⁵`.
- Everything else on this ground is rejected. In each case the condition is not a coset condition
  in `q`, or the search length is only about √modulus (the Grosswald regime, sieve-free closing near
  `10³¹`), or the statement has two parameters.

## Class A

### A1. Sun Conj. 3.33: primes in `(n, 2n)` with a prescribed Legendre symbol · effort M · tier U possible

- **Statement** (arXiv:1211.1588v29, p. 17, read): "(i) For each integer n > 8 with n ≠ 14, there is
  a prime p between n and 2n with (n/p) = 1. If n ∈ Z⁺ is not a square, then there is a prime p
  between n and 2n with (n/p) = −1. (ii) For any integer n > 5 there is a prime p ∈ (n, 2n) with
  (2n/p) = 1. For any integer n > 6 there is a prime p ∈ (n, 2n) with (−n/p) = −1." Remark: verified
  for `n ≤ 5·10⁸`. On MathOverflow 332147 (2019-05-21) Sun writes "I don't know how to prove the
  conjecture". The StackExchange API on 2026-11-26 shows 0 answers and 0 comments.
- **Why it is open unconditionally.** `p ↦ (n/p)` is a real character of conductor up to `4n`, and
  `x = 2n` is comparable to the conductor. Without GRH, a Siegel zero would bias `χ(p)` toward −1
  up to well beyond `q`, so even the `+1` half is out of reach.
- **Deduction.**
  1. For odd `p ∤ n`, `(n/p) = χ_D(p)`, where `χ_D` is the Kronecker character of `Q(√n₀)` (`n₀`
     the squarefree part). It is primitive mod `|D| ≤ 4n` (`8n` for `2n`, `4n` for `−n`). It is
     non-trivial when `n` (respectively `2n`) is not a square; `−n` is never a square. A prime
     `p ∈ (n, 2n)` never divides `4n` or `8n`.
  2. Take the tent `f` supported on `[n, 2n]` with apex `y = n + ⌊0.36n⌋`:
     `f = A₁(n−m)₊ + A₂(y−m)₊ + A₃(2n−m)₊`, where `A₁ = 1/(y−n)`, `A₃ = 1/(2n−y)` and
     `A₂ = −A₁ − A₃`. Then `Σ Λ(m)χ(m)f(m) = Σ Aᵢxᵢ·bachSum(χ, xᵢ)`. Use
     `Weinberger.bach_primitive_of_GRH` for `χ_D` and `Erdos985.bach_principal_of_GRH` for the
     principal part. The principal part is `∫f = n/2` with error `Σ|Aᵢ|xᵢ(√xᵢ/20 + 3)`. The prime
     powers in `(n, 2n)` cost at most `ψ(2n) − θ(2n)`.
  3. A counterexample forces `n/4 ≤ E₀/2 + E_χ/2 + PP`. Computed: this fails, so no counterexample
     exists, for every `n ≥ 7.85·10⁴` (conductor `4n`) and every `n ≥ 8.76·10⁴` (conductor `8n`),
     using `ψ − θ ≤ 1.43√x`. With the crude elementary bound `PP ≤ (√(2n) + (2n)^{1/3} log₂ 2n)·log 2n`,
     the closing points are `n ≥ 2.8·10⁵` and `n ≥ 2.95·10⁵`. I scanned the margin: it stays
     positive above these points.
- **Finite range.** `n < 3·10⁵` for all four parts, with a witness prime per `n`. That is trivial
  (`native_decide`, or even `decide +kernel` with certificates).
- **Numerics (done).** Every `n ≤ 10⁷`, all four parts. The failures are exactly `n ∈ {1,2,3,5,6,7,8,14}`
  for (n/p) = 1, none for (n/p) = −1 with `n` not a square, `{1,5}` for (2n/p) = 1 and `{1,2,5,6}`
  for (−n/p) = −1. These match Sun's ranges. The most primes of `(n, 2n)` ever needed is 38.
- **Missing Lean.** (a) The character `p ↦ jacobiSym n p` as a `DirichletCharacter` mod `4n`
  (`jacobiSym.mul_right`, `jacobiSym.mod_right`), passed through `primitiveCharacter`. (b) It is
  non-trivial for non-square `n`, by an elementary CRT construction of an odd `b` with `J(n|b) = −1`.
  (c) The three-kernel tent identity for `bachSum`, and the numerics. (d) A checker for `n < 3·10⁵`.
  No new analysis is needed. Effort M.
- **Catch.** Once noticed, it is an easy application of GRH, so someone else may post it soon:
  search again before announcing. The statement is not in formal-conjectures (only A185150, the
  `(n², (n+1)²)` version, which is out of reach).
- **Novelty search (2026-11-26).**
  - arXiv/web: Exa ×3 and WebSearch (extended) ×1 for "prime in (n,2n) with Legendre symbol",
    "GRH Bertrand quadratic character", "Sun Conjecture 2.9/3.33". Only Sun's own papers and
    generic Bertrand material came back.
  - MathOverflow 332147: unanswered.
  - OEIS: 6 searches. There is no dedicated sequence; the statement appears only in the A185150
    comment.
  - Zenodo API: 6 queries, including the QRH/RH-corollary note series. Nothing relevant.
  - formal-conjectures: the clone at `9097e2f` has only `OEIS/185150.lean` (squares interval).
    `gh pr list --search` for Bertrand, "Legendre symbol", jacobiSym and 1211.1588 found nothing
    on this statement.
  - solved-conjectures clone `43152d5`: nothing.
  - openai/math: nothing (the hits for "bertrand" are unrelated tex).
  - GitHub code search ("jacobiSym Bertrand", "332147", …): nothing.

## Class B

- **B1. Knapp–Köcher–Schmid, Funct. Approx. 47 (2012).** `ϱ_p` is the least odd prime `≠ p` that is
  a quadratic residue mod `p`. They prove `ϱ_p < √p` for every `p ∉ {3,5,7,17,19,43,67,163}` except
  for at most one possible large prime (`p ≡ 7 mod 8`, `h(−p) > 100`), and they say this exception
  does not exist under ERH. Our deduction: `bach_primitive_of_GRH` with the Legendre character and
  `x = √p` gives roughly `p^{1/4} > (4/3)(log p + 5/3) + 6`, which holds from about `p ≈ 3·10⁵`.
  Check (done): every prime `p ≤ 10⁷` has exactly KKS's 8 exceptions, and the largest `ϱ_p/√p` for
  `p > 1000` is 0.65 (at `p = 2273`). Effort S. Since GRH ⇒ X is published, only the unconditional
  status is new. Their remark that `ϱ_p < p^c` holds for `p > β(c)` also follows for every `c > 0`
  with an explicit `β(c)`.

## Rejected (with reason)

- **Coset condition, but √-regime or two parameters (L/XL):**
  - A243847(i): a prime `q < p_n` that is a primitive root mod `p_n` and mod `p_{2n}`.
  - A243847(ii) / A291690 comment: a prime `q < p_n` that is a primitive root mod `p_n` and
    `p_{n+1}`, except `n = 1, 4, 8`.
  - In both, the search length is `p` against a modulus near `p²`. The error ratio is
    `2^{ω(p−1)+ω(p′−1)}`. Sieve-free, a given `Ω` holds from these points: `Ω=8` from `1.9·10⁸`,
    `16` from `3.2·10¹³`, `24` from `3.9·10¹⁸`, `32` from `4·10²³`. The worst case closes near
    `1.1·10³¹`. The finite check needs a tree search like grosswald-grh's, and `p′` is not
    controlled by the tree on `p − 1`.
  - Numerics: no failures for `p_n ≤ 2·10⁶` beyond the stated exceptions. The largest least `q`
    were 683 (A291690) and 859 (A243847).
  - Sun Conj. 4.1(i) (1405.0290; A291690): `g ≤ √(4pq+1)` for all pairs of primes. This has two
    parameters and is in the Grosswald regime on the modulus `pq`.
- **Not a coset condition in `q`:**
  - A234972, A235709, A235712, A236966: `2^q ± 1`. The condition is on `q` mod `ord_p(2)`, a
    progression to a modulus near `p`. With `x ≈ p` this needs `x ≫ φ(m)/δ·log⁴`, so it is beyond
    GRH unless `ord_p(2) ≤ √p/log² p`.
  - A242345 (`2^q − q`).
  - Factorial, Catalan, Bell, Bernoulli, Euler, tangent, harmonic, Franel and trinomial forms
    (A236306, A237112, A236308, A237594, A242210, A242222, Conj. 3.9–3.11).
  - Partition, Fibonacci, Lucas, `5^k + 10^m` and binomial-sum forms (A241504/16, A241568, A331506,
    A305048, A305030).
  - `k² ± 1`, `k(k+1)`, triangular (A239957, A241476, A241492, A239963).
  - Sun Conj. 4.17(i) (inverse of `k²` mod `p` is prime): a thin, non-subgroup set.
  - A344173/4: thin prime sets `x³ + 2y³`, `x⁴ + y²`.
- **Shifted or additive:** shifted primes `q ± 1` (`χ(q+a)` over primes is not controlled by GRH
  for Dirichlet L), A243403 `q(n−q)`, A229899/A229910 (already proved: Cohen et al.), Conj. 4.7
  (intervals anywhere, Pólya–Vinogradov barrier), Jarso–Trudgian.
- **Artin-type or varying modulus:** A291615 (`q` a primitive root mod `p_q`), A243755, A243837/9
  (published under GRH, Pan–Sun 2019), A242748/50, A261387, A332020, Conj. 4.5 (`φ(p−1)`).
- **Already taken today:** A243164 (Sun 3.25 first part), primitive roots mod `p²`, KMT, Cohen–Trudgian.
- **Looked at, nothing open of our shape:** Treviño and Norton least `k`-th power nonresidue
  (theorems, not conjectures); Benli–Pollack (prime `k`-th power residues, no explicit
  conjecture); Ambrose 2013 (unconditional theorem); formal-conjectures PR #7425 (simultaneous
  primitive roots, a different problem).

## Not reached

- Sun's 2021 book of 820 conjectures (not located).
- Guy's UPINT F8/F9 text (worked from memory only; no new statement).
- The OEIS listings past the first 100 results per query (the site requires sign-in). I read about
  120 Sun entries (primitive root, QR, QNR, Legendre, Jacobi) and about 80 non-Sun entries.
- The full texts of Kerr–McGown–Trudgian and Cohen–Trudgian (the earlier lane covered them).
- A second web engine pass on the B1 novelty.
- Lean-level constants: the thresholds above use the Lean `bach_primitive_of_GRH` and
  `bach_principal_of_GRH` inequalities, but the bound `ψ − θ ≤ 1.43√x` was not located in Lean.
