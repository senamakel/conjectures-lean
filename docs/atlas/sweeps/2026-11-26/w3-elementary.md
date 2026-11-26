# Lane `w3-elementary`: open statements with a short elementary proof

**Paused, incomplete (owner's instruction, 2026-11-26).** Research only; nothing built, no Lean
edited, nothing committed. **No class-A candidate was verified.** The lane did not reach its
target of ten. What follows is the triage done so far, the leads not yet checked, and what was
not reached.

## Setup

- formal-conjectures clone at `9097e2f`: 1,102 `research open` declarations outside
  `ErdosProblems/` (OEIS 394). I read every OEIS statement and the smallest 191 from `Paper`,
  `Arxiv`, `Mathoverflow`, `Other`, `Books`, `Kourovka`, `LittProblems` and `WrittenOnTheWallII`.
- Prior art loaded: fc open PRs (933, with their touched files), and Epoch AI's OEIS Open results
  (`epoch-research/LeanOpenProblems-results`, sparse clone of every `metadata.json`). Epoch settled
  155 OEIS A-numbers, 107 proved and 60 disproved, out of the 492 conjectures in its benchmark.
  These include exactly the shapes this lane targets: Bala supercongruences (A333096, A357565,
  A357674, A361883, A364173, A364176, A141057), Sun's distinct-fractional-parts conjecture for the
  Catalan numbers (A000108), conjectured recurrences and g.f.s, and integrality and parity claims.
  **This ground has been worked over by frontier models already.** Of fc's 394 OEIS open
  declarations, 69 have an Epoch settlement for the same A-number and 41 are touched by an open fc
  PR, leaving 301. Epoch's statements are Tsoukalas's and may differ from fc's; see
  `disproof-fc-other.md`.
- OEIS: the web API is blocked for this IP (rate limit). Full local copy of `oeis/oeisdata`
  (shallow clone, `~/.cache/w3elem/oeisdata`, outside the repos) with a grep index of the
  `%C/%F/%N` lines (3.1M lines).
- Read and skipped: `disproof-erdos.md`, `disproof-fc-other.md`, `novel-oeis-lists.md` (A038107(i),
  A238165(ii), A243164, Hassani and Axler are taken there).

## Leads not yet verified (each needs numerics and a novelty search before it counts)

1. **A262439 (Sun, 2015), half of part (i):** `π(1+n(n+1)/2)^{1/n} > π(1+(n+1)(n+2)/2)^{1/(n+1)}`
   for every `n ≥ 3`. It has the same shape as A038107(i), which was proved elementary in PR #23.
   The deduction is to bound the increment by the count of integers coprime to 6 in an interval of
   length `n+1`, then use `π(X) log π(X) ≥ X(1 − log log X/log X)`. The first half of (i)
   (strictly increasing) needs a prime in every interval of length about `√(2X)`, so it is
   Legendre-strength and is not claimed. **Not checked numerically, novelty not searched.**
   Most promising; effort S.
2. **Sun's ratio-monotonicity conjectures** for P-recursive binomial sums: A180364, A245769,
   A246065(i), A246138, A246512, A246567(ii), A246875, A295112. They claim `a(n+1)/a(n)` is
   monotone and `a(n+1)^{1/(n+1)}/a(n)^{1/n}` is monotone. The method is standard but not short
   (Chen–Guo–Wang; Hou–Zhang's asymptotic r-log-convexity). Several of these are likely proved in
   that literature: probably class B/C until searched. Effort M each.
3. **A002618 (Sun):** interval sums of `1/(iφ(i))` have distinct fractional parts. This is the
   sibling of the A000108 statement that Epoch proved. No p-adic uniqueness argument found yet.

## Triaged and rejected (reason)

- **A135508** (`x(n) = 2x(n−1) + lcm(x(n−1), n)`, McEachen 2025). Reduction found: for prime `p`,
  `a(p−1) = p` iff `gcd(x(p−3), p−2) > 1`. The conjecture then needs every odd composite `m` to
  share a prime with `x(m−1)`, which needs a bound on the first index where a prime `q` divides
  `x`. Computed for `q < 20000/3`: the first index is always `jq − 2` with `j ≤ 29`, and 911, 937,
  … do not divide `x(n)` for any `n ≤ 20000`. No counterexample for `p < 20000` (agrees with
  `disproof-fc-other`). There is no structural reason behind the bound, so no elementary proof.
- **A245212** (`a(n) = σ(n)` iff `n` is a power of 2). Reduced to: odd `m > 1` with
  `(mτ(m) − σ(m))/(F(m) − mτ(m)) = (a2^{a+1}+1)/(2^{a+1}−1)`, where `F(m) = Σ_{d∣m} dτ(d)`. This
  rules out `m` prime. The general case is a coincidence-type Diophantine condition with no proof
  found. Not checked numerically beyond hand cases.
- **A63880** (`σ = 2·usigma` ⇒ `n ≡ 108 mod 216`). The 2-adic bookkeeping is consistent; the
  equation is multiperfect-like (odd solutions not excluded). Hard.
- **A67720, A56777.** Coincidence equations in `φ`, `σ`. Hard.
- **A80101** (at most 2 prime powers between consecutive primes). Needs a prime between
  consecutive prime squares, `(x, x+4√x)`: not reachable even under RH.
- **A87207, A111114, A2326** (equivalent to "no `p³ ∣ 2^{p−1}−1`"), **A4290, A1157, A38107**
  (π(n²) fractional parts), **A262408(ii)** (FLT for π: heuristically finite, not provable).
  Rejected as hard.
- **Kourovka 20.51** (an odd-order non-abelian group with `t` classes for each odd `t > 3`).
  Frobenius groups `C_q ⋊ C_d` give `t = d + (q−1)/d`, and direct products handle composite `t`.
  Prime `t` reduces to a Goldbach-type condition (`de+1` a prime power with `d+e = t`). Not
  elementary as it stands.
- **A234246(ii), A236998(iii)** (squares from `k + φ(n−k)`, `kφ(n−k)`). These reduce to cototient
  or squarefree-kernel representations of Goldbach type.
- The bulk of the remaining OEIS open statements are Sun's additive "a(n) > 0" representation
  conjectures (Goldbach-type) and Bala/Sun supercongruences modulo `p³` or higher. Neither is
  short or elementary.

## Not reached

- The OEIS "Conjecture" corpus beyond grep sampling: 7,054 `%F` lines contain "Conjecture",
  including 48 of Mathar's "Conjecture: D-finite with recurrence" (provable by creative telescoping
  when the sequence is a binomial sum) and 290 Bala comment/formula lines. These are the most
  promising untouched ground, since Epoch's set covered only 492.
- Novelty searches (arXiv, MathOverflow, Zenodo, fc PRs by keyword, 1337 clone, openai/math,
  GitHub code search) for any lead above.
- fc `Wikipedia/` and `GreensOpenProblems/` were not sampled.
- Fonollosa's `Arxiv/2607.08366` MinModulus, `Arxiv/2501.03234` S(k) > 0 and
  `Paper/CatchUpConjecture` were flagged as small and recent, but their definitions were not read.
