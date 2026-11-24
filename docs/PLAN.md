# Plan: Grosswald's conjecture under GRH in Lean

Source: K. McGown, E. Treviño, T. Trudgian, *Resolving Grosswald's conjecture on GRH*,
arXiv:1508.05182 (MTT below). Targets: `Grosswald/Statement.lean` (fixed).

Throughout, `x := Nat.sqrt p - 2` (a natural number). If a prime `q < x` is a primitive root,
then `q ≤ Nat.sqrt p - 3 < √p - 2`, so it witnesses `HasSmallPrimePrimitiveRoot p`.

## Map from MTT to Lean

| MTT | Lean | Notes |
|---|---|---|
| Lemma 1 (Bach) | `Erdos985.Analytic.bach_nonprincipal_of_GRH`, `bach_principal_of_GRH` | `bachC p x` is literally MTT's `c(p,x)` (with `x^{3/2}` as `rpow`); stated for every natural `x ≥ 1`, so `x ≈ √p` is fine. |
| Theorem 2 | special case `S = ∅` of the sieve | |
| Theorem 3 (sieve) | `Grosswald/Sieve.lean`: `principal_le_sieve` | Re-derived in the form `S₀ ≤ (2^{n-s}(2+(s-1)/δ) - 1)·B` for any set `S` of prime factors of `p-1` with `δ = 1 - Σ_{ℓ∈S} 1/ℓ > 0` (no parity condition needed). Uses `Erdos985.Indicator.W`/`norm_W_le`. |
| Theorem 3 + Lemma 1 at `x = ⌊√p⌋-2` | `Grosswald/Analytic.lean`: `not_sieveIneq_of_GRH` | If `p > 2.5·10^15` has no small prime primitive root, then for every admissible `S` the inequality `SieveIneq ω s δ p` fails. |
| Robin's ω bound / Corollary 2 | `Grosswald/Tail.lean` | Replaced by `256^ω · ∏_{r<256} r ≤ (p-1)·256^{54}` (`Erdos985.pow_card_primeFactors_mul_le`), giving `2^ω ≤ 4520·p^{1/8}`, which closes every `p ≥ 10^47` with `S = ∅`. For `p < 10^47` one gets `ω(p-1) ≤ 30` from a primorial bound. |
| "Choose p large enough so that …" | `Grosswald/Crit.lean`: `crit K Y0 : Bool` + `crit_sound` | A rational, executable sufficient condition. Uses `log y ≤ log a + y/a - 1` (tangent line, `a = 2^m(1+u)`), `log 2 < 0.6931471808`, and the alternating `log(1+u)` series with remainder (`Real.abs_log_sub_add_sum_range_le`). |
| Corollary 4 + Algorithm 1 | `Grosswald/Alg.lean`: `checkNode` + `checkNode_sound` | One recursive checker for every `n = ω(p-1) ∈ [1, 30]`. A node `(n, X, Y)` covers primes with `X ⊆ pf(p-1)`, `Y ∩ pf(p-1) = ∅`. Lower bound `1 + ∏L` (L = first n primes not in Y), upper bound from the sieve with `M` = the `s` largest elements of `L`. For `n ∉ {12,13,14}` the root node closes immediately (= Corollary 4). |
| exceptions list + "find ĝ directly" | leaves of `checkNode` | Every `p = k·∏X + 1` in `[lower, upper)` is checked: some `q ∈ Y` divides `k`, or `ω(p-1) ≠ n`, or base-2 Fermat fails, or a prime `q < ⌊√p⌋-2` passes the Lucas test against the factor list `X ∪ pf(k)`, or `minFac p ≠ p`. |
| Proof of Theorem 1 | `Grosswald/Main.lean` | `prime_primitive_root_of_GRH_large`, `grosswald_of_GRH`. |
| range `409 < p ≤ 2.5·10^15` | hypothesis `VerifiedUpTo 2500000000000000` | not computed (about 7·10^13 primes). |

## Soundness of the sieve choices (no order statistics)

`L` is checked to be *downward closed among primes outside `Y`*: every prime `q ∉ Y`, `q ∉ L`
exceeds every element of `L`. Write `F = pf(p-1)`, `|F| = |L| = n`, `F ∩ Y = ∅`.

* Lower bound: elements of `F \ L` exceed all of `L \ F` and the two sets have the same size, so
  `∏F ≥ ∏L` and `p ≥ 1 + ∏L`.
* Upper bound: split `L = L₀ ++ M`, `|M| = s`. Pick any `S ⊆ F \ L₀` with `|S| = s` (possible as
  `|F ∩ L₀| ≤ n - s`). Elements of `S \ M` are not in `L`, so they exceed all of `M \ S`; hence
  `Σ_S 1/ℓ ≤ Σ_M 1/q`, `δ_S ≥ δ_M`, and the sieve constant for `S` is at most that for `M`.

## Computation

Python prototype (`scripts/`) of Algorithm 1 with our constants: n = 12, 13, 14 need splitting
(25 / 169 / 19 nodes), about 1.5·10^7 candidates in total. These run under `native_decide`,
chunked per `n` (and per subtree where needed), in `Grosswald/Run/`.

## Can the range below `2.5·10^15` be computed here? (sized 2026-11-24)

Goal: drop the hypothesis `VerifiedUpTo 2500000000000000` by lowering the threshold `LOW` of
Algorithm 1 to some `T` and checking `409 < p ≤ T` directly under `native_decide`. Numbers
below come from `scripts/uncovered.c` (exact factorisation of `p - 1`, best sieve set `S`),
`scripts/tree_low.py` and a C port of it (same counts at `2.5·10^15`, `10^15`, `3·10^14`), and
`native_decide` timings on this box.

**Where `2.5·10^15` comes from.** It is not produced by the analytic argument; it is the end of
the Cohen–Oliveira e Silva–Trudgian computation, and MTT start there ("we may assume
`p ≥ 2.5·10^15`", proof of their Corollary 2). MTT's Theorem 1 for `p > 409` uses that
computation; there is no GRH-only threshold near `10^10` in the paper. The analytic side needs
`K · c(p,x) √x log p < x/2 - √x/20 - 3` with `x ≈ √p`, i.e. roughly `p^{1/4} > (4/3) K log p`,
where `K = 2^{n-s}(2 + (s-1)/δ) - 1` is the sieve constant. The prime 2 always divides `p - 1`
and cannot be sieved, so `K ≥ 3`, and `K` grows like `2^{n-s}` in `n = ω(p - 1)`. Root-node
thresholds (first `n` primes, best `s`): `n = 4: 4.5·10^10`, `5: 4.2·10^11`, `6: 2.6·10^12`,
`7: 1.2·10^13`, `8: 5.0·10^13`, `9: 1.7·10^14`, `10: 5.1·10^14`, `11: 1.5·10^15`,
`12: 3.8·10^15`, `13: 8.5·10^15`.

**Primes the sieve cannot cover, even with perfect knowledge of `p - 1`.** Fraction of primes
near `x` for which no admissible `S ⊆ pf(p-1)` satisfies the inequality (2·10^6-wide samples):

| x | 10^8 | 10^9 | 10^10 | 10^11 | 10^12 | 10^13 | 10^14 | 10^15 |
|---|---|---|---|---|---|---|---|---|
| uncovered | 92% | 75% | 42% | 17% | 2.7% | 0.13% | 0.002% | 0 |

Integrated: about `6.2·10^9` primes in `(409, 2.5·10^15)` need an explicit primitive root
whatever the case split (`1.2·10^9` of them in `[3·10^11, 10^12]`, `1.1·10^9` in
`[10^12, 3·10^12]`). That is a floor for any checker built on this sieve.

**Algorithm 1 with a lower `LOW`** (enumerated `k`, split limit `LIM`):

| LOW | LIM 10^6 | LIM 10^7 | LIM 10^8 |
|---|---|---|---|
| 2.5·10^15 | 1.5·10^7 | | |
| 10^15 | 5.1·10^7 | | |
| 3·10^14 | 3.5·10^8 | | 6.0·10^9 |
| 10^14 | | 5.3·10^9 | 1.9·10^10 |
| 10^13 | | | 1.1·10^11 |

Below `10^13` the tree does not terminate in reasonable time for `n ≤ 6`: the lower bound
`1 + ∏L` stays far below `LOW` while the `Y` branch keeps splitting.

**Cost per prime in Lean.** The current leaves cost about `30 µs` per enumerated `k` (1.5·10^7
`k` in about 460 CPU-s). One `Erdos985.Compute.powMod` at `p ≈ 10^12` costs about `16 µs` under
`native_decide` (2·10^6 Fermat tests in 29 CPU-s); the same test in C with 128-bit
arithmetic is about `0.3 µs`, and a segmented sieve plus Lucas search over all primes near
`10^12` costs about `3 µs` per prime in C.

**Verdict.** No `(T, checker)` pair fits a budget of about one CPU-day (`8.6·10^4` s):

* The floor alone, `6.2·10^9` primes at one `powMod` each, is `1.0·10^5` CPU-s in Lean; a
  Lucas certificate needs `ω(p-1) + 1` to `~6` of them per prime, so realistically
  `4–6·10^5` CPU-s, before paying anything to *find* those primes.
* Finding them: below `T` every prime must be visited (`π(10^11) = 4.1·10^9`,
  `π(10^12) = 3.8·10^10`, `π(10^13) = 3.5·10^11`); above `T` Algorithm 1 enumerates
  `≥ 1.1·10^11` candidates already at `T = 10^13` (`3·10^6` CPU-s at 30 µs).
* Best split found: `T ≈ 10^12` gives at least `3.8·10^10 + ~3·10^9` primes to certify, about
  `6·10^5` CPU-s at a single `powMod` per prime and several times that in practice, i.e.
  10–100 CPU-days, plus a proved-sound segmented sieve (primality of `p` and complete
  factorisation of `p - 1`) that does not exist yet.

What would have to change: a native-speed verified checker (≈50× faster `powMod`, e.g. a
`UInt64` Montgomery multiplication with a correctness proof, run as compiled code) *and* a
proved segmented sieve would bring the floor to roughly the C figures (`~5` CPU-hours for the
`6.2·10^9` uncovered primes, `~1–2` CPU-days for all primes below `10^12`); a sharper explicit
formula (smaller `c(p,x)`, as for Bach's constant in ankeny-grh) would shrink the uncovered set.
Neither is in scope here.

The cheapest real improvement is lowering `LOW` to `3·10^14` (`3.5·10^8` candidates, about
three CPU-hours at the current speed). That proves the GRH part for `p > 3·10^14`, but the
hypothesis would still be `VerifiedUpTo 300000000000000` (about `9·10^12` primes), so the
tier stays C + H. It has not been done.
