# Plan: Sun's Conjecture 3.25 (A243164) under GRH

The feasibility study is `docs/scoping/sun-a243164-primitive-roots.md` at the repository root
(thresholds, finite-range size, novelty search). This file tracks the Lean work.

## Status (2026-11-26)

| File | Content | Status |
|---|---|---|
| `Statement.lean` | `SunA243164Statement` | done |
| `Assembly.lean` | `GoodPrime`, `GoodFrom`, `VerifiedBelow`, `sunA243164_of_goodFrom_of_verified`, `primeCounting_nthPrime` | done |
| `PrimePowers.lean` | `Epp`, `Epp_le_psi_sub_theta`, `Epp_le` (`≤ log 4 (√x + ⌊log₂ x⌋ x^{1/3})`) | done |
| `TwistedSieve.lean` | `principal_le_sieve_twisted` (MTT Theorem 3 twisted by a unit, with `Epp`) | done |
| `Analytic.lean` | `SieveIneq`, `SieveNumerics`, `not_sieveIneq_of_GRH`, `goodFrom_of_GRH` | done |
| `Compute/Checker.lean`, `Compute/ChunkNN.lean`, `Compute.lean` | `countFrom_sound`, `verifiedBelow_10_8` (20 `native_decide`) | done |
| `Main.lean` | `sunA243164_of_GRH_of_numerics` | done |
| `Numerics.lean` | `sieveNumerics_10_8 : SieveNumerics 100000000` | **to do** |

Once `Numerics.lean` exists, `Main.lean` gets `sunA243164_of_GRH : DirichletLNonvanishingRightOfHalf →
SunA243164Statement` and `Unconditional/` drops the `hnum` argument.

## What `Numerics.lean` has to prove

For every prime `P ≥ 10^8` find `S ⊆ F = (P−1).primeFactors` with `δ_S > 0` and

```
Epp x < δ_S θ_{F∖S} (x/2 − √x/20 − 3 − K_S · bachC(P, x) √x log P),   x = π(P).
```

Inputs, all proved: `Chebyshev.pi_ge_of_four_le` (`x ≥ P log 2 / log P`), `x < P`
(`primeCounting_lt_self`), `Sieve.Epp_le`.

Choice of `S` (from the scoping computation): `E = F ∖ S` = the two smallest prime factors of
`P − 1` (all of them if `ω ≤ 2`), `S` the rest. Worst case for a given `ω = |F|`: the `i`-th
smallest prime factor is at least the `i`-th prime, so `θ_E ≥ (1/2)(2/3) = 1/3` and
`δ_S ≥ 1 − Σ_{3 ≤ i ≤ ω} 1/p_i`; also `P ≥ 1 + p_1 ⋯ p_ω`. Port grosswald-grh's
`Grosswald.Alg.LOk_spec`, `dominates`, `Grosswald.Combi.prod_le_prod_of_dominates` (without its
`10^13 < p` in `InClass`).

Cases and relative margins (computed with exactly these bounds, `docs/scoping`):

| Case | Range | margin at the worst point |
|---|---|---|
| `ω ≤ 8` | `P ≥ 10^8` | 14% (`ω = 8`, `P = 10^8`) |
| `ω = 9, 10, 11` | `P ≥ 1 + p_1⋯p_ω` | 20%, 77%, 94% |
| `ω ≥ 12` | `P ≥ 7.4·10^12` | 59% at `ω = 12` with no sieve (`S = ∅`), 98% at `ω = 15` |

For `ω ≤ 11` a rational checker in the style of `Grosswald.Crit.crit_sound` (tangent bounds for
`log`, a lower bound `Y0` for `√x`) evaluated by `decide` or `norm_num` per `ω`. Monotonicity in
`P` comes for free if the check is phrased as "for every `y ≥ Y0`" as in `Grosswald.Crit.core`.
For `ω ≥ 12`, bound `2^ω` through `Erdos985.pow_card_primeFactors_mul_le` with a larger base
(the margin is large there), as erdos-985's `ω ≥ 10` case does.

## Finite range: measured

`Compute.ChunkNN` evaluates `countFrom (N·5·10^6) (5·10^6) π(N·5·10^6 − 1)` with `native_decide`.
Chunk 19 (`[9.5·10^7, 10^8)`): 96 s CPU, 6.5 GB peak RSS, on the shared box under load ~140.
Twenty chunks, about 30 CPU-minutes. Build at most four at a time (RAM).

Primality inside the checker is exact: for odd `m` passing the base-2 Fermat test, the search
for `q` is itself a Lucas certificate (`(qn)^{m−1} ≡ 1`, `(qn)^{(m−1)/r} ≢ 1`, Mathlib's
`lucas_primality`), so `Nat.minFac` runs only on base-2 pseudoprimes and the six primes of
index `≤ 6`.
