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
