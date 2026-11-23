# Grosswald's conjecture under GRH in Lean

Grosswald (1981) conjectured that the least primitive root `g(p)` of every prime `p > 409`
satisfies `g(p) < √p - 2`. McGown, Treviño and Trudgian
([*Resolving Grosswald's conjecture on GRH*](https://arxiv.org/abs/1508.05182), MTT below)
proved it under the Generalized Riemann Hypothesis, building on the computation of Cohen,
Oliveira e Silva and Trudgian for `409 < p ≤ 2.5·10^15`.

This project proves in Lean:

```lean
-- Grosswald/Main.lean
theorem Grosswald.prime_primitive_root_of_GRH_large (hGRH : DirichletLNonvanishingRightOfHalf) :
    ∀ p : ℕ, p.Prime → 2500000000000000 < p → HasSmallPrimePrimitiveRoot p

theorem Grosswald.grosswald_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (hcomp : VerifiedUpTo 2500000000000000) : GrosswaldStatement
```

The statements and definitions are in `Grosswald/Statement.lean`. Two inputs are hypotheses:

* **GRH** for Dirichlet L-functions (`DirichletLNonvanishingRightOfHalf`, copied verbatim from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)),
* **the finite range** `409 < p ≤ 2.5·10^15` (`VerifiedUpTo 2500000000000000`), which is the
  Cohen–Oliveira e Silva–Trudgian computation (about `7·10^13` primes) and is not redone here.

There is no `sorry`. `#print axioms Grosswald.grosswald_of_GRH` gives

```
[propext, Classical.choice, Quot.sound,
 Grosswald.Run.first31_ok._native.native_decide.ax_1_1,
 Grosswald.Run.n12._native.native_decide.ax_1_1,
 Grosswald.Run.n13_A1._native.native_decide.ax_1_1,
 Grosswald.Run.n13_A2._native.native_decide.ax_1_1,
 Grosswald.Run.n13_B._native.native_decide.ax_1_1,
 Grosswald.Run.n13_C._native.native_decide.ax_1_1,
 Grosswald.Run.n13_D._native.native_decide.ax_1_1,
 Grosswald.Run.n13_small._native.native_decide.ax_1_1,
 Grosswald.Run.n14._native.native_decide.ax_1_1,
 Grosswald.Run.roots_ok._native.native_decide.ax_1_1]
```

The last ten are the trust assumptions of the ten `native_decide` evaluations in
`Grosswald/Run/`. Each one says that the compiled evaluation of a Boolean checker agrees with
its definition. The checker's soundness is proved without them.

## How the proof goes

Let `p > 2.5·10^15` have no prime primitive root `q < √p - 2`, and put `x = ⌊√p⌋ - 2`, so
no prime `q < x` is a primitive root.

1. **Bach's bounds** (MTT Lemma 1), from the [erdos-985](https://github.com/senamakel/erdos-985)
   library: `|Σ_{n<x} Λ(n)(1 - n/x) - x/2| ≤ √x/20 + 3` and, for `χ ≠ 1` mod `p`,
   `|Σ_{n<x} Λ(n)χ(n)(1 - n/x)| ≤ c(p,x) √x log p`, with MTT's `c(p,x)` (`Erdos985.bachC`).
2. **The sieve** (MTT Theorem 3, `Grosswald/Sieve.lean`): for any set `S` of prime factors of
   `p - 1` with `δ = 1 - Σ_{ℓ∈S} 1/ℓ > 0`,
   `Σ_{n<x} Λ(n)(1 - n/x) ≤ (2^{ω-|S|}(2 + (|S|-1)/δ) - 1) · c(p,x) √x log p`.
   With `S = ∅` this is MTT Theorem 2. So, under GRH, the inequality
   `K · c(p,x)√x log p < x/2 - (√x/20 + 3)` must fail for every admissible `S`
   (`not_sieveIneq_of_GRH`, `Grosswald/Analytic.lean`).
3. **Large `p`** (`Grosswald/Tail.lean`): instead of Robin's bound on `ω`, we use
   `256^ω · ∏_{r<256} r ≤ (p - 1) · 256^{54}`, i.e. `2^ω < 4520 · p^{1/8}`, which settles
   every `p ≥ 10^47` with `S = ∅`. Below `10^47`, `ω(p - 1) ≤ 30`.
4. **An executable criterion** (`Grosswald/Crit.lean`): `crit K Y0` is a rational test that
   implies the inequality of step 2 for every `p ≥ (Y0² + 2)²`. It uses the tangent bound
   `log y ≤ log a + y/a - 1`, `log 2 < 0.6931471808` and the alternating series for
   `log(1 + u)` with its remainder.
5. **Algorithm 1** (`Grosswald/Alg.lean`): a recursive checker `checkNode n fuel X Y` with a
   soundness proof `checkNode_sound`. A node covers the primes with `ω(p - 1) = n`, all of `X`
   dividing `p - 1` and none of `Y`. Lower bound: `p ≥ 1 + ∏L`, `L` the first `n` primes
   outside `Y`. Upper bound: the sieve with `M` the `s` largest primes of `L`. The exchange
   lemmas in `Grosswald/Combi.lean` justify both bounds without order statistics. Large
   intervals are split on the next prime; small ones are enumerated over `p = k ∏X + 1`, and
   each candidate is ruled out (a prime of `Y` divides `k`, a small odd prime divides `p`, the
   base-2 Fermat test fails, `ω(p - 1) ≠ n`, `minFac p ≠ p`) or given a prime primitive root
   `q < ⌊√p⌋ - 2` by Lucas' test. This last case is MTT's list of 68,030 exceptions.
6. **The computation** (`Grosswald/Run/`): the roots `(n, [2], [])` for every
   `n ∈ [1, 30] \ {12, 13, 14}` close at once, which is MTT Corollary 4. For `n = 12, 14` the whole
   tree, and for `n = 13` five subtrees (`covered_13` in `Main.lean` puts them back together),
   are evaluated by `native_decide`. That is about `1.5·10^7` candidates in all.

| File | Content |
|---|---|
| `Grosswald/Statement.lean` | target definitions (fixed) |
| `Grosswald/Sieve.lean` | MTT Theorem 3 |
| `Grosswald/Analytic.lean` | GRH + Bach + sieve at `x = ⌊√p⌋ - 2` |
| `Grosswald/Crit.lean` | rational criterion for Bach's inequality |
| `Grosswald/Tail.lean` | `p ≥ 10^47` |
| `Grosswald/Combi.lean` | exchange lemmas for the bounds of Algorithm 1 |
| `Grosswald/Alg.lean` | Algorithm 1 and its soundness |
| `Grosswald/Run/*.lean` | `native_decide` evaluations |
| `Grosswald/Main.lean` | assembly |
| `docs/PLAN.md` | map from MTT to Lean |
| `scripts/*.py` | float prototypes used to size the computation (not part of the proof) |

## Building

```
lake build
```

The `native_decide` files take about ten minutes of CPU in total. Measured wall times: N13A1
162 s, N13A2 101 s, N13B 92 s, N12 90 s, N13C 57 s, N13D 32 s, N14 about 20 s, Roots about 10 s.

The analytic toolkit (explicit formula for Dirichlet L-functions with weight `(1 − n/x)`,
Hadamard factorization, Perron formula, zero-sum bounds under GRH) comes from
[erdos-985](https://github.com/senamakel/erdos-985), required as a lake dependency.
