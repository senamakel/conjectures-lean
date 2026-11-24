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

## Tier and provenance

* `prime_primitive_root_of_GRH_large`: tier **C** (GRH is an explicit argument); tier **U** through
  `Unconditional/` (see below).
* `grosswald_of_GRH`: tier **C + H**. Besides GRH it takes the finite range as the cited
  hypothesis `VerifiedUpTo 2500000000000000`. Through `Unconditional/` it becomes
  `grosswald_of_verified`, tier **U + H**. The full `GrosswaldStatement` is therefore not proved
  unconditionally here; see "Why the range below `2.5·10^15` stays a hypothesis".

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
| `scripts/*.py`, `scripts/uncovered.c` | float prototypes used to size the computation (not part of the proof) |

## Why the range below `2.5·10^15` stays a hypothesis

`2.5·10^15` is where the Cohen–Oliveira e Silva–Trudgian computation ends; MTT start their GRH
argument there, and so does this repo. Replaying the range inside Lean is out of reach:

* even with the exact factorisation of every `p - 1`, the sieve inequality fails for about
  `6.2·10^9` primes in `(409, 2.5·10^15)` (92% of primes near `10^8`, 17% near `10^11`, 0.13%
  near `10^13`), and each of them needs an explicit Lucas certificate;
* lowering Algorithm 1's start to `10^13` already enumerates about `1.1·10^11` candidates, and
  every prime below the start (`π(10^12) = 3.8·10^10`) has to be visited;
* under `native_decide`, one modular exponentiation at `p ≈ 10^12` costs about 16 µs.

The best split costs an estimated 10–100 CPU-days and needs a proved segmented sieve that does
not exist here. The numbers, the scripts that produced them, and what would have to improve
are in [`docs/PLAN.md`](docs/PLAN.md#can-the-range-below-2510-15-be-computed-here-sized-2026-11-24).

## Building

```
lake build
```

Toolchain Lean `v4.36.0` (`lean-toolchain`), Mathlib `fc4f59e5` (through erdos-985, pinned at
`9538edb`). Run `lake exe cache get` once before the first build. The `native_decide` files take
about eight minutes of CPU in total. Measured on 2026-11-24 (95-core x86-64 box, full `lake build`
of this repo after the Mathlib cache: 3 min 44 s wall, 787 s CPU, 7.3 GB peak RSS): N13A1 130 s,
N13A2 83 s, N12 80 s, N13B 70 s, N13C 47 s, N13D 24 s, N14 21 s, Roots 4 s.

The analytic toolkit (explicit formula for Dirichlet L-functions with weight `(1 − n/x)`,
Hadamard factorization, Perron formula, zero-sum bounds under GRH) comes from
[erdos-985](https://github.com/senamakel/erdos-985), required as a lake dependency.

## Unconditional version

`Unconditional/GrosswaldUnconditional.lean` imports [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with its theorem:

| Theorem | Statement | Axioms |
|---|---|---|
| `prime_primitive_root_large_unconditional` | every prime `p > 2.5·10^15` has a prime primitive root `q < √p − 2` | standard three + 10 `native_decide` |
| `grosswald_of_verified` | `VerifiedUpTo 2500000000000000 → GrosswaldStatement` | same |

The range `409 < p ≤ 2.5·10^15` stays the hypothesis `VerifiedUpTo` (the Cohen–Oliveira e
Silva–Trudgian computation).

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on macOS:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.
