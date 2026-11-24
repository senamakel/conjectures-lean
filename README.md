# Bach's explicit Ankeny theorem under GRH, in Lean

E. Bach (*Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990))
proved under GRH that every proper subgroup of `(ℤ/q)ˣ` omits a unit below `2 log² q`; in
particular the least quadratic non-residue mod an odd prime `p` is at most `2 log² p`.
Unconditionally only Burgess-type bounds `p^{1/(4√e)+ε}` are known.

This repository proves, assuming GRH for Dirichlet L-functions
(`Erdos985.DirichletLNonvanishingRightOfHalf`, copied verbatim from
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)):

```lean
theorem Ankeny.bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : BachSubgroupBound (21 / 5)
theorem Ankeny.leastNonresidue_of_bach {c : ℝ} (h : BachSubgroupBound c) : LeastNonresidueBound c
theorem Ankeny.leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBound (21 / 5)
```

So, under GRH, **every proper subgroup of `(ℤ/q)ˣ` omits a unit of residue `≤ 4.2 log² q`, for
every `q`**, and the least quadratic non-residue mod an odd prime `p` is `≤ 4.2 log² p`. The
definitions in `Ankeny/Statement.lean` are unchanged; only the numeral `2` in the two GRH theorems
became `21 / 5` (see below). There is no `sorry`.

Real output of `#print axioms` (`lake env lean`, 2026-11-24, after a clean `lake build`):

```
#print axioms Ankeny.bach_of_GRH
-- [propext, Classical.choice, Quot.sound,
--  Ankeny.chunk_ok_0._native.native_decide.ax_1_1, …, Ankeny.chunk_ok_7._native.native_decide.ax_1_1]
#print axioms Ankeny.leastNonresidue_of_GRH
-- (the same eleven axioms)
```

The eight `native_decide` axioms come from the finite computation for `q < 2^17` (below).

## Proof outline

The analytic toolkit (weighted explicit formula, Hadamard factorisation, zero-sum bound under GRH,
principal-character bound) is the [erdos-985](https://github.com/senamakel/erdos-985) library,
a lake dependency. See `docs/PLAN.md` for the blueprint.

1. `Ankeny/Character.lean`: a proper subgroup `H` is killed by a non-trivial Dirichlet character
   `χ` (a character of the finite abelian group `(ℤ/q)ˣ/H`).
2. `Ankeny/Analytic.lean`: for primitive non-trivial `χ*` mod `f`,
   `‖Σ_{n<x} Λ(n) χ*(n)(1 − n/x)‖ ≤ (2/3)(√x + 2 + 3/x)(log f + 5/3) + log x + 1.6`
   (the erdos-985 ingredients re-assembled for an arbitrary modulus).
3. `Ankeny/PrimePowers.lean`, `Ankeny/Split.lean`: if `χ(n) = 1` for all `n < x` coprime to `q`,
   compare with the principal sum `≥ x/2 − √x/20 − 3`. Prime powers `p^k` with `p | q` cost at
   most `ω(q) log x`; those with `χ*(p) ≠ 0` (so `p ∤ f`) are absorbed into the zero sum because
   `log f + Σ log p ≤ log q`. Result (`key_inequality`):
   `x/2 − √x/20 − 3 − ω(q) log x ≤ (2/3)(√x + 2 + 3/x)(log q + 5/3) + log x + 1.6`.
4. `Ankeny/Large.lean`, `Ankeny/Numerics.lean`: with `x = ⌊4.2 log² q⌋` this fails for
   `q ≥ 2^17` (using `ω(q) ≤ 6 + (log q − 10)/log 16` and a tangent bound for `log`).
5. `AnkenyCheck.lean`, `Ankeny/Checker.lean`, `Ankeny/Finite.lean`, `Ankeny/Compute*.lean`: for
   `3 ≤ q < 2^17` a graph search shows that the units below `⌊4.2 (⌊log₂ q⌋ log 2)²⌋` generate
   `(ℤ/q)ˣ`. The checker's soundness is proved in Lean; the checker itself uses only core Lean
   and is precompiled (`precompileModules`) so that `native_decide` runs it natively, in eight
   chunks (about 20 CPU-minutes in total).
6. `Ankeny/LeastNonresidue.lean`: the squares are a proper subgroup mod an odd prime.

## Why `21/5` and not Bach's `2`

The zero-sum bound available from erdos-985 is `Σ_ρ 1/|ρ(ρ+1)| ≤ (2/3)(log f + 5/3)` (Hadamard
at `s = 3/2`). The main terms then compare `x/2` with `(2/3)√x log q`, which forces
`c > 16/9 ≈ 1.78` even asymptotically, and the lower-order terms (the `+2` and `+5/3`, the
prime powers dividing `q`, the gamma factor) push the modulus beyond which a given `c` works up
very fast. With the bounds used here the analytic argument needs roughly

| c   | 5      | 4.5      | 4.2      | 4        | 3       | 2           |
|-----|--------|----------|----------|----------|---------|-------------|
| Q₀  | 2^14   | 2^16     | 2^17     | ~2^19    | ~10^9   | ~e^750      |

and every `q < Q₀` must be covered by computation. `2^17` (about `8·10^9` search steps) is
what is comfortable here; `2^18` would give `c ≈ 4.05` for about four times the work. Bach
reaches `2` with a sharper explicit formula (a different weight and sharper zero-sum and
gamma-factor estimates) together with a large computation; redoing the erdos-985 analytic layer
with those sharper estimates was out of scope.

## Building

```
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985). The finite computation dominates the build.
Measured 2026-11-24 on a 95-core box with a warm Mathlib cache (`lake exe cache get` first):
a clean `lake build` (erdos-985 included) took 5 min wall, about 26 CPU-minutes; the eight
`native_decide` chunks took 21, 57, 97, 135, 166, 203, 240 and 278 s (about 20 CPU-minutes in
total, growing roughly linearly with `q`).

## Unconditional version

`Unconditional/AnkenyUnconditional.lean` imports [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with its theorem:

| Theorem | Statement | Axioms |
|---|---|---|
| `bach_unconditional` | `Ankeny.BachSubgroupBound (21 / 5)` | standard three + 8 `native_decide` |
| `leastNonresidue_unconditional` | `Ankeny.LeastNonresidueBound (21 / 5)` | standard three + 8 `native_decide` |

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
