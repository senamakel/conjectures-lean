# Bach's explicit Ankeny theorem under GRH in Lean

E. Bach (*Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990))
proved under GRH that every proper subgroup of `(ℤ/q)ˣ` omits a unit below `2 log² q`. In
particular the least quadratic non-residue mod an odd prime `p` is at most `2 log² p`.
Unconditionally the best bounds are of Burgess type, `p^{1/(4√e)+ε}`.

This repository proves, in Lean, that every proper subgroup of `(ℤ/q)ˣ` omits a unit of residue
`≤ (21/5) log² q` for every `q`, and that the least quadratic non-residue mod an odd prime `p` is
`≤ (21/5) log² p`. The main library is a complete Lean proof that GRH implies both bounds,
following Ankeny (1952) and Bach (1990), with every modulus `q < 2^17` covered by a proved-sound
checker. `Unconditional/` proves `BachSubgroupBound (21/5)` unconditionally in Lean, with GRH
supplied by the certified proof of L. Alpöge in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
Literature status: RH-consequence. Our constant is `21/5`; Bach's is `2` (see "Why `21/5`").

```lean
theorem Ankeny.bach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : BachSubgroupBound (21 / 5)
theorem Ankeny.leastNonresidue_of_bach {c : ℝ} (h : BachSubgroupBound c) : LeastNonresidueBound c
theorem Ankeny.leastNonresidue_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBound (21 / 5)

theorem bach_unconditional : Ankeny.BachSubgroupBound (21 / 5)                -- Unconditional/
theorem leastNonresidue_unconditional : Ankeny.LeastNonresidueBound (21 / 5)  -- Unconditional/
```

## Tier and provenance

`Ankeny.bach_of_GRH` and `Ankeny.leastNonresidue_of_GRH` are tier C: GRH for Dirichlet
L-functions is the explicit hypothesis `Erdos985.DirichletLNonvanishingRightOfHalf`, copied word
for word from riemann-hypothesis `src/Statements.lean`. `Ankeny.leastNonresidue_of_bach` is a
reduction with no hypothesis beyond `BachSubgroupBound c`. `bach_unconditional` and
`leastNonresidue_unconditional` are tier U: the same statements with the hypothesis closed by
`LFunction_ne_zero_of_half_lt_re`.

The target definitions `BachSubgroupBound` and `LeastNonresidueBound` are in
`Ankeny/Statement.lean`. They are this repository's own transcription of Bach's theorem; no
formal-conjectures statement exists. The two GRH theorems state them with the constant `21 / 5`.
The project has no `sorry`.

## Axioms

Real output of `#print axioms` (`lake env lean`, 2026-11-24, after a clean `lake build`):

```
#print axioms Ankeny.bach_of_GRH
-- [propext, Classical.choice, Quot.sound,
--  Ankeny.chunk_ok_0._native.native_decide.ax_1_1, …, Ankeny.chunk_ok_7._native.native_decide.ax_1_1]
#print axioms Ankeny.leastNonresidue_of_GRH
-- (the same eleven axioms)
```

The eight `native_decide` axioms come from the finite computation for `q < 2^17` (step 5
below). Each one evaluates the proved-sound checker on one chunk of moduli; together they take
about 20 CPU-minutes.

## Proof outline

The analytic toolkit (weighted explicit formula, Hadamard factorisation, zero-sum bound under
GRH, principal-character bound) is the [erdos-985](../erdos-985/)
library, a lake dependency. `docs/PLAN.md` has the blueprint.

1. `Ankeny/Character.lean`: a non-trivial Dirichlet character `χ` kills a proper subgroup `H`
   (a character of the finite abelian group `(ℤ/q)ˣ/H`).
2. `Ankeny/Analytic.lean`: for primitive non-trivial `χ*` mod `f`,
   `‖Σ_{n<x} Λ(n) χ*(n)(1 − n/x)‖ ≤ (2/3)(√x + 2 + 3/x)(log f + 5/3) + log x + 1.6`
   (the erdos-985 ingredients re-assembled for an arbitrary modulus).
3. `Ankeny/PrimePowers.lean`, `Ankeny/Split.lean`: if `χ(n) = 1` for all `n < x` coprime to `q`,
   compare with the principal sum `≥ x/2 − √x/20 − 3`. Prime powers `p^k` with `p | q` cost at
   most `ω(q) log x`. Those with `χ*(p) ≠ 0` (so `p ∤ f`) are absorbed into the zero sum because
   `log f + Σ log p ≤ log q`. The result is `key_inequality`:
   `x/2 − √x/20 − 3 − ω(q) log x ≤ (2/3)(√x + 2 + 3/x)(log q + 5/3) + log x + 1.6`.
4. `Ankeny/Large.lean`, `Ankeny/Numerics.lean`: with `x = ⌊4.2 log² q⌋` this fails for
   `q ≥ 2^17` (using `ω(q) ≤ 6 + (log q − 10)/log 16` and a tangent bound for `log`).
5. `AnkenyCheck.lean`, `Ankeny/Checker.lean`, `Ankeny/Finite.lean`, `Ankeny/Compute*.lean`: for
   `3 ≤ q < 2^17` a graph search shows that the units below `⌊4.2 (⌊log₂ q⌋ log 2)²⌋` generate
   `(ℤ/q)ˣ`. The checker's soundness is proved in Lean. The checker itself uses only core Lean
   and is precompiled (`precompileModules`), so `native_decide` runs it natively, in eight
   chunks (about 20 CPU-minutes in total).
6. `Ankeny/LeastNonresidue.lean`: the squares are a proper subgroup mod an odd prime.

## Layout

| File | Content |
|---|---|
| `Ankeny/Statement.lean` | the target definitions `BachSubgroupBound`, `LeastNonresidueBound` |
| `Ankeny/Character.lean` | a character that is trivial on a proper subgroup |
| `Ankeny/Analytic.lean` | the weighted prime sum for a primitive character under GRH |
| `Ankeny/PrimePowers.lean`, `Ankeny/Split.lean` | the comparison with the principal sum, `key_inequality` |
| `Ankeny/Large.lean`, `Ankeny/Numerics.lean` | the contradiction for `q ≥ 2^17` |
| `Ankeny/Checker.lean`, `Ankeny/Finite.lean`, `Ankeny/Compute.lean`, `Ankeny/Compute/Chunk*.lean` | the finite check for `q < 2^17` and its soundness |
| `AnkenyCheck.lean` | the precompiled core-Lean checker |
| `Ankeny/LeastNonresidue.lean` | the least quadratic non-residue from the subgroup bound |
| `Ankeny/Main.lean` | `bach_of_GRH`, `leastNonresidue_of_bach`, `leastNonresidue_of_GRH` |
| `Unconditional/AnkenyUnconditional.lean` | the tier-U theorems |

## Why `21/5` and not Bach's `2`

Our constant is `21/5`; Bach's is `2`. The zero-sum bound available from erdos-985 is
`Σ_ρ 1/|ρ(ρ+1)| ≤ (2/3)(log f + 5/3)` (Hadamard at `s = 3/2`). The main terms then compare
`x/2` with `(2/3)√x log q`, which forces `c > 16/9 ≈ 1.78` even asymptotically. The lower-order
terms (the `+2` and `+5/3`, the prime powers dividing `q`, the gamma factor) push up very fast
the modulus beyond which a given `c` works. With the bounds used here the analytic argument
needs roughly

| c   | 5      | 4.5      | 4.2      | 4        | 3       | 2           |
|-----|--------|----------|----------|----------|---------|-------------|
| Q₀  | 2^14   | 2^16     | 2^17     | ~2^19    | ~10^9   | ~e^750      |

and computation must cover every `q < Q₀`. `2^17` (about `8·10^9` search steps) is the range
checked here; `2^18` would give `c ≈ 4.05` for about four times the work. Bach reaches `2` with
a sharper explicit formula (a different weight and sharper zero-sum and gamma-factor estimates)
together with a large computation. This repository does not redo the erdos-985 analytic layer
with those estimates.

## Building

```
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985). The finite computation dominates the build.
Measured 2026-11-24 on a 95-core box with a warm Mathlib cache (`lake exe cache get` first):
a clean `lake build` (erdos-985 included) took 5 min wall, about 26 CPU-minutes. The eight
`native_decide` chunks took 21, 57, 97, 135, 166, 203, 240 and 278 s (about 20 CPU-minutes in
total, growing roughly linearly with `q`).

## Unconditional version

`Unconditional/AnkenyUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with its theorem:

```lean
theorem bach_unconditional : Ankeny.BachSubgroupBound (21 / 5) :=
  Ankeny.bach_of_GRH LFunction_ne_zero_of_half_lt_re
```

| Theorem | Statement | Axioms |
|---|---|---|
| `bach_unconditional` | `Ankeny.BachSubgroupBound (21 / 5)` | standard three + 8 `native_decide` |
| `leastNonresidue_unconditional` | `Ankeny.LeastNonresidueBound (21 / 5)` | standard three + 8 `native_decide` |

Checked 2026-11-24 with `scripts/check-unconditional.sh` against riemann-hypothesis `507a75d91d`: the build succeeded and `#print axioms` of both theorems printed exactly the standard three plus the 8 `native_decide` axioms (no `sorryAx`). The run took about 18 min wall, dominated by importing riemann-hypothesis.

To run the check:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first. On macOS:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.
On Linux: `sudo prlimit --pid $$ --nofile=2000000:2000000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

- GRH statement and theorem (`DirichletLNonvanishingRightOfHalf`,
  `LFunction_ne_zero_of_half_lt_re`): from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
  checked against commit `507a75d91d`. The definition reaches this repository through
  erdos-985's `Erdos985/Statement.lean`; the theorem is imported only from `Unconditional/`.
  That repository has no licence file.
- Analytic toolkit: [erdos-985](../erdos-985/), required at
  `9538edb`, which vendors the Hadamard factorisation library from
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  (Apache-2.0). This repository vendors no files.
- Bach's theorem: Bach, *Explicit bounds for primality testing and related problems*, Math.
  Comp. 55 (1990), making explicit Ankeny's 1952 `log² p` bound.
