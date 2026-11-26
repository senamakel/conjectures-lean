# Grosswald's conjecture under GRH in Lean

**Literature status: RH-consequence.** Grosswald (1981) conjectured that the least primitive
root `g(p)` of every prime `p > 409` satisfies `g(p) < √p - 2`. McGown, Treviño and Trudgian
([*Resolving Grosswald's conjecture on GRH*](https://arxiv.org/abs/1508.05182), 2016, MTT below)
proved it under the Generalized Riemann Hypothesis, using the computation of Cohen, Oliveira e
Silva and Trudgian for `409 < p ≤ 2.5·10^15`. The main library is a complete
Lean proof that GRH implies Grosswald's conjecture, following MTT, with the finite range redone
here (`409 < p < 10^13` prime by prime, `p > 10^13` by MTT's Algorithm 1). `Unconditional/`
proves Grosswald's conjecture unconditionally in Lean, with GRH supplied by the certified proof
in leanprover-community/riemann-hypothesis.

```lean
-- Grosswald/Main.lean
theorem Grosswald.grosswald_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    GrosswaldStatement

theorem Grosswald.prime_primitive_root_of_GRH_above (hGRH : DirichletLNonvanishingRightOfHalf) :
    ∀ p : ℕ, p.Prime → 10000000000000 < p → HasSmallPrimePrimitiveRoot p

theorem Grosswald.verifiedUpTo_10_13 : VerifiedUpTo 10000000000000
```

## Tier and provenance

* `grosswald_of_GRH`: tier **C** (GRH is the only hypothesis); tier **U** through
  `Unconditional/` (`grosswald`).
* `prime_primitive_root_of_GRH_above`: tier **C**, and `prime_primitive_root_of_GRH_large` (MTT's
  threshold `2.5·10^15`) is a corollary.
* `verifiedUpTo_10_13`: tier **D**, pure computation, no GRH.

`DirichletLNonvanishingRightOfHalf` is copied verbatim from
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
The target definitions are in `Grosswald/Statement.lean` (fixed).

## Axioms

`#print axioms Grosswald.grosswald_of_GRH` (output of 2026-11-25, 2953 entries, shortened here
to the first and last of each family):

```
'Grosswald.grosswald_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Grosswald.Direct.Run.a1._native.native_decide.ax_1_1,
 Grosswald.Direct.Run.a2._native.native_decide.ax_1_1,
 Grosswald.Direct.Run.b0000._native.native_decide.ax_1_1,
 …
 Grosswald.Direct.Run.b2499._native.native_decide.ax_1_1,
 Grosswald.Run.c00000._native.native_decide.ax_1_1,
 …
 Grosswald.Run.c00446._native.native_decide.ax_1_1,
 Grosswald.Run.first31_ok._native.native_decide.ax_1_1]
```

That is the standard three plus 2950 `native_decide` axioms: 2 + 2500 direct chunks
(`Grosswald.Direct.Run.a1`, `a2`, `b0000`…`b2499`), 447 Algorithm 1 chunks
(`Grosswald.Run.c00000`…`c00446`) and `first31_ok`. Each says that the compiled evaluation of a
Boolean checker agrees with its definition. The checkers' soundness
(`Grosswald.Direct.range_sound`, `Grosswald.Alg.checkNode_sound`, `Grosswald.Leaf.leafOk_sound`)
is proved from the standard three alone:

```
'Grosswald.Direct.range_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## How the proof goes

1. **Bach's bounds** (MTT Lemma 1), from [erdos-985](../erdos-985/):
   `|Σ_{n<x} Λ(n)(1 - n/x) - x/2| ≤ √x/20 + 3` and, for `χ ≠ 1` mod `p`,
   `|Σ_{n<x} Λ(n)χ(n)(1 - n/x)| ≤ c(p,x) √x log p` (`Erdos985.bachC`), at `x = ⌊√p⌋ - 2`.
2. **The sieve** (MTT Theorem 3, `Grosswald/Sieve.lean`): for a set `S` of prime factors of `p - 1`
   with `δ = 1 - Σ_{ℓ∈S} 1/ℓ > 0`, `Σ Λ(n)(1 - n/x) ≤ (2^{ω-|S|}(2 + (|S|-1)/δ) - 1) c(p,x) √x log p`.
   Under GRH a counterexample violates every such inequality (`not_sieveIneq_of_GRH`).
3. **`p ≥ 10^47`** (`Grosswald/Tail.lean`): `2^ω < 4520 p^{1/8}` closes it with `S = ∅`; below,
   `ω(p - 1) ≤ 30` (`First31.lean`).
4. **Algorithm 1 for `p > 10^13`** (`Grosswald/Alg.lean`, `Combi.lean`, `Crit.lean`): a node
   `(n, X, Y)` covers primes with `ω(p - 1) = n`, `X ⊆ pf(p - 1)`, `Y ∩ pf(p - 1) = ∅`; lower
   bound `max(1 + ∏L, 10^13 + 1)`, upper bound from the sieve and the rational test `crit`.
   Large nodes split on the next prime (split limit `LIM n`: `10^8` for `n ≤ 8`, `10^7` for
   `n ≤ 10`, `10^6` above); leaves enumerate `p = k ∏X + 1` with the native checker
   `GrosswaldCompute.leafOk` (`Grosswald/LeafSound.lean`): a `q ∈ Y` divides `k`, or Fermat base 2
   fails, or a prime `g < 2000`, `g < √p - 2`, passes Lucas' test against `X`, the sieved primes
   of `k` and the cofactor, or a trial divisor of `p` is found. `Grosswald/Covered.lean` glues the
   447 subtrees (`scripts/treecut.c`, `scripts/gen_tree.py`; about `4.2·10^10` enumerated `k`).
5. **`409 < p < 10^13 + 10^8`** (`Grosswald/Direct/`): `GrosswaldCompute.segOk a L` checks the odd
   `n ∈ [a, a + 2L)`: an untrusted segmented sieve proposes a divisor of `n` or the odd primes
   below `B = ⌊√(a + 2L)⌋ + 1` dividing `n - 1`; the checker verifies the divisor, or that every
   prime `q < B` was offered to every `n` with `q ∣ n - 1` (`cwOk`, `progAll`), and runs Lucas'
   test for some `g` with `g + 3 ≤ ⌊√a⌋`. Since all listed numbers are below `B` and `B² > n`,
   the cofactor is `1` or prime, so the list holds every prime factor of `n - 1`
   (`Grosswald/Direct/Sound.lean`). 2502 chunks, glued by `segsOk_append`
   (`scripts/gen_direct.py`).

The checkers live in `GrosswaldCompute/` (core Lean only, `precompileModules = true`), so
`native_decide` runs them as compiled code; `Nat.powMod` is core's GMP-backed `lean_nat_powmod`.
Map from MTT to Lean and the sizing: [`docs/PLAN.md`](docs/PLAN.md).

| File | Content |
|---|---|
| `Grosswald/Statement.lean` | target definitions (fixed) |
| `Grosswald/Sieve.lean` | MTT Theorem 3 |
| `Grosswald/Analytic.lean` | GRH + Bach + sieve at `x = ⌊√p⌋ - 2` |
| `Grosswald/Crit.lean` | rational criterion for Bach's inequality |
| `Grosswald/Tail.lean`, `First31.lean` | `p ≥ 10^47`; `ω(p - 1) ≤ 30` below |
| `Grosswald/Combi.lean` | exchange lemmas for the bounds of Algorithm 1 |
| `Grosswald/Alg.lean`, `LeafSound.lean` | Algorithm 1 and its soundness |
| `Grosswald/Covered.lean`, `Run/*.lean` | Algorithm 1 subtrees (`native_decide`) and their assembly |
| `Grosswald/Direct/Sound.lean` | soundness of the segmented checker |
| `Grosswald/Direct/Run/*.lean`, `Group/*.lean`, `Main.lean` | the finite range (`native_decide`) |
| `GrosswaldCompute/Seg.lean`, `Leaf.lean` | the executable checkers (core Lean, compiled) |
| `Grosswald/Main.lean` | assembly |
| `scripts/gen_direct.py`, `gen_tree.py`, `treecut.c`, `tree_cut.txt` | chunk generators (not part of the proof) |
| `scripts/*.py`, `scripts/uncovered.c` | float prototypes used for sizing (not part of the proof) |

## Deviations from the literature

* The computed range is redone in Lean rather than cited: `409 < p < 10^13` prime by prime, and
  `10^13 < p ≤ 2.5·10^15` by MTT's Algorithm 1 under GRH (MTT cite Cohen–Oliveira e
  Silva–Trudgian up to `2.5·10^15`).
* Leaves check every prime `p = k ∏X + 1` with Lucas' test (no `ω(p - 1) = n` filter), with
  prime roots `g < 2000`.

## Building

Toolchain Lean `v4.36.0`, Mathlib `fc4f59e5` (through erdos-985 at `9538edb`). Run
`lake exe cache get` once, then `lake build`. That evaluates every chunk, which is a large
computation: measured on a 95-core box under load, a direct chunk (`4·10^9` integers) takes
about 2100 s wall (≈ 0.65 µs per odd number unloaded) and the whole direct range about
`3.3·10^6` CPU-s; Algorithm 1 is about `4.2·10^10` enumerated `k` at ≈ 5.6 µs each
(`2.3·10^5` CPU-s). Lake builds as many modules in parallel as there are cores; to bound the
load, `scripts/run_direct.sh` and `scripts/run_tree.sh` build the chunk modules a few at a time
(concurrency in `.lake/direct.jobs`, `.lake/tree.jobs`) before the final `lake build`.

## Unconditional version

`Unconditional/GrosswaldUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with `LFunction_ne_zero_of_half_lt_re`:

| Theorem | Statement | Axioms |
|---|---|---|
| `grosswald` | `GrosswaldStatement` | standard three + the 2950 `native_decide` of `grosswald_of_GRH` |
| `prime_primitive_root_large_unconditional` | every prime `p > 10^13` has a prime primitive root `q < √p − 2` | standard three + 448 `native_decide` (the Algorithm 1 chunks and `first31_ok`) |

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first (Linux:
`sudo prlimit --pid $$ --nofile=2000000:2000000`; macOS:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`).

Checked 2026-11-25 against riemann-hypothesis `507a75d91d`; the log shows no `sorryAx`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the
Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh).
This check links against the community build cache and does not repeat those kernel checks.

## Credits

No vendored files. The analytic toolkit comes from [erdos-985](../erdos-985/)
as a lake dependency; MTT's argument and Algorithm 1 follow arXiv:1508.05182.
