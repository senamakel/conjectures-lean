# Completeness of Euler's idoneal numbers under GRH in Lean

Euler called `n` *idoneal* if it cannot be written as `ab + bc + ca` with `0 < a < b < c`
(equivalently, every genus of forms of discriminant `−4n` is a single class), and found 65 of
them, the largest `1848`. This repository proves in Lean that Euler's 65 numbers are the only
idoneal numbers. `idoneal_completeness` is proved unconditionally, with GRH supplied by the
certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
and the main library holds a complete Lean proof that GRH implies completeness.

The implication is due to P. J. Weinberger (*Exponents of the class groups of complex quadratic
fields*, Acta Arith. 22 (1973), 117-124), who proved that Euler's list is complete under GRH
(label: **RH-consequence**). Unconditionally he showed that at most two more exist (sometimes
misquoted as one); formal-conjectures lists completeness as open. The analytic step here is a
count of small split primes in place of Weinberger's `L(1, χ)` and genus-theory argument, and
every `n < 10^8` is covered by a proved-sound checker.

The repository also keeps a side result on class number one, which is not a target (label:
**known, via GRH here**). The nine imaginary quadratic fields of class number one were found
unconditionally by Heegner (1952), Baker (1966) and Stark (1967). The version here assumes GRH
and two cited classical inputs, and no further work on it is planned.

The headline theorems, with GRH for Dirichlet L-functions as a hypothesis:

```lean
theorem Weinberger.idoneal_completeness_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Idoneal.IdonealCompletenessStatement          -- ∀ n, IsIdoneal n → n ∈ knownIdonealNumbers

theorem Weinberger.isIdoneal_iff_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (n : ℕ) :
    IsIdoneal n ↔ n ∈ knownIdonealNumbers

theorem Weinberger.knownIdonealNumbers_are_idoneal : ∀ n ∈ knownIdonealNumbers, IsIdoneal n
```

The class-number-one side result:

```lean
-- known, via GRH here; not a target (Heegner 1952, Baker 1966, Stark 1967 proved it outright)
theorem Weinberger.ClassNumber.starkHeegner_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPS : ClassNumberOneNorms) (hH : HeegnerClassNumberOne) : StarkHeegnerStatement
```

`Unconditional/WeinbergerUnconditional.lean` proves
`idoneal_completeness : Idoneal.IdonealCompletenessStatement`, with GRH closed by
leanprover-community/riemann-hypothesis. The repository has no `sorry`.

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `idoneal_completeness_of_GRH`, `isIdoneal_iff_of_GRH` | C | GRH |
| `idoneal_completeness`, `isIdoneal_iff` (`Unconditional/`) | U | none |
| `knownIdonealNumbers_are_idoneal` | D | none |
| `starkHeegner_of_GRH` (not a target) | C + H | GRH, `ClassNumberOneNorms`, `HeegnerClassNumberOne` |
| `starkHeegner_of_cited` (`Unconditional/`, not a target) | U + H | `ClassNumberOneNorms`, `HeegnerClassNumberOne` |

- GRH is `Erdos985.DirichletLNonvanishingRightOfHalf`, from the
  [erdos-985](https://github.com/senamakel/erdos-985) dependency, which copies it word for word
  from `src/Statements.lean` of
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
- `Idoneal.IsIdoneal`, `Idoneal.knownIdonealNumbers` and the statement of
  `idoneal_numbers_completeness` are copied word for word from formal-conjectures,
  [`FormalConjectures/Wikipedia/IdonealCompleteness.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/IdonealCompleteness.lean),
  where it is an open problem stated with `sorry`. `IdonealCompletenessStatement` names that
  statement as a `Prop`.
- `ClassNumberProblem.IsClassNumberOne` and the statement of
  `class_number_problem.variants.imaginary` are copied word for word from
  [`FormalConjectures/Wikipedia/ClassNumberProblem.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/ClassNumberProblem.lean)
  (`StarkHeegnerStatement`).
- The two tier-H inputs of part B are in `Weinberger/ClassNumber/Hypotheses.lean`. Both are
  classical and need no analytic input, but the Mathlib pin cannot reach them yet from
  `NumberField.classNumber (AdjoinRoot (X ^ 2 - C d))`:
  `ClassNumberOneNorms` (if `ℚ(√d)` has class number one and `p ∣ N(t + ω)`, then `p = N(u + vω)`
  for some integers `u, v`) and `HeegnerClassNumberOne` (the nine fields have class number one).
  See `docs/SCOPING.md` and the end of `docs/BLUEPRINT.md` for what proving them would take.
  Part B is proved under GRH given these two facts; the Heegner-Baker-Stark theorem needs
  neither GRH nor the cited inputs.

## Axioms

Real output of `lake env lean AxiomsCheck.lean`, 2026-11-24, after a clean `lake build`:

```
'Weinberger.idoneal_completeness_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Weinberger.Compute.chunk_ok_0._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_1._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_2._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_3._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_4._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_5._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_6._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_7._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_8._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_9._native.native_decide.ax_1_1]
'Weinberger.isIdoneal_iff_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Weinberger.Compute.chunk_ok_0._native.native_decide.ax_1_1,
 … (chunk_ok_1 … chunk_ok_9) …,
 Weinberger.Compute.known_noRep._native.native_decide.ax_1_1]
'Weinberger.knownIdonealNumbers_are_idoneal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Weinberger.Compute.known_noRep._native.native_decide.ax_1_1]
'Weinberger.not_isIdoneal_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Weinberger.ClassNumber.starkHeegner_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Weinberger.ClassNumber.chunkB_ok_0._native.native_decide.ax_1_1,
 … (chunkB_ok_1 … chunkB_ok_8) …,
 Weinberger.ClassNumber.chunkB_ok_9._native.native_decide.ax_1_1]
'Weinberger.exists_split_prime_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(The `…` lines elide the consecutive chunk names; the full output is in the PR description.)

The `native_decide` axioms:

- `chunk_ok_0` … `chunk_ok_9` (10): `checkFrom (i·10^7) 10^7 = true`, which finds for every
  `n < 10^8` outside the 65 a factorisation `n + a² = u·v` with `2a < u < v`. About 60 to 80 s each.
- `known_noRep` (1): the exhaustive search `repB` finds no representation `ab + bc + ca` of any
  of the 65 numbers. A few seconds.
- `chunkB_ok_0` … `chunkB_ok_9` (10, part B only): `checkFromB (i·10^7) 10^7 = true`, which
  finds for every `n < 10^8` except the nine Heegner values a prime `p` with an ideal of norm
  `p` and `4p < n` (or `n ≡ 0 mod 4`). About 25 to 35 s each.

The analytic theorem `not_isIdoneal_of_GRH` (no idoneal number `≥ 10^8`) uses the standard
three axioms only.

## Proof outline

The full blueprint, with every Lean statement, is [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md). The
route does not go through the class number formula or genus theory, neither of which the Mathlib pin
has (see [`docs/SCOPING.md`](docs/SCOPING.md)).

1. `Weinberger/Elementary.lean`: `n = ab + bc + ca` iff `n + a² = (a + b)(a + c)`. So if `n` is
   idoneal, `−n` is a non-residue mod every odd prime `p ∤ n` with `p² < n`
   (`not_isSquare_of_isIdoneal`).
2. `Weinberger/Character.lean`: `χ_{−4n}` as a Dirichlet character mod `4n`, built from the
   Jacobi symbol; at odd primes `p ∤ n` it is `(−n/p)`. The proof works with its primitive
   character `ψ` (conductor `≤ 4n`).
3. `Weinberger/GRH.lean`: under GRH,
   `‖Σ_{m<x} Λ(m)ψ(m)(1 − m/x)‖ ≤ (√x + 2 + 3/x)(2/3)(log N + 5/3) + log x + 1.6` for any
   primitive non-trivial `ψ` mod `N`, reassembled from erdos-985's explicit formula and GRH zero
   sum. With erdos-985's principal bound `|S₀ − x/2| ≤ √x/20 + 3`.
4. `Weinberger/Sieve.lean`: if `ψ(p) = −1` for every prime `p < x` outside a set `P` that holds
   all primes with `p² < x`, then `Σ Λ(m)(1 − m/x)(1 + Re ψ(m)) ≤ 2 #P log x`.
5. `Weinberger/Numerics.lean`, `Weinberger/Large.lean`: with `x = ⌊√n⌋`,
   `P = {p < x : p² < x or p ∣ 2n}`, `#P ≤ √x + 1 + ω(2n)` and `2^{ω(2n)} ≤ 2n`, steps 3 and 4
   contradict for `n ≥ 10^8` (margin about 856 out of `x/2 = 5000` at the threshold). This is
   `exists_split_prime_of_GRH`: every `n ≥ 10^8` has a small odd prime that splits in `ℚ(√−n)`.
6. `Weinberger/Compute.lean`, `Weinberger/Compute/`: for `n < 10^8` a proved-sound checker finds
   a representation of every non-listed `n`; a second checker confirms the 65.
7. `Weinberger/ClassNumber/`: for squarefree `d = −n` of class number one, a split prime `p`
   with `4p < n` would be a norm `u² + uv + ((1+n)/4)v²`, impossible; `p = 2` handles
   `n ≡ 1, 2 (mod 4)`. The large range uses step 5, the range `n < 10^8` its own checker.

## Layout

| File | Content |
|---|---|
| `Weinberger/Statement.lean` | target statements (formal-conjectures, verbatim) |
| `Weinberger/Elementary.lean` | `ab + bc + ca` and factorisations of `n + a²` |
| `Weinberger/Character.lean` | `χ_{−4n}` from the Jacobi symbol |
| `Weinberger/GRH.lean` | Bach's non-principal bound for any primitive character |
| `Weinberger/Sieve.lean` | the split-prime sum and its upper bound |
| `Weinberger/Numerics.lean` | the inequality for `x ≥ 10^4` |
| `Weinberger/Large.lean` | `exists_split_prime_of_GRH`, `not_isIdoneal_of_GRH` |
| `Weinberger/Compute.lean`, `Compute/` | checker, soundness, 10 + 1 `native_decide` |
| `Weinberger/Main.lean` | part A assembly |
| `Weinberger/ClassNumber/Hypotheses.lean` | the two tier-H inputs of part B |
| `Weinberger/ClassNumber/Elementary.lean`, `Checker.lean`, `Compute/`, `Main.lean` | part B |
| `Unconditional/WeinbergerUnconditional.lean` | GRH discharged by riemann-hypothesis |
| `AxiomsCheck.lean` | `#print axioms` for the headline theorems |

## Deviations from the literature

### Threshold `10^8`

Weinberger's analytic argument goes through `L(1, χ)` and genus theory. Here the analytic step is a GRH
count of small split primes, with the erdos-985 constants, and it reaches `n ≥ 10^8` (`3·10^7` would do with the same bounds; `10^8` leaves a 17% margin). A
computation of about 10 CPU-minutes checks the range below.

### Part B uses two cited facts

Part B assumes the two tier-H inputs described above, because the Mathlib pin has no bridge from
`NumberField.classNumber` of `AdjoinRoot (X² − C d)` to norms of quadratic integers. The
statement itself is unchanged.

## Building

```bash
lake exe cache get   # Mathlib
lake build           # default target: Weinberger
lake env lean AxiomsCheck.lean
```

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`). Measured 2026-11-24 on a 95-core
box with the Mathlib cache and erdos-985's analytic modules already built: a clean
`lake build` of this package took 2 min 46 s wall, about 13 CPU-minutes. The ten part-A chunks
take 59 to 81 s each, the ten part-B chunks 22 to 35 s each. Building erdos-985's analytic modules
from scratch adds about 1 min 20 s wall (4 CPU-minutes).

## Unconditional version

`Unconditional/WeinbergerUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the GRH hypothesis with its theorem `LFunction_ne_zero_of_half_lt_re`:

| Theorem | Statement | Axioms |
|---|---|---|
| `idoneal_completeness` | `Idoneal.IdonealCompletenessStatement` | standard three + 10 `native_decide` |
| `isIdoneal_iff` | `∀ n, IsIdoneal n ↔ n ∈ knownIdonealNumbers` | standard three + 11 `native_decide` |
| `starkHeegner_of_cited` | `ClassNumberOneNorms → HeegnerClassNumberOne → StarkHeegnerStatement` | standard three + 10 `native_decide` |

Real output of `scripts/check-unconditional.sh /home/ubuntu/work/personal/riemann-hypothesis`
(2026-11-24, riemann-hypothesis `507a75d91d`, 42 min wall including the wait for the shared
lock; no errors):

```
'idoneal_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Weinberger.Compute.chunk_ok_0._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_1._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_2._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_3._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_4._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_5._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_6._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_7._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_8._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_9._native.native_decide.ax_1_1]
'isIdoneal_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Weinberger.Compute.chunk_ok_0._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_1._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_2._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_3._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_4._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_5._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_6._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_7._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_8._native.native_decide.ax_1_1,
 Weinberger.Compute.chunk_ok_9._native.native_decide.ax_1_1,
 Weinberger.Compute.known_noRep._native.native_decide.ax_1_1]
'starkHeegner_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Weinberger.ClassNumber.chunkB_ok_0._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_1._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_2._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_3._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_4._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_5._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_6._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_7._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_8._native.native_decide.ax_1_1,
 Weinberger.ClassNumber.chunkB_ok_9._native.native_decide.ax_1_1]
```

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on Linux
`sudo prlimit --pid $$ --nofile=2000000:2000000`, on macOS
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

- No files are vendored. The analytic toolkit is the erdos-985 lake dependency (which vendors
  part of PrimeNumberTheoremAnd under Apache-2.0; see its `Vendor/PNT/NOTICE.md`).
  `Weinberger/GRH.lean` re-assembles erdos-985's `bach_nonprincipal_of_GRH` proof for an
  arbitrary modulus.
- `Weinberger/Statement.lean` copies definitions from google-deepmind/formal-conjectures
  (commit `86a2f58`, Apache-2.0). `Weinberger.Compute.repB_of_rep` follows that file's
  `exists_triple_iff_bounded`.
