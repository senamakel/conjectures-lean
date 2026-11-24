# Erdős Problem 985 in Lean

[Erdős Problem 985](https://www.erdosproblems.com/985) asks whether every odd prime `p` has a
prime primitive root `q < p`. This project proves that it does: `erdos_985` is proved
unconditionally in Lean, with GRH for Dirichlet L-functions supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
The main library holds a complete Lean proof that GRH implies the statement.

**Status in the literature.** Erdős Problem 985 is open: unconditionally it is not even
known that every sufficiently large prime has a prime primitive root below `p` (the best
uniform bound is Ha's `ĝ(p) ≪ p^{3.1}`, J. Number Theory 133 (2013)). The implication
"GRH for Dirichlet L-functions implies Erdős 985" follows from Theorem 1 of McGown, Treviño
and Trudgian, *Resolving Grosswald's conjecture on
GRH*, Funct. Approx. Comment. Math. 55 (2016) 215–225 (arXiv:1508.05182). Under GRH that
theorem gives a prime primitive root below `√p − 2` for every prime `p > 2791`, and the
primes up to 2791 are a finite check. Our proof follows the argument of their Theorem 2, with
the search range `[1, p)` in place of `[1, √p − 2)`, so the analysis closes at `p ≥ 10^8`
without their sieve, and every prime below `10^8` is covered by a proved-sound checker. This
repository proves `erdos_985_of_GRH`, with GRH as an explicit hypothesis (label
**RH-consequence**, tier C), including a complete proof of the Bach-type estimate that
McGown–Treviño–Trudgian state as their Lemma 1 without proof. `Unconditional/` closes the GRH
hypothesis with the certified proof and gives `erdos_985`.

```lean
theorem erdos_985 : Erdos985.Erdos985Statement   -- Unconditional/Erdos985Unconditional.lean

theorem Erdos985.erdos_985_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Erdos985Statement                           -- Erdos985/Main.lean

def Erdos985.Erdos985Statement : Prop :=          -- Erdos985/Statement.lean
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1
```

**Tiers.** `Erdos985.erdos_985_of_GRH` is tier C: GRH for Dirichlet L-functions is the explicit
hypothesis `DirichletLNonvanishingRightOfHalf`. `erdos_985` is tier U: the same statement with
the hypothesis closed by `LFunction_ne_zero_of_half_lt_re` from leanprover-community/riemann-hypothesis
(see "Axioms and unconditional version" below).

The statement is the same as `erdos_985` in
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/985.lean).
The project has no `sorry`. A write-up of the proof in mathematical terms is in
[`paper/erdos985.pdf`](paper/erdos985.pdf).

## How it was built

The Lean development was built with [OpenHuman](https://github.com/tinyhumansai/openhuman)
agents running in an [RSI Ralph](https://github.com/tinyhumansai/rsi-ralph) loop. RSI Ralph
keeps asking a team of agents to improve a working copy and only keeps a change when a score
says it is better.

The stack behind the agents:

| Role | Provider |
|---|---|
| Memory | [LivingBrain](https://livingbrain.com) |
| Search | [Exa](https://exa.ai) ([@ExaAILabs](https://x.com/ExaAILabs)) |
| Inference | [GMI Cloud](https://gmicloud.ai) ([@gmi_cloud](https://x.com/gmi_cloud)) |
| Models | [GLM](https://z.ai) models by Z.ai, served on GMI Cloud |

## How it uses the riemann-hypothesis formalization

The argument needs the Generalized Riemann Hypothesis for Dirichlet L-functions. We take it
from [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
which formalizes L. Alpöge's proof of RH and of GRH for Dirichlet L-functions. It was announced
on 2026-11-20 and certified by the Lean FRO and the Mathlib Initiative on 2026-11-21.

`Erdos985/Statement.lean` copies the hypothesis `DirichletLNonvanishingRightOfHalf` word for
word from that repository's `src/Statements.lean`. Both projects build on the same Lean
(v4.36.0) and Mathlib (`fc4f59e5`), so the two definitions are the same term. The main
library proves `erdos_985_of_GRH` with GRH as a hypothesis and doesn't import the RH code.
Then `Unconditional/Erdos985Unconditional.lean` imports both projects and closes the
hypothesis with their theorem in one line:

```lean
theorem erdos_985 : Erdos985.Erdos985Statement :=
  Erdos985.erdos_985_of_GRH LFunction_ne_zero_of_half_lt_re
```

`#print axioms erdos_985` lists Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) and the 20 `native_decide` axioms from the finite check described below. The
riemann-hypothesis proof brings in no axioms of its own.

We also studied how that repository handles zeros of L-functions (rectangle residues, a local
Landau lemma, zero counting in windows) before choosing a Hadamard-product route for the
explicit formula. `docs/BACH_BLUEPRINT.md` has the comparison.

## How the proof goes

Under GRH, Bach's explicit bounds on the weighted prime sums `Σ_{n<x} Λ(n)χ(n)(1 − n/x)`
(Lemma 1 of McGown, Treviño and Trudgian,
[*Resolving Grosswald's conjecture on GRH*](https://arxiv.org/abs/1508.05182), after Bach,
Math. Comp. 66 (1997)) rule out a counterexample with `p ≥ 10^8`. A computer check covers
the primes below that.

| File | Content |
|---|---|
| `Erdos985/Statement.lean` | the hypothesis and the statement |
| `Erdos985/Bach.lean` | the weighted sums and Bach's constant `c(p, x)` |
| `Erdos985/Analytic/` | Bach's bounds from GRH, with Bach's constants |
| `Erdos985/Indicator.lean` | if no prime `q < x ≤ p` is a primitive root, then `S₀ ≤ (2^ω(p−1) − 1) · max_{χ≠1} ‖S_χ‖` |
| `Erdos985/Numerics.lean` | for `p ≥ 10^8`, Bach's bounds make that inequality impossible |
| `Erdos985/Compute.lean` | every odd prime `p < 10^8` has a prime primitive root `q < p` |
| `Erdos985/Main.lean` | combines the above |

The analytic part proves `bach_nonprincipal_of_GRH` and `bach_principal_of_GRH`. It writes
`L'/L` as a sum over zeros with the Hadamard product of the completed L-function, which has
order 1. A weighted Perron formula with kernel `x^s/(s(s+1))` then picks up one term per
zero. Under GRH the zero sum is bounded through the identity for `Σ_ρ Re 1/(s − ρ)` at
`s = 3/2`, using digamma values at 3/4 and 5/4 and `Σ Λ(n) n^{-3/2} ≤ 1.515`. The Hadamard
factorization library in `Vendor/PNT` comes from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
(Apache-2.0, see `Vendor/PNT/NOTICE.md`).

For the indicator step, take one character `ψ` of order `p − 1`. If `n` is not a primitive
root, one factor of `∏_{ℓ | p−1} ((1 − 1/ℓ) − (1/ℓ) Σ_{0<i<ℓ} ψ(n)^{i(p−1)/ℓ})` vanishes.
Expanding the product over subsets of the prime factors gives the bound with the sharp
constant `2^ω − 1`.

The numerics split into three cases: `ω(p−1) ≤ 8`, `ω = 9` (where `p − 1 ≥ 23 · 9699690`,
the tight case with about a 4% margin), and `ω ≥ 10` (via `16^ω(n) · 30030 ≤ 16^6 · n`).

For the finite check, the checker runs a base-2 Fermat filter on each prime, then searches
small primes `q` and tests `q^((p−1)/r) ≢ 1` for each prime `r | p − 1`. Mathlib's
`orderOf_eq_of_pow_and_pow_div_prime` turns that into the order. Its soundness is proved
(`Erdos985.Compute.checkAll_sound`), and it is evaluated with `native_decide` in 20 chunks
of 5·10⁶ that lake builds in parallel.

## Deviations from the literature

McGown, Treviño and Trudgian prove a prime primitive root below `√p − 2` for every prime
`p > 2791` under GRH. This project proves the weaker conclusion `q < p` that Erdős 985 asks for.
With the search range `[1, p)` the analytic argument closes at `p ≥ 10^8` without their sieve,
so the threshold is `10^8` instead of `2791`, and the finite check covers every odd prime below
`10^8`. The Bach-type estimate they cite as their Lemma 1 is proved here in full
(`bach_nonprincipal_of_GRH`, `bach_principal_of_GRH`).

## Building

```bash
lake exe cache get   # Mathlib
lake build
```

The full build takes about a minute on a 95-core machine with the Mathlib cache.

To build `erdos_985` against the riemann-hypothesis repository:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # clones it there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files, so raise the open-file limit first. On macOS:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`
and then `ulimit -n 1400000`. On Linux, `sudo prlimit --pid $$ --nofile=2000000:2000000`.

## Axioms and unconditional version

Checked on 2026-11-24 (erdos-985 `9538edb`, riemann-hypothesis `507a75d91d`, Lean v4.36.0,
Mathlib `fc4f59e5`). `lake build` of this repository: no `sorry` warnings, about 98 s wall
(1395 CPU-seconds, the 20 `Compute.Chunk*` modules take about 60 s each in parallel).
`#print axioms Erdos985.erdos_985_of_GRH` lists the three standard axioms plus the 20
`native_decide` axioms `Erdos985.Compute.chunk_ok_{0..19}._native.native_decide.ax_1_1`. Each
evaluates the finite checker on 5·10⁶ numbers; its soundness is `Erdos985.Compute.checkAll_sound`.

| Theorem | Statement | Axioms |
|---|---|---|
| `Erdos985.erdos_985_of_GRH` | `DirichletLNonvanishingRightOfHalf → Erdos985Statement` | standard three + 20 `native_decide` |
| `erdos_985` | `Erdos985Statement` | standard three + 20 `native_decide` |

Output of `scripts/check-unconditional.sh /path/to/riemann-hypothesis` for `erdos_985`:

```
'erdos_985' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Erdos985.Compute.chunk_ok_0._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_1._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_10._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_11._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_12._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_13._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_14._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_15._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_16._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_17._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_18._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_19._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_2._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_3._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_4._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_5._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_6._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_7._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_8._native.native_decide.ax_1_1,
 Erdos985.Compute.chunk_ok_9._native.native_decide.ax_1_1]
```

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

Resources: the riemann-hypothesis cache is about 93 GB, the import needs about 19 GB of RAM and
about 900,000 open files (hard limit must be raised, see Building). With a warm cache the whole
script took about 9.5 minutes.

## Credits

- **Hadamard factorization library** (`Vendor/PNT/`): vendored from
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), source
  commit `a4fb6989b07e9c76b511807ae93e33e25b820e9b` (Lean v4.35.0), licence Apache-2.0
  (`Vendor/PNT/LICENSE`). `Vendor/PNT/NOTICE.md` lists the vendored files. Each carries the
  line "Modified for erdos-985: ported to Lean v4.36.0 / Mathlib fc4f59e5": import paths
  rewritten to the `Vendor.PNT.` prefix plus the minimal API-drift fixes, with no statement
  weakened.
- **GRH statement and theorem** (`DirichletLNonvanishingRightOfHalf`,
  `LFunction_ne_zero_of_half_lt_re`): from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
  checked against commit `507a75d91d`. Only the one-line definition is copied (see
  `Erdos985/Statement.lean`); that repository has no licence file. Its code is imported, never
  copied, and only from `Unconditional/`.
- **Problem statement**: [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  `FormalConjectures/ErdosProblems/985.lean` (Apache-2.0).
- **Bach's bounds**: Bach, Math. Comp. 66 (1997), in the form of Lemma 1 of McGown, Treviño and
  Trudgian, [arXiv:1508.05182](https://arxiv.org/abs/1508.05182).
