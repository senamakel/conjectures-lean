# Erdős 770(iii) under GRH in Lean

Let `h(n)` be the least `M > 2` such that `2ⁿ − 1, 3ⁿ − 1, …, Mⁿ − 1` have greatest common
divisor `1`, and let `P(n)` be the largest prime `p` with `p − 1 ∣ n`. For `p = P(n)` and
`2 ≤ i < p`, Fermat gives `p ∣ iⁿ − 1`, so `h(n) ≥ P(n)`. Erdős problem 770
(<https://www.erdosproblems.com/770>) asks about the size of `h(n)` in three parts; part (iii) asks
whether, for every `ε > 0` and all large `n`, `P(n) > n^ε` implies `h(n) = P(n)`. The
formal-conjectures statement is `erdos_770.parts.iii`
([source](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/ErdosProblems/770.lean)).

This repository proves 770(iii) under GRH in Lean, in an explicit form: `h(n) ≤ max(P(n),
⌈200 (log n)²⌉)` for every `n ≥ 2` (with Bach's constant `2`, from lls-grh; the earlier constant
`420`, from ankeny-grh's `21/5`, is kept). `Unconditional/` proves part (iii) and the explicit bound
unconditionally in Lean, with GRH supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
Parts (i) and (ii) of Erdős 770 are open and are not treated here.

**Status in the literature: RH-consequence.** Unconditionally, part (iii) is claimed for
`ε > 1/2` (Zeng, 2026) and for `ε > 1/(4√e)` (Korsky, in the notes to his 5 August 2026
manuscript on Erdős 769); both are unrefereed. Under GRH, Korsky's notes state the bound
`h(n) ≤ max{P(n), C (log n)²}` without proof, and a self-published note (Zenodo
10.5281/zenodo.23608372, October 2026) proves the asymptotic statement under a weaker
"quasi-RH" hypothesis. The Lean proof follows those sources. The explicit form with `C = 200` (or `C = 420`),
valid for every `n ≥ 2`, was not found in them (searched 2026-11-24). Those sources were read
through secondary pages (see `docs/scoping` in the conjectures repo), and the Korsky notes were
not opened in the original.

## Main theorems

Headline (constant `200`, Bach's constant `2`):

```lean
theorem Erdos770.explicitBound200_of_bach (hB : Ankeny.BachSubgroupBound 2) : ExplicitBound200

theorem Erdos770.explicitBound200_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    ExplicitBound200
```

with `ExplicitBound200 := ExplicitBound 200 2` in `Erdos770/Statement2.lean`: `h(n) ≤ max(P(n),
⌈200 (log n)²⌉)` for every `n ≥ 2`. The hypothesis `Ankeny.BachSubgroupBound 2` is discharged under
GRH by `LLS.bach2_of_GRH` ([lls-grh](https://github.com/senamakel/lls-grh)). The earlier results
with `420`, which need only ankeny-grh's `BachSubgroupBound (21/5)`, stay as they were:

```lean
theorem Erdos770.explicitBound_of_bach (hB : Ankeny.BachSubgroupBound (21 / 5)) :
    ExplicitBound 420 2

theorem Erdos770.erdos_770_iii_of_bach (hB : Ankeny.BachSubgroupBound (21 / 5)) : Erdos770Part3

theorem Erdos770.explicitBound_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    ExplicitBound 420 2

theorem Erdos770.erdos_770_iii_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : Erdos770Part3
```

with, in `Erdos770/Statement.lean`,

```lean
def ExplicitBound (C : ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, h n ≤ ((max (P n) ⌈C * Real.log n ^ 2⌉₊ : ℕ) : ℕ∞)

def Erdos770Part3 : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop,
    let p := sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}
    p > (n : ℝ) ^ (ε : ℝ) → h n = p
```

So `ExplicitBound 420 2` says `h(n) ≤ max(P(n), ⌈420 (log n)²⌉)` for every `n ≥ 2`. The
repository has no `sorry`. `n = 1` is excluded because `h 1 = 3` while `P 1 = 2` and `⌈420 log² 1⌉ = 0`.

## Tiers and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `explicitBound200_of_bach`, `erdos_770_iii_of_bach200` | H | `Ankeny.BachSubgroupBound 2`, proved under GRH by [lls-grh](https://github.com/senamakel/lls-grh) |
| `explicitBound200_of_GRH` | C | `DirichletLNonvanishingRightOfHalf` (`Erdos985`), copied word for word from riemann-hypothesis `src/Statements.lean` |
| `Erdos770.Unconditional.explicitBound200` | U | none; the GRH hypothesis is closed by riemann-hypothesis (see below) |
| `explicitBound_of_bach`, `erdos_770_iii_of_bach` | H | `Ankeny.BachSubgroupBound (21 / 5)`, proved under GRH by [ankeny-grh](https://github.com/senamakel/ankeny-grh) (its proof is in that repo, not cited) |
| `explicitBound_of_GRH`, `erdos_770_iii_of_GRH` | C | `DirichletLNonvanishingRightOfHalf` (`Erdos985`), copied word for word from riemann-hypothesis `src/Statements.lean` |
| `Erdos770.Unconditional.explicitBound`, `Erdos770.Unconditional.erdos_770_iii` | U | none; the GRH hypothesis is closed by riemann-hypothesis (see below) |

`h` and the body of `Erdos770Part3` are copied word for word from formal-conjectures (see
`Erdos770/Statement.lean` and `NOTICE`). `ExplicitBound` and `P` are not from formal-conjectures;
`P n` is the same `sSup` that appears in `erdos_770.parts.iii`.

## Axioms

Real `#print axioms` output (`lake env lean`, 2026-11-24, after `lake build`):

```
#print axioms Erdos770.explicitBound200_of_bach
-- [propext, Classical.choice, Quot.sound]
#print axioms Erdos770.explicitBound200_of_GRH
-- [propext, Classical.choice, Quot.sound,
--  LLS.chunk2_ok_0._native.native_decide.ax_1_1, …, LLS.chunk2_ok_14._native.native_decide.ax_1_1]
#print axioms Erdos770.explicitBound_of_bach
-- [propext, Classical.choice, Quot.sound]
#print axioms Erdos770.erdos_770_iii_of_bach
-- [propext, Classical.choice, Quot.sound]
#print axioms Erdos770.explicitBound_of_GRH
-- [propext, Classical.choice, Quot.sound,
--  Ankeny.chunk_ok_0._native.native_decide.ax_1_1, …, Ankeny.chunk_ok_7._native.native_decide.ax_1_1]
#print axioms Erdos770.erdos_770_iii_of_GRH
-- (the same eleven axioms)
```

This repository has no `native_decide` of its own. The 15 `LLS.chunk2_ok_*` axioms of the `200`
theorems are inherited from lls-grh through `LLS.bach2_of_GRH`: its proved-sound checker certifies
the finite range of moduli for Bach's constant `2` (about 22 CPU-minutes in 15 chunks; lls-grh's
build also contains older chunk modules of about 2.3 CPU-hours). The eight `native_decide` axioms are inherited
from ankeny-grh through `Ankeny.bach_of_GRH`: they come from its finite check that, for every
modulus `3 ≤ q < 2^17`, the units below `⌊4.2 (⌊log₂ q⌋ log 2)²⌋` generate `(ℤ/q)ˣ`, run by a
checker whose soundness is proved in Lean, in eight chunks of about 20 CPU-minutes in total.

Output of `scripts/check-unconditional.sh` (2026-11-24, riemann-hypothesis `507a75d91d`):

```
'Erdos770.Unconditional.explicitBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Ankeny.chunk_ok_0._native.native_decide.ax_1_1,
 …,
 Ankeny.chunk_ok_7._native.native_decide.ax_1_1]
'Erdos770.Unconditional.erdos_770_iii' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Ankeny.chunk_ok_0._native.native_decide.ax_1_1,
 …,
 Ankeny.chunk_ok_7._native.native_decide.ax_1_1]
```

No `sorryAx` appears.

## Proof outline

Full blueprint: [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md). The outline is for the `420` bound.
The `200` bound (`Erdos770/Main200.lean`, `Numerics200.lean`) runs the same steps with `c = 2`:
`BachSubgroupBound c` gives `M < c log² r ≤ 100 c log² n` for `r ≤ n¹⁰`, so `K = ⌈100 c log² n⌉`
(`420 = 100·21/5`, `200 = 100·2`). Step 6 is redone for `K = ⌈200 u²⌉`: `π(K) ≥ 13 u j`,
`(π K).choose j ≥ (12 u)^j`, `log K ≤ (5/2) log(12 u)` from `K² ≤ (12u)⁵`, and `j log(12 u) > u`.
With `K = ⌈420 log² n⌉` and
`M = max (P n) K`:

1. `Erdos770/Basic.lean` (`P_le_h`): `P n ≤ h n`, by Fermat and `P n − 1 ∣ n`.
2. `Erdos770/Core.lean` (`exists_bad_prime`): if `gcd(2ⁿ−1, …, Mⁿ−1) ≠ 1`, some prime `r` divides
   every `iⁿ − 1` with `2 ≤ i ≤ M`; then `r > M`. Otherwise `h n ≤ M`.
3. `Core.lean` (`lt_of_bach`): `H = ker (x ↦ xⁿ)` in `(ZMod r)ˣ` contains `1, …, M` and is proper
   (else `r − 1 ∣ n` and `r ≤ P n ≤ M`). Bach's bound with `21/5` gives `M < (21/5) log² r`.
4. Small `r ≤ n¹⁰`: `(21/5) log² r ≤ (21/5)·100 log² n = 420 log² n ≤ K ≤ M`, a contradiction.
5. `Core.lean` (`choose_le_of_bad`): for large `r > n¹⁰`, products of `j` distinct primes `≤ K`
   with `K^j ≤ n¹⁰` are distinct elements of `H`, and `|H| ≤ n`, so `(π K).choose j ≤ n`.
6. `Erdos770/Numerics.lean` (`numeric`): with `u = log n`, `j = ⌊10u / log K⌋` and Mathlib's
   Chebyshev bound `π(K) log K ≥ K log 2`, the count `(π K).choose j` exceeds `(21u)^j > n`,
   for every `n ≥ 3`. This contradicts step 5.
7. `Erdos770/Main.lean` (`explicitBound_of_bach`, `erdos_770_iii_of_explicit`): `log² x = o(x^ε)`,
   so eventually `420 log² n + 1 < n^ε < P n`, the maximum is `P n`, and `h n = P n` by step 1.
8. `Erdos770/GRH.lean`: `Ankeny.bach_of_GRH` supplies the hypothesis of step 3.

## Layout

| File | Content |
|---|---|
| `Erdos770/Statement.lean` | `h`, `Erdos770Part3` (from formal-conjectures), `P`, `ExplicitBound` |
| `Erdos770/Basic.lean` | `P n` is the largest such prime; `P n ≤ h n` |
| `Erdos770/Core.lean` | bad prime, subgroup argument, counting bound |
| `Erdos770/Numerics.lean` | the real-analysis inequality for every `n ≥ 3` (constant `420`) |
| `Erdos770/Statement2.lean` | `ExplicitBound200` |
| `Erdos770/Numerics200.lean` | the same inequality for constant `200` |
| `Erdos770/Main200.lean` | `explicitBound200_of_bach`, `erdos_770_iii_of_bach200` |
| `Erdos770/GRH200.lean` | `explicitBound200_of_GRH` |
| `Erdos770/Main.lean` | `explicitBound_of_bach`, `erdos_770_iii_of_bach` |
| `Erdos770/GRH.lean` | `explicitBound_of_GRH`, `erdos_770_iii_of_GRH` |
| `Unconditional/Erdos770Unconditional.lean` | tier U versions (not in the default build) |
| `scripts/check-unconditional.sh` | builds and checks the file above |
| `docs/BLUEPRINT.md` | the blueprint |

## Deviations from the literature

The literature (Korsky's notes) states `h(n) ≤ max{P(n), C (log n)²}` under GRH with an unspecified
`C`. The headline here is `C = 200 = 2·10²`, with `2` Bach's own constant (proved under GRH in
lls-grh) and `10` the splitting exponent explained below. The earlier bound has `C = 420 = (21/5)·10²`: `21/5` is the constant of `Ankeny.bach_of_GRH` (Bach's own
constant is `2`, see ankeny-grh), and `10` is the exponent at which the proof splits the prime `r`
into `r ≤ n¹⁰` and `r > n¹⁰`. The `n ≥ 2` statements of both constants are proved here. Taking `10` rather than a value near `3` makes the counting
inequality of step 6 hold for every `n ≥ 3` with crude bounds, so no finite check of `h n` for
small `n` is needed. A splitting exponent nearer `2` would give a smaller `C` at the price of a sharper counting
inequality; this repository does not attempt it. Erdős 770 parts (i) and (ii) stay open and are not
treated. The
statement covers `n ≥ 2`.

## Building

```
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5`; ankeny-grh is required at `4f00a7395c7d` (it brings in
erdos-985) and lls-grh at `8a2924f396d9` (it brings in miller-grh and robin-rh; lls-grh's own
Ankeny pin is `129ad57`, an ancestor of ours with identical Lean sources). The `LLS` build
(chunk modules included) is about 2.3 CPU-hours cold, plus about 22 CPU-minutes for `Bach2`. The first build compiles `Ankeny.Main`, with its `native_decide` chunks: about 11 min
wall, 38 CPU-minutes (run `lake exe cache get` first for Mathlib). Rebuilds of this repository
alone take about 3.5 min.

## Unconditional version

`Unconditional/Erdos770Unconditional.lean` imports riemann-hypothesis (commit `507a75d91d`) and
closes the hypothesis with its theorem `LFunction_ne_zero_of_half_lt_re`:

| Theorem | Statement | Axioms |
|---|---|---|
| `Erdos770.Unconditional.explicitBound200` | `ExplicitBound 200 2` | standard three + 15 `native_decide` |
| `Erdos770.Unconditional.explicitBound` | `ExplicitBound 420 2` | standard three + 8 `native_decide` |
| `Erdos770.Unconditional.erdos_770_iii` | `Erdos770Part3` | standard three + 8 `native_decide` |

Checked 2026-11-25 with `scripts/check-unconditional.sh` against riemann-hypothesis `507a75d91d`: the run exited 0 and `#print axioms` printed, for `explicitBound200`, the standard three plus the 15 `LLS.chunk2_ok_*` `native_decide` axioms, and, for `explicitBound` and `erdos_770_iii`, the standard three plus the 8 `Ankeny.chunk_ok_*` ones (no `sorryAx`). The run took about 51 min wall, which includes time queued for a memory slot and shared load; the `lean` process peaked at about 11.9 GB resident.

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first (on Linux,
`sudo prlimit --pid $$ --nofile=2000000:2000000`; on macOS,
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

- `Erdos770/Statement.lean`: `h` and the body of `Erdos770Part3` are copied from
  google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/770.lean`, commit
  `86a2f58a4d7a3a0637d15d5b2ce627592b54b956`, Apache-2.0, Copyright 2026 The Formal Conjectures
  Authors. Changes: the namespace, and the statement given as a `Prop`. See `NOTICE`.
- `Ankeny.BachSubgroupBound` and `Ankeny.bach_of_GRH`: [ankeny-grh](https://github.com/senamakel/ankeny-grh),
  which builds on [erdos-985](https://github.com/senamakel/erdos-985).
- `LLS.bach2_of_GRH`: [lls-grh](https://github.com/senamakel/lls-grh), after Bach (1990).
- `LFunction_ne_zero_of_half_lt_re`: leanprover-community/riemann-hypothesis (not vendored).
