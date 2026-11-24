# Deterministic Miller–Rabin under GRH in Lean

Under GRH every odd composite `n` has a strong-pseudoprime witness `a ≤ 2 log² n` (Miller 1976;
constant `2` by Bach, Math. Comp. 55 (1990)). Unconditional polynomial-time primality testing
is Agrawal–Kayal–Saxena (2002), by a different method.

This repository proves in Lean that every odd composite `n` has a strong-pseudoprime witness
`a ≤ (21/5) log² n`, and that an executable Miller test with `3 · (⌊log₂ n⌋ + 1)²` bases decides
primality. The main library is a complete Lean proof that GRH implies both, following Miller
and Bach. `Unconditional/` proves `MillerStatement (21/5)` and the correctness of the
executable test unconditionally in Lean, with GRH supplied by the certified proof of L. Alpöge
in [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
Literature status: RH-consequence. Our constant is `21/5`; Bach's is `2`.

The proof has two halves. This repository proves the unconditional reduction: Bach's subgroup
bound implies Miller's statement and a correct primality test. Bach's bound itself is proved
from GRH, with constant `21/5`, in the sibling
[`ankeny-grh`](https://github.com/senamakel/ankeny-grh) repository, a lake dependency.
`Miller/GRH.lean` combines the two.

```lean
theorem Miller.miller_of_bach {c : ℝ} (h : BachSubgroupBound c) : MillerStatement c
theorem Miller.prime_iff_of_bach {c : ℝ} (h : BachSubgroupBound c) (n : ℕ) (hn : Odd n) (h1 : 1 < n) :
    n.Prime ↔ ∀ a : ℕ, 0 < a → a < n → (a : ℝ) ≤ c * Real.log n ^ 2 → IsStrongProbablePrime n a

theorem Miller.miller_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : MillerStatement (21 / 5)
theorem Miller.prime_iff_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (n : ℕ) (hn : Odd n)
    (h1 : 1 < n) :
    n.Prime ↔ ∀ a : ℕ, 0 < a → a < n → (a : ℝ) ≤ 21 / 5 * Real.log n ^ 2 →
      IsStrongProbablePrime n a
theorem Miller.millerTestGRH_iff_prime (hGRH : DirichletLNonvanishingRightOfHalf) {n : ℕ} (hn : Odd n)
    (h1 : 1 < n) : millerTestGRH n = true ↔ n.Prime

theorem miller_unconditional : Miller.MillerStatement (21 / 5)                 -- Unconditional/
theorem millerTestGRH_iff_prime_unconditional {n : ℕ} (hn : Odd n) (h1 : 1 < n) :
    Miller.millerTestGRH n = true ↔ n.Prime                                    -- Unconditional/
```

## Tier and provenance

`miller_of_bach` and `prime_iff_of_bach` take `BachSubgroupBound c` as a hypothesis and use the
standard three axioms only. `miller_of_GRH`, `prime_iff_of_GRH` and `millerTestGRH_iff_prime` are
tier C: GRH for Dirichlet L-functions is the explicit hypothesis
`Erdos985.DirichletLNonvanishingRightOfHalf`, copied word for word from riemann-hypothesis
`src/Statements.lean`. `miller_unconditional` and `millerTestGRH_iff_prime_unconditional` are
tier U: the hypothesis is closed by `LFunction_ne_zero_of_half_lt_re`.

`Miller/Statement.lean` fixes the target definitions `BachSubgroupBound`,
`IsStrongProbablePrime` and `MillerStatement`. `BachSubgroupBound` is copied verbatim from
`Ankeny.BachSubgroupBound` (ankeny-grh), so the two definitions are the same term and
`Ankeny.bach_of_GRH` plugs straight into `miller_of_bach`. No formal-conjectures statement
exists. The project has no `sorry`.

## Results

Axiom lists are real output of `#print axioms` (`lake env lean` on `Miller/Axioms.lean`,
2026-11-24, ankeny-grh `129ad57`).

### Reduction from Bach's bound (standard axioms only)

| Theorem | File |
| --- | --- |
| `miller_of_bach : BachSubgroupBound c → MillerStatement c` | `Miller/Reduction.lean` |
| `prime_iff_of_bach : BachSubgroupBound c → Odd n → 1 < n → (n.Prime ↔ ∀ a, 0 < a → a < n → a ≤ c log² n → IsStrongProbablePrime n a)` | `Miller/Reduction.lean` |
| `exists_proper_subgroup_liars`: for odd composite `n` the strong liars lie in a proper subgroup of `(ZMod n)ˣ` | `Miller/Liars.lean` |
| `isStrongProbablePrime_of_prime`: a prime is a strong probable prime to every base `0 < a < p` | `Miller/Basic.lean` |

### Conditional on Bach's constant 2 (not a headline result)

| Theorem | File |
| --- | --- |
| `millerTest_iff_prime : BachSubgroupBound 2 → Odd n → 1 < n → (millerTest n = true ↔ n.Prime)` | `Miller/Test.lean` |

The hypothesis `BachSubgroupBound 2` is Bach's original constant. No repository in this family
proves it: ankeny-grh proves `21/5`. The GRH-based test is `millerTestGRH` below, which uses
`3 · (⌊log₂ n⌋ + 1)²` bases.

### GRH theorems (standard three + 8 `native_decide`)

| Theorem | Statement |
| --- | --- |
| `miller_of_GRH` | `GRH → MillerStatement (21 / 5)` |
| `prime_iff_of_GRH` | `GRH → Odd n → 1 < n → (n.Prime ↔ ∀ a, …, a ≤ (21/5) log² n → IsStrongProbablePrime n a)` |
| `millerTestGRH_iff_prime` | `GRH → Odd n → 1 < n → (millerTestGRH n = true ↔ n.Prime)` |

## Axioms

```
#print axioms Miller.miller_of_GRH
-- [propext, Classical.choice, Quot.sound,
--  Ankeny.chunk_ok_0._native.native_decide.ax_1_1, …, Ankeny.chunk_ok_7._native.native_decide.ax_1_1]
-- (same list for prime_iff_of_GRH and millerTestGRH_iff_prime)
#print axioms Miller.miller_of_bach      -- [propext, Classical.choice, Quot.sound]
#print axioms Miller.prime_iff_of_bach   -- [propext, Classical.choice, Quot.sound]
```

The GRH theorems carry the 8 `native_decide` axioms of ankeny-grh's finite check
(`Ankeny.chunk_ok_0 … chunk_ok_7`). They evaluate ankeny-grh's proved-sound checker on every
modulus `q < 2^17`, about 20 CPU-minutes in total. This repository adds no `native_decide` of
its own. `Miller/Axioms.lean` prints the axioms of every theorem above.

## The executable test

`millerTest n` tests bases `1 ≤ a ≤ min (n - 1) ((Nat.log 2 n + 1)^2)` with binary modular
exponentiation, and `(Nat.log 2 n + 1)^2 ≥ 2 log² n` is proved. `millerTestGRH n` uses
`3 · (Nat.log 2 n + 1)^2` bases, and `log_sq_le_millerBoundGRH` proves that this is at least
`(21/5) log² n`. `#guard` checks reject 561, 1105, 2047, 1373653, 25326001 and 3215031751 and
agree with `Nat.Prime` on all odd numbers below 3000.

## Proof outline

Write `n - 1 = 2^s d` with `d` odd. A non-unit base is always a witness, so it suffices to put
the unit strong liars in a proper subgroup `H` and apply Bach to `H`.

1. `Miller/Liars.lean`, case `p² ∣ n`: take `H = {u : u^(n-1) = 1}`. The unit `1 + n/p` has
   order `p ∤ n - 1`.
2. `Miller/Liars.lean`, otherwise: `n = p m` with `p, m > 2` coprime. Take `r₀` maximal below
   `s` with some `w^(2^{r₀} d) = -1` and `H = {u : u^(2^{r₀} d) = ±1}`. The unit `↔ (w, 1)`
   under the Chinese remainder theorem lies outside `H`.
3. `Miller/Reduction.lean`: Bach's bound gives a unit `a ≤ c log² n` outside `H`, which is a
   witness (`miller_of_bach`, `prime_iff_of_bach`).
4. `Miller/GRH.lean`: `Ankeny.bach_of_GRH` supplies `BachSubgroupBound (21 / 5)`.

The blueprint is [`docs/PLAN.md`](docs/PLAN.md).

## Layout

| File | Content |
|---|---|
| `Miller/Statement.lean` | the target definitions |
| `Miller/Basic.lean` | a prime is a strong probable prime to every base |
| `Miller/Liars.lean` | the strong liars lie in a proper subgroup |
| `Miller/Reduction.lean` | `miller_of_bach`, `prime_iff_of_bach` |
| `Miller/Test.lean` | the executable `millerTest`, `millerTest_iff_prime` |
| `Miller/GRH.lean` | the GRH theorems and `millerTestGRH` |
| `Miller/Axioms.lean` | `#print axioms` for every theorem |
| `Unconditional/MillerUnconditional.lean` | the tier-U theorems |

## Deviations from the literature

The constant is `21/5`; Bach's is `2`. The constant comes from ankeny-grh's
`BachSubgroupBound (21 / 5)`, whose README explains why its analytic argument stops there.
Any better `BachSubgroupBound c` gives `MillerStatement c` through `miller_of_bach`.

## Building

`lake build` (Lean v4.36.0, Mathlib `fc4f59e5` via the `erdos-985` dependency, ankeny-grh at
`129ad57`). The build time is dominated by ankeny-grh's eight `native_decide` chunks.

## Unconditional version

`Unconditional/MillerUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with its theorem:

```lean
theorem miller_unconditional : Miller.MillerStatement (21 / 5) :=
  Miller.miller_of_GRH LFunction_ne_zero_of_half_lt_re
```

| Theorem | Statement | Axioms |
|---|---|---|
| `miller_unconditional` | `Miller.MillerStatement (21 / 5)` | standard three + ankeny-grh's 8 `native_decide` |
| `millerTestGRH_iff_prime_unconditional` | `millerTestGRH n = true ↔ n.Prime` for odd `n > 1` | same |

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
  checked against commit `507a75d91d`, through erdos-985's `Erdos985/Statement.lean`. That
  repository has no licence file; its code is imported only from `Unconditional/`.
- `BachSubgroupBound` and `Ankeny.bach_of_GRH`: [ankeny-grh](https://github.com/senamakel/ankeny-grh),
  required at `129ad57`.
- Analytic toolkit: [erdos-985](https://github.com/senamakel/erdos-985), required at `9538edb`.
  This repository vendors no files.
- Miller's test: Miller (1976), with Bach's constant (Math. Comp. 55, 1990).
