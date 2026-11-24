# Deterministic Miller–Rabin under GRH in Lean

Under GRH every odd composite `n` has a strong-pseudoprime witness `a ≤ 2 log² n` (Miller 1976;
constant `2` by Bach, Math. Comp. 55 (1990)).

**Literature status: RH-consequence.** Miller's test is conditional on GRH (Miller 1976); this
repository is a Lean proof that GRH implies it, following Miller and Bach, with our constant
`21/5` weaker than Bach's `2`. It is not new mathematics. Unconditional polynomial-time primality
testing is Agrawal–Kayal–Saxena (2002), by a different method.

This repository proves the **unconditional
reduction**: Bach's subgroup bound implies Miller's statement and a correct primality test.
Bach's bound itself is proved from GRH, with constant `21/5`, in the sibling
[`ankeny-grh`](https://github.com/senamakel/ankeny-grh) repository, which is a lake dependency.
`Miller/GRH.lean` combines the two:

- `Miller.miller_of_GRH : GRH → MillerStatement (21 / 5)`
- `Miller.prime_iff_of_GRH`, and `Miller.millerTestGRH_iff_prime`, the executable test with
  `3 · (⌊log₂ n⌋ + 1)²` bases, which is at least `(21/5) log² n`.

Their axioms are the standard three plus the 8 `native_decide` axioms of ankeny-grh's finite
check (`Ankeny.chunk_ok_0 … chunk_ok_7`, below `q < 2^17`; about 20 CPU-minutes). These are
not "standard axioms only".

`Miller/Statement.lean` fixes the target definitions (`BachSubgroupBound`,
`IsStrongProbablePrime`, `MillerStatement`); they must not change.

## Results

No `sorry` anywhere. The first block is the reduction from Bach's bound, which uses the standard
three axioms only (`propext`, `Classical.choice`, `Quot.sound`). The GRH theorems below it
carry ankeny-grh's 8 `native_decide` axioms. Axiom lists are real output of `#print axioms`
(`lake env lean` on `Miller/Axioms.lean`, 2026-11-24, ankeny-grh `129ad57`).

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

This is a legitimate reduction, but its hypothesis `BachSubgroupBound 2` is Bach's original
constant, which **no repository here proves** (ankeny-grh reaches `21/5` only). Treat it as
"conditional on Bach's constant 2", not as a result about GRH. The GRH-based test is
`millerTestGRH` below, which uses `3 · (⌊log₂ n⌋ + 1)²` bases.

### GRH theorems (standard three + 8 `native_decide`)

| Theorem | Statement |
| --- | --- |
| `miller_of_GRH` | `GRH → MillerStatement (21 / 5)` |
| `prime_iff_of_GRH` | `GRH → Odd n → 1 < n → (n.Prime ↔ ∀ a, …, a ≤ (21/5) log² n → IsStrongProbablePrime n a)` |
| `millerTestGRH_iff_prime` | `GRH → Odd n → 1 < n → (millerTestGRH n = true ↔ n.Prime)` |

```
#print axioms Miller.miller_of_GRH
-- [propext, Classical.choice, Quot.sound,
--  Ankeny.chunk_ok_0._native.native_decide.ax_1_1, …, Ankeny.chunk_ok_7._native.native_decide.ax_1_1]
-- (same list for prime_iff_of_GRH and millerTestGRH_iff_prime)
#print axioms Miller.miller_of_bach      -- [propext, Classical.choice, Quot.sound]
#print axioms Miller.prime_iff_of_bach   -- [propext, Classical.choice, Quot.sound]
```

`millerTest n` is executable: it tests bases `1 ≤ a ≤ min (n - 1) ((Nat.log 2 n + 1)^2)` with
binary modular exponentiation; `(Nat.log 2 n + 1)^2 ≥ 2 log² n` is proved. `#guard` checks reject
561, 1105, 2047, 1373653, 25326001 and 3215031751 and agree with `Nat.Prime` on all odd numbers
below 3000. `Miller/Axioms.lean` prints the axioms of every theorem above.

## Proof outline

Write `n - 1 = 2^s d` with `d` odd. A non-unit base is always a witness, so it suffices to put
the unit strong liars in a proper subgroup `H` and apply Bach to `H`.

* If `p² ∣ n`: `H = {u : u^(n-1) = 1}`; the unit `1 + n/p` has order `p ∤ n - 1`.
* Otherwise `n = p m` with `p, m > 2` coprime. Take `r₀` maximal below `s` with some
  `w^(2^{r₀} d) = -1` and `H = {u : u^(2^{r₀} d) = ±1}`; the unit `↔ (w, 1)` under the Chinese
  remainder theorem lies outside `H`.

See [`docs/PLAN.md`](docs/PLAN.md).

## Building

`lake build` (Lean v4.36.0, Mathlib via the `erdos-985` dependency).

## Unconditional version

`Unconditional/MillerUnconditional.lean` imports [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with its theorem:

| Theorem | Statement | Axioms |
|---|---|---|
| `miller_unconditional` | `Miller.MillerStatement (21 / 5)` | standard three + ankeny-grh's 8 `native_decide` |
| `millerTestGRH_iff_prime_unconditional` | `millerTestGRH n = true ↔ n.Prime` for odd `n > 1` | same |

Checked 2026-11-24 with `scripts/check-unconditional.sh` against riemann-hypothesis `507a75d91d`: the build succeeded and `#print axioms` of both theorems printed exactly the standard three plus the 8 `native_decide` axioms (no `sorryAx`). The run took about 18 min wall, dominated by importing riemann-hypothesis.

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
