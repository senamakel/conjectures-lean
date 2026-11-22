# Deterministic Miller–Rabin under GRH in Lean

Under GRH every odd composite `n` has a strong-pseudoprime witness `a ≤ 2 log² n` (Miller 1976;
constant `2` by Bach, Math. Comp. 55 (1990)). This repository proves the **unconditional
reduction**: Bach's subgroup bound implies Miller's statement and a correct primality test.
Bach's bound itself is proved from GRH in the sibling `ankeny-grh` repository; see
[`Miller/Unconditional/README.md`](Miller/Unconditional/README.md) for how the two connect.

`Miller/Statement.lean` fixes the target definitions (`BachSubgroupBound`,
`IsStrongProbablePrime`, `MillerStatement`); they must not change.

## Results (no `sorry`, standard axioms only)

| Theorem | File |
| --- | --- |
| `miller_of_bach : BachSubgroupBound c → MillerStatement c` | `Miller/Reduction.lean` |
| `prime_iff_of_bach : BachSubgroupBound c → Odd n → 1 < n → (n.Prime ↔ ∀ a, 0 < a → a < n → a ≤ c log² n → IsStrongProbablePrime n a)` | `Miller/Reduction.lean` |
| `exists_proper_subgroup_liars`: for odd composite `n` the strong liars lie in a proper subgroup of `(ZMod n)ˣ` | `Miller/Liars.lean` |
| `isStrongProbablePrime_of_prime`: a prime is a strong probable prime to every base `0 < a < p` | `Miller/Basic.lean` |
| `millerTest_iff_prime : BachSubgroupBound 2 → Odd n → 1 < n → (millerTest n = true ↔ n.Prime)` | `Miller/Test.lean` |

`millerTest n` is executable: it tests bases `1 ≤ a ≤ min (n - 1) ((Nat.log 2 n + 1)^2)` with
binary modular exponentiation; `(Nat.log 2 n + 1)^2 ≥ 2 log² n` is proved. `#guard` checks reject
561, 1105, 2047, 1373653, 25326001 and 3215031751 and agree with `Nat.Prime` on all odd numbers
below 3000. `Miller/Axioms.lean` prints the axioms: `propext`, `Classical.choice`, `Quot.sound`.

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
