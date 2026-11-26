# Plan: a prime `q < p` that is a primitive root modulo `p²`, under GRH

Target (`PrimitiveRootSq/Statement.lean`):

```lean
def PrimitiveRootSqStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod (p ^ 2)) = p * (p - 1)
def PrimitiveRootPowStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q : ℕ, q.Prime ∧ q < p ∧
    ∀ k : ℕ, 1 ≤ k → orderOf (q : ZMod (p ^ k)) = (p ^ k).totient
```

Both follow from the intermediate statement "there is a prime `q < p` with
`orderOf (q : ZMod p) = p - 1` and `(q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1`" by the classical lift
(`PrimitiveRootSq/Lift.lean`, proved: Mathlib has `ZMod.orderOf_one_add_mul_prime` but not the
lift itself).

## Small cases and the finite range

A C program (scratch, not kept) checked every odd prime `p < 10^8` (5,761,454 primes): each has
a prime `q < 224` that is a primitive root modulo `p` with `q^(p−1) ≢ 1 (mod p²)`. So the
statement has **no exceptions** below `10^8`. The least prime primitive root modulo `p` fails
modulo `p²` for exactly one prime below `10^8`: `p = 40487`, `q = 5` (the next prime root, `q = 13`, works there; McGown–Sorenson list
40487 and 6692367337 as the primes below `10^16` with `g(p) ≠ h(p)`). The largest least witness
below `10^8` is `q = 223` at `p = 73189117`.

## The analytic inequality

Notation, all at `x = p`: `w(n) = 1 − n/p`, `S₀ = Σ_{n<p} Λ(n) w(n)`, `ω = ω(p − 1)`,
`θ = ∏_{ℓ | p−1} (1 − 1/ℓ)`, `A = √p + 2 + 3/p`, `L = log p`, and

- `B₁ = A·(2/3)(L + 5/3) + L + 1.6`, the GRH bound for `‖bachSum χ p‖` for a primitive
  character `χ` modulo `p`;
- `B₂ = A·(2/3)(2L + 5/3) + L + 1.6`, the same bound for a primitive character modulo `p²`.

Both come from erdos-985's explicit formula, whose zero sum is proved for **any** modulus `N`
and any primitive `χ ≠ 1` (`Erdos985.Analytic.zeroSum_le`: `≤ (2/3)(log N + 5/3)`). erdos-985
assembles it only for prime `N` (`bach_nonprincipal_of_GRH`); `PrimitiveRootSq/Bach.lean`
re-assembles it for general `N` (the same 40 lines), so nothing analytic is new.

Suppose no prime `q < p` is a primitive root modulo `p` with `q^(p−1) ≢ 1 (mod p²)`. Take a
character `ψ` of order `p − 1` modulo `p`, and a character `η` modulo `p²` with `η^p = 1` on
units and `η(1 + p)` a primitive `p`-th root of unity. Then:

1. `I(n) = ∏_{ℓ | p−1} ((1 − 1/ℓ) − (1/ℓ) Σ_{0<i<ℓ} ψ(n)^{i(p−1)/ℓ})` is `1` when `n` is a
   primitive root modulo `p` and `0` otherwise. Expanding the product exactly as erdos-985
   does gives `Re Σ_{n<p} Λ(n) w(n) I(n) ≥ θ (S₀ − (2^ω − 1) B₁)`.
2. `J(n) = (1/p) Σ_{0≤j<p} η(n)^j` is `1` if `η(n) = 1` and `0` otherwise. If `n = q^k < p`
   is a primitive root modulo `p`, so is `q`, and the assumption gives `q^(p−1) ≡ 1 (mod p²)`,
   so `η(n) = 1`. Hence `I(n) ≤ J(n)` on the support of `Λ`.
3. `η^j` (`0 < j < p`) is non-trivial on `1 + p`, so it does not factor through level `p`: it
   is primitive modulo `p²`. So `Σ Λ w J ≤ (S₀ + (p − 1) B₂)/p`.

Together:

```
θ · (S₀ − (2^ω − 1) B₁)  ≤  (S₀ + (p − 1) B₂) / p  ≤  S₀⁺/p + B₂,      S₀⁺ = p/2 + √p/20 + 3.
```

The extra cost against erdos-985 is the term `(S₀⁺/p + B₂)/θ`, about `(4/3)√p log p / θ`. The
scout's model put a `2/θ` next to `2^ω`; this is the same thing. Expanding `1_W` against the
full product instead (characters `ψ^a η^j`) would cost `2^ω B₂`, which is far worse: with it the
threshold rises to about `10^10`.

Lower bound for `θ` (proved in `PrimitiveRootSq/Theta.lean`): splitting the prime factors at
29,

```
θ ≥ c₂₉ · (28/29)^ω,   c₂₉ = ∏_{ℓ<29} (1 − 1/ℓ) = 36495360 / 223092870 ≈ 0.163588.
```

## Threshold `P₀ = 10^8`: the same as erdos-985

With `S₀ ≥ p/2 − √p/20 − 3` (erdos-985's `bach_principal_of_GRH`), the contradiction needs

```
c₂₉ (28/29)^ω · (p/2 − √p/20 − 3 − (2^ω − 1) B₁)  >  0.5001 + B₂.
```

It holds for every prime `p ≥ 10^8`. Same three cases as erdos-985's `Numerics.lean`, same
tangent bounds for `log`; relative margin `(LHS − RHS)/(p/2)` at the worst point, computed with
the bounds the Lean proof uses:

| Case | Range used | `1/θ` bound | worst margin |
|---|---|---|---|
| `ω ≤ 8` | `p ≥ 10^8`, `log` tangent at `√p = 2^14` | `8.094` | 26.8% (at `p = 10^8`) |
| `ω = 9` | `p − 1 ≥ 2·3·…·23 = 223092870` | `8.383` | 1.64% (at `p = 223092871`) |
| `ω ≥ 10` | `2^ω ≤ 4.87 p^{1/4} + 1`, `log` tangent at `p^{1/4} = 256` | `0.00852 · 2^ω` | 24% |

(erdos-985's own margin in the `ω = 9` case is about 4.9%; our extra term uses up 3.3 points
of it.) Per-`ω` thresholds with the true `1/θ`: `ω = 8` closes at `4.7·10^7`, `ω = 9` from its
primorial. With the cruder `θ ≥ (1/3)(4/5)^ω` the `ω = 9` case would need `p ≥ 2.4·10^8`, which
is why the split is at 29.

## Finite check: every odd prime `p < 10^8`

erdos-985's certificate cannot be reused as it stands (its checker is a `Bool` function that
returns no witness, and its witness fails at `p = 40487`). `PrimitiveRootSq/Compute/Checker.lean`
copies it and adds one test per candidate, `powMod q (p − 1) (p·p) ≠ 1`; soundness
`PrimitiveRootSq.Compute.checkAll_sound` is proved. It reuses erdos-985's `powMod`, `powMod_eq`
and `smallPrimes` (primes below 2000, more than the 223 needed).

Cost: 20 chunks of `5·10^6`, one `native_decide` each. The heaviest chunk, `[9.5·10^7, 10^8)`,
built in 103 s (93 s CPU, 6.1 GB peak RSS) on the shared 95-core box under load ~118. All 20 chunks were then built: about
26 CPU-minutes in total (1580 CPU-s), under the one-hour cap. Built in batches of three to stay inside the
box's free RAM.

## Module plan

| File | Content | Status |
|---|---|---|
| `Statement.lean` | the two targets | done |
| `Lift.lean` | primitive root mod `p` with `q^(p−1) ≢ 1 (mod p²)` ⇒ mod every `p^k` | done |
| `Compute/Checker.lean`, `Compute/ChunkNN.lean`, `Compute.lean` | finite range `p < 10^8` | done |
| `Bach.lean` | `bach_primitive_of_GRH`: GRH bound for primitive `χ` at any modulus `N` | done |
| `Character.lean` | `η` modulo `p²`, primitivity of `η^j` | done |
| `Indicator.lean` | the inequality above from "no good `q`" | done |
| `Theta.lean` | `θ ≥ c₂₉ (28/29)^ω` | done |
| `Numerics.lean` | the three cases for `p ≥ 10^8` | done |
| `Main.lean` | `primitiveRootSq_of_GRH`, `primitiveRootPow_of_GRH` | done |
| `Unconditional/PrimitiveRootSqUnconditional.lean` | one-line discharge | written, not run |
