# Prime primitive roots modulo `p²` and every `p^k` under GRH in Lean

Erdős Problem 985 (<https://www.erdosproblems.com/985>) asks whether every odd prime `p` has a
prime `q < p` that is a primitive root modulo `p`. This project proves, under GRH for Dirichlet
L-functions, the stronger statement that every odd prime `p` has a prime `q < p` that is a
primitive root modulo `p²`, and therefore modulo `p^k` for every `k ≥ 1`. There are no
exceptions, `p = 3` included (`q = 2` has order 6 modulo 9). `Unconditional/` proves the same
statements in Lean with GRH supplied by the Lean proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).

**Status in the literature: RH-consequence (explicit form not found).** The statement is open
without GRH, because it implies Erdős 985 (best uniform unconditional bound for the least prime
primitive root modulo `p`: Ha, J. Number Theory 133 (2013), `ĝ(p) ≪ p^{3.1}`). For *integer*
primitive roots modulo `p²` the unconditional state is: Kerr, McGown and Trudgian
([arXiv:1908.11497](https://arxiv.org/abs/1908.11497), J. Number Theory 215 (2020)) show that
every prime has a primitive root modulo `p²` below `p` (indeed below `p^{0.99}`); Chen (IJNT 18
(2022)) gets `p^{0.74}`; McGown and Sorenson (*Computation of the least primitive root*,
Math. Comp. 94 (2025), 909–917, published online 2024) compute `h(p)` for `p ≤ 10^{16}` and prove
`h(p) < p^{2/3}`. None of these gives a *prime* root. Under GRH, Martin (*The least prime
primitive root and the shifted sieve*, Acta Arith. 80 (1997); arXiv:math/9807104, Corollary 3.1)
bounds the least prime primitive root modulo any `q` with primitive roots by
`≪ (ω(φ(q)) log ω(φ(q)))⁴ (log q)²` with an unspecified constant; at `q = p²` that gives our
statement for all sufficiently large `p`, not for every `p`. We did not find the statement for
every odd prime, under GRH or otherwise, in the sources listed under "Literature search" below.

## Main theorems

```lean
theorem PrimitiveRootSq.primitiveRootSq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    PrimitiveRootSqStatement                                    -- PrimitiveRootSq/Main.lean

theorem PrimitiveRootSq.primitiveRootPow_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    PrimitiveRootPowStatement                                   -- PrimitiveRootSq/Main.lean

def PrimitiveRootSqStatement : Prop :=                          -- PrimitiveRootSq/Statement.lean
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod (p ^ 2)) = p * (p - 1)

def PrimitiveRootPowStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q : ℕ, q.Prime ∧ q < p ∧
    ∀ k : ℕ, 1 ≤ k → orderOf (q : ZMod (p ^ k)) = (p ^ k).totient
```

Unconditional (`Unconditional/PrimitiveRootSqUnconditional.lean`, not in the default build):

```lean
theorem PrimitiveRootSq.Unconditional.primitiveRootSq : PrimitiveRootSqStatement
theorem PrimitiveRootSq.Unconditional.primitiveRootPow : PrimitiveRootPowStatement
```

## Tier and provenance

`primitiveRootSq_of_GRH` and `primitiveRootPow_of_GRH` are **tier C**: GRH is the explicit
hypothesis `Erdos985.DirichletLNonvanishingRightOfHalf`, which erdos-985 copies word for word
from `src/Statements.lean` of riemann-hypothesis. The `Unconditional/` theorems are **tier U**.
No formal-conjectures statement exists for the `p²` question; the statements mirror
formal-conjectures' `erdos_985` (as transcribed in erdos-985's `Statement.lean`), with
"primitive root modulo `m`" written `orderOf (q : ZMod m) = φ(m)`.

## Axioms

`lake build` on 2026-11-26 (Lean v4.36.0, Mathlib `fc4f59e5`), then `#print axioms`:

```
'PrimitiveRootSq.primitiveRootSq_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PrimitiveRootSq.Compute.chunk_ok_0._native.native_decide.ax_1_1,
 PrimitiveRootSq.Compute.chunk_ok_1._native.native_decide.ax_1_1,
 ...
 PrimitiveRootSq.Compute.chunk_ok_19._native.native_decide.ax_1_1]
```

(20 `chunk_ok_N` axioms, `N = 0, …, 19`; `primitiveRootPow_of_GRH` has the same list.) The
analytic part and the lift use the standard three only: `key_inequality`, `numerics` and
`orderOf_prime_pow` each print `[propext, Classical.choice, Quot.sound]`.

Each `native_decide` evaluates the checker `PrimitiveRootSq.Compute.checkFrom` on `5·10⁶`
consecutive integers; together they cover every `n < 10⁸`. The checker's soundness,
`PrimitiveRootSq.Compute.checkAll_sound`, is proved: for each odd prime `p < 10⁸` it produces a
prime `q < p` with `q^((p−1)/r) ≢ 1 (mod p)` for every prime `r ∣ p − 1` and
`q^(p−1) ≢ 1 (mod p²)`. The 20 chunks take about 26 CPU-minutes in total (50–100 s each).

## How the proof goes

Details and the numbers behind each constant are in [`docs/PLAN.md`](docs/PLAN.md).

1. **Lift** (`Lift.lean`). If `q` is a primitive root modulo the odd prime `p` and
   `q^(p−1) ≢ 1 (mod p²)`, then `q` is a primitive root modulo every `p^k`: write
   `q^(p−1) = 1 + p·a` with `p ∤ a` and use Mathlib's `ZMod.orderOf_one_add_mul_prime`. So it
   suffices to find a prime `q < p` that is a primitive root modulo `p` with
   `q^(p−1) ≢ 1 (mod p²)`.
2. **A character of order `p` modulo `p²`** (`Character.lean`). Take `η` with `η^p = 1` on units
   and `η(1 + p)` a primitive `p`-th root of unity. Its kernel contains every `a` with
   `a^(p−1) ≡ 1 (mod p²)`, and each `η^j`, `0 < j < p`, is primitive of conductor `p²` (it is
   non-trivial on `1 + p ≡ 1 (mod p)`).
3. **Bach's bound at any modulus** (`Bach.lean`). erdos-985's explicit formula and zero-sum bound
   `Σ_ρ m_ρ/|ρ(ρ+1)| ≤ (2/3)(log N + 5/3)` hold for every primitive `χ` modulo any `N`. We
   assemble them as `‖Σ_{n<x} Λ(n)χ(n)(1 − n/x)‖ ≤ (√x + 2 + 3/x)(2/3)(log N + 5/3) + log x + 1.6`
   and use it at `N = p` (constant `B₁`) and `N = p²` (constant `B₂`, with `2 log p`).
4. **Indicator inequality** (`Indicator.lean`). If no good `q < p` exists, then with
   `S₀ = Σ_{n<p} Λ(n)(1 − n/p)` and `θ = φ(p−1)/(p−1)`:
   `θ (S₀ − (2^ω − 1) B₁) ≤ (S₀ + (p − 1) B₂)/p`. The left side is erdos-985's expansion of the
   primitive-root indicator modulo `p`; the right side bounds it termwise by the indicator of
   `η(n) = 1`, expanded over the `p` powers of `η`.
5. **`θ ≥ (36495360/223092870)(28/29)^ω`** (`Theta.lean`), splitting the prime factors at 29.
6. **Numerics** (`Numerics.lean`). With `S₀ ≥ p/2 − √p/20 − 3` (erdos-985's
   `bach_principal_of_GRH`), the inequality fails for every `p ≥ 10⁸`: cases `ω(p−1) ≤ 8`,
   `ω = 9` (`p − 1 ≥ 223092870`, relative margin about 1.6%) and `ω ≥ 10` (`2^ω ≤ 4.87 p^{1/4} + 1`).
7. **Finite range** (`Compute/`). Every odd prime `p < 10⁸` is checked directly (step 1's two
   conditions). The largest witness needed is `q = 223` (at `p = 73189117`). The least prime
   primitive root modulo `p` fails modulo `p²` only at `p = 40487` (`q = 5`, `5^40486 ≡ 1 (mod
   40487²)`) below `10⁸`; there `q = 7` works.

| File | Content |
|---|---|
| `PrimitiveRootSq/Statement.lean` | the two target statements |
| `PrimitiveRootSq/Lift.lean` | primitive root mod `p` with `q^(p−1) ≢ 1 (mod p²)` ⇒ mod every `p^k` |
| `PrimitiveRootSq/Character.lean` | `η` modulo `p²`; primitivity of `η^j` |
| `PrimitiveRootSq/Bach.lean` | `bach_primitive_of_GRH` at any modulus |
| `PrimitiveRootSq/Indicator.lean` | `key_inequality` |
| `PrimitiveRootSq/Theta.lean` | `theta_ge` |
| `PrimitiveRootSq/Numerics.lean` | `numerics` for `p ≥ 10⁸` |
| `PrimitiveRootSq/Compute/Checker.lean` | the checker and `checkAll_sound` |
| `PrimitiveRootSq/Compute/ChunkNN.lean`, `Compute.lean` | the 20 `native_decide` chunks, `small_primes_good` |
| `PrimitiveRootSq/Main.lean` | `exists_good_of_GRH`, `primitiveRootSq_of_GRH`, `primitiveRootPow_of_GRH` |

## Deviations from the literature

No published statement fixes a target for this question, so there is no constant to match. The
threshold above which the analysis alone suffices is `10⁸`, the same as erdos-985's: the extra
term from the order-`p` characters costs about `(4/3)√p log p / θ`, which fits inside
erdos-985's margins (it uses 3.3 of the 4.9 percentage points in the tightest case `ω = 9`).
Expanding the `p²` condition against the full character product instead would cost
`2^ω B₂` and push the threshold to about `10^{10}`.

## Building

```bash
lake build          # Lean v4.36.0, Mathlib fc4f59e5, requires ../erdos-985 by path
```

Reuse erdos-985's build output (it is not rebuilt; this project imports only its analytic
modules and `Erdos985.Compute.Checker`, none of its `native_decide` chunks). The 20 `Compute`
chunks need about 6 GB of RAM each and 26 CPU-minutes in total; the rest builds in a few minutes.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `PrimitiveRootSq.Unconditional.primitiveRootSq` | `PrimitiveRootSqStatement` | standard three + 20 `native_decide` (expected; not yet run) |
| `PrimitiveRootSq.Unconditional.primitiveRootPow` | `PrimitiveRootPowStatement` | standard three + 20 `native_decide` (expected; not yet run) |

Each closes GRH in one line with `LFunction_ne_zero_of_half_lt_re` from riemann-hypothesis at
commit `507a75d91d`. Run `scripts/check-unconditional.sh /path/to/riemann-hypothesis`. It needs
the riemann-hypothesis community cache (about 93 GB), about 19 GB of RAM and an open-file limit
around 2,000,000 (`sudo prlimit --pid $$ --nofile=2000000:2000000` on Linux). The check has not
been run yet for this project.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Literature search (2026-11-26)

Searched and not found: a statement, conditional or not, that every odd prime has a *prime*
primitive root modulo `p²` (or modulo all `p^k`) below `p`.

- arXiv and the web (Exa): least prime primitive root modulo `p²` / prime powers, under GRH.
  Found KMT 2019, Chen 2022, McGown–Sorenson 2024 (integer roots only), MTT 2016 and Shoup 1992
  (modulo `p` only), Martin 1997 (asymptotic, all moduli, unspecified constant), Carella 2017.
- erdosproblems.com/985 and its discussion thread (two comments, both about the mod-`p`
  question); the erdosproblems.ai wiki page for 985.
- Zenodo (via Exa): primitive-root notes found concern modulo `p` only (e.g. 10.5281/zenodo.23004937).
- formal-conjectures (clone at `9097e2f`, and PRs searched for "primitive root" and "985", all
  states): only `ErdosProblems/985.lean` and PR #8222 (`ĝ(p) < √p − 2` modulo `p`), #7425
  (simultaneous primitive roots). Nothing modulo `p²`.
- 1337isnot1337/solved-conjectures (all remote branches, `git grep "primitive root"`): only
  cyclotomic Hadamard files.
- GitHub code search (Lean, `orderOf` with `ZMod (p ^ 2)`): no primitive-root-mod-`p²` results.
- The 2026-11-26 scout report (`docs/atlas/sweeps/2026-11-26/novel-via-rh.md`) lists further
  queries with the same outcome.

## Credits

The Lean development was built by OpenHuman agents. `PrimitiveRootSq/Bach.lean` repeats the
assembly of erdos-985's `bach_nonprincipal_of_GRH` for general modulus, `Indicator.lean` reuses
erdos-985's character expansion (`Erdos985.Indicator.W`, `norm_W_le`) and follows its
`principal_le_of_no_prime_primitive_root`, `Numerics.lean` follows erdos-985's `Numerics.lean`,
and `Compute/Checker.lean` extends erdos-985's checker; all from this repository (GPLv3). The
analytic method is that of McGown, Treviño and Trudgian, *Resolving Grosswald's conjecture on
GRH*, Funct. Approx. Comment. Math. 55 (2016), after Bach, Math. Comp. 66 (1997).
