# Erdős Problem 985 from GRH, in Lean

[Erdős Problem 985](https://www.erdosproblems.com/985) asks whether every odd prime `p` has a
**prime** primitive root `q < p`. This project proves that it does, assuming GRH for Dirichlet
L-functions:

```lean
theorem Erdos985.erdos_985_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1
```

The statement matches `erdos_985` in
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/985.lean).
The hypothesis is copied word for word from `src/Statements.lean` of
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
and both projects use the same Mathlib (`fc4f59e5`, Lean v4.36.0). The theorem
`LFunction_ne_zero_of_half_lt_re` there, which claims a proof of GRH for Dirichlet L-functions,
therefore fills the hypothesis directly. That proof was announced on 2026-11-20 and its
independent verification is still in progress.

## What a reader has to trust

`#print axioms Erdos985.erdos_985_of_GRH` prints:

| Axiom | Where it comes from |
|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | Lean's standard axioms |
| `sorryAx` | the two cited Bach lemmas in `Erdos985/Bach.lean`, and nothing else |
| 20 × `…native_decide.ax_*` | the finite check for `p < 10^8`, one per chunk |

- **The Bach lemmas** are Lemma 1 of McGown, Treviño and Trudgian,
  [*Resolving Grosswald's conjecture on GRH*](https://arxiv.org/abs/1508.05182). They follow
  Bach, *Comments on search procedures for primitive roots*, Math. Comp. 66 (1997). Under GRH they give explicit bounds for
  `Σ_{n<x} χ(n)Λ(n)(1 − n/x)`. Proving them in Lean needs an explicit formula for `ψ(x, χ)`
  with explicit constants: the Hadamard product of the completed L-function and an explicit
  zero count. Mathlib has neither yet, so this is the one gap in the proof.
- **The finite check** runs a checker whose soundness is proved
  (`Erdos985.Compute.checkAll_sound`, which uses only the standard axioms). It is evaluated
  with `native_decide`, which also trusts Lean's compiler. Replacing it with kernel-checked
  certificates would remove that assumption.

## How the proof goes

| File | Content |
|---|---|
| `Erdos985/Statement.lean` | the hypothesis and the statement |
| `Erdos985/Bach.lean` | the cited analytic input (MTT Lemma 1), stated at integer `x` |
| `Erdos985/Indicator.lean` | if no prime `q < x ≤ p` is a primitive root, then `S₀ ≤ (2^ω(p−1) − 1) · max_{χ≠1} ‖S_χ‖` |
| `Erdos985/Numerics.lean` | for `p ≥ 10^8`, Bach's bounds make that inequality impossible |
| `Erdos985/Compute.lean` | every odd prime `p < 10^8` has a prime primitive root `q < p` |
| `Erdos985/Main.lean` | combines the above |

- **Indicator.** Take one character `ψ` of order `p − 1`. If `n` is not a primitive root, one
  factor of `∏_{ℓ | p−1} ((1 − 1/ℓ) − (1/ℓ) Σ_{0<i<ℓ} ψ(n)^{i(p−1)/ℓ})` vanishes. Expanding
  the product over subsets of the prime factors gives the bound directly, with the sharp
  constant `2^ω − 1`.
- **Numerics.** The proof splits into three cases: `ω(p−1) ≤ 8`, `ω = 9` (here `p − 1 ≥ 23 · 9699690`,
  the tight case with about a 4% margin), and `ω ≥ 10` (via `16^ω(n) · 30030 ≤ 16^6 · n`).
- **Compute.** For each prime the checker uses a base-2 Fermat filter, then searches small
  prime `q`, testing `q^((p−1)/r) ≢ 1` for each prime `r | p − 1`. Mathlib's
  `orderOf_eq_of_pow_and_pow_div_prime` then gives the order. The range is split into 20
  chunks of 5·10⁶ that lake builds in parallel, about 2 minutes on 18 cores.

## Building

```bash
lake exe cache get   # Mathlib
lake build
```

### Checking it against the riemann-hypothesis repository

`Unconditional/Erdos985Unconditional.lean` fills the hypothesis with
`LFunction_ne_zero_of_half_lt_re`. It needs that project's compiled modules, so it is not in
the default build. The community cache provides them, but that cache includes outputs from
untrusted builds, so this links the two proofs and does not verify the GRH proof:

```bash
# in a clone of leanprover-community/riemann-hypothesis
lake exe cache get
lake build --no-build Main
# then, from this project
RH=/path/to/riemann-hypothesis
LEAN_PATH="$(cd $RH && lake env printenv LEAN_PATH):$PWD/.lake/build/lib/lean" \
  lean Unconditional/Erdos985Unconditional.lean
```

The import opens about 900,000 module files. On macOS, raise the limits first, until the next
reboot:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`,
then `ulimit -n 1400000` in the shell that runs `lean`.

Result, checked on 2026-11-22: `erdos_985` compiles, and `#print axioms erdos_985` lists
`propext`, `Classical.choice`, `Quot.sound`, `sorryAx` (Bach's lemma only) and the 20
`native_decide` axioms. The riemann-hypothesis proof adds no axioms of its own.
