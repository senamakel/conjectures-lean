# Robin's inequality under RH in Lean

`Robin.robin_of_RH : RiemannHypothesis → RobinStatement`, i.e. under RH
`σ(n) < e^γ n log log n` for every `n > 5040` (Robin 1984), in Lean 4 + Mathlib.

* `Robin/Statement.lean` fixes the target statements (definitions unchanged).
* `Robin/Main.lean` proves `robin_of_RH`.
* `docs/PLAN.md` has the blueprint, the constants, and the status of every file.

The proof avoids colossally abundant numbers and zero counting. For `log n = x` it bounds
`σ(n)/n` by `n^ε ∏_p max_k (1 + ⋯ + p⁻ᵏ)p^{−kε}` with `ε = log(1+1/x)/log x`. It then shows,
for `x ≥ e^{30}`, that the result is below `e^γ log x`, using Mertens' theorem with an explicit
remainder and the RH bound `|∫₀ᵗ ψ − t²/2| ≤ t^{3/2}/20 + 4t`. That bound comes from the weighted
explicit formula of [erdos-985](https://github.com/senamakel/erdos-985), which is a lake
dependency; here it is re-derived under RH instead of GRH.

The range `5040 < n ≤ exp(e^{30})` is the one cited `sorry`, `robin_small_range`: Morrill and
Platt's unconditional verification of Robin's inequality for `5040 < n ≤ 10^{10^{13.11485}}`
(Integers 21 (2021); arXiv:1809.10813, Theorem 13), extending Briggs (2006). The sorry-free form
`Robin.robin_of_RH_of_verified` takes that range as an explicit hypothesis, `RobinVerifiedRange`.

RH itself is a hypothesis; it is proved as `riemannHypothesis` in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).

`Robin.lagarias_of_RH` derives Lagarias's form `σ(n) ≤ H_n + exp(H_n) log H_n` from it, with a
finite check for `n ≤ 5040` (one documented `native_decide` over ℚ for `13 ≤ n ≤ 5040`).

Build: `lake build Robin`.

## Unconditional version

`Unconditional/RobinUnconditional.lean` imports [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with its theorem:

| Theorem | Statement | Axioms |
|---|---|---|
| `robin_of_verified` | `RobinVerifiedRange → RobinStatement` | standard three only |
| `robin_unconditional` | `RobinStatement` | standard three + `sorryAx` (the cited Morrill–Platt range) |
| `lagarias_unconditional` | `LagariasStatement` | standard three + `sorryAx` + 1 `native_decide` |

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
