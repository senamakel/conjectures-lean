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

The range `5040 < n ≤ exp(e^{30})` is the one cited `sorry`: Morrill and Platt's unconditional
verification of Robin's inequality for `n ≤ 10^{10^{13.11}}` (Integers 21 (2021),
arXiv:1809.10813), extending Briggs (2006).

RH itself is a hypothesis; it is proved as `riemannHypothesis` in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).

`Robin.lagarias_of_RH` derives Lagarias's form `σ(n) ≤ H_n + exp(H_n) log H_n` from it, with a
finite check for `n ≤ 5040` (one documented `native_decide` over ℚ for `13 ≤ n ≤ 5040`).

Build: `lake build Robin`.
