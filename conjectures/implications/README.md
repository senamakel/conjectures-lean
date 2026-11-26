# Implications between open conjectures in Lean

Each module proves one implication `X → Y` between open conjectures, where the deduction is
published or folklore and both statements are copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) where it has them.
Every theorem here is tier C: the premise is an explicit hypothesis. None of them proves `X` or
`Y`; each becomes an unconditional theorem the day its premise is proved in Lean.

The edges come from the [implication atlas](../../docs/atlas/).

| Module | Premise | Consequence | Source | Axioms |
| :--- | :--- | :--- | :--- | :--- |
| [`Erdos142/FromQuantitativeDensity`](Implications/Erdos142/FromQuantitativeDensity.lean) | openai/math `OAI.Erdos3.QuantitativeDensityTheorem` (`r_k(N) ≤ C N exp(−c (log log N)^{1+η})`, `k ≥ 3`; proved there as `manuscriptQuantitativeDensityTheorem`, copied verbatim, tier H) | fc `erdos_142.variants.lower` (`r_k(N) = o(N / log N)`, `k ≥ 2`); Erdős #140 for all `k ≥ 3` (our statement; fc has no #140 file) | elementary: `maxCard ≤ extremalNumber` and `(log N)^C = exp(C log log N)`; the consequence is remarked on erdosproblems.com/142 | standard three |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build Implications`, or one module at a time.
