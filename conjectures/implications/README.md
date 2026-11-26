# Implications between open conjectures in Lean

Each module proves one implication `X → Y` between open conjectures, where the deduction is
published or folklore and both statements are copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) where it has them.
Every theorem here is tier C: the premise is an explicit hypothesis. None of them proves `X` or
`Y`; each becomes an unconditional theorem the day its premise is proved in Lean.

The edges come from the [implication atlas](../../docs/atlas/).

| Module | Premise | Consequence | Source | Axioms |
| :--- | :--- | :--- | :--- | :--- |
| `Implications.FourExponentials.TwoPowThreePow` | `Exponentials.four_exponentials_conjecture` | `Exponentials.two_pow_three_pow_transcendental` | folklore (four exponentials applied to `(1, t)`, `(log 2, log 3)`) | standard three |
| `Implications.Hadamard.ButsonDoubling` | `ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture` | `Hadamard.HadamardConjecture` | Turyn 1970, doubling | standard three |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build Implications`, or one module at a time.
