# Implications between open conjectures in Lean

Each module proves one implication `X → Y` between open conjectures, where the deduction is
published or folklore and both statements are copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) where it has them.
Every theorem here is tier C: the premise is an explicit hypothesis. None of them proves `X` or
`Y`; each becomes an unconditional theorem the day its premise is proved in Lean.

The edges come from the [implication atlas](../../docs/atlas/).

| Module | Premise | Consequence | Source | Axioms |
| :--- | :--- | :--- | :--- | :--- |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build Implications`, or one module at a time.
