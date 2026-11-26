# Implications between open conjectures in Lean

Each module proves one implication `X → Y` between open conjectures, where the deduction is
published or folklore and both statements are copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) where it has them.
Every theorem here is tier C: the premise is an explicit hypothesis. None of them proves `X` or
`Y`; each becomes an unconditional theorem the day its premise is proved in Lean.

The edges come from the [implication atlas](../../docs/atlas/).

| Module | Premise | Consequence | Source | Axioms |
| :--- | :--- | :--- | :--- | :--- |
| `ABC/Erdos936` | abc (`ABC.abc`) | Erdős 936: `2^n ± 1`, `n! ± 1` are powerful only finitely often (`erdos_936.variants.*`, all four) | Cushing–Pascoe, arXiv:1611.01192, Lemma 4.3; CrowdMath, arXiv:2005.07321, Thm 2.3 | standard three |
| `ABC/Erdos977` | abc (`ABC.abc`) | Erdős 977, factorial variant: `P(n!+1)/n → ∞` (`erdos_977.variants.factorial`) | after Murty–Wong 2002 (they prove `P(n!+1) > (1+o(1)) n log n`; only `→ ∞` is proved here) | standard three |
| `Implications.FourExponentials.TwoPowThreePow` | `Exponentials.four_exponentials_conjecture` | `Exponentials.two_pow_three_pow_transcendental` | folklore (four exponentials applied to `(1, t)`, `(log 2, log 3)`) | standard three |
| `Implications.Hadamard.ButsonDoubling` | `ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture` | `Hadamard.HadamardConjecture` | Turyn 1970, doubling | standard three |
| [`PrimeGaps.Erdos382`](Implications/PrimeGaps/Erdos382.lean) | Cramér's conjecture `CramerConjecture.cramer_conjecture`, its strict form `cramer_conjecture.variants.strict_bound`, or Firoozbakht's conjecture `Firoozbakht.firoozbakht_conjecture` (each via `SubpowerGaps`: gaps `≤ p_n^ε` eventually) | Erdős 382 (i) `erdos_382.parts.i` | Cambie, quoted at erdosproblems.com/382; Firoozbakht ⇒ Cramér via Chebyshev's `π(x) log x ≥ x log 2` | standard three |
| `Wieferich/Rotkiewicz` | `{n : ℕ \| Squarefree (mersenne n)}.Infinite` | `{p : ℕ \| p.Prime ∧ ¬ IsWieferichPrime p}.Infinite`; also `sq_dvd_mersenne_iff_isWieferichPrime` (no premise) | Rotkiewicz 1965 | standard three |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build Implications`, or one module at a time.
