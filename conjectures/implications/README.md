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
| `ABC/Erdos936` | abc (`ABC.abc`) | Erdős 936: `2^n ± 1`, `n! ± 1` are powerful only finitely often (`erdos_936.variants.*`, all four) | Cushing–Pascoe, arXiv:1611.01192, Lemma 4.3; CrowdMath, arXiv:2005.07321, Thm 2.3 | standard three |
| `ABC/Erdos977` | abc (`ABC.abc`) | Erdős 977, factorial variant: `P(n!+1)/n → ∞` (`erdos_977.variants.factorial`) | after Murty–Wong 2002 (they prove `P(n!+1) > (1+o(1)) n log n`; only `→ ∞` is proved here) | standard three |
| `ABC/Variants` | abc (`ABC.abc`) | `ABC.abc.variants.lt_constant_mul` and `ABC.abc.variants.quality`; all three forms proved equivalent | folklore (finite set gives the constant; constant at `ε/2` gives finiteness; `rad(abc) ≥ 2` makes the quality form the same set) | standard three |
| `ABC/PowerfulTriples` | abc (`ABC.abc`) | only finitely many `n` with `n, n+1, n+2` powerful (`Erdos364.FinitelyManyPowerfulTriples`, our finiteness weakening of fc `erdos_364`, which says none exist) | folklore, noted at erdosproblems.com/364: abc on `(1, n(n+2), (n+1)²)` at `ε = 1/4` | standard three |
| `ABC/Erdos366` | abc (`ABC.abc`) | finitely many `n` with (`n` 2-full, `n+1` 3-full), (3-full, 2-full), (3-full, 3-full) (`Erdos366.*Finite`, our finiteness companions of fc `erdos_366`, `.variants.three_two`, `.variants.weaker`) | Turturean, erdosproblems.com/366 comments: abc on `(n, 1, n+1)` | standard three |
| `ABC/Brocard` | abc (`ABC.abc`) | Brocard's `n! + 1 = m²` has finitely many solutions (`Erdos398.BrocardFinite`, our finiteness weakening of fc `erdos_398 = {4, 5, 7}`) | Overholt 1993; here a corollary of `ABC/Erdos936` (a square is powerful) | standard three |
| `ABC/Silverman` | abc (`ABC.abc`) | `{p : ℕ \| p.Prime ∧ ¬ IsWieferichPrime p}.Infinite` (conclusion of fc `Mersenne.rotkiewicz_...`; definitions from `Wieferich/Rotkiewicz`) | Silverman 1988, elementary form: primes dividing `2^n − 1` once are non-Wieferich, and abc on `(1, 2^n − 1, 2^n)` bounds `rad(2^n−1)² ≤ Q²(2^n−1)` away | standard three |
| `Implications.FourExponentials.TwoPowThreePow` | `Exponentials.four_exponentials_conjecture` | `Exponentials.two_pow_three_pow_transcendental` | folklore (four exponentials applied to `(1, t)`, `(log 2, log 3)`) | standard three |
| `Implications.Hadamard.ButsonDoubling` | `ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture` | `Hadamard.HadamardConjecture` | Turyn 1970, doubling | standard three |
| [`PrimeGaps.Erdos382`](Implications/PrimeGaps/Erdos382.lean) | Cramér's conjecture `CramerConjecture.cramer_conjecture`, its strict form `cramer_conjecture.variants.strict_bound`, or Firoozbakht's conjecture `Firoozbakht.firoozbakht_conjecture` (each via `SubpowerGaps`: gaps `≤ p_n^ε` eventually) | Erdős 382 (i) `erdos_382.parts.i` | Cambie, quoted at erdosproblems.com/382; Firoozbakht ⇒ Cramér via Chebyshev's `π(x) log x ≥ x log 2` | standard three |
| `Wieferich/Rotkiewicz` | `{n : ℕ \| Squarefree (mersenne n)}.Infinite` | `{p : ℕ \| p.Prime ∧ ¬ IsWieferichPrime p}.Infinite`; also `sq_dvd_mersenne_iff_isWieferichPrime` (no premise) | Rotkiewicz 1965 | standard three |
| `Dickson/` (`Schinzel`, `Specialisations`, `Erdos891`, `Erdos647`) | Schinzel's H; Dickson's conjecture | Dickson and Bunyakovsky (from H); twin, generalised twin, cousin, sexy and Sophie Germain primes; Erdős 891 Weisenberg variant; Erdős 647 windowed variant (all from Dickson) | specialisations; Weisenberg (erdosproblems.com/891); Erdős 647: our construction, `n = k!·t` with `(k!/j)t − 1` prime | standard three |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build Implications`, or one module at a time.
