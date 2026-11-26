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
| [`HardyLittlewood.Richards`](Implications/HardyLittlewood/Richards.lean) | first Hardy–Littlewood conjecture, all tuples (`∀ m, FirstHardyLittlewoodConjectureFor m`) | the second fails: `¬ ∀ x y ≥ 2, π(x + y) ≤ π x + π y` (`HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture`) | Hensley–Richards 1973; Richards 1974 | standard three |
| [`PrimeGaps.Erdos382`](Implications/PrimeGaps/Erdos382.lean) | Cramér's conjecture `CramerConjecture.cramer_conjecture`, its strict form `cramer_conjecture.variants.strict_bound`, or Firoozbakht's conjecture `Firoozbakht.firoozbakht_conjecture` (each via `SubpowerGaps`: gaps `≤ p_n^ε` eventually) | Erdős 382 (i) `erdos_382.parts.i` | Cambie, quoted at erdosproblems.com/382; Firoozbakht ⇒ Cramér via Chebyshev's `π(x) log x ≥ x log 2` | standard three |
| `Wieferich/Rotkiewicz` | `{n : ℕ \| Squarefree (mersenne n)}.Infinite` | `{p : ℕ \| p.Prime ∧ ¬ IsWieferichPrime p}.Infinite`; also `sq_dvd_mersenne_iff_isWieferichPrime` (no premise) | Rotkiewicz 1965 | standard three |

## Richards: the two Hardy–Littlewood conjectures are incompatible

[`Implications/HardyLittlewood/Richards.lean`](Implications/HardyLittlewood/Richards.lean) is a
Lean proof of Richards' theorem (Hensley–Richards, *Acta Arith.* 25 (1973/74), 375–391;
Richards, *Bull. Amer. Math. Soc.* 80 (1974), 419–438): the first Hardy–Littlewood conjecture
implies that the second is false. The statement is formal-conjectures'
`HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture` (`FormalConjectures/Wikipedia/HardyLittlewood.lean`,
commit `9097e2f`, marked `research solved` with body `sorry`), copied unchanged:

```lean
theorem not_first_and_secondHardyLittlewoodConjecture :
    (∀ {k : ℕ} (m : Fin k.succ → ℕ), FirstHardyLittlewoodConjectureFor m) →
      ¬(∀ {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y), SecondHardyLittlewoodConjectureFor x y)
```

The definitions `IsPrimeConstellation`, `IsAdmissiblePrimeConstellation`, `Nat.numResidues`,
`Nat.primeTupleCounting`, `FirstHardyLittlewoodConjectureFor` and
`SecondHardyLittlewoodConjectureFor` are copied word for word into
[`Statement.lean`](Implications/HardyLittlewood/Statement.lean) (Apache-2.0, © 2025 The Formal
Conjectures Authors). Both conjectures remain open; the theorem is tier C, conditional on the
first conjecture, and says that at most one of the two is true.

Proof:

1. [`Tuple.lean`](Implications/HardyLittlewood/Tuple.lean) holds an admissible 447-tuple
   `0 = m₀ < m₁ = 2 < ⋯ < m₄₄₆ = 3158` of even numbers, `admissible_447_3158.txt` from the
   Polymath8 database of narrow admissible tuples (math.mit.edu/~primegaps); Engelsma first
   found a 447-tuple of width 3159. For each `q = 2, …, 447` a residue class missed by the tuple
   is listed and checked. Also there: `π(3159) ≤ 446`, by trial division with a checker proved
   complete for primes. All checks are kernel `decide`; there is no `native_decide`.
2. The Hardy–Littlewood constant of the tuple is positive (`tprod_pos`). Every factor is
   positive because the tuple misses a class mod every prime, and for `q > 3158` the factor
   `(1 − 447/q)/(1 − 1/q)^447` is within `2·447²/q²` of `1`, so the logs are summable and the
   product equals the exponential of their sum.
3. The integral `∫ t in 2..n, 1/log t ^ 447` is positive for `n ≥ 3`, so the asymptotic of the
   first conjecture makes the counting function nonzero for some `n`: there is a `p` with all 447
   numbers `p + mᵢ` prime, and `p ≥ 3` since `p + 2` is prime.
4. These are 447 primes in `[p, p + 3158]`, so `π(p − 1 + 3159) ≥ π(p − 1) + 447`. The second
   conjecture at `x = p − 1`, `y = 3159` gives `≤ π(p − 1) + π(3159) ≤ π(p − 1) + 446`.

Axioms (`#print axioms HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture`):

```
'HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`lake build Implications.HardyLittlewood.Richards`: `Tuple` (the kernel checks) took 100 s wall
on a heavily loaded build box, `Richards` 9 s.

The Lean proof was built with [OpenHuman](https://github.com/tinyhumansai/openhuman) agents
running in an [RSI Ralph](https://github.com/tinyhumansai/rsi-ralph) loop.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build Implications`, or one module at a time.
