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
| [`PrimeGaps.FiroozbakhtOppermann`](Implications/PrimeGaps/FiroozbakhtOppermann.lean), [`PrimeGaps.Andrica`](Implications/PrimeGaps/Andrica.lean) | Firoozbakht's conjecture `Firoozbakht.firoozbakht_conjecture`; Oppermann's `Oppermann.oppermann_conjecture`; Andrica's `Andrica.andrica_conjecture` | Oppermann (`oppermann_of_firoozbakht`), hence Andrica, Legendre `LegendreConjecture.legendre_conjecture` and Brocard `Brocard.brocard_conjecture`; Oppermann ⇒ Andrica ⇒ Legendre; Oppermann ⇒ Brocard (fc's own proof, ported) | Firoozbakht ⇒ Oppermann/Andrica/Legendre/Brocard attributed to Ferreira–Mariano (not consulted; our proof: Chebyshev's `π(x) log x ≥ x log 2` gives `p_{k+1} - p_k < √p_k` for `p_k ≥ 2^16`, plus a kernel-`decide` chain of 535 primes for `127 ≤ m < 65731`); Oppermann ⇒ Andrica as on Wikipedia | standard three |
| `Wieferich/Rotkiewicz` | `{n : ℕ \| Squarefree (mersenne n)}.Infinite` | `{p : ℕ \| p.Prime ∧ ¬ IsWieferichPrime p}.Infinite`; also `sq_dvd_mersenne_iff_isWieferichPrime` (no premise) | Rotkiewicz 1965 | standard three |
| `Dickson/` (`Schinzel`, `Specialisations`, `Erdos891`, `Erdos647`) | Schinzel's H; Dickson's conjecture | Dickson and Bunyakovsky (from H); twin, generalised twin, cousin, sexy and Sophie Germain primes; Erdős 891 Weisenberg variant; Erdős 647 windowed variant (all from Dickson) | specialisations; Weisenberg (erdosproblems.com/891); Erdős 647: our construction, `n = k!·t` with `(k!/j)t − 1` prime | standard three |
| `Dickson/` (`Consecutive`, `Erdos141`, `Erdos218`, `BalancedPrimes`) | Dickson's conjecture | every admissible pattern occurs infinitely often as consecutive primes; Erdős 141 (`erdos_141`, `variants.eleven`, `.infinite_three`, `.infinite_general_case`); Erdős 218 `variants.infinite_equal_prime_gap`; `BalancedPrimes.balanced_primes`, `.balanced_primes_order` | standard: CRT puts a distinct prime `q_j > H` into each unwanted position, then Dickson on the forms `M t + a + h`; the patterns used are `0, k!, …, (k−1)·k!` | standard three |
| [`PrimeGaps.Granville`](Implications/PrimeGaps/Granville.lean) (refutations, route b) | Granville's conjecture `CramerConjecture.cramer_conjecture.variants.granville` (`limsup g_n/(log p_n)² ≥ 2e^{−γ}`); Firoozbakht `Firoozbakht.firoozbakht_conjecture` with fc's cited `firoozbakht_conjecture_consequence` (tier H) | the negations of `cramer_conjecture.variants.limsup_eq_one`, `cramer_conjecture.variants.strict_bound` and Shanks's `MaximalPrimeGap.shanks_maximal_prime_gap_conjecture`; Firoozbakht + its consequence ⇒ ¬ Granville | Granville 1995, Scand. Actuar. J. (remark recorded in the fc docstrings; primary source not read); only input `1 < 2e^{−γ}` from `γ < 2/3 < log 2` | standard three |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build Implications`, or one module at a time.

## Refutations between open prime-gap conjectures (`PrimeGaps.Granville`)

These are route-b refutations (`Y ⇒ ¬X`, see `AGENTS.md`, "Disproofs"). Granville's conjecture
implies that three other open conjectures are false; Granville's conjecture itself stays open,
and so do the other three. None of the four is proved or disproved here.

```lean
theorem not_limsupEqOne_of_granville (hG : CramerConjecture.Granville) :
    ¬ CramerConjecture.LimsupEqOne
theorem not_strictBound_of_granville (hG : CramerConjecture.Granville) :
    ¬ CramerConjecture.StrictBound
theorem not_shanks_of_granville (hG : CramerConjecture.Granville) :
    ¬ MaximalPrimeGap.ShanksConjecture
theorem strictBound_of_firoozbakht (hF : Firoozbakht.FiroozbakhtConjecture)
    (hK : Firoozbakht.FiroozbakhtConsequence) : CramerConjecture.StrictBound
theorem not_granville_of_firoozbakht (hF : Firoozbakht.FiroozbakhtConjecture)
    (hK : Firoozbakht.FiroozbakhtConsequence) : ¬ CramerConjecture.Granville
```

All five statements in [`Granville/Statement.lean`](Implications/PrimeGaps/Granville/Statement.lean)
(`Granville`, `LimsupEqOne`, `sup_primeGap`, `ShanksConjecture`, `FiroozbakhtConsequence`) are
copied word for word from formal-conjectures `9097e2f` (Apache-2.0); `cramerRatio`, `StrictBound`
and `FiroozbakhtConjecture` are the copies in `Erdos382.lean`. formal-conjectures states
Granville's conjecture without a real `limsup` (for each `c < 2e^{−γ}`, infinitely many `n` have
`c ≤ g_n / (log p_n)²`), and `limsup_eq_one` as two `ε`-statements, so no junk value of an
unbounded `limsup` enters any of them.

- Granville ⇒ ¬ `limsup_eq_one`: take `c = (1 + 2e^{−γ})/2 > 1` and `ε = (c − 1)/2`.
- Granville ⇒ ¬ `strict_bound`: take `c = 1`.
- Granville ⇒ ¬ Shanks: if `g_n ≥ c (log p_n)²` then `G(p_n + 1) ≥ g_n`, while Shanks gives
  `G(p_n + 1) ≤ (1 + ε)(log(p_n + 1))² ≤ (1 + ε)(log p_n + 1)²`, which is below `c (log p_n)²`
  once `log p_n ≥ 3(1 + ε)/ε`.
- Firoozbakht ⇒ ¬ Granville is proved only with fc's `firoozbakht_conjecture_consequence`
  (`g_n < (log p_n)² − log p_n` for `n > 3`, attributed on Wikipedia to Kourbatov 2015 and not checked; `research solved` in fc
  but not proved in Lean) as an explicit tier-H hypothesis. The module's own Firoozbakht bound
  (`cramer_of_firoozbakht` in `Erdos382.lean`, via Chebyshev) has constant `2/log 2 ≈ 2.885`,
  above `2e^{−γ} ≈ 1.1229`; getting below it without the cited consequence needs an explicit
  lower bound for `π(x)` of the form `x/(log x − 1)` (Dusart), which Mathlib does not have.

The only arithmetic input is `1 < 2e^{−γ}`, from Mathlib's `Real.eulerMascheroniConstant_lt_two_thirds`
and `Real.log_two_gt_d9`. The conjecture and the incompatibility are Granville's (*Harald Cramér
and the distribution of prime numbers*, Scand. Actuar. J. 1995, 12–28); the remark is taken from
the formal-conjectures docstrings and was not checked against the paper.

```
'Implications.PrimeGaps.not_limsupEqOne_of_granville' depends on axioms: [propext, Classical.choice, Quot.sound]
'Implications.PrimeGaps.not_strictBound_of_granville' depends on axioms: [propext, Classical.choice, Quot.sound]
'Implications.PrimeGaps.not_shanks_of_granville' depends on axioms: [propext, Classical.choice, Quot.sound]
'Implications.PrimeGaps.strictBound_of_firoozbakht' depends on axioms: [propext, Classical.choice, Quot.sound]
'Implications.PrimeGaps.not_granville_of_firoozbakht' depends on axioms: [propext, Classical.choice, Quot.sound]
```
