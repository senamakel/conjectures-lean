# Selberg's bound for Erdős Problem 233 and primes in almost all short intervals under RH in Lean

This repository proves, in Lean, that the sum of squares of the first `N` prime gaps is
`O(N log⁴ N)`. `erdos_233_upper_bound` is proved unconditionally, with RH supplied by the
certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
and the main library holds a complete Lean proof that RH implies the bound, following Selberg
(*Arch. Math. Naturvid.* 47 (1943)). Label: **RH-consequence**.

[Erdős Problem 233](https://www.erdosproblems.com/233) concerns the sum of squares of prime
gaps `d_n = p_{n+1} − p_n`. Heath-Brown conjectured `Σ_{n<N} d_n² ≍ N log² N`. The lower bound
`≫ N log² N` follows from the prime number theorem; the conjectured upper bound is open, also
under the Riemann hypothesis. Under RH, Cramér gave an earlier upper bound (formal-conjectures
attributes the `N log⁴ N` form to him), and Selberg proved `Σ_{p_n ≤ x} d_n² ≪ x log³ x`, which
is `Σ_{n<N} d_n² ≪ N log⁴ N` in index form because `p_N ≍ N log N`. formal-conjectures lists
this bound as the variant `erdos_233.variants.upper_bound`, tagged `research solved` (known under
RH). Cully-Hugill and Dudek give an explicit version,
[arXiv:2206.00433](https://arxiv.org/abs/2206.00433). Erdős 233 itself (`≪ N log² N`) remains
open, and this repository does not prove it.

The same paper of Selberg (*On the normal density of primes in small intervals, and the
difference between consecutive primes*, Arch. Math. Naturvid. 47 (6) (1943) 87-105) proves,
under RH, that almost all intervals `(x, x + Φ(x) log² x]` contain a prime whenever
`Φ(x) → ∞`, and that `π(x + h) − π(x) ~ h/log x` for almost all `x` in that range (label:
**RH-consequence**). The statements here follow the secondary accounts in Huang, Liu and Rudnick
([arXiv:1903.04005](https://arxiv.org/abs/1903.04005), §1), Cully-Hugill and Dudek
([arXiv:2206.00433](https://arxiv.org/abs/2206.00433), §1: increasing `h = o(x)` with
`h/log² x → ∞`; "almost all" means an exceptional set of measure `o(x)`, Selberg's footnote 4,
p. 161), and H. Maier's foreword to *Irregularities in the Distribution of Prime Numbers*
(Springer, 2018), which states the asymptotic form. Without RH, the best known result is primes
in almost all intervals `[x, x + x^{1/20+ε}]` (Jia, as quoted by Cully-Hugill and Dudek). The
main library proves that RH implies the existence form, following Selberg (1943), and
`Unconditional/` proves it unconditionally with the certified proof of RH. The asymptotic form
(`SelbergAsymptoticStatement`) is not proved; a smoothed version of it is (see below).

```lean
theorem Erdos233.erdos_233_upper_bound_of_RH (hRH : RiemannHypothesis) :
    Erdos233.Erdos233UpperBoundStatement          -- Erdos233/Main.lean

theorem erdos_233_upper_bound : Erdos233.Erdos233UpperBoundStatement
                                                   -- Unconditional/Erdos233Unconditional.lean

def Erdos233.Erdos233UpperBoundStatement : Prop :=   -- Erdos233/Statement.lean
    (fun N => ((∑ n ∈ Finset.range N, (primeGap n) ^ 2) : ℝ)) =O[atTop] fun N => N * (log N)^4
```

Primes in almost all short intervals (`Erdos233/Statement2.lean`, `Erdos233/AlmostAll.lean`):

```lean
def Erdos233.primelessSet (h : ℝ → ℝ) (X : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ¬ ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + h x}

def Erdos233.SelbergAlmostAllStatement : Prop :=
  ∀ h : ℝ → ℝ, Tendsto (fun x => h x / Real.log x ^ 2) atTop atTop →
    Tendsto (fun X => (volume (primelessSet h X)).toReal / X) atTop (𝓝 0)

def Erdos233.SelbergAsymptoticStatement : Prop :=      -- fixed target, NOT proved
  ∀ h : ℝ → ℝ, Monotone h → Tendsto (fun x => h x / Real.log x ^ 2) atTop atTop →
    Tendsto (fun x => h x / x) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → Tendsto (fun X => (volume (selbergBadSet h ε X)).toReal / X) atTop (𝓝 0)
  -- selbergBadSet h ε X: x ∈ [X, 2X] with |π(x+h x) − π(x) − h x/log x| > ε h x/log x

theorem Erdos233.selberg_almost_all_of_RH (hRH : RiemannHypothesis) :
    SelbergAlmostAllStatement

theorem Erdos233.primeless_measure_le (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ X : ℝ, X₀ ≤ X → ∀ H : ℝ, 64 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ H → H ≤ X / 2 →
    volume.real {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
        ¬ ∃ p : ℕ, p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + H}
      ≤ C * X * Real.log X ^ 2 / H

def Erdos233.SmoothedSelbergStatement : Prop :=        -- the weaker form proved
  ∀ H : ℝ → ℝ, Tendsto (fun X => H X / Real.log X ^ 2) atTop atTop →
    Tendsto (fun X => H X / X) atTop (𝓝 0) → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun X => (volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
        ε * (H X / X * y) ^ 2 < |D2 (H X / X) y - (H X / X * y) ^ 2|}).toReal / X)
      atTop (𝓝 0)

theorem Erdos233.smoothed_asymptotic_of_RH (hRH : RiemannHypothesis) :
    SmoothedSelbergStatement

theorem Erdos233.large_gaps_of_RH (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ x : ℕ, X₀ ≤ x → ∀ h : ℝ, 256 * (Real.log (5 * x) ^ 2 / Real.log 2) ≤ h → h ≤ 2 * x →
    ∑ n ∈ (block x).filter (fun n => h ≤ primeGap n), (primeGap n : ℝ)
      ≤ C * x * Real.log x ^ 2 / h
```

### Why this formulation

"Almost all" is Selberg's notion: the exceptional set has Lebesgue measure `o(X)`. The
statements measure it inside the dyadic block `[X, 2X]` with `volume`, an outer measure, so no
measurability side condition is needed. Summing blocks gives the same statement inside `[1, X]`.

The existence form assumes only `h(x)/log² x → ∞`. Cully-Hugill and Dudek also assume
monotonicity and `h = o(x)`, but existence does not need them (a larger `h` only helps), and the
proof does not use them. The asymptotic form keeps both (`Monotone h`, `h(x)/x → 0`): without
`h = o(x)` the main term `h/log x` is wrong (take `h = x²`), and the literature states it for
increasing `h`.

`SmoothedSelbergStatement` counts primes and prime powers with the tent weight of `D2`
(`D2 δ y = Σ_n Λ(n) w(n)`, `w` the tent of height `δy` on `(y, y(1+2δ))`, see
`Erdos233/Basic.lean`), at step `δ = H(X)/X` fixed across the block. It is an almost-all
asymptotic for this smoothed count. The sharp count `π(x+h) − π(x)` is the subject of
`SelbergAsymptoticStatement`.

## Tier and provenance

`Erdos233.erdos_233_upper_bound_of_RH` is tier C: RH is the explicit hypothesis
`RiemannHypothesis`, Mathlib's own definition (as in formal-conjectures). `erdos_233_upper_bound`
is tier U: it closes RH in one line with `riemannHypothesis` from
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
`selberg_almost_all_of_RH`, `primeless_measure_le`, `smoothed_asymptotic_of_RH` and
`large_gaps_of_RH` are tier C (same `RiemannHypothesis`); `selberg_almost_all`,
`smoothed_selberg_asymptotic` and `large_gaps` in `Unconditional/` are tier U.
`SelbergAsymptoticStatement` is a fixed target with no proof.

* `Erdos233UpperBoundStatement` and `primeGap` are copied verbatim from formal-conjectures
  [`ErdosProblems/233.lean`](https://github.com/google-deepmind/formal-conjectures/blob/d9f6ffa8dd7fc2b8b597dd1f7a824d27b12b88af/FormalConjectures/ErdosProblems/233.lean)
  (`erdos_233.variants.upper_bound`) and
  [`NumberTheory/PrimeGap.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean).
  `Erdos233Statement` (the open `erdos_233`, `N log² N`) is copied too, for reference; nothing
  here proves it.
* formal-conjectures has no statement of Selberg's almost-all theorem (searched 2026-11-24 for
  "Selberg", "short interval", "almost all" and `primeCounting`), so the definitions in
  `Erdos233/Statement2.lean` are this repository's own.
* There are no cited (`Prop`) hypotheses: every analytic input, including the explicit formula
  for real `x`, the local zero density and the mean-value estimate, is proved here or in
  erdos-985.

## Axioms

`lake env lean scripts/axioms.lean` (2026-11-24, this repository's `finality` branch):

```
'Erdos233.erdos_233_upper_bound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos233.selberg_almost_all_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos233.primeless_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos233.smoothed_asymptotic_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos233.large_gaps_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The repository has no `sorry`, no `native_decide` and no `axiom` or `opaque` declarations.

## Proof outline

The full blueprint, with the Lean statement of every step, is [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).
Instead of Selberg's `θ(y + δy) − θ(y)` we use the second difference
`D2 δ y = ψ₁(y(1+2δ)) − 2ψ₁(y(1+δ)) + ψ₁(y)` of `ψ₁(y) = Σ_{n≤y} Λ(n)(y − n)`, whose explicit
formula converges absolutely, so no truncated Perron formula is needed.

1. Every zero of `ξ` has real part `1/2` under RH (`RH.lean`).
2. `|D2 δ y − δ²y²| ≤ 6 + y^{3/2} |Σ_ρ m_ρ c_ρ(δ) y^{iγ}|`, from erdos-985's weighted explicit
   formula re-proved for real `x` (`Explicit.lean`, `Explicit/Formula.lean`).
3. `Σ_ρ m_ρ/(1 + (T−γ)²) ≤ C log(|T|+2)`, unconditional, from Hadamard at `2 + iT`
   (`Density.lean`).
4. `|c_ρ(δ)| ≤ min(δ², 4δ/|ρ|, 52/(1+γ²))`, hence `Σ m|c|² log(|γ|+2) ≪ δ³ log²(2/δ)`
   (`Coeff.lean`, `Coeff/`).
5. `∫_U^{U+2} |Σ m c e^{iγu}|² du ≪ Σ m|c|² log(|γ|+2)`, with a Gaussian weight (`MeanValue.lean`).
6. `∫_x^{4x} y³ |F δ (log y)|² dy ≪ x⁴ δ³ log²(2/δ)` (`MeanSquare.lean`).
7. Proper prime powers in `(A, B]` carry `Λ`-mass `≤ (log² B/log 2)((B−A)/√A + 1)` (`PrimePowers.lean`).
8. With `δ = h/x`, `16 log²(5x)/log 2 ≤ h ≤ x/8`: `Σ_{x ≤ p_n < 2x, d_n ≥ 16h} d_n ≪ x log² x / h`,
   because every gap forces `y^{3/2}|F| ≥ h²/2` on a set of measure `≥ d_n/2` (`Gaps.lean`).
9. Dyadic levels `h = 2^i h₀`: `Σ_{x ≤ p_n < 2x} d_n² ≪ x log³ x` (`Dyadic.lean`).
10. Dyadic blocks in `x` and `p_N ≤ 18 N log N` (Chebyshev, Mathlib) give `≪ N log⁴ N` (`Main.lean`).

Selberg's almost-all theorem reuses Steps 1 to 7 (`AlmostAll.lean`):

11. `window_forces`: if `(y, y(1+2δ))` has no prime, `X ≤ y ≤ 4X`, `16 log²(5X)/log 2 ≤ δX`
    and `δ ≤ 1/8`, then `y^{3/2}|F δ (log y)| ≥ (δX)²/2` (the core of Step 8).
12. `large_wave_measure`: Chebyshev's inequality on Step 6, `|{y ∈ [X,2X] : y^{3/2}|F| ≥ t}| ≤
    C X⁴ δ³ log²(2/δ) / t²`.
13. `primeless_measure_le`: `δ = H/(4X)`, `t = (H/4)²/2` give measure `≤ 64 C X log² X / H` for
    the `y ∈ [X, 2X]` with no prime in `(y, y + H]`.
14. `selberg_almost_all_of_RH`: `H = K log² X ≤ h(y)` on `[X, 2X]` for large `X`, so the
    exceptional proportion is `≤ 64C/K`, and `K` is arbitrary.
15. `smoothed_asymptotic_of_RH`: `|D2 − δ²y²| ≤ 6 + y^{3/2}|F|` (Step 2) and Step 12 with
    `t = εH²/2` give proportion `≤ 16 C log² X / (ε² H) → 0`.
16. `large_gaps_of_RH`: Step 8 with `h/16` in place of `h`.

The mean square of Step 6 is as strong as Selberg's (`≪ x⁴δ³ log²(2/δ)` for the second
difference, i.e. `δ x² log²` for the first), so the existence form reaches Selberg's exact
threshold `h/log² x → ∞` with no extra logarithms.

## Layout

| File | Content |
|---|---|
| `Erdos233/Statement.lean` | formal-conjectures statements (verbatim) |
| `Erdos233/Basic.lean` | `psi1`, `D2`, `coef`, `zeroWave`, `block` |
| `Erdos233/RH.lean` | Step 1 |
| `Erdos233/Explicit.lean`, `Explicit/Formula.lean` | Step 2; real-`x` explicit formula |
| `Erdos233/Density.lean` | Step 3 |
| `Erdos233/Coeff.lean`, `Coeff/Bounds.lean`, `Coeff/Series.lean` | Step 4 |
| `Erdos233/MeanValue.lean` | Step 5 |
| `Erdos233/MeanSquare.lean` | Step 6 |
| `Erdos233/PrimePowers.lean` | Step 7 |
| `Erdos233/Primes.lean` | `p_n` facts: blocks, Bertrand, telescoping |
| `Erdos233/Gaps.lean` | Step 8 |
| `Erdos233/Dyadic.lean` | Step 9 |
| `Erdos233/Main.lean` | Step 10, `erdos_233_upper_bound_of_RH` |
| `Erdos233/Statement2.lean` | Selberg's almost-all statements (this repository's own) |
| `Erdos233/AlmostAll.lean` | Steps 11 to 16 |
| `Unconditional/Erdos233Unconditional.lean` | `erdos_233_upper_bound` (not in the default build) |

## Deviations from the literature

* The bound is exactly the formal-conjectures statement (`N log⁴ N` in index form); the
  constant is not explicit.
* Selberg's mean square uses `θ(y + δy) − θ(y)`; we use the second difference of `ψ₁`, and
  the zero-density input is the windowed sum of Step 3 rather than `N(T+1) − N(T) ≪ log T`.
  A zero-counting library now exists in density-rh; this repository keeps its own short
  Step 3 and does not depend on it.
* `SelbergAsymptoticStatement` (the sharp `π(x + h) − π(x) ~ h/log x`) is not proved. Two
  pieces are missing: (a) passing from the tent-weighted `Λ`-count of `D2` to the sharp count
  of an interval of length `h(y)`, which needs a mean square for a first difference (or a
  sandwich by many tents with an additive step; the zero coefficients `coef δ ρ` of
  `Erdos233/Coeff/` are for the multiplicative second difference only), and (b) handling an
  `h(y)` that varies across `[X, 2X]` (Saffari–Vaughan, Lemma 6, 1977, do this by averaging
  over the step), plus the partial summation from `θ` to `π`. The mean square itself does not
  need sharpening. We prove the smoothed form `SmoothedSelbergStatement` instead.
* `large_gaps_of_RH` is the dyadic-block form of the large-gap bound used inside Selberg's
  `Σ d_n²` argument, with explicit thresholds `256 log²(5x)/log 2 ≤ h ≤ 2x`.
* `erdos_233` itself (`N log² N`) is not proved and is open even under RH; see the last
  section of `docs/BLUEPRINT.md`.

## Building

```bash
lake exe cache get   # Mathlib
lake build           # target Erdos233; Lean v4.36.0, Mathlib fc4f59e5, erdos-985 9538edb
lake env lean scripts/axioms.lean
```

Clean `lake build` of this package (Mathlib and erdos-985 already built), 2026-11-24, 95-core
box: about 4 minutes wall, 176 CPU-seconds. No module takes more than a minute; the largest
are `Erdos233.Explicit.Formula` (53 s), `Erdos233.Gaps` (45 s) and `Erdos233.Main` (39 s).
No module uses `native_decide`. `Erdos233.AlmostAll` (round 5) elaborates in about 23 s
wall, 31 CPU-seconds, on the same box under load.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `Erdos233.erdos_233_upper_bound_of_RH` | `RiemannHypothesis → Erdos233UpperBoundStatement` | standard three |
| `erdos_233_upper_bound` | `Erdos233UpperBoundStatement` | standard three |
| `selberg_almost_all` | `SelbergAlmostAllStatement` | standard three |
| `smoothed_selberg_asymptotic` | `SmoothedSelbergStatement` | standard three |
| `large_gaps` | `Σ_{X ≤ p_n < 2X, d_n ≥ h} d_n ≤ C X log² X / h` | standard three |

Checked on 2026-11-24 against riemann-hypothesis `507a75d91d` (this repository at `a4230f2`):

```bash
sudo prlimit --pid $$ --nofile=2000000:2000000   # Linux; the import opens ~900k files
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

```
'erdos_233_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Round 5 (Selberg's almost-all theorem), checked on 2026-11-24 against riemann-hypothesis
`507a75d91d`, this repository at `57abe66`, 22 minutes wall:

```
'erdos_233_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'selberg_almost_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'smoothed_selberg_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound]
'large_gaps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The riemann-hypothesis import needs its community cache (about 93 GB), about 19 GB of RAM and
about 900,000 open files. The run above took 37 minutes wall, most of it restoring that cache.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* Statements: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (Apache-2.0), commits `d9f6ffa8` and `86a2f58a`; see the header of `Erdos233/Statement.lean`.
* `Erdos233/Explicit/Formula.lean` adapts proofs from
  [senamakel/erdos-985](https://github.com/senamakel/erdos-985) (`Analytic/Principal/Identity.lean`,
  `Analytic/Perron/Weighted.lean`, `Analytic/ExplicitFormula/Bounds/GammaPart.lean`,
  `Analytic/Principal/Bounds/Gamma.lean`) from natural to real `x`. erdos-985 is a lake
  dependency; its Hadamard factorization comes from PrimeNumberTheoremAnd (Apache-2.0, see its
  `Vendor/PNT/NOTICE.md`).
