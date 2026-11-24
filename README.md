# Selberg's bound for Erdős Problem 233 under RH in Lean

**Literature status: RH-consequence** (Cramér 1936; Selberg, *Arch. Math. Naturvid.* 47
(1943)). Nothing here is new mathematics.

[Erdős Problem 233](https://www.erdosproblems.com/233) concerns the sum of squares of prime
gaps `d_n = p_{n+1} − p_n`. Heath-Brown conjectured `Σ_{n<N} d_n² ≍ N log² N`; the lower bound
`≫ N log² N` follows from the prime number theorem, and the conjectured upper bound is open,
also under the Riemann hypothesis. Under RH, Cramér gave an earlier upper bound (formal-conjectures
attributes the `N log⁴ N` form to him; we have not checked the exact power), and Selberg proved `Σ_{p_n ≤ x} d_n² ≪ x log³ x`, which is
`Σ_{n<N} d_n² ≪ N log⁴ N` in index form because `p_N ≍ N log N`. formal-conjectures lists this
bound as the variant `erdos_233.variants.upper_bound` (tagged `research solved`, i.e. known under RH). An
explicit version is Cully-Hugill–Dudek, [arXiv:2206.00433](https://arxiv.org/abs/2206.00433).

The main library is a Lean proof that RH implies `Σ_{n<N} d_n² ≪ N log⁴ N`, following Selberg
(1943). `Unconditional/` gives `Σ_{n<N} d_n² ≪ N log⁴ N`, given the Lean proof of RH in
leanprover-community/riemann-hypothesis, which has not been independently verified. Erdős 233
itself (`≪ N log² N`) stays open; nothing here addresses it.

```lean
theorem Erdos233.erdos_233_upper_bound_of_RH (hRH : RiemannHypothesis) :
    Erdos233.Erdos233UpperBoundStatement          -- Erdos233/Main.lean

theorem erdos_233_upper_bound : Erdos233.Erdos233UpperBoundStatement
                                                   -- Unconditional/Erdos233Unconditional.lean

def Erdos233.Erdos233UpperBoundStatement : Prop :=   -- Erdos233/Statement.lean
    (fun N => ((∑ n ∈ Finset.range N, (primeGap n) ^ 2) : ℝ)) =O[atTop] fun N => N * (log N)^4
```

## Tier and provenance

* `Erdos233.erdos_233_upper_bound_of_RH` is **tier C**: RH is the explicit hypothesis
  `RiemannHypothesis`, Mathlib's own definition (as in formal-conjectures), not restated.
* `erdos_233_upper_bound` is **tier U**: it closes RH with `riemannHypothesis` from
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
  in one line.
* `Erdos233UpperBoundStatement` and `primeGap` are copied verbatim from formal-conjectures
  [`ErdosProblems/233.lean`](https://github.com/google-deepmind/formal-conjectures/blob/d9f6ffa8dd7fc2b8b597dd1f7a824d27b12b88af/FormalConjectures/ErdosProblems/233.lean)
  (`erdos_233.variants.upper_bound`) and
  [`NumberTheory/PrimeGap.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean).
  `Erdos233Statement` (the open `erdos_233`, `N log² N`) is copied too, for reference; nothing
  here proves it.
* There are no cited (`Prop`) hypotheses: every analytic input, including the explicit formula
  for real `x`, the local zero density and the mean-value estimate, is proved here or in
  erdos-985.

## Axioms

`lake env lean scripts/axioms.lean` (2026-11-24, this repository's `finality` branch):

```
'Erdos233.erdos_233_upper_bound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no `axiom` or `opaque` declarations.

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
| `Unconditional/Erdos233Unconditional.lean` | `erdos_233_upper_bound` (not in the default build) |

## Deviations from the literature

* The bound is exactly the formal-conjectures statement (`N log⁴ N` in index form); the
  constant is not explicit.
* Selberg's mean square uses `θ(y + δy) − θ(y)`; we use the second difference of `ψ₁`, and
  the zero-density input is the windowed sum of Step 3 rather than `N(T+1) − N(T) ≪ log T`.
  A zero-counting library now exists in density-rh; this repository keeps its own short
  Step 3 and does not depend on it.
* This is **not** a proof of `erdos_233` (`N log² N`), which is open even under RH; see the
  last section of `docs/BLUEPRINT.md`.

## Building

```bash
lake exe cache get   # Mathlib
lake build           # target Erdos233; Lean v4.36.0, Mathlib fc4f59e5, erdos-985 9538edb
lake env lean scripts/axioms.lean
```

Clean `lake build` of this package (Mathlib and erdos-985 already built), 2026-11-24, 95-core
box: about 4 minutes wall, 176 CPU-seconds. No module takes more than a minute; the largest
are `Erdos233.Explicit.Formula` (53 s), `Erdos233.Gaps` (45 s) and `Erdos233.Main` (39 s).
There are no `native_decide` modules.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `Erdos233.erdos_233_upper_bound_of_RH` | `RiemannHypothesis → Erdos233UpperBoundStatement` | standard three |
| `erdos_233_upper_bound` | `Erdos233UpperBoundStatement` | standard three |

Checked on 2026-11-24 against riemann-hypothesis `507a75d91d` (this repository at `a4230f2`):

```bash
sudo prlimit --pid $$ --nofile=2000000:2000000   # Linux; the import opens ~900k files
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

```
'erdos_233_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The riemann-hypothesis import needs its community cache (about 93 GB), about 19 GB of RAM and
about 900,000 open files. The run above took 37 minutes wall, most of it restoring that cache.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent verification is still pending.

## Credits

* Statements: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (Apache-2.0), commits `d9f6ffa8` and `86a2f58a`; see the header of `Erdos233/Statement.lean`.
* `Erdos233/Explicit/Formula.lean` adapts proofs from
  [senamakel/erdos-985](https://github.com/senamakel/erdos-985) (`Analytic/Principal/Identity.lean`,
  `Analytic/Perron/Weighted.lean`, `Analytic/ExplicitFormula/Bounds/GammaPart.lean`,
  `Analytic/Principal/Bounds/Gamma.lean`) from natural to real `x`. erdos-985 is a lake
  dependency; its Hadamard factorization comes from PrimeNumberTheoremAnd (Apache-2.0, see its
  `Vendor/PNT/NOTICE.md`).
