# Artin's primitive root conjecture under Hooley's hypothesis, in Lean

Work in progress.

The target is Hooley's 1967 theorem, as stated in
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean):

```lean
theorem conditional_artin_primitive_roots.parts.i (a : ℤ) (ha : ¬IsSquare a) (ha' : a ≠ -1)
    (h : HooleyHypothesis a) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime}
```

That is: if `a` is not a square and not `-1`, and RH holds for the Dedekind zeta functions of
the Kummer fields `ℚ(ζ_k, a^{1/k})` with `k` squarefree, then a positive proportion of primes
`p` have `a` as a primitive root.

## This result stays conditional

[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
proves RH for ζ and GRH for Dirichlet L-functions. The Kummer fields are not abelian over ℚ,
so their zeta functions are not products of Dirichlet L-functions, and that repository does
not supply `HooleyHypothesis`. Unlike [erdos-985](https://github.com/senamakel/erdos-985),
this project has no unconditional version. The erdos-985 analytic library also covers only
Dirichlet characters, so the Chebotarev and Kummer-field parts have to be built here.

## Layout

| File | Content |
|---|---|
| `Artin/Statement.lean` | definitions copied word for word from formal-conjectures; do not change |
| `Artin/Interfaces.lean` | the split: analytic half and sieve half, joined by `EffectiveKummerChebotarev` |
| `Artin/Main.lean` | the target theorem, from the two halves |
| `Artin/Sieve/PrimitiveRoot.lean` | primitive-root criterion and the inclusion–exclusion identity, exact and truncated (sorry-free) |
| `Artin/Sieve/Selberg/` | the Selberg upper-bound sieve, vendored from PrimeNumberTheoremAnd (see Credits) |
| `Artin/Sieve/BrunTitchmarsh.lean` | Brun–Titchmarsh: `π(x; q, 1) ≤ 20000 x / (φ(q) log(x/q))` for `x > q ≥ 1` (sorry-free) |
| `Artin/Sieve/BrunTitchmarshLargePrimes.lean` | blueprint B3: primes `q ∈ (√x / log² x, √x log x]` sift out `≤ 23040000 x log log x / log² x` primes for `x ≥ e^256`, so `o(π(x))` (sorry-free) |
| `Artin/Sieve/HugePrimes.lean` | blueprint B4: primes sifted by `q > √x log x` number `≤ (\|a\|+1) x / log² x` (sorry-free) |
| `Artin/Sieve/Density.lean` | blueprint B7: `N(x)/π(x) → δ` gives `(S a).HasDensity δ` (sorry-free) |
| `Artin/Kummer/Degree.lean` | blueprint B5: Kummer degrees, bounds and exact formulas `[K_k:ℚ] m(k) = k φ(k)` (sorry-free) |
| `Artin/Kummer/Conductor.lean` | quadratic subfields of `ℚ(ζ_k)`: `√a ∈ ℚ(ζ_k)` iff `a₀ ≡ 1 (mod 4)` and `\|a₀\| ∣ k` (sorry-free) |
| `Artin/Kummer/Density.lean` | blueprint B6: `δ(a) = Σ μ(k)/[K_k:ℚ]` converges and is positive for `a` not a square, `a ≠ -1` (sorry-free) |
| `docs/BLUEPRINT.md` | the plan, step by step |

## Building

Uses Lean v4.36.0 and the same Mathlib as erdos-985 (`fc4f59e5`), which it requires as a lake
dependency. `.lake/packages` is a symlink to the shared package directory
`../lean-grh-shared/packages`, which other projects also use: don't run `lake update`,
`lake clean` or `lake exe cache get` against it. Build one module at a time:

```bash
lake build Artin.Main
```

## Credits

`Artin/Sieve/Selberg/` is vendored from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (commit
`a4fb698`, files `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/*.lean`, by Arend Mellendijk),
under the Apache License 2.0; a copy of the licence is in `Artin/Sieve/Selberg/LICENSE`. The files
are adapted to our Mathlib pin, and each starts with a NOTICE comment listing its changes. The
arithmetic-progression set-up in `Artin/Sieve/BrunTitchmarsh.lean` follows the interval version in
PrimeNumberTheoremAnd's `BrunTitchmarsh.lean`.
