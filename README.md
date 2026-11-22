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
| `Artin/Interfaces.lean` | the split: analytic half (sorried) and the definitions joining it to the sieve half, `EffectiveKummerChebotarev` |
| `Artin/SieveHalf.lean` | the sieve half `artin_of_effectiveKummerChebotarev`: `EffectiveKummerChebotarev a → ∃ δ > 0, (S a).HasDensity δ` for `a` not a square, `a ≠ -1` (sorry-free) |
| `Artin/Main.lean` | the target theorem, from the two halves |
| `Artin/Sieve/PrimitiveRoot.lean` | primitive-root criterion and the inclusion–exclusion identity, exact and truncated (sorry-free) |
| `Artin/Sieve/Selberg/` | the Selberg upper-bound sieve, vendored from PrimeNumberTheoremAnd (see Credits) |
| `Artin/Sieve/BrunTitchmarsh.lean` | Brun–Titchmarsh: `π(x; q, 1) ≤ 20000 x / (φ(q) log(x/q))` for `x > q ≥ 1` (sorry-free) |
| `Artin/Sieve/BrunTitchmarshLargePrimes.lean` | blueprint B3: primes `q ∈ (√x / log² x, √x log x]` sift out `≤ 23040000 x log log x / log² x` primes for `x ≥ e^256`, so `o(π(x))` (sorry-free) |
| `Artin/Sieve/HugePrimes.lean` | blueprint B4: primes sifted by `q > √x log x` number `≤ (\|a\|+1) x / log² x` (sorry-free) |
| `Artin/Sieve/KummerInputs.lean` | blueprint B5/B6 as hypotheses: `KummerDegreeLowerBound` (`k φ(k) ≪ [K_k : ℚ]`) and `KummerDensityPos` (`Σ μ(k)/[K_k : ℚ] > 0`), discharged from `Artin/Kummer/` in `Artin/SieveHalf.lean` |
| `Artin/Sieve/Assembly.lean` | blueprint B1, B2 and the join with B3, B4, B7: `artin_of_effectiveKummerChebotarev_of_kummer`, the sieve half modulo the two Kummer inputs (sorry-free) |
| `Artin/Sieve/Density.lean` | blueprint B7: `N(x)/π(x) → δ` gives `(S a).HasDensity δ` (sorry-free) |
| `Artin/Kummer/Degree.lean` | blueprint B5: Kummer degrees, bounds and exact formulas `[K_k:ℚ] m(k) = k φ(k)` (sorry-free) |
| `Artin/Kummer/Conductor.lean` | quadratic subfields of `ℚ(ζ_k)`: `√a ∈ ℚ(ζ_k)` iff `a₀ ≡ 1 (mod 4)` and `\|a₀\| ∣ k` (sorry-free) |
| `Artin/Kummer/Density.lean` | blueprint B6: `δ(a) = Σ μ(k)/[K_k:ℚ]` converges and is positive for `a` not a square, `a ≠ -1` (sorry-free) |
| `Artin/Analytic/Interface.lean` | the statement the analytic core (A1–A4) must prove: `psiK K x = Σ_{𝔭, m ≥ 1, N𝔭^m < x} log N𝔭`, `PsiKBound K C` (`\|ψ_K(x) − x\| ≤ C √x (log \|d_K\| + n_K log x) log x` for `x ≥ 2`) and the bundle `KummerPsiBounds a` (one `C` for all `K_k`, `k` squarefree); definitions only, no axioms |
| `Artin/Analytic/Splitting.lean` | blueprint A5: for `p ∤ k a`, `p` splits completely in `K_k` iff `k ∣ p − 1` and `a^((p−1)/k) = 1` mod `p` (`kummerCond_iff_exists_absNorm_eq`, `split_of_kummerCond`), via the decomposition group rather than Dedekind–Kummer; at most `[K : ℚ]` primes above any `p` (sorry-free) |
| `Artin/Analytic/Discriminant.lean` | blueprint A6: `log \|d_{K_k}\| ≤ 4 [K_k : ℚ] log(k \|a\|)` (`log_abs_discr_le`), by Hadamard's inequality on a basis of monomials `ζ^i α^j` (sorry-free) |
| `Artin/Analytic/Counting.lean` | blueprint A5 counting and A7: `0 ≤ ψ_K(x) − n θ_k(x) ≤ n log x (2 log(k\|a\|) + √x)`, then `\|θ_k(x) − x/n\| ≪ √x log x log(kx)`, then discrete partial summation, giving `effectiveKummerChebotarev_of_kummerPsiBounds : KummerPsiBounds a → EffectiveKummerChebotarev a` for `a ≠ 0`; the `k = 1` field `ℚ` replaces a separate `π(x) − li(x)` hypothesis (sorry-free) |
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
