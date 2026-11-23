# Artin's primitive root conjecture under Hooley's hypothesis, in Lean

Hooley's 1967 theorem is proved in Lean, with no `sorry`, once one standard analytic input is
assumed: Hecke's analytic continuation of the Dedekind zeta functions involved.

```lean
theorem conditional_artin_primitive_roots.parts.i_of_continuation (a : ℤ) (ha : ¬IsSquare a)
    (ha' : a ≠ -1) (h : HooleyHypothesis a)
    (hc : ∀ k : ℕ, Squarefree k → DedekindContinuation (Artin.Kummer.KField a k)) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime}
```

`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.

In words: if `a` is not a square and not `-1`, and RH holds for the Dedekind zeta functions of
the Kummer fields `K_k = ℚ(ζ_k, a^{1/k})` with `k` squarefree, then a positive proportion of
primes `p` have `a` as a primitive root.

`HooleyHypothesis`, `S` and `HasDensity` are copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean),
whose `conditional_artin_primitive_roots.parts.i` is the same statement without `hc`.

## Why the continuation is a hypothesis

`HooleyHypothesis` is about every function that is holomorphic on `ℂ ∖ {1}` and agrees with
`ζ_K` on `Re s > 1`. To use it, a proof needs such a function. Neither our Mathlib pin nor
upstream Mathlib has the analytic continuation of `ζ_K`. `DedekindContinuation K`
(`Artin/Analytic/Continuation.lean`) states what Hecke's theorem gives:
* a continuation `Z`;
* the entire function `ξ = s(s−1)·|d_K|^{s/2}·Γ_ℝ^{r₁}·Γ_ℂ^{r₂}·Z` with `ξ(1−s) = ξ(s)`;
* a polynomial bound for `ξ` on `1/2 ≤ Re s ≤ 2`.

The riemann-hypothesis repository proves the continuation and the functional equation, but not
the strip bound. That repository has no licence, so none of its code is copied here. An
`Unconditional/` module that imports it, as erdos-985 does, would still need the strip bound.
The formal-conjectures statement without `hc` remains `sorry` in `Artin/Main.lean` (via
`effectiveKummerChebotarev_of_hooley`) until Hecke's theorem is formalised.

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
| `Artin/MainContinuation.lean` | `conditional_artin_primitive_roots.parts.i_of_continuation`: the main result: the target with Hecke's continuation `DedekindContinuation (K_k)` as an extra hypothesis, through `kummerPsiBounds_of_hooley_of_continuation`, `effectiveKummerChebotarev_of_kummerPsiBounds` and the sieve half (sorry-free) |
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
| `Artin/Analytic/Continuation.lean` | `DedekindContinuation K`: Hecke's theorem as a hypothesis (a continuation `Z` of `ζ_K`, `ξ(s) = s(s−1)\|d_K\|^{s/2}Γ_ℝ^{r₁}Γ_ℂ^{r₂}Z(s)` entire, `ξ(1−s) = ξ(s)`, `ξ = O((1+\|s\|)²)` on `1/2 ≤ Re s ≤ 2`); definitions only |
| `Artin/Analytic/Core/VonMangoldt.lean` | `Λ_K(n)`, `ψ_K(x) = Σ_{n<x} Λ_K(n)` (`psiK_eq_sum`) and `Λ_K ≤ n Λ` (`vonMangoldtK_le`), the convolution identity `log · a = Λ_K ⋆ a` for the ideal count `a(n)`, `-ζ_K'/ζ_K = Σ Λ_K(n) n^{-s}` and `ζ_K = exp(Σ Λ_K(n)/log n · n^{-s}) ≠ 0` on `Re s > 1` (sorry-free) |
| `Artin/Analytic/Core/NonvanishingOne.lean` | `ζ_K(1+it) ≠ 0` for `t ≠ 0` (`Z_ne_zero_on_one_line`), Mertens' `3 + 4 cos θ + cos 2θ ≥ 0` argument adapted from Mathlib's `LFunction_ne_zero_of_re_eq_one` (sorry-free) |
| `Artin/Analytic/Core/GammaPart.lean` | `Γ_ℝ'/Γ_ℝ`, `Γ_ℂ'/Γ_ℂ` by parity, and their part of the explicit formula as `Σ_k tau x (2k+a)` (adapted from erdos-985, sorry-free) |
| `Artin/Analytic/Core/Growth.lean` | `ξ_K` has order at most 1 (`xi_growth_aux`): strip bound, functional equation, and for `Re s ≥ 2` the bounds `\|Γ(w)\| ≤ Γ(Re w)`, `Γ(σ) ≤ (σ+1)^{σ+1}` and `\|ζ_K(s)\| ≤ ζ_K(2)`, through erdos-985's `LogGrowth` (sorry-free) |
| `Artin/Analytic/Core/Xi.lean` | blueprint A1: `ξ_K` from `DedekindContinuation`; `ξ(1) = γ_K(1)·Res ζ_K ≠ 0` (Mathlib's class number formula), zeros in `0 < Re ρ < 1` and on `Re ρ = 1/2` under RH, Hadamard (erdos-985), `ζ_K'/ζ_K = ξ'/ξ − 1/s − 1/(s−1) − G_K`, `Re ξ'/ξ(s) = Σ m_ρ Re 1/(s−ρ)` (sorry-free) |
| `Artin/Analytic/Core/ZeroSum.lean` | blueprint A2: `Σ m_ρ/\|ρ(ρ+1)\| ≤ log \|d_K\| + 9n` and `#{ρ : \|Im ρ − T\| ≤ 1} ≤ 9(log \|d_K\| + n log(\|T\|+3))` under RH (proved from A1 and the Euler-product facts) |
| `Artin/Analytic/Core/ExplicitFormula.lean` | blueprint A3: the weighted explicit formula for `Σ_{n<x} Λ_K(n)(1 − n/x)` (proved from the above) |
| `Artin/Analytic/Core/Unsmoothing.lean` | blueprint A4: differencing `y W_K(y) = Σ_{m≤y} ψ_K(m)` at `x ± √x`, giving `psiKBound_of_continuation` (`∃ C, ∀ K, RH → DedekindContinuation K → PsiKBound K C`); the increment estimates `gammaDiff_le` (explicit `tau` terms) and `zeroDiff_le` (`Re ξ'/ξ` on a dyadic grid of real points) are proved |
| `docs/BLUEPRINT.md` | the plan, step by step |

## The continuation hypothesis

`HooleyHypothesis` only constrains functions `Z` that continue `ζ_K` to `ℂ ∖ {1}`. Using it needs
such a `Z`, with the functional equation, and neither our Mathlib pin nor upstream Mathlib has
Hecke's continuation of `ζ_K`. As in erdos-985, the library takes it as an explicit hypothesis,
`DedekindContinuation` (`Artin/Analytic/Continuation.lean`), and proves
`conditional_artin_primitive_roots.parts.i_of_continuation`. The statement of `Artin/Main.lean`
without that hypothesis stays sorried (`effectiveKummerChebotarev_of_hooley`). A later
`Unconditional/` module could discharge the hypothesis from a formalisation of Hecke's theorem.

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
