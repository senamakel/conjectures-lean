# Artin's primitive root conjecture under Hooley's hypothesis, in Lean

Artin (1927) conjectured that every integer `a` that is neither `-1` nor a square is a primitive
root modulo infinitely many primes, indeed modulo a positive proportion of them. Hooley (1967,
*On Artin's conjecture*, J. reine angew. Math. 225, 209–220) proved this under the Riemann
hypothesis for the Dedekind zeta functions of the Kummer fields `K_k = ℚ(ζ_k, a^{1/k})`. It is
open unconditionally; Heath-Brown (1986) showed that at most two primes `a` fail it.

**Literature status: RH-consequence (tier C stays).** The conditional theorem is Hooley (1967).
This repository is a complete Lean proof of Hooley's theorem: for every `a` that is neither `-1`
nor a square, the Riemann hypothesis for the Kummer fields (`HooleyHypothesis a`) implies that
`a` is a primitive root modulo a set of primes of positive density. Hecke's continuation of the
Dedekind zeta functions is taken from riemann-hypothesis's Tate-thesis modules, so
`HooleyHypothesis a` is the only hypothesis left, and the axioms are the standard three. That
remaining hypothesis is RH for the Kummer fields `K_k`, which are non-abelian for odd prime `k`,
and the certified proof covers ζ and Dirichlet L-functions only, so the result stays tier C.

```lean
-- Artin/MainContinuation.lean (main library)
theorem conditional_artin_primitive_roots.parts.i_of_continuation (a : ℤ) (ha : ¬IsSquare a)
    (ha' : a ≠ -1) (h : HooleyHypothesis a)
    (hc : ∀ k : ℕ, Squarefree k → DedekindContinuation (Artin.Kummer.KField a k)) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime}

-- Unconditional/ArtinUnconditional.lean (imports riemann-hypothesis's Tate-thesis modules)
theorem Artin.Unconditional.dedekindContinuation (K : Type*) [Field K] [NumberField K] :
    DedekindContinuation K

theorem Artin.Unconditional.conditional_artin_primitive_roots_parts_i (a : ℤ) (ha : ¬IsSquare a)
    (ha' : a ≠ -1) (h : HooleyHypothesis a) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime}
```

In words: if `a` is not a square and not `-1`, and RH holds for `ζ_{K_k}` for every squarefree
`k`, then a positive proportion of primes `p` have `a` as a primitive root. This is Hooley's
theorem under his hypothesis. It is not a proof of Artin's conjecture.

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `conditional_artin_primitive_roots.parts.i_of_continuation` | C + H | `HooleyHypothesis a` (open), `DedekindContinuation` (Hecke's theorem, cited) |
| `Artin.Unconditional.conditional_artin_primitive_roots_parts_i` | C, with Hecke's theorem taken from riemann-hypothesis | `HooleyHypothesis a` (open) |

`HooleyHypothesis`, `DedekindZetaRH`, `IsDedekindZeta`, `S` and `HasDensity` are copied word
for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean)
(commit `c8dd64f`, `Artin/Statement.lean`), whose `conditional_artin_primitive_roots.parts.i` is
the statement of `Artin.Unconditional.conditional_artin_primitive_roots_parts_i`.
`DedekindContinuation K` (`Artin/Analytic/Continuation.lean`) is ours: Hecke's continuation of
`ζ_K`, the entire `ξ = s(s−1)·|d_K|^{s/2}·Γ_ℝ^{r₁}·Γ_ℂ^{r₂}·Z` with `ξ(1−s) = ξ(s)`, and
`‖ξ(s)‖ ≤ M(1+‖s‖)²` on `1/2 ≤ Re s ≤ 2`. In the main library it is a cited hypothesis (tier H);
`Unconditional/` discharges it.

The repository contains no `sorry`. The main library, which may not import
riemann-hypothesis, proves the formal-conjectures statement only with `DedekindContinuation` as
an extra hypothesis; the hypothesis-free form lives in `Unconditional/` (see "Hecke's theorem
inside the main library" for what a Mathlib-only proof would need).

## Axioms

Main library, from `lake env lean` on a file that imports `Artin` and runs `#print axioms`
(2026-11-24, this commit):

```
'ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i_of_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Artin.artin_of_effectiveKummerChebotarev' depends on axioms: [propext, Classical.choice, Quot.sound]
'Artin.Analytic.effectiveKummerChebotarev_of_hooley_of_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Artin.Analytic.psiKBound_of_continuation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Artin.Analytic.dedekindContinuation_of_weakFEPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Artin.Analytic.exists_norm_Λ₀_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `native_decide` anywhere.

## Proof outline

The full plan is [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

1. **Split** (`Artin/Interfaces.lean`): `EffectiveKummerChebotarev a`, the number of primes
   `p < x` splitting completely in `K_k` is `π(x)/[K_k:ℚ] + O(√x log(kx))` uniformly in
   squarefree `k`.
2. **Sieve half** (`Artin/SieveHalf.lean`, `Artin/Sieve/`, `Artin/Kummer/`): Hooley's sieve
   over `k` with Brun–Titchmarsh (`π(x;q,1) ≤ 20000 x/(φ(q) log(x/q))`) for the middle range of
   primes `q`, and the Kummer degree formula `[K_k:ℚ] m(k) = k φ(k)` giving the density
   `δ(a) = Σ μ(k)/[K_k:ℚ] > 0`.
3. **Analytic core** (`Artin/Analytic/Core/`): from `DedekindContinuation` and RH for `ζ_K`,
   `ξ_K` has order 1 and a Hadamard product, zeros near height `T` number
   `≤ 9(log|d_K| + n log(|T|+3))`, and the weighted explicit formula unsmoothed at `x ± √x` gives
   `|ψ_K(x) − x| ≤ C √x (log|d_K| + n log x) log x` with an absolute `C`.
4. **Counting** (`Artin/Analytic/Counting.lean`, `Splitting.lean`, `Discriminant.lean`):
   `log|d_{K_k}| ≤ 4[K_k:ℚ] log(k|a|)` and partial summation turn step 3 into step 1.
5. **Hecke's continuation** (`Artin/Analytic/ContinuationOfFEPair.lean`,
   `Unconditional/ArtinUnconditional.lean`): riemann-hypothesis writes `Λ_K` as
   `π^{-r₂}|d_K|^{s/2}Λ_P(s)` for a Mathlib `WeakFEPair` `P`; the entire part `Λ₀` is bounded on
   `a ≤ Re s ≤ b` by `∫_0^∞ |f_modif(t)| (t^{a−1} + t^{b−1}) dt`, which gives the strip bound.

## Deviations from the literature

Hooley's hypothesis is used as formal-conjectures states it (RH for `ζ_{K_k}`, `k` squarefree).
The main library also assumes Hecke's continuation, a theorem, because neither our Mathlib pin
nor upstream Mathlib has it; `Unconditional/` removes that assumption. Constants are not
optimised (Brun–Titchmarsh constant `20000`, sieve threshold `x ≥ e^256`); they only affect the
error terms, not the density.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `Artin.Unconditional.dedekindContinuation` | `DedekindContinuation K` for every number field `K` | `propext`, `Classical.choice`, `Quot.sound` |
| `Artin.Unconditional.conditional_artin_primitive_roots_parts_i` | formal-conjectures `conditional_artin_primitive_roots.parts.i`: `HooleyHypothesis a → ∃ x > 0, (S a).HasDensity x {p \| p.Prime}` | `propext`, `Classical.choice`, `Quot.sound` |

```bash
scripts/check-unconditional.sh [path/to/riemann-hypothesis]
```

checked against [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
commit `507a75d91d`. Only `GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation` (79
modules, about 15k lines, of that repository's Tate-thesis and adele/idele files) is imported,
and none of its RH or GRH theorems is used. The script still runs `lake exe cache get` there,
which downloads the whole cache (about 93 GB) and needs the same open-file limit as the siblings
(it raises `ulimit -n` to the hard limit; the full `Main` import opens about 900k files). The
import itself is light: checking `Unconditional/ArtinUnconditional.lean` took 17 s wall and
6.6 GB peak RAM (`/usr/bin/time -v`, 2026-11-24), against about 19 GB for the full `Main` import.

Output of `lean Unconditional/ArtinUnconditional.lean` (2026-11-24):

```
'Artin.Unconditional.dedekindContinuation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Artin.Unconditional.conditional_artin_primitive_roots_parts_i' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

Here the linked proofs are its Tate-thesis modules, not its RH/GRH proof.

## This result stays conditional

Even with Hecke's theorem supplied, `HooleyHypothesis a` remains a hypothesis, and nothing
available discharges it. Checked against riemann-hypothesis `507a75d91d` (2026-11-24):

* Its zero-location theorems (`src/Main.lean`) are `riemannHypothesis`,
  `LFunction_ne_zero_of_half_lt_re` and `LFunction_eq_zero_re(_of_isPrimitive)`: ζ and
  Dirichlet L-functions only.
* Its Tate thesis (`src/GroundTheory/GlobalFields/TateThesis/`) covers Hecke L-functions of any
  number field: continuation (`HeckeCharacter.exists_LFunction_continuation`), functional
  equation (`completedLFunction_eq_rootNumber_mul`), nonvanishing for `Re s ≥ 1`
  (`LFunction_ne_zero`, `LFunction_continuation_ne_zero`). No statement in the repository
  locates zeros of `ζ_K` or of a Hecke L-function inside the critical strip.
* Its only factorisation of a Dedekind zeta function into Dirichlet L-functions is for
  imaginary quadratic fields (`dedekindZeta_eq_mul_LFunction`).

`ζ_{K_k}` factors as a product of Artin L-functions of `Gal(K_k/ℚ)`. That group embeds in
`ℤ/k ⋊ (ℤ/k)ˣ`, and for an odd prime `k = q` with `a` not a `q`-th power it is all of
`ℤ/q ⋊ (ℤ/q)ˣ`, which is not abelian. Its irreducible representations are induced from
characters of the abelian subgroup `Gal(K_k/ℚ(ζ_k))`, so the factors are Hecke L-functions of
finite-order characters of cyclotomic fields `ℚ(ζ_m)`. GRH for those is open, and the
riemann-hypothesis repository does not claim it. Only the `k = 1` instance of `HooleyHypothesis`
(RH) is covered, and `k = 2` would follow from RH plus GRH for one Kronecker character. So this
project has no tier-U version; its strongest result is the formal-conjectures statement with
`HooleyHypothesis` as its only hypothesis.

## Hecke's theorem inside the main library

Dropping `hc` from the main-library theorem needs `DedekindContinuation (K_k)` proved without
riemann-hypothesis.
Mathlib at `fc4f59e5` has `NumberField.dedekindZeta` (the series, `Re s > 1`),
`dedekindZeta_residue` and `tendsto_sub_one_mul_dedekindZeta_nhdsGT` (the class number formula),
`NumberField.HeckeCharacter.LFunction` (as an arithmetic function only), the fundamental cone of
the mixed embedding, the abstract `WeakFEPair` Mellin machinery, and one-dimensional Poisson
summation. It has no continuation or functional equation for `ζ_K`. With
`dedekindContinuation_of_weakFEPair` in place, what is missing is a `WeakFEPair` representation
of `Λ_K`. Hecke's route needs

1. Poisson summation for a full-rank lattice in `ℝ^{r₁} × ℂ^{r₂}` (Mathlib has it only on `ℝ`),
   and the trace-dual lattice of an ideal (the different);
2. the theta function of an ideal class and its inversion formula `θ(1/t) = t^{n/2}|d|^{1/2} θ'(t)`;
3. integration over the norm-one hypersurface modulo units (a fundamental domain for the unit
   lattice; Mathlib's fundamental cone and its volume, used for the residue, are the starting point);
4. summing over the class group and packaging the Mellin transform as a `WeakFEPair`.

For comparison, the riemann-hypothesis repository's adelic version is 79 modules, about 15k
lines on top of Mathlib. Specialising to Kummer fields does not help: their zeta functions are
not products of `ζ` and Dirichlet L-functions. This is a multi-week formalisation and is not
attempted here.

## Layout

| File | Content |
|---|---|
| `Artin/Statement.lean` | definitions copied word for word from formal-conjectures; do not change |
| `Artin/Interfaces.lean` | the split: the definitions joining the analytic half to the sieve half, `EffectiveKummerChebotarev` |
| `Artin/SieveHalf.lean` | the sieve half `artin_of_effectiveKummerChebotarev`: `EffectiveKummerChebotarev a → ∃ δ > 0, (S a).HasDensity δ` for `a` not a square, `a ≠ -1` (sorry-free) |
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
| `Artin/Analytic/ContinuationOfFEPair.lean` | `exists_norm_Λ₀_le` (the entire part `Λ₀` of any Mathlib `WeakFEPair` is bounded on vertical strips) and `dedekindContinuation_of_weakFEPair` (a completed zeta `c \|d_K\|^{s/2} Λ_P(s)` with functional equation and a continuation `Z` gives `DedekindContinuation K`); Mathlib only, sorry-free |
| `Artin/Analytic/Continuation.lean` | `DedekindContinuation K`: Hecke's theorem as a hypothesis (a continuation `Z` of `ζ_K`, `ξ(s) = s(s−1)\|d_K\|^{s/2}Γ_ℝ^{r₁}Γ_ℂ^{r₂}Z(s)` entire, `ξ(1−s) = ξ(s)`, `ξ = O((1+\|s\|)²)` on `1/2 ≤ Re s ≤ 2`); definitions only |
| `Artin/Analytic/Core/VonMangoldt.lean` | `Λ_K(n)`, `ψ_K(x) = Σ_{n<x} Λ_K(n)` (`psiK_eq_sum`) and `Λ_K ≤ n Λ` (`vonMangoldtK_le`), the convolution identity `log · a = Λ_K ⋆ a` for the ideal count `a(n)`, `-ζ_K'/ζ_K = Σ Λ_K(n) n^{-s}` and `ζ_K = exp(Σ Λ_K(n)/log n · n^{-s}) ≠ 0` on `Re s > 1` (sorry-free) |
| `Artin/Analytic/Core/NonvanishingOne.lean` | `ζ_K(1+it) ≠ 0` for `t ≠ 0` (`Z_ne_zero_on_one_line`), Mertens' `3 + 4 cos θ + cos 2θ ≥ 0` argument adapted from Mathlib's `LFunction_ne_zero_of_re_eq_one` (sorry-free) |
| `Artin/Analytic/Core/GammaPart.lean` | `Γ_ℝ'/Γ_ℝ`, `Γ_ℂ'/Γ_ℂ` by parity, and their part of the explicit formula as `Σ_k tau x (2k+a)` (adapted from erdos-985, sorry-free) |
| `Artin/Analytic/Core/Growth.lean` | `ξ_K` has order at most 1 (`xi_growth_aux`): strip bound, functional equation, and for `Re s ≥ 2` the bounds `\|Γ(w)\| ≤ Γ(Re w)`, `Γ(σ) ≤ (σ+1)^{σ+1}` and `\|ζ_K(s)\| ≤ ζ_K(2)`, through erdos-985's `LogGrowth` (sorry-free) |
| `Artin/Analytic/Core/Xi.lean` | blueprint A1: `ξ_K` from `DedekindContinuation`; `ξ(1) = γ_K(1)·Res ζ_K ≠ 0` (Mathlib's class number formula), zeros in `0 < Re ρ < 1` and on `Re ρ = 1/2` under RH, Hadamard (erdos-985), `ζ_K'/ζ_K = ξ'/ξ − 1/s − 1/(s−1) − G_K`, `Re ξ'/ξ(s) = Σ m_ρ Re 1/(s−ρ)` (sorry-free) |
| `Artin/Analytic/Core/ZeroSum.lean` | blueprint A2: `Σ m_ρ/\|ρ(ρ+1)\| ≤ log \|d_K\| + 9n` and `#{ρ : \|Im ρ − T\| ≤ 1} ≤ 9(log \|d_K\| + n log(\|T\|+3))` under RH (proved from A1 and the Euler-product facts) |
| `Artin/Analytic/Core/ExplicitFormula.lean` | blueprint A3: the weighted explicit formula for `Σ_{n<x} Λ_K(n)(1 − n/x)` (proved from the above) |
| `Artin/Analytic/Core/Unsmoothing.lean` | blueprint A4: differencing `y W_K(y) = Σ_{m≤y} ψ_K(m)` at `x ± √x`, giving `psiKBound_of_continuation` (`∃ C, ∀ K, RH → DedekindContinuation K → PsiKBound K C`); the increment estimates `gammaDiff_le` (explicit `tau` terms) and `zeroDiff_le` (`Re ξ'/ξ` on a dyadic grid of real points) are proved |
| `Unconditional/ArtinUnconditional.lean` | not in the default build: imports the Tate-thesis modules of riemann-hypothesis, proves `DedekindContinuation K` for every number field and the formal-conjectures statement from `HooleyHypothesis` alone |
| `scripts/check-unconditional.sh` | builds and checks the module above |
| `docs/BLUEPRINT.md` | the plan, step by step |

## Building

Lean v4.36.0, Mathlib `fc4f59e5` (through erdos-985, required at
`9538edb73dc72c8fdc04b4e0df076c8930ee2fba` over HTTPS). From a fresh clone:

```bash
lake exe cache get   # Mathlib's cache
lake build           # the whole library; ~2.7 min wall (550 s CPU) on 16 cores, with erdos-985
```

Build one module at a time while iterating, e.g. `lake build Artin.MainContinuation`. No module
here is expensive; the slowest take a few seconds each.

## Credits

`Artin/Sieve/Selberg/` is vendored from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (commit
`a4fb698`, files `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/*.lean`, by Arend Mellendijk),
under the Apache License 2.0; a copy of the licence is in `Artin/Sieve/Selberg/LICENSE`. The files
are adapted to our Mathlib pin, and each starts with a NOTICE comment listing its changes. The
arithmetic-progression set-up in `Artin/Sieve/BrunTitchmarsh.lean` follows the interval version in
PrimeNumberTheoremAnd's `BrunTitchmarsh.lean`.
