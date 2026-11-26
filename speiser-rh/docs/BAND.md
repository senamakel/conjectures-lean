# The band `5/2 ≤ |Im s| < 7`: design and sizing of the certified computation

`SpeiserBand (5/2) 7` asks for `ζ'(s) ≠ 0` on `0 < σ < 1/2`, `5/2 ≤ |t| < 7`. The analytic
arguments in `Speiser/Gamma.lean` (above 7) and `Speiser/Low.lean` (below 5/2) cannot reach it
(README, "Deviations"). This file records the options considered, the one chosen and implemented, and the
sizing. The sizing numbers in the options section come from float prototypes (`mpmath` for
reference values); the proof is the implemented computation described in the last section.

Numerics on the band (grid step 0.02, `mpmath`): `min |ζ'| ≈ 0.1685` (at `σ = 1/2`,
`t ≈ 4.66`), `max |ζ'| ≈ 0.26`, `max |ζ''| ≈ 0.124`. So `ζ'` stays well away from 0, and
the band needs no RH: the computation proves the band unconditionally (tier D).

## Options

**(a) Argument principle for `ζ'` on the rectangle.** Certify that the winding number of `ζ'`
along the boundary is 0. This needs the same `ζ'` evaluator as (b) on the boundary, plus a
formal argument principle for a rectangle, which Mathlib lacks at this pin (it has Cauchy's
formula and some circle versions). It costs strictly more Lean than (b) for no saving in
evaluations, so it was not chosen.

**(b) Exclusion on cells (chosen).** Cover the band by cells `D(c, r)` and check
`|ζ'(c)| > sup_{D(c,r)} |ζ'(s) − ζ'(c)|`. With Euler–Maclaurin for `ζ` and Cauchy estimates
for the tail, every quantity is an explicit rational bound.

**(c) Certified low zeros.** Under RH, `ξ'/ξ(s) = Σ_ρ m_ρ (1/(s−ρ) − 1/(1/2−ρ))`. Splitting off
the zeros with `|γ| ≤ Γ₀` (known to high precision) and bounding the tail by
`Re ξ'/ξ(1) = Σ_ρ m_ρ (1/2)/(1/4 + γ²) = 0.0231` would separate `ξ'/ξ(s)` from the gamma side
`E(s)`. The band needs at least the first zero to within about `0.1`, and `γ₁ ≥ 14` with the
crude tail bound is not enough (`|ξ'/ξ| ≤ 0.86` against `|E| ≈ 0.5`); several zeros are
needed. Certifying them needs (i) the same `ζ` evaluator, on the critical line up to height
`Γ₀ ≈ 30–50`, with sign changes of Hardy's `Z`, and (ii) a certified zero count `N(Γ₀)`
(Turing's method or the argument principle) to rule out unseen zeros. Both are more Lean than
(b), and (ii) needs Backlund/Turing-type explicit `S(T)` bounds, which nothing here provides.
Not chosen.

## The chosen design, option (b), as implemented

**Status: implemented and run.** `Speiser.Band.speiserBand : SpeiserBand (5/2) 7` is proved
with standard axioms plus 2 `native_decide` (`Speiser/Band/Run.lean`), 186 s of CPU.

**Euler–Maclaurin with a positive kernel** (`Speiser/Band/EulerMaclaurin.lean`). For
`f(x) = x^{−s}` and `n > 0` let `K(u) = u²(1−u)²/24` (`0 ≤ K ≤ 1/384`). One application of the
fundamental theorem of calculus to `G = K f‴ − K′ f″ + K″ f′ − K‴ f + F`, where `F′ = f` and
`K⁗ = 1`, gives

`r_n(s) := (f(n) + f(n+1))/2 − ∫_n^{n+1} f − (f′(n+1) − f′(n))/12 = −∫_0^1 K(u) f⁗(n+u) du`,

so `|r_n(s)| ≤ |s(s+1)(s+2)(s+3)| n^{−σ−4}/384` for `σ ≥ −4`.

**ζ on boxes** (`Zeta.lean`). Telescoping for `Re s > 1` gives

`ζ(s) = Σ_{n<N} n^{−s} + N^{−s}/2 + N^{1−s}/(s−1) + s N^{−s−1}/12 + Σ_{n≥N} r_n(s)`.

The tail is holomorphic on `Re s > −2`, so the identity theorem carries the formula to the boxes
`U± = {−1 < σ < 2, 1 < ±t < 10}`. The code uses `N = 9`.

**The cell test** (`Deriv.lean`, `Check.lean`). For a box with centre `c` and `ℓ¹` half-width `r`:

- `ζ' = M1 + T'` on `U±`, with `M1` the explicit derivative of the main part;
- `‖M1(s) − M1(c)‖ ≤ r · sup_{D(c,r)} ‖M2‖` (mean value inequality, `M2 = M1'` explicit and
  bounded term by term);
- `‖T'(s)‖ ≤ P(‖s‖ + ρ)/(147456 ρ)` by Cauchy's estimate with `ρ = 2/5`, from
  `‖T(z)‖ ≤ P(‖z‖)/147456` for `Re z ≥ −1/2` (`Σ_{n≥9} n^{−7/2} ≤ (1/3)·Σ_{n≥9} n^{−3} ≤ 1/384`),
  where `P(a) = a(a+1)(a+2)(a+3)`.

The cell is accepted when `|M1(c)|` exceeds the sum of `M1(c)`'s enclosure radius and those two
bounds.

**Arithmetic** (`SpeiserCompute/Core.lean`, core only, `precompileModules`). Fixed point
`2^{−64}` in `Int`, with complex discs. Products are rounded down and radii up. `exp` is computed
by a 16-term Taylor series (Mathlib's `Complex.exp_bound`) after dividing by `2^6`, followed by
six squarings, and `‖exp u − 1‖ ≤ 2‖u‖` covers the split. The enclosures of `log 2, 3, 5, 7`,
with width `5·10⁻¹²`, come from `Real.abs_log_sub_add_sum_range_le`. Soundness of each operation
is in `Sound.lean`.

**Run** (`Run.lean`). `coverOK` bisects `[0, 1/2] × [5/2, 7]` and its mirror image, at most 40
levels: **71,223 accepted cells per half, 186 s of CPU in all.**

The first prototype used exact `Rat` arithmetic and was about 25× slower, about 70 minutes; that
is why the code moved to fixed point.

**Lean size.** About 2,000 lines across `Speiser/Band/` and `SpeiserCompute/`.

**Sizing, earlier float prototype** (for reference; `t > 0` half; the counts depend on the tail
bound used):

| `N` | `ρ` | cells |
|---|---|---|
| 5 | 0.4 | 3,146 |
| 8 | 0.5 | 15,724 |
| 9 (Lean tail bound) | 0.5 | 59,674 |
| 12 | 0.5 | 63,244 |
| 16 (Lean tail bound) | 0.5 | 334,397 |
