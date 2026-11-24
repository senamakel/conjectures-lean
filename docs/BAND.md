# The band `5/2 ≤ |Im s| < 7`: design and sizing of the certified computation

`SpeiserBand (5/2) 7` asks for `ζ'(s) ≠ 0` on `0 < σ < 1/2`, `5/2 ≤ |t| < 7`. The analytic
arguments in `Speiser/Gamma.lean` (above 7) and `Speiser/Low.lean` (below 5/2) cannot reach it
(README, "Deviations"). This file records the options considered, the one chosen, and the
sizing. Numbers come from float prototypes (`mpmath` for reference values); nothing here is a
proof.

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

## The chosen design, option (b)

**Euler–Maclaurin with a positive kernel.** For `f(x) = x^{−s}` and `n ≥ 1` let
`K(u) = u²(1−u)²/24` (`K ≥ 0`, `K ≤ 1/384`). One application of the fundamental theorem of
calculus to `G(u) = K f'''(n+u) − K' f''(n+u) + K'' f'(n+u) − K''' f(n+u) + F(n+u)`, where
`F' = f` and `K'''' = 1`, gives

`r_n(s) := (f(n) + f(n+1))/2 − ∫_n^{n+1} f − (f'(n+1) − f'(n))/12 = −∫_0^1 K(u) f''''(n+u) du`,

so `|r_n(s)| ≤ |s(s+1)(s+2)(s+3)| n^{−σ−4}/384` for `σ ≥ −4`. Summing and telescoping for
`Re s > 1`:

`ζ(s) = Σ_{n<N} n^{−s} + N^{−s}/2 + N^{1−s}/(s−1) + s N^{−s−1}/12 + T_N(s)`, with
`T_N(s) = Σ_{n≥N} r_n(s)`.

The right side is holomorphic on `Re s > −3`, `s ≠ 1` (the tail converges locally uniformly by
the bound above), so the identity theorem on the convex sets `{−1 < σ < 2, 1 < t < 10}` and
their conjugates carries it into the band. The prototype matches `mpmath`'s `ζ'` to `2·10⁻⁶` at
`N = 8`.

**The cell test.** For a cell disc `D(c, r)` and a tail radius `ρ`:

- `M'(c)` (the derivative of the explicit main part) by complex disc arithmetic;
- `|T'(s)| ≤ max_{D(c, r+ρ)} |T| / ρ` at `s = c` and at every `s ∈ D(c, r)` (Cauchy's estimate,
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), with
  `max |T| ≤ |P₄|max / (384 (σ_min + 3) (N−1)^{σ_min+3})`;
- `|M'(s) − M'(c)| ≤ r · sup_{D(c,r)} |M''|`, from termwise bounds `|n^{−s}| ≤ n^{−(σ_c − r)}`;

and accept when `|M'(c)| > 2 max|T|/ρ + r · sup|M''|`.

**Sizing** (float prototype `em2.py`, adaptive bisection of `[0, 1/2] × [5/2, 7]`, no
failures; the `t < 0` half is the mirror image, so double these counts):

| `N` | `ρ` | cells (`t > 0`) | smallest cell radius | prototype time |
|---|---|---|---|---|
| 4 | 0.3 | 2,896 | 0.0029 | < 0.1 s |
| 5 | 0.4 | 3,146 | 0.0118 | < 0.1 s |
| 6 | 0.5 | 5,600 | 0.0090 | 0.1 s |
| 8 | 0.5 | 15,724 | 0.0059 | 0.2 s |
| 12 | 0.5 | 63,244 | 0.0029 | 0.9 s |

With `N = 5`: about 6,300 cells in all, each needing about 10 complex exponentials
`n^{−c} = exp(−c log n)` (`n ≤ 5`) at about 30 bits (`2^{−40}` dyadic rounding keeps the
numbers small; the error budget is `|ζ'| ≥ 0.168` against tails of about `0.01`). That is about
`6·10⁴` disc operations: **seconds of CPU** in a compiled checker, far under the 10-minute
limit. The `ρ`/`N` choice moves the count by a factor 2, not more.

**Lean cost.** About 1,700 lines:

| Part | Content | Lines (estimate) |
|---|---|---|
| Euler–Maclaurin | `r_n` identity (one FTC), the `r_n` bound, telescoping for `Re s > 1`, local uniform summability, identity theorem on two convex boxes | 500 |
| Disc arithmetic | `ℚ × ℚ` centres, `ℚ` radii, add, mul, inverse, dyadic rounding; `exp` on a disc by `exp(z) = exp(z/2^k)^{2^k}` and `Complex.exp_bound`; `log 2`, `log 3`, `log 5` enclosures (Mathlib's `log_two` bounds and series) | 600 |
| Checker | cell list, per-cell test as a `Bool`, soundness `test c r = true → ∀ s ∈ D(c,r), ζ'(s) ≠ 0` | 400 |
| Glue | covering of the band by the cell list (an interval-cover check on rationals), conjugate half, `SpeiserBand (5/2) 7` | 200 |

The checker runs by `native_decide` (about 6,300 cells; or kernel `decide` after splitting
into chunks, which is slower but avoids `native_decide`), following robin-rh's pattern:
a core-only checker with a separate soundness proof. The result `SpeiserBand (5/2) 7` is tier
D; with `speiserBelow_of_RH` and `speiserAbove_of_RH` it gives `SpeiserStatement` under RH, so
`Unconditional/` would close the full target.
