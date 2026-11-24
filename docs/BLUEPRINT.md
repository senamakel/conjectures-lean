# Blueprint: `Σ_{n<N} d_n² ≪ N log⁴ N` under RH

Target: `Erdos233.erdos_233_upper_bound_of_RH (hRH : RiemannHypothesis) :
Erdos233UpperBoundStatement`, the formal-conjectures statement `erdos_233.variants.upper_bound`.
Notation: `d_n = primeGap n = p_{n+1} − p_n`, `p_n = Nat.nth Nat.Prime n`, `ρ = β + iγ` runs over
the zeros of `ξ = xiZeta` (erdos-985) with multiplicity `m_ρ`.

The route is Selberg's (Arch. Math. Naturvid. 47 (1943)), applied to the smoothed second
difference of `ψ₁(y) = Σ_{n≤y} Λ(n)(y − n)` instead of to `θ(y + δy) − θ(y)`. The smoothing
is what lets us use erdos-985's *absolutely convergent* weighted explicit formula (no truncated
Perron formula is needed).

Every step below is a Lean theorem in this repository; none is a hypothesis.

## Definitions (`Erdos233/Basic.lean`)

| Name | Meaning |
|---|---|
| `Zeros`, `mult` | zeros of `xiZeta`, multiplicity |
| `psi1 y` | `Σ_{n ∈ range(⌊y⌋+1)} Λ(n)(y − n)` |
| `D2 δ y` | `psi1(y(1+2δ)) − 2 psi1(y(1+δ)) + psi1(y)` |
| `coef δ ρ` | `((1+2δ)^{ρ+1} − 2(1+δ)^{ρ+1} + 1)/(ρ(ρ+1))` |
| `zeroWave c u` | `Σ_ρ m_ρ c_ρ e^{iγu}`; `F δ = zeroWave (coef δ)` |
| `block x` | `Finset.Ico (π'(x)) (π'(2x))`, the indices with `x ≤ p_n < 2x` |

## Steps

1. `zero_re_of_RH (hRH) (ρ : Zeros) : ρ.re = 1/2` (`RH.lean`). Zeros of `ξ` lie in
   `0 < Re < 1`, are zeros of `ζ`, are not trivial zeros.

2. `D2_bound (hRH) (hδ : 0 < δ) (hy : 1 ≤ y) :
   |D2 δ y − δ²y²| ≤ 6 + y^{3/2} ‖F δ (log y)‖` (`Explicit.lean`, `Explicit/Formula.lean`).
   `Explicit/Formula.lean` re-proves erdos-985's `explicit_formula_zeta` for real `x ≥ 1`
   (`explicit_formula_real`); only the Perron step (`perron_weightedR`) changes. In the second
   difference the affine terms vanish, `y²/2` gives `δ²y²`, `y log y + y·G(y)` (with
   `|Re G + log y − 1| ≤ 3/(2y)`) contributes at most 6 in absolute value, and the zero `ρ`
   gives `−y^{ρ+1} coef δ ρ` with `|y^{ρ+1}| = y^{3/2}` under RH.

3. `zero_density : ∃ C > 0, ∀ T, Σ_ρ m_ρ/(1 + (T − γ)²) ≤ C log(|T| + 2)` (`Density.lean`,
   unconditional). Real part of Hadamard's `ξ'/ξ(2+iT) = b + Σ m(1/(s−ρ) + 1/ρ)`, with
   `Re 1/ρ ≥ 0`, `Re 1/(s−ρ) ≥ 1/(4(1+(T−γ)²))`, `|ζ'/ζ(2+iT)| ≤ 0.6` and
   `Re ψ(1+it) ≤ 1 + ½ log(1+t²)`.

4. `coef_sums (hRH) : ∃ C > 0, ∀ δ ∈ (0, 1/2], Σ m‖coef‖ < ∞ ∧
   Σ m‖coef‖² log(|γ|+2) ≤ C δ³ log²(2/δ)` (`Coeff.lean`, `Coeff/Bounds.lean`,
   `Coeff/Series.lean`). Per zero: `‖coef‖ ≤ δ²`, `≤ 4δ/‖ρ‖`, `≤ 52/(1+γ²)`. Zeros are grouped
   by `⌊|γ|⌋`, each group bounded by Step 3, and the series
   `Σ_n min(δ⁴, 16δ²/(n²+1/4)) log²(n+4) ≤ 300 δ³ log²(2/δ)` is summed by telescoping.

5. `mean_value : ∃ C > 0, ∀ c, Σ m‖c‖ < ∞ → Σ m‖c‖² log(|γ|+2) < ∞ → ∀ U,
   ∫_U^{U+2} ‖zeroWave c u‖² du ≤ C Σ m‖c‖² log(|γ|+2)` (`MeanValue.lean`). Gaussian weight
   `e·exp(−(u−U−1)²) ≥ 1` on the window, expansion over `Zeros × Zeros`, Fourier transform
   `|ŵ(τ)| ≤ 2e√π/(1+τ²)` (`integral_cexp_quadratic`), `|ab| ≤ (a²+b²)/2`, Step 3.

6. `mean_square (hRH) : ∃ C > 0, ∀ x ≥ 1, ∀ δ ∈ (0, 1/2],
   ∫_x^{4x} (y^{3/2} ‖F δ (log y)‖)² dy ≤ C x⁴ δ³ log²(2/δ)` (`MeanSquare.lean`). `y³ ≤ 64x³`,
   substitution `y = e^u`, `e^u ≤ 4x`, `log 4 < 2`, Steps 4–5.

7. `psi_sub_theta_window (2 ≤ A ≤ B) : (ψ−θ)(B) − (ψ−θ)(A) ≤
   (log B/log 2) · log B · ((B−A)/√A + 1)` (`PrimePowers.lean`, unconditional). Mathlib's
   `ψ = θ + Σ_{k≥2} θ(x^{1/k})`, `θ(b) − θ(a) ≤ log b (b − a + 1)`,
   `B^{1/k} − A^{1/k} ≤ √B − √A ≤ (B−A)/√A`.

8. `gap_sum (hRH) : ∃ C X₀ > 0, ∀ x ≥ X₀, ∀ h, 16 log²(5x)/log 2 ≤ h ≤ x/8 →
   Σ_{n ∈ block x, d_n ≥ 16h} d_n ≤ C x log² x / h` (`Gaps.lean`). With `δ = h/x`: on
   `G_n = (p_n, p_{n+1}/(1+2δ))` the window `(y, y(1+2δ))` has no prime, so
   `D2 δ y ≤ δy · (Step 7) ≤ δ²y²/4` (`D2_le`, needs `16 log²(5x)/log 2 ≤ √x`, true for large
   `x`), and Step 2 gives `y^{3/2}‖F‖ ≥ h²/2`. The `G_n` are disjoint, lie in `[x, 4x]`
   (Bertrand: `p_{n+1} ≤ 2p_n`), and `|G_n| ≥ d_n − 8h ≥ d_n/2`; Step 6 finishes.

9. `block_sq (hRH) : ∃ C X₀ > 0, ∀ x ≥ X₀, Σ_{n ∈ block x} d_n² ≤ C x log³ x`
   (`Dyadic.lean`). `d² ≤ 16h₀d + 32 Σ_{i ≤ log₂ x} [16·2^i h₀ ≤ d] 2^i h₀ d`
   (`sq_le_dyadic`), Step 8 at each level, `Σ_{block} d_n ≤ 4x`.

10. `erdos_233_upper_bound_of_RH` (`Main.lean`). Cover `n < N` by `n < π'(x₀)` and the blocks
    `2^j x₀`, `j ≤ log₂ p_N`: total `≪ p_N log³ p_N`. Chebyshev
    (`Chebyshev.pi_ge_of_four_le`) gives `p_N ≤ 18 N log N`.

## What is not proved

`erdos_233` itself (`Σ_{n<N} d_n² ≪ N log² N`, Heath-Brown's conjecture) is open, also under
RH: the RH mean square in Step 6 is sharp up to constants for this method, and the `log x`
lost to the dyadic levels in Step 9 is the gap between `log³` and `log²` (in `p_n ≤ x`
indexing). Removing it needs input beyond RH, e.g. pair correlation of zeros (Heath-Brown,
Goldston–Montgomery style arguments).

## Round 5: primes in almost all short intervals (Selberg 1943)

Statements: `Erdos233/Statement2.lean`. Proofs: `Erdos233/AlmostAll.lean`. Everything reuses
Steps 1–7; no new analytic input.

1. `window_forces`. If `(y, y(1+2δ))` has no prime, `X ≤ y ≤ 4X`, `16 L ≤ δX`
   (`L = log²(5X)/log 2`), `16 L ≤ √X` and `δ ≤ 1/8`: `D2 δ y ≤ δy · (ψ − θ)|_y^{y(1+2δ)} ≤
   (δy)²/4 + δy L` (`D2_le`, `psi_sub_theta_window`), and `D2_bound` gives
   `y^{3/2}|F δ (log y)| ≥ (δy)²/2 ≥ (δX)²/2`.
2. `large_wave_measure`. `mul_meas_ge_le_integral_of_nonneg` (Chebyshev) on
   `W y = (y^{3/2}|F δ (log y)|)²` over `volume.restrict (Ioc X 4X)`, with `mean_square`:
   `|{y ∈ [X,2X] : t ≤ y^{3/2}|F|}| ≤ C X⁴δ³ log²(2/δ)/t²` (the point `y = X` is null).
3. `primeless_measure_le`. `δ = H/(4X)` makes `y(1+2δ) ≤ y + H` on `[X, 2X]`; with
   `t = (H/4)²/2`, `X⁴δ³/t² = 16 X/H` and `log(2/δ) ≤ 2 log X`, so the bound is
   `64 C X log² X / H` for `64 L ≤ H ≤ X/2`.
4. `selberg_almost_all_of_RH`. Given `η`, take `K = max(512, 2C/η)`; eventually
   `h(y) ≥ K log² y ≥ K log² X =: H` on `[X, 2X]` and `H ≤ X/2`; `64 L ≤ H` because
   `log²(5X) ≤ 4 log² X` and `512 log 2 > 256`. Proportion `≤ C/K ≤ η/2`.
5. `smoothed_asymptotic_of_RH`. With `δ = H(X)/X`, `|D2 − δ²y²| > εδ²y²` forces
   `y^{3/2}|F| ≥ εδ²X² − 6 ≥ εH²/2` once `εH ≥ 12`. Step 2 gives proportion
   `≤ 4C log²(2/δ)/(ε²H) ≤ 16 C log² X/(ε² H)`.
6. `large_gaps_of_RH`. `gap_sum` at `h/16`.

Not done: the sharp `SelbergAsymptoticStatement`. It needs the sharp count `ψ(y + h(y)) − ψ(y)`
in mean square (a first difference with additive step: new zero coefficients
`((1 + h/y)^{ρ} − 1)/ρ`-type bounds replacing `Coeff/`), the Saffari–Vaughan averaging over the
step to let `h` vary with `y`, and partial summation from `θ` to `π`. Estimated several days.
