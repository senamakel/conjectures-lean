# Blueprint: RH ⇒ bounds for the Mertens function and its smoothed relatives

Targets (`Mertens/Statement.lean`): `InvZetaBound`, `MertensBound`, `RieszBound`,
`HardyLittlewoodBound`, `RedhefferBound`, and Redheffer's identity `det R_n = M(n)`.

Notation: `s = σ + it`; `μ` is the Möbius function, `M(x) = ∑_{n ≤ x} μ(n)`;
`ζ₁(s) = (s-1)ζ(s)` is Mathlib's entire `riemannZeta₁`; `invZ(s) = (s-1)/ζ₁(s)`, equal to
`1/ζ(s)` for `s ≠ 1` and holomorphic on `σ > 1/2` under RH.

## Route choice for `M(x)`

Littlewood's theorem is usually proved with a sharp-cutoff (truncated) Perron formula, which
neither Mathlib nor erdos-985 has. It is not needed. With `A(N) = ∑_{0<n<N} μ(n)(N - n)`,

    M(N) = A(N+1) - A(N)                                      (exactly),

and each `A(N)` is given by the absolutely convergent Cesàro kernel `N^{s+1}/(s(s+1))` that
erdos-985's `perron_weighted` already provides. The difference kernel
`d(s) = (N+1)^{s+1} - N^{s+1}` has two bounds, `‖d‖ ≤ 2(N+1)^{σ+1}` (trivial) and
`‖d‖ ≤ ‖s+1‖(N+1)^σ` (mean value theorem). Their geometric mean with weight `θ`,
`‖d‖ ≤ 2^θ (N+1)^{σ+θ} ‖s+1‖^{1-θ}`, decays like `|t|^{-1-θ}` after division by `s(s+1)`, which
is integrable against `|1/ζ| ≪ |t|^ε` once `θ > ε`. The price is a factor `N^θ`, harmless
because `θ` can be taken as `2ε`. The "x^{3/4} barrier" noted in the tracker comes from using
only the trivial bound; the short-interval trick `|M(x+h) - M(x)| ≤ h+1` with `h = x^{1/2}` also
works but is unnecessary.

## Step A: `1/ζ ≪ |t|^ε` on `σ ≥ 1/2 + δ` (`Mertens/InvZeta.lean`)

* `norm_invZ_le`: under RH, for `0 < δ < 3/2`, `ε > 0`, `∃ C > 0, ∀ s, 1/2 + δ ≤ σ ≤ 2 →
  ‖invZ s‖ ≤ C (|t| + 2)^ε`.
  From lindelof-rh: `exists_log_zetaQ` (holomorphic `M` with `exp M = ζ₁/(s+1)`),
  `norm_log_zetaQ_le` (Borel–Carathéodory, `‖M‖ ≤ C log(|t|+2)`) and
  `norm_le_log_rpow_of_strip` (three lines, `‖M‖ ≤ C log(|t|+2)^α` with `α < 1` on
  `σ ≥ 1/2 + δ`). Then `‖invZ‖ = ‖s-1‖/(‖s+1‖‖exp M‖) ≤ exp ‖M‖` and
  `C L^α ≤ ε L + K` (`exists_log_rpow_le`).
* `invZeta_bound_of_RH : InvZetaBound`; `σ > 2` from `1/ζ = ∑ μ(n) n^{-s}`.

## Step B: moving a vertical line (`Mertens/Shift.lean`)

* `integral_vertical_eq_of_strip`: `f` holomorphic on `a ≤ σ ≤ b`, integrable on both edges,
  uniformly `→ 0` as `|t| → ∞` ⇒ `∫ f(a+it) dt = ∫ f(b+it) dt`. Cauchy on rectangles
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), horizontal sides `≤ η(b-a)`.

## Step C: Cesàro–Perron for `μ` on `σ₀ ∈ (1/2, 2)` (`Mertens/Perron.lean`)

* `F y s = invZ(s) y^s/(s(s+1))`; `norm_F_le`: `‖F y s‖ ≤ K y^σ (1+|t|)^{-3/2}` on the strip
  (Step A with `ε = 1/2`, `‖s(s+1)‖ ≥ m(1+|t|)²/4`).
* `cesaro_moebius_eq`: `∑_{0<n<N} μ(n)(1 - n/N) = (1/2π) ∫ F N (σ₀ + it) dt`, from erdos-985's
  `perron_weighted` at `c = 2` and Step B.

## Step D: `M(N) = A(N+1) - A(N)` (`Mertens/Littlewood.lean`, `mertens_nat_eq`)

## Step E: the difference integrand (`Mertens/Littlewood.lean`, `norm_diff_F_le`)

`‖(N+1) F_{N+1}(s) - N F_N(s)‖ ≤ K (N+1)^{σ₀+θ} (1+|t|)^{ε-θ-1}` for `0 ≤ θ ≤ 1`, via
`norm_diff_le_triv`, `norm_diff_le_mvt` and `le_rpow_mul_rpow` (`z ≤ X, z ≤ Y ⇒ z ≤ X^θ Y^{1-θ}`).

## Step F: assembly (`Mertens/Main.lean`)

* `abs_mertens_nat_le`: `|M(N)| ≤ K (N+1)^{1/2+3ε}` (`σ₀ = 1/2 + ε`, `θ = 2ε`).
* `mertens_of_RH : MertensBound`.

## Redheffer (`Mertens/Redheffer.lean`, `Mertens/RedhefferBound.lean`)

* `det_redheffer (n) (hn : 1 ≤ n) : (redheffer n).det = mertens n` (tier D). `V_{ij} = μ(j/i)[i ∣ j]`
  is unit upper triangular; `V R` is lower triangular with diagonal `(M(n), 1, …, 1)` because
  `∑_{i ∣ j ∣ k} μ(j/i) = [i = k]` (`moebius_mul_coe_zeta`).
* `redheffer_of_RH : RedhefferBound`.

## Step G: Abel summation (`Mertens/Abel.lean`)

* `abel_tendsto`: `|S(n)| ≤ K(n+1)^β`, partial sums of `(n+1)^β |w(n+1) - w(n)|` `≤ B`,
  `(n+1)^β w(n) → 0` ⇒ `∑ c(n) w(n)` converges to some `L` with `|L| ≤ K B`.
* `interp_term`: two monomial bounds `D_i x^{p_i} n^{q_i}` on `|Δw|` interpolate to one.
* `sum_range_le_of_terms`: `∑ A x^P n^{-(1+η)} ≤ A x^P ζ(1+η)`.

## Step H: weights (`Mertens/Weights.lean`)

`W_R = (x/t²)e^{-x/t²}`: `|ΔW_R| ≤ 2x n^{-3}`, `≤ 32 n/x`. `W_H = (1/t)e^{-x/t²}`:
`|ΔW_H| ≤ 2 n^{-2}`, `≤ 5/x`. Mean value theorem plus `(1+u)e^{-u} ≤ 1`, `u²(1+u)e^{-u} ≤ 8`,
`(1+2u)e^{-u} ≤ 2`, `u(1+2u)e^{-u} ≤ 5`.

## Step I: Hardy–Littlewood (`Mertens/HardyLittlewood.lean`)

`θ = (β+1+ε)/2` gives `(n+1)^β|ΔW_H| ≪ x^{θ-1} n^{-(1+ε)}`, `θ - 1 = -1/4 + 2ε`.
`hardyLittlewood_of_RH : HardyLittlewoodBound` (convergence for every `x > 0` and the bound).

## Step J: Riesz (`Mertens/Riesz.lean`)

* `riesz_eq`: `riesz x = ∑ μ(n) (x/n²) e^{-x/n²}` (expand `1/ζ(2k) = ∑ μ(n) n^{-2k}`, swap the
  absolutely convergent double series, sum the exponential series).
* `θ = (β+2+ε)/4`, `2θ - 1 = 1/4 + 2ε`; `riesz_of_RH : RieszBound`.

## Status

| Step | File | Status |
|---|---|---|
| A | `Mertens/InvZeta.lean` | done |
| B | `Mertens/Shift.lean` | done |
| C | `Mertens/Perron.lean` | done |
| D–E | `Mertens/Littlewood.lean` | done |
| F | `Mertens/Main.lean` | done |
| Redheffer | `Mertens/Redheffer.lean`, `Mertens/RedhefferBound.lean` | done |
| G–H | `Mertens/Abel.lean`, `Mertens/Weights.lean` | done |
| I | `Mertens/HardyLittlewood.lean` | done |
| J | `Mertens/Riesz.lean` | done |
| stretch | Franel–Landau (Farey sequences) | not started |
