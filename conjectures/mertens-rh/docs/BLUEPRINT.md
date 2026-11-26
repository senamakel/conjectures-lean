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

## Round 5: Titchmarsh's bound `M(x) ≤ √x exp(C log x / log log x)` (`Mertens/Sharp*.lean`)

Targets: `Mertens/Statement3.lean`. Notation: `L = log x` (Dirichlet-polynomial length of
littlewood-rh's explicit formula), `s₀ = σ₀ + it`, `η = σ₀ - 1/2`, `W = Re ξ'/ξ(s₀)`,
`C = (x+1)L² + x + 1 + Σ 1/k²`.

1. `integral_zero_term_ge`, `integral_zeroSum_ge` (RH, `ηL ≥ 1`):
   `∫_{σ₀}^2 Re zeroSum(σ+it, x) dσ ≥ -2W`.
2. `re_logDeriv_xi_le` (RH, `t ≥ 1`, `ηL ≥ 4`): `W ≤ 2C/L + 2‖R(s₀)‖`;
   `norm_archR_le`: `‖R(s)‖ ≤ log(3+|t|) + 5` on `0 ≤ σ ≤ 2`, `|t| ≥ 1`.
3. `norm_inv_zeta_le_large` (RH, `t ≥ 1`, `x ≥ e²`, `σ₀ ≤ 2`, `ηL ≥ 4`):
   `‖ζ(s₀)⁻¹‖ ≤ exp(A + (4C + 4 log(3+t) + 20)/L)`.
4. `re_logDeriv_xi_le_two`, `log_norm_xi_ge`, `norm_invZ_le_small` (RH, `|t| ≤ 1`):
   `‖invZ s‖ ≤ K₁ (3/(2η))^{K₂}`.
5. `norm_invZ_le_sharp` (RH, `l ≥ 2`, `1/2 + 4/l ≤ σ ≤ 2`, all `t`):
   `‖invZ s‖ ≤ exp(A(l² e^l + 1)) (|t|+3)^{4/l}`; `invZetaSharpWith_of_RH : InvZetaSharpBoundWith 8`
   with `l = ½ log log t`.
6. `norm_diff_F_le_of`, `integral_one_add_abs_rpow_neg` (`∫ (1+|t|)^{-(1+α)} = 2/α`),
   `abs_mertens_nat_le_sharp` (`l ≥ 8`): `|M(N)| ≤ 8 l e^{A(l²e^l+1)} (N+1)^{1/2+12/l}`.
7. `eventually_le_div_log`: `A((log u)² √u + 1) + B ≤ u/log u` eventually
   (`(log u)³ = o(√u)`); `mertensSharp_of_RH` with `l = ½ log log x`, `C = 25`.

## Round 6: Titchmarsh's bound for `L`, and `1/ζ` on `σ ≥ 1/2 + 1/log log t`

Targets: `Mertens/Statement4.lean` (`LiouvilleSharpBound`) and the fixed round-5 target
`InvZetaSharpBound` (`Mertens/Statement3.lean`).

1. `sum_sqInd_rpow_le_log` (`β ≥ 1/2`): `∑_{n ≤ N} 1_□(n) n^{-β} ≤ 1 + log N` (via
   `harmonic_le_one_add_log`); `abs_liouvilleSum_nat_le_of`: a bound `|M(n)| ≤ K(n+1)^β` for all
   `n ≥ 1` gives `|L(N)| ≤ K 2^β N^β (1 + log N)`.
2. `liouvilleSharp_of_RH`: step 1 with `abs_mertens_nat_le_sharp` at `l = ½ log log x`, and
   `eventually_le_div_log (A+2) 5`; `C = 25`.
3. `sum_inv_sqrt_le`: `∑_{n ≤ N} (√n)⁻¹ ≤ 2√N`; `norm_dirPoly_le_half` (`Re s ≥ 1/2`):
   `‖D(s,x)‖ ≤ 2√x (log x)²`; `norm_ER_le_half`: `‖E_R(s,x)‖ ≤ √x + 1 + S`.
4. `norm_zeroTerm_le_sharp` (`ηL ≥ 3/2`): `‖zeroTerm x t ρ σ₀‖ ≤ (5/4) m_ρ/|ρ - s₀|²`
   (`e^{-3/2} ≤ 1/4`).
5. `re_logDeriv_xi_le_half` (`t ≥ 1`, `ηL ≥ 3/2`): `W ≤ 6 Chalf(x)/L + 6‖R(s₀)‖`,
   `Chalf x = 2√x L² + √x + 1 + S`.
6. `norm_inv_zeta_le_large_half` (`t ≥ 1`, `x ≥ e²`, `σ₀ ≤ 2`, `ηL ≥ 3/2`):
   `‖ζ(s₀)⁻¹‖ ≤ exp(A + (8 Chalf(x) + 12 log(3+t) + 60)/L)`.
7. `eventually_le_div_log_rpow` (`0 ≤ α < 1`): `A((log u)² u^α + 1) + B ≤ u/log u` eventually;
   `invZetaSharp_of_RH` with `L = (3/2) log log t`, `α = 3/4`, `C = 9`.
8. `InvZetaSharpBoundWith.mono`: the bound for `c` gives it for every `c' ≥ c`.

Why round 5 stopped at `c > 4`: Selberg's device absorbed `2W/η` into `LW/2`, which needs
`ηL ≥ 4`, and `C ≈ x L²` forces `x ≤ log t/(log log t)²`, i.e. `L < log log t`. Steps 3–4 lower
the first requirement to `ηL ≥ 3/2` (any `ηL > 1.28`, the root of `a = 1 + e^{-a}`, would do) and
replace `x` by `√x` in the second (`L < 2 log log t`). `c = 1` uses `ηL = 3/2`,
`L = (3/2) log log t`. The same argument would reach any `c > 0.64` (`c ≈ a/2` with
`a > 1.28`); only `c = 1` is stated and proved.
