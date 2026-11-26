# Blueprint: RH ⇒ Littlewood's bound

Target (`Littlewood/Statement.lean`): `Littlewood.littlewood_of_RH (hRH : RiemannHypothesis) :
LittlewoodBound`, i.e. `∃ C t₀, ∀ t ≥ t₀, ‖ζ(1/2 + it)‖ ≤ exp (C log t / log log t)`. It is
proved with `C = 4`.

## Sources and route

Littlewood, *On the zeros of the Riemann zeta-function*, Proc. Cambridge Philos. Soc. 22 (1924),
295–318. Titchmarsh's 1930 tract (*The Zeta-Function of Riemann*, Theorem 63, §5.72; checked
against the archive.org scan) derives it from the bound on `S₁(t)` (his Theorem 62). The
second edition puts it in §14.14; that edition was not available to check.

The Lean proof does not follow Littlewood's `S₁(t)` route. It follows the explicit-formula
argument later used by Soundararajan (Ann. Math. 2009, Prop. of §2) and Chandee–Soundararajan
(Bull. LMS 2011), simplified because the constant does not matter:

1. Lindelöf's transfer (lindelof-rh, from the monotonicity of `|ξ|` under RH):
   `|ζ(1/2+it)| ≤ C₁ t^{δ/2} |ζ(1/2+δ+it)|`, here with `δ = 1/log x`.
2. An explicit formula for `ζ'/ζ` with the weight `log (x/n)` (the kernel `x^w/w²`), evaluated
   term by term, so no contour is ever shifted.
3. Integrate it over `σ ∈ [σ₀, 2]` to get `log |ζ(σ₀+it)|`. Under RH each zero's
   `-1/(ρ-s)²` term integrates exactly to `Re 1/(s₂-ρ) - Re 1/(s₀-ρ)`. The negative part
   `-Re 1/(s₀-ρ) = -(σ₀-1/2)/|s₀-ρ|²` absorbs the `x^{ρ-s}` term, whose integral is at most
   `1/(log x |s₀-ρ|²)`, as soon as `(σ₀ - 1/2) log x ≥ 1`. This positivity step is where RH
   does the work, and the uniformity in `σ₀ - 1/2 → 0` comes from it.
4. Choose `x = √(log t)`.

### Why not three circles

Before writing this, we checked whether lindelof-rh's machinery (Borel–Carathéodory,
Hadamard three lines for a holomorphic `log ζ`) is quantitative enough. It is not:

* The Borel–Carathéodory bound `|log ζ| ≤ C_δ log t` on `σ ≥ 1/2 + δ` has `C_δ ≍ 1/δ`.
* Three lines between `1/2 + δ` and a line `σ₁ > 1`, evaluated at `1/2 + 2δ`, saves a factor
  `(A_right/A_left)^θ` with `θ ≍ δ`. With `δ ≍ 1/log log t` that is a constant, not the
  needed `1/log log t`.
* The same holds after subtracting a Dirichlet polynomial of length `x ≤ (log t)²` (which the
  left-line bound allows): the saving is at best `x^{-δ} = e^{-O(1)}`.
* The Cesàro weight `1 - n/x` (erdos-985's kernel `x^w/(w(w+1))`) also fails: its zero terms
  are `x^{ρ-s}/((ρ-s)(ρ-s+1))`, only `1/|s-ρ|` near `t`. Summing gives an extra
  `log(1/δ) = log log log t` factor, and getting rid of it costs a `log log log log t` factor in
  the transfer step.

So the `1/log x` that the `x^w/w²` kernel puts in front of the zero terms, combined with the
exact integration of the `1/(ρ-s)²` terms, is the essential input.

## Assembly (`Littlewood/Main.lean`)

```lean
theorem littlewood_of_RH (hRH : RiemannHypothesis) : LittlewoodBound

theorem log_norm_zeta_le (hRH : RiemannHypothesis) :
    ∃ A B : ℝ, ∀ t x : ℝ, 1 ≤ t → Real.exp 2 ≤ x →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (A + Real.log t / (2 * Real.log x) +
        (2 * ((x + 1) * Real.log x ^ 2 + (x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) + B +
          Real.log (3 + t)) / Real.log x)
```

`log_norm_zeta_le` takes `σ₀ = 1/2 + 1/log x` in `key_bound` and `δ = 1/log x` in
`Lindelof.norm_zeta_half_le`. `littlewood_of_RH` puts `x = √(log t)` and uses
`exists_threshold` (Step 11).

## Step 1: Perron kernels (`Littlewood/Kernel.lean`)

On the line `w = 2 + iv` (`lineP v`):

```lean
theorem perron_log {y : ℝ} (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, (y : ℂ) ^ lineP v * (1 / lineP v ^ 2)
      = if 1 ≤ y then (Real.log y : ℂ) else 0
theorem perron_pole {y : ℝ} (hy : 1 ≤ y) {b : ℂ} (hb : b.re ≤ 1) (hb0 : b ≠ 0) :
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, (y : ℂ) ^ lineP v * (1 / ((lineP v - b) * lineP v))
      = ((y : ℂ) ^ b - 1) / b
theorem kerPole_bound : ∃ K, 0 ≤ K ∧ ∀ y > 0, ∀ b, b.re ≤ 1 → Integrable … ∧
    ∫ ‖y^w / ((w - b) w)‖ ≤ K y² (1 + ‖b‖)^{-1/2}
```

Both kernels are Mellin transforms of profiles on `(0, 1]` (erdos-985 `perron_prof`). The
`L¹` bound comes from erdos-985 `perron_pair_integral_norm_le` and `|w + 1| ≤ (3/2)|w|`.

## Step 2: term-by-term Perron (`Littlewood/Termwise.lean`)

```lean
theorem perron_termwise {ι} [Countable ι] {G : ℂ → ℂ} {s : ℂ} {x : ℝ} (hx : 1 ≤ x)
    (a m : ι → ℂ) (ha : ∀ i, (a i - s).re ≤ 1) (has : ∀ i, a i ≠ s)
    (hsum : Summable fun i => ‖m i‖ / ‖a i - s‖ * (1 + ‖a i - s‖) ^ (-(1 / 2 : ℝ)))
    (hG : ∀ v, HasSum (fun i => m i * (1 / (s + lineP v - a i) - 1 / (s - a i)))
      (G (s + lineP v) - G s))
    (hGc : Continuous fun v => G (s + lineP v)) :
    Integrable … ∧ (1/2π) ∫ G(s+w) x^w/w² dv
      = G s * log x + ∑' i, m i * ((x ^ (a i - s) - 1) / (a i - s) ^ 2)
```

Each term is `(m_i/b_i) x^w/((w-b_i)w)`, and the interchange is dominated by `kerPole_bound`.

## Step 3: Dirichlet side (`Littlewood/Dirichlet.lean`)

`perron_vonMangoldt`: for `Re s > 0`, `(1/2π) ∫ L(Λ, s+w) x^w/w² dv = Σ_{n ≤ x} Λ(n) n^{-s} log(x/n)`.

## Step 4: zeros of ξ (`Littlewood/XiSide.lean`)

* `hasSum_logDeriv_xi_sub`: Hadamard (erdos-985 `hadamard_logDeriv`), differenced, so the
  constant drops out.
* `hasSum_re_logDeriv_xi` (RH): `Re ξ'/ξ(s) = Σ_ρ m Re 1/(s-ρ)` for `Re s > 1/2`. The constant
  and the `1/ρ` terms cancel against the expansion at `1 - s̄`.
* `summable_zero_weight` (RH): the `hsum` hypothesis of Step 2, from `Σ m/|ρ|^{3/2} < ∞` and
  `|ρ| ≤ (|s|/(σ - 1/2) + 1)|ρ - s|`.
* `perron_xi` (RH): Step 2 for `G = -ξ'/ξ`.

## Step 5: the archimedean factor (`Littlewood/GammaSide.lean`)

* `logDeriv_riemannZeta_eq_archR`: `ζ'/ζ = ξ'/ξ - R` on `Re s > 0`, with
  `R(s) = 1/(s-1) - ½ log π + ½ ψ(1 + s/2)`.
* `perron_R`: Step 2 applied to `R` (pole at `1`, constant, and the digamma series with poles at
  `-2k-2`): `(1/2π)∫ R(s+w)x^w/w² = R(s) log x + E_R(s,x)`.
* `norm_ER_le`: `‖E_R‖ ≤ x + 1 + Σ 1/(k+1)²` for `Re s ≥ 0`, `|Im s| ≥ 1`.
* `norm_digamma_one_add_le`: `‖ψ(1+w)‖ ≤ 2 log(2+‖w‖) + 3` for `Re w ≥ 0`. Each series term is at most
  `2(1/(k+1) - 1/(k+2+‖w‖))`, whose sum is the real `ψ(2+‖w‖) - ψ(1) ≤ log(2+‖w‖) + γ`.
* `norm_archR_two_le`: `‖R(2+it)‖ ≤ log(3+|t|) + 5`.

## Step 6: the explicit formula (`Littlewood/Explicit.lean`)

```lean
theorem explicit_formula (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x : ℂ) * (-(deriv riemannZeta s / riemannZeta s))
      = dirPoly s x + zeroSum s x - ER s x
```

## Step 7: one zero (`Littlewood/ZeroIntegral.lean`)

```lean
theorem integral_zero_term_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) (t : ℝ) {x σ₀ : ℝ} (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (hηL : 1 ≤ (σ₀ - 1 / 2) * Real.log x) :
    ∫ σ in σ₀..2, (((x : ℂ) ^ (ρ - (σ + t I)) - 1) / (ρ - (σ + t I)) ^ 2).re
      ≤ (1 / ((2 : ℂ) + t * I - ρ)).re
```

## Step 8: FTC and the pieces (`Littlewood/Integrate.lean`)

`log_norm_zeta_sub_eq` (RH): `log|ζ(σ₀+it)| - log|ζ(2+it)| = ∫_{σ₀}^{2} Re(-ζ'/ζ)`.
`summable_mult_div_normSq` (RH), `norm_dirPoly_le` (`‖D‖ ≤ (x+1)(log x)²`).

## Step 9: the key bound (`Littlewood/Bound.lean`)

```lean
theorem key_bound (hRH : RiemannHypothesis) {t x σ₀ : ℝ} (ht : 1 ≤ t) (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (hηL : 1 ≤ (σ₀ - 1 / 2) * Real.log x) :
    Real.log x * (Real.log ‖riemannZeta (σ₀ + t * I)‖ - Real.log ‖riemannZeta (2 + t * I)‖)
      ≤ 2 * ((x + 1) * Real.log x ^ 2 + (x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) +
        (deriv xiZeta ((2 : ℂ) + t * I) / xiZeta ((2 : ℂ) + t * I)).re
```

The zero sum is integrated term by term (`integral_zeroSum_le`, `integral_tsum_of_summable_integral_norm`
on `Ioc σ₀ 2`) and summed with `hasSum_re_logDeriv_xi` at `2 + it`.

## Step 10–11: constants (`Littlewood/Main.lean`, `Littlewood/Asymptotic.lean`)

`re_logDeriv_xi_two_le`: `Re ξ'/ξ(2+it) ≤ B + log(3+t) + 5`. With `u = log t`, `ℓ = log u` and
`x = √u`, the exponent is `3u/ℓ + (√u + 1)ℓ + O((√u + 1)/ℓ)`. `exists_threshold` shows it is
at most `4u/ℓ` once `u ≥ max(U₁, e⁴, M⁸)`. Here `log u ≤ u^{1/8}` for `u ≥ U₁`, and
`M = |A| + 14 + 4|S| + 2|B|`.

## Status

No `sorry`. `#print axioms Littlewood.littlewood_of_RH`: `[propext, Classical.choice, Quot.sound]`.
