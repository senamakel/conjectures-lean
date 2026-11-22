# Blueprint: RH ⇒ Lindelöf

Target: `Lindelof.lindelof_of_RH (hRH : RiemannHypothesis) : LindelofHypothesis`, i.e. for every
`ε > 0`, `‖ζ(1/2 + it)‖ = O(t^ε)` as `t → ∞`.

The route follows Titchmarsh §14.2 for the region `σ > 1/2`. To get down to the critical line it
uses the monotonicity of `|ξ|` under RH instead of Phragmén–Lindelöf, so neither Stirling's
formula nor the convexity principle is needed.

Notation: `s = σ + it`; `ξ(s) = s(s-1)Λ(s)` is erdos-985's `xiZeta`; `Λ = completedRiemannZeta
= Γℝ · ζ` with `Γℝ(s) = π^{-s/2} Γ(s/2)`; `ζ₁(s) = (s-1)ζ(s)` is Mathlib's entire
`riemannZeta₁` (`ζ₁(1) = 1`).

## Step 1: RH in usable forms (`Lindelof/RH.lean`)

* `riemannZeta₁_ne_zero`: RH ⇒ `ζ₁(s) ≠ 0` for `σ > 1/2`. (Trivial zeros have `σ < 0`; `ζ₁(1) = 1`.)
* `xiZeta_zero_re`: RH ⇒ every zero of `ξ` has real part `1/2`. (`ξ(0) = ξ(1) = 1`;
  `ξ(1-s) = ξ(s)` handles `σ ≤ 0`.)

## Step 2: `|ξ|` increases to the right of the critical line (`Lindelof/Monotone.lean`)

Under RH, for `1/2 ≤ σ ≤ σ'`: `|ξ(σ+it)| ≤ |ξ(σ'+it)|`.

Proof. `hadamard_logDeriv` (erdos-985) gives `ξ'/ξ(z) = b + Σ_ρ m_ρ (1/(z-ρ) + 1/ρ)`. By
`ξ(1-s) = ξ(s)` and `ξ(s̄) = conj ξ(s)`, `|ξ(σ+it)| = |ξ(1-σ+it)|`, so
`g(σ) = log|ξ(σ+it)|` satisfies `g'(σ) = -g'(1-σ)`. Subtracting the two Hadamard sums kills `b`:

    2 g'(σ) = Σ_ρ m_ρ Re[1/(σ+it-ρ) - 1/(1-σ+it-ρ)] = Σ_ρ m_ρ (2σ-1)/|σ+it-ρ|² ≥ 0,

using `Re ρ = 1/2`, so `|σ+it-ρ| = |1-σ+it-ρ|`. Work with `‖ξ‖²` to avoid `log`, and use
continuity at `σ = 1/2`.

## Step 3: a Gamma ratio bound (`Lindelof/GammaRatio.lean`)

There is `C` such that for `1/4 ≤ a ≤ b ≤ 1` and `|y| ≥ 1`:

    |Γ(b+iy)| ≤ C |y|^{b-a} |Γ(a+iy)|.

Proof from the Gauss product `GammaSeq_tendsto_Gamma`:
`|Γ(b+iy)/Γ(a+iy)| = lim n^{b-a} Π_{k≤n} |a+k+iy|/|b+k+iy|`, and
`Σ_{k≤n} ½ log(((b+k)²+y²)/((a+k)²+y²)) ≥ (b-a)(log n - log(|y|+2)) - C`.
(The terms with `k ≤ |y|` cost at most `(b-a) log(|y|+2)`; the tail with `k > |y|` differs from
`(b-a)/(k+1)` by `O(y²/k³ + 1/k²)`.)

## Step 4: consequences for ζ (`Lindelof/Transfer.lean`)

From Steps 2–3 with `ζ = ξ / (s(s-1) Γℝ(s))`:

* `norm_zeta_half_le`: `∃ C, ∀ δ ∈ (0, 1/2], ∀ t ≥ 1,
  ‖ζ(1/2+it)‖ ≤ C t^{δ/2} ‖ζ(1/2+δ+it)‖`.
* `norm_zeta_le_poly`: `∃ C, ∀ σ ∈ [1/2, 2], ∀ t ≥ 1, ‖ζ(σ+it)‖ ≤ C t`
  (compare with `σ' = 2`, where `|ζ| ≤ ζ(2)`).

## Step 5: a logarithm of ζ₁ on `σ > 1/2` (`Lindelof/LogZeta.lean`)

The half-plane `H = {σ > 1/2}` is convex, hence simply connected; `ζ₁` is continuous and
nonvanishing there (Step 1). `Complex.exists_continuousOn_eqOn_exp_comp` gives a continuous `L`
with `exp ∘ L = ζ₁` on `H`; it is holomorphic (local inverse of `exp`). Normalize by an integer
multiple of `2πi` so that `L` agrees with `log(s-1) + Σ_p -log(1-p^{-s})` at `s = 2`, hence on
`σ > 1` by connectedness, so `‖L(s)‖ ≤ C` for `2 ≤ σ ≤ 3`.

## Step 6: Borel–Carathéodory (`Lindelof/BorelCaratheodory.lean`)

`Re L = log|ζ₁| ≤ C log(|t|+2)` on `1/2 < σ ≤ 3` (Step 4 polynomial bound plus compactness for
small `|t|`). `Complex.borelCaratheodory` on discs centred at `5/2 + it` of radius `2 - δ/2`
gives, for each `δ > 0`, `‖L(s)‖ ≤ C_δ log(|t|+2)` for `1/2+δ ≤ σ ≤ 3`.

## Step 7: Hadamard three-lines (`Lindelof/ThreeLines.lean`)

Apply `Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip` to
`F(s) = L(s) · exp((s - it₀)²)` on the strip `1/2+δ ≤ σ ≤ 2`. The Gaussian factor makes `F`
bounded and localizes it at height `t₀`: `|F| ≤ C log(t₀+2)` on the left edge and `|F| ≤ C` on the
right. For `σ ≥ 1/2+2δ` this gives `‖L(σ+it₀)‖ ≤ C (log(t₀+2))^α` with
`α = (2-σ)/(2-1/2-δ) < 1`.

## Step 8: assembly (`Lindelof/Main.lean`)

Given `ε`, take `δ = ε` in Step 4: `‖ζ(1/2+it)‖ ≤ C t^{ε/2} ‖ζ(1/2+ε+it)‖`, and
`‖ζ(1/2+ε+it)‖ ≤ |exp L| / |s-1| ≤ exp(C (log t)^α) = O(t^{ε/2})` by Step 7, because
`(log t)^α = o(log t)`.

## Status

| Step | File | Status |
|---|---|---|
| 1 | `Lindelof/RH.lean` | todo |
| 2 | `Lindelof/Monotone.lean` | todo |
| 3 | `Lindelof/GammaRatio.lean` | todo |
| 4 | `Lindelof/Transfer.lean` | todo |
| 5 | `Lindelof/LogZeta.lean` | todo |
| 6 | `Lindelof/BorelCaratheodory.lean` | todo |
| 7 | `Lindelof/ThreeLines.lean` | todo |
| 8 | `Lindelof/Main.lean` | todo |
