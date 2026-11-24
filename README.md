# Littlewood's bound for ζ(1/2 + it) under RH in Lean

**Literature status: RH-consequence.** Littlewood (*On the zeros of the Riemann
zeta-function*, Proc. Cambridge Philos. Soc. 22 (1924), 295–318) proved that the Riemann
hypothesis implies

    |ζ(1/2 + it)| ≤ exp(C log t / log log t)    for all large t,

for some absolute constant `C`. Titchmarsh's 1930 tract *The Zeta-Function of Riemann*
gives it as Theorem 63 (§5.72); the second edition of *The Theory of the Riemann Zeta-Function*
has it in §14.14. Chandee and Soundararajan (Bull. LMS 43 (2011)) showed that any
`C > (log 2)/2` works. Without RH, the best known bounds are powers of `t` (Bourgain 2017:
`t^{13/84+ε}`), and even the weaker Lindelöf hypothesis is open. This repository's main library is a Lean proof that RH implies
Littlewood's bound, following Littlewood (1924), with an explicit-formula argument in the
style of Soundararajan (2009). `Unconditional/` gives Littlewood's bound, given the Lean
proof of RH in leanprover-community/riemann-hypothesis, which has not been independently
verified.

```lean
/-- `Littlewood/Statement.lean` -/
def LittlewoodBound : Prop :=
  ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (C * Real.log t / Real.log (Real.log t))

/-- `Littlewood/Main.lean` (proved with `C = 4`) -/
theorem littlewood_of_RH (hRH : RiemannHypothesis) : LittlewoodBound

/-- `Littlewood/Main.lean`: the same bound with the Dirichlet-polynomial length `x` explicit -/
theorem log_norm_zeta_le (hRH : RiemannHypothesis) :
    ∃ A B : ℝ, ∀ t x : ℝ, 1 ≤ t → Real.exp 2 ≤ x →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (A + Real.log t / (2 * Real.log x) +
        (2 * ((x + 1) * Real.log x ^ 2 + (x + 1 + ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2)) + B +
          Real.log (3 + t)) / Real.log x)
```

## Tier and provenance

| Theorem | Tier |
|---|---|
| `Littlewood.littlewood_of_RH` | **C** (RH is an explicit hypothesis) |
| `littlewood_bound` (`Unconditional/`) | **U** |

* `RiemannHypothesis` is Mathlib's definition, used unchanged. leanprover-community/riemann-hypothesis
  proves it as `riemannHypothesis : RiemannHypothesis`.
* `LittlewoodBound` is stated here. formal-conjectures has no statement of this result
  (searched 2026-11-24). It bounds the norm rather than `log |ζ|`, so no junk value of
  `Real.log 0` enters. It is stated only for `t → +∞`, since `ζ(s̄) = conj ζ(s)` gives the other side.
* There are no cited hypotheses (tier H) and no `sorry`.

## Axioms

From `lake env lean` on a file containing `import Littlewood` and the `#print axioms` lines:

```
'Littlewood.littlewood_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Littlewood.log_norm_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Littlewood.key_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Littlewood.explicit_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the standard three. There is no `native_decide`.

## Proof outline

The full blueprint, with every step's Lean statement, is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).
Notation: `s = σ + it`, `ρ = 1/2 + iγ` runs over the zeros of `ξ` with multiplicity `m_ρ`.

1. **Transfer to the half line** (lindelof-rh, `Lindelof.norm_zeta_half_le`). Under RH,
   `|ξ(σ+it)|` increases in `σ ≥ 1/2`, so `|ζ(1/2+it)| ≤ C₁ t^{δ/2} |ζ(1/2+δ+it)|`. It is
   used with `δ = 1/log x`, at a cost of `log t / (2 log x)`.
2. **Perron kernels** (`Kernel.lean`). `(1/2π)∫ y^w/w² = log y` and
   `(1/2π)∫ y^w/((w-b)w) = (y^b-1)/b` on `Re w = 2`, by Mellin inversion (erdos-985 `perron_prof`).
3. **Term-by-term Perron** (`Termwise.lean`). If `G(z) - G(s) = Σ m_i (1/(z-a_i) - 1/(s-a_i))`,
   then `(1/2π)∫ G(s+w) x^w/w² = G(s) log x + Σ m_i (x^{a_i-s}-1)/(a_i-s)²`. No contour is shifted.
4. **The three expansions.** `L(Λ, ·)` (`Dirichlet.lean`) gives `Σ_{n≤x} Λ(n) n^{-s} log(x/n)`.
   `-ξ'/ξ` (`XiSide.lean`, Hadamard from erdos-985) gives the zero terms. The archimedean factor
   `R(s) = 1/(s-1) - ½ log π + ½ ψ(1+s/2)` (`GammaSide.lean`, digamma series) gives
   `E_R` with `|E_R| ≤ x + 1 + Σ 1/(k+1)²`.
5. **Explicit formula** (`Explicit.lean`):
   `log x · (-ζ'/ζ(s)) = D(s,x) + Σ_ρ m_ρ (x^{ρ-s}-1)/(ρ-s)² - E_R(s,x)` for `Re s > 1/2`.
6. **Integrate over `σ ∈ [σ₀, 2]`** (`ZeroIntegral.lean`, `Integrate.lean`, `Bound.lean`).
   `log|ζ(σ₀+it)| - log|ζ(2+it)| = ∫ Re(-ζ'/ζ)`. For each zero, `-1/(ρ-s)²` integrates exactly
   to `Re 1/(2+it-ρ) - Re 1/(s₀-ρ)`, and `x^{ρ-s}/(ρ-s)²` integrates to at most
   `1/(log x |s₀-ρ|²)`. Under RH, `Re 1/(s₀-ρ) = (σ₀-1/2)/|s₀-ρ|²`, so the second term is absorbed
   once `(σ₀ - 1/2) log x ≥ 1`. What remains is `Σ m_ρ Re 1/(2+it-ρ) = Re ξ'/ξ(2+it) ≤ log t + O(1)`.
   Result (`key_bound`):
   `log x · (log|ζ(σ₀+it)| - log|ζ(2+it)|) ≤ 2((x+1)(log x)² + x + 1 + S) + Re ξ'/ξ(2+it)`.
7. **Constants** (`Main.lean`, `Asymptotic.lean`). Take `σ₀ = 1/2 + 1/log x` and `x = √(log t)`,
   so `log x = ½ log log t`. The exponent is `3 log t / log log t + O(√(log t) log log t)`,
   hence at most `4 log t / log log t` for large `t`.

## Layout

| File | Content |
|---|---|
| `Littlewood/Statement.lean` | `LittlewoodBound` (target) |
| `Littlewood/Kernel.lean` | Perron kernels `y^w/w²`, `y^w/((w-b)w)` and their `L¹` bounds |
| `Littlewood/Termwise.lean` | `perron_termwise`: Perron for a pole expansion |
| `Littlewood/Dirichlet.lean` | `perron_vonMangoldt`: the Dirichlet side |
| `Littlewood/XiSide.lean` | Hadamard for `ξ`, `Re ξ'/ξ = Σ m Re 1/(s-ρ)` under RH, `perron_xi` |
| `Littlewood/GammaSide.lean` | `ζ'/ζ = ξ'/ξ - R`, digamma bounds, `perron_R`, `norm_ER_le` |
| `Littlewood/Explicit.lean` | `explicit_formula` |
| `Littlewood/ZeroIntegral.lean` | one zero integrated over `[σ₀, 2]` |
| `Littlewood/Integrate.lean` | FTC for `log|ζ|`, summability, `‖D‖ ≤ (x+1)(log x)²` |
| `Littlewood/Bound.lean` | integrated zero sum, `key_bound` |
| `Littlewood/Asymptotic.lean` | the choice `x = √(log t)` |
| `Littlewood/Main.lean` | `log_norm_zeta_le`, `littlewood_of_RH` |
| `Unconditional/LittlewoodUnconditional.lean` | `littlewood_bound` (imports riemann-hypothesis) |

## Deviations from the literature

* **Constant.** The proof gives `C = 4`. Littlewood's theorem asks only for some `C`, so this is
  the full target. The sharp `(log 2)/2 + ε` (Chandee–Soundararajan) needs the Guinand–Weil
  formula with Beurling–Selberg majorants and is not attempted.
* **Route.** Littlewood and Titchmarsh go through `S₁(t) = ∫ S`. Here we integrate an explicit
  formula for `ζ'/ζ` in `σ`, as in Soundararajan (Ann. Math. 170 (2009)). A shorter "three
  circles" proof using lindelof-rh's machinery does not reach `log t / log log t`; see the
  blueprint, "Why not three circles".

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 `9538edb` and lindelof-rh `9165bfe` (lake
dependencies). Fetch the Mathlib cache first:

```
lake exe cache get
lake build            # target `Littlewood`
```

Building this repository's twelve modules takes about 3 minutes wall time (2 CPU-minutes) once the
dependencies are built; no module takes more than 90 s, most of it spent loading Mathlib.
No module uses `native_decide`.

## Unconditional version

`Unconditional/LittlewoodUnconditional.lean` imports riemann-hypothesis and closes the hypothesis
in one line:

| Theorem | Statement | Axioms |
|---|---|---|
| `littlewood_bound` | `Littlewood.LittlewoodBound` | `propext`, `Classical.choice`, `Quot.sound` |

Checked against riemann-hypothesis commit `507a75d91d` on 2026-11-24 (39 min wall time,
including the wait for a free check slot; most of the rest is loading the riemann-hypothesis
import) with

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

Output:

```
'littlewood_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files. Raise
the open-file limit first, e.g. `prlimit --nofile=2000000:2000000`.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

No files are vendored. The analytic toolkit (Hadamard factorisation of `ξ`, Perron/Mellin
kernels, the digamma series) comes from the erdos-985 dependency, and the transfer to the half
line from the lindelof-rh dependency. Both are used as lake packages.
