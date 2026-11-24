# The Lindelöf hypothesis from RH and GRH in Lean

The [Lindelöf hypothesis](https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis) (Lindelöf,
1908) says that `ζ(1/2 + it) = O(t^ε)` for every `ε > 0`. Littlewood (1912) proved that it
follows from the Riemann hypothesis (Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd
ed., §14.2); the same argument gives `L(1/2 + it, χ) = O_{χ,ε}(t^ε)` for every Dirichlet
character `χ` under GRH. Unconditionally only subconvexity bounds are known (for `ζ`, Bourgain
2017: `ζ(1/2 + it) = O(t^{13/84 + ε})`). This project formalises both implications.

**Literature status: RH-consequence.** Both implications are classical (Littlewood 1912, in
Titchmarsh). This repository is a complete Lean proof that RH implies the Lindelöf hypothesis
for ζ and that GRH implies it for every Dirichlet L-function, following Littlewood.
`Unconditional/` proves both statements unconditionally in Lean, with RH and GRH supplied by the
certified proof in leanprover-community/riemann-hypothesis, from the standard three axioms only.

```lean
theorem Lindelof.lindelof_of_RH (hRH : RiemannHypothesis) : Lindelof.LindelofHypothesis

theorem Lindelof.dirichletLindelof_of_GRH
    (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    Lindelof.DirichletLindelofHypothesis
```

The targets, fixed in `Lindelof/Statement.lean` (its definitions must not change):

```lean
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖) =O[atTop] fun t : ℝ => t ^ ε

def DirichletLindelofHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (ε : ℝ), 0 < ε →
    (fun t : ℝ => ‖DirichletCharacter.LFunction χ (1 / 2 + t * I)‖) =O[atTop]
      fun t : ℝ => t ^ ε
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `Lindelof.lindelof_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `Lindelof.dirichletLindelof_of_GRH` | C | `Erdos985.DirichletLNonvanishingRightOfHalf` |
| `lindelof_hypothesis` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `dirichletLindelof` (`Unconditional/`) | U | none; GRH from riemann-hypothesis |

`DirichletLNonvanishingRightOfHalf` is copied word for word from `src/Statements.lean` of
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
by [erdos-985](https://github.com/senamakel/erdos-985) (`Erdos985/Statement.lean`). The main
library takes RH/GRH as hypotheses and never imports riemann-hypothesis. No formal-conjectures
statement of the Lindelöf hypothesis is used; the targets are this repository's own.

The Dirichlet statement is in the `t`-aspect: the implied constant depends on `χ` and `ε`. It
covers every character, primitive or not, including the trivial one (whose pole at `s = 1` does
not meet the critical line).

## Axioms

`lake env lean` on a file with `#print axioms` after `import Lindelof`:

```
'Lindelof.lindelof_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lindelof.dirichletLindelof_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no `axiom` declarations.

## Proof outline

The full plan is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md). For `ζ`, with `ξ(s) = s(s-1)Λ(s)`:

1. RH in usable forms: `ζ₁ ≠ 0` on `σ > 1/2`, zeros of `ξ` on `σ = 1/2` (`Lindelof/RH.lean`).
2. `|ξ(σ+it)|` increases in `σ ≥ 1/2`: Hadamard's `ξ'/ξ` expansion at `z` and `1 - z̄` gives
   `2 Re ξ'/ξ = Σ_ρ m_ρ (2σ-1)/|s-ρ|² ≥ 0` (`Lindelof/Monotone.lean`, stated for any entire
   function of order one with zeros on the line).
3. `|Γ(b+iy)| ≤ C |y|^{b-a} |Γ(a+iy)|` for `0 ≤ a ≤ b ≤ 1`, `C = e⁵`, from the Gauss product
   (`Lindelof/GammaRatio.lean`); extended to `b ≤ 2` with `Γ(s+1) = sΓ(s)`.
4. `‖ζ(1/2+it)‖ ≤ C t^{δ/2} ‖ζ(1/2+δ+it)‖` and `‖ζ(s)‖ ≤ C|t|` on `σ ≥ 1/2`
   (`Lindelof/Transfer.lean`).
5. A holomorphic logarithm `M` of `ζ₁(s)/(s+1)` on `σ > 1/2`, bounded on `2 ≤ σ ≤ 5`
   (`Lindelof/LogZeta.lean`).
6. Borel–Carathéodory: `‖M‖ ≤ C_δ log(|t|+2)` on `σ ≥ 1/2 + δ` (`Lindelof/BorelCaratheodory.lean`).
7. Hadamard three-lines with a Gaussian: `‖M(σ+it)‖ ≤ C (log(|t|+2))^α`, `α < 1`
   (`Lindelof/ThreeLines.lean`).
8. Assembly, once for any `f` with `LogBounds f` (`Lindelof/Main.lean`).

For `L(s, χ)`: reduce to the primitive character `χ'` inducing `χ` (finitely many Euler factors,
each `≤ 2` in norm on `σ = 1/2`), and to `ζ` when `χ = 1`. For primitive `χ' ≠ 1`, replace `ξ` by
`Λ(s, χ')`: conjugation symmetry `conj Λ(s̄, χ) = Λ(s, χ⁻¹)` and the functional equation give
`Λ'/Λ(1 - z̄) = -log N - conj Λ'/Λ(z)`, so `‖Λ(σ+it)‖ ≤ N^{(σ'-σ)/2} ‖Λ(σ'+it)‖`
(`Lindelof/DirichletCompleted.lean`). Then `L = Λ/Γℝ(s+κ)`, `‖L - 1‖ ≤ π²/6 - 1` on `σ ≥ 2`, and a
logarithm of `L` itself feed Steps 6–8 (`Lindelof/DirichletBounds.lean`).

## Layout

| File | Content |
|---|---|
| `Lindelof/Statement.lean` | Target definitions (fixed) |
| `Lindelof/RH.lean` | Step 1 |
| `Lindelof/Monotone.lean` | Step 2, generic and for `ξ` |
| `Lindelof/GammaRatio.lean` | Step 3 |
| `Lindelof/Transfer.lean` | Step 4 for `ζ`; Gamma ratio on `[0, 2]` |
| `Lindelof/LogZeta.lean` | Step 5 for `ζ` |
| `Lindelof/BorelCaratheodory.lean` | Step 6, generic and for `ζ` |
| `Lindelof/ThreeLines.lean` | Step 7 |
| `Lindelof/Main.lean` | Step 8: `LogBounds`, `lindelof_of_RH` |
| `Lindelof/DirichletCompleted.lean` | Dirichlet Step 2: conjugation, log-derivative identity, monotonicity |
| `Lindelof/DirichletBounds.lean` | Dirichlet Steps 4–5, primitive case |
| `Lindelof/Dirichlet.lean` | Reduction to primitive characters, `dirichletLindelof_of_GRH` |
| `Unconditional/LindelofUnconditional.lean` | One-line discharges from riemann-hypothesis |

## Deviations from the literature

None in the statements. Two choices in the route: monotonicity of `|ξ|` (resp. `N^{σ/2}|Λ|`)
replaces Phragmén–Lindelöf, so neither Stirling's formula nor the convexity principle is needed;
and the Gamma ratio bound uses the constant `e⁵` rather than a sharp one, which only affects
implied constants.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`).

```
lake exe cache get
lake build            # target `Lindelof`
```

From a warm Mathlib cache the first build (erdos-985's analytic modules plus this library) takes
about 85 s wall time. Each module of this library elaborates in under 10 CPU-seconds
(`lake env lean Lindelof/<Module>.lean`; the heaviest are `BorelCaratheodory` and `Transfer`, about
8 s each). There is no `native_decide`.

## Unconditional version

`Unconditional/LindelofUnconditional.lean` imports riemann-hypothesis and closes the hypotheses
in one line each:

| Theorem | Statement | Axioms |
|---|---|---|
| `lindelof_hypothesis` | `Lindelof.LindelofHypothesis` | `propext`, `Classical.choice`, `Quot.sound` |
| `dirichletLindelof` | `Lindelof.DirichletLindelofHypothesis` | `propext`, `Classical.choice`, `Quot.sound` |

Checked against riemann-hypothesis commit `507a75d91d` on 2026-11-24 (about 30 min wall time,
most of it loading the riemann-hypothesis import) with

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

Output:

```
'lindelof_hypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichletLindelof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise
the open-file limit first, e.g. `prlimit --nofile=2000000:2000000`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored here. The analytic toolkit (Hadamard factorisation, growth of `ξ` and of
`Λ(s, χ)`, zeros of `Λ(s, χ)` under GRH) comes from
[erdos-985](https://github.com/senamakel/erdos-985), required as a lake dependency; its own
README credits the files it vendors.
