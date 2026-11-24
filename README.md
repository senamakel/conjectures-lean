# The density hypothesis from RH in Lean

Let `N(σ, T)` count the zeros `ρ = β + iγ` of `ζ(s)`, with multiplicity, in `σ ≤ β ≤ 1`,
`0 < γ ≤ T`. The density hypothesis says that `N(σ, T) = O_ε(T^{2(1-σ)+ε})` uniformly in
`1/2 ≤ σ ≤ 1` (see [Wikipedia](https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis#The_density_hypothesis)
and Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., ch. 9 *(section unverified)*).
It follows from RH, and from the Lindelöf hypothesis. Unconditionally the best uniform exponent is `30/13` in place of `2`
(Ingham, Quart. J. Math. 11 (1940) for `σ ≤ 7/10`, with Guth–Maynard, arXiv:2405.20552 (2024) for
`σ ≥ 7/10`). This project proves the formal-conjectures statement from RH, and on the way formalises
the Riemann–von Mangoldt upper bounds `N(T) ≪ T log T` and `N(T + 1) - N(T) ≪ log T`
unconditionally, as a library for other projects.

**Literature status, two labels.** (1) The zero-counting bounds `N(T) ≪ T log T` and
`N(T + 1) - N(T) ≪ log T` are **known** (von Mangoldt 1905); no RH is used, and this is a Lean
formalisation of them. (2) The density hypothesis is an **RH-consequence**: it is immediate from
RH (and from Lindelöf). The Lean proof is conditional on RH, and its unconditional form is only
as reliable as the Lean proof of RH in leanprover-community/riemann-hypothesis, which has not been
independently verified. It is not new mathematics.

```lean
theorem DensityHypothesis.densityHypothesis_of_RH (hRH : RiemannHypothesis) :
    DensityHypothesis.Statement

-- unconditional zero counting (namespace `Density`)
theorem Density.zeroCountOn_riemannZeta_le_of_subset_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ S : Set ℂ,
      S ⊆ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} →
      (zeroCountOn riemannZeta S : ℝ) ≤ C * T * Real.log T

theorem Density.zeroCountOn_riemannZeta_le_of_subset_box :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, ∀ S : Set ℂ,
      S ⊆ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im - T| ≤ 1} →
      (zeroCountOn riemannZeta S : ℝ) ≤ C * Real.log (|T| + 2)
```

The target, in `Density/Statement.lean` (its definitions must not change):

```lean
noncomputable def Complex.zeroCountOn (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ s ∈ S, analyticOrderNatAt f s

noncomputable abbrev DensityHypothesis.zetaZeroCount (σ T : ℝ) : ℕ :=
  Complex.zeroCountOn riemannZeta
    {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T}

def DensityHypothesis.Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε)
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `DensityHypothesis.densityHypothesis_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `density_hypothesis` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `Density.zeroCountOn_riemannZeta_le_of_subset_strip` | D | none |
| `Density.zeroCountOn_riemannZeta_le_of_subset_box` | D | none |

The statement is formal-conjectures'
[`density_hypothesis_zeta_zeros`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/DensityHypothesis.lean)
(`research open` there; it follows from RH), and `zeroCountOn` is from
[`FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean),
both copied word for word at commit `86a2f58`; the only edits (dropped `module`/`public`
markers and `@[category]` attributes, the open theorem turned into a `Prop`) are listed in the
file's docstring. The implied constant depends only on `ε`, uniformly in `σ ∈ [1/2, 1]` and
`T ≥ 2`, exactly as stated there. The main library takes RH as a hypothesis and never imports
riemann-hypothesis.

## Axioms

`lake env lean` on a file with `#print axioms` after `import Density` (the same list is pinned by
`#guard_msgs` in `Density/AxiomCheck.lean`, so the default build fails if it changes):

```
'DensityHypothesis.densityHypothesis_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.zeroCountOn_riemannZeta_le_of_subset_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.zeroCountOn_xiZeta_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.zeroCountOn_le_of_jensen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.zeroCountOn_riemannZeta_eq_xiZeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.zeroCountOn_riemannZeta_le_of_subset_box' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no `axiom` declarations.

## Proof outline

Write `ξ(s) = s(s-1)Λ(s)` for erdos-985's entire `Erdos985.Analytic.xiZeta`.

1. **Jensen's inequality for `zeroCountOn`** (`Density/ZeroCount/Jensen.lean`): if `f` is analytic
   on `|s - c| ≤ R`, `f c ≠ 0` and `‖f‖ ≤ M` on `|s - c| = R`, the zeros in any
   `S ⊆ {|s - c| ≤ r}` number at most `log(M/‖f c‖)/log(R/r)`. This restates Mathlib's
   `AnalyticOnNhd.sum_divisor_le`.
2. **`ζ` and `ξ` have the same multiplicities right of `Re s = -2`** (`Density/ZeroCount/Xi.lean`):
   near `ρ ≠ 0, 1`, `ζ = ξ · Γℝ⁻¹/(s(s-1))` with an analytic cofactor that vanishes only at the
   trivial zeros; at `0` and `1` both orders are `0` (`ζ` is not analytic at its pole).
3. **`N(T) ≪ T log T`** (`Density/ZeroCount/Global.lean`): Step 1 for `ξ` on `|s| ≤ r ⊂ |s| ≤ 2r`
   with `ξ(0) = 1` and erdos-985's `‖ξ(s)‖ ≤ C exp(C‖s‖ log(‖s‖+2))` gives
   `≤ ((log C₀ + 4C₀)/log 2) · r log(r+2)` zeros (`C₀ = max C 1`); the strip
   `0 ≤ β ≤ 1, |γ| ≤ T` lies in `|s| ≤ T + 1`, giving `C = (9/2)(log C₀ + 4C₀)/log 2`.
4. **`N(T+1) - N(T) ≪ log T`** (`Density/ZeroCount/Local.lean`): zeros of `ξ` have `0 < β < 1`;
   erdos-985's Hadamard expansion of `ξ'/ξ` at `2 + iT` minus the one at `2` gives
   `Σ_ρ m_ρ/(4 + (T-γ)²) ≤ Re ξ'/ξ(2+iT) + K` with `K = -Re ξ'/ξ(2) + 2Σ m_ρ/|ρ|²`; each zero with
   `|γ - T| ≤ 1` has weight `≥ 1/5`. Then `ξ'/ξ = 1/s + 1/(s-1) - ½log π + ½ψ(s/2) + ζ'/ζ`,
   `Re ψ(1+iy) ≤ ψ(1) + 2 + log(|y|+1)` (digamma series split at `⌈|y|⌉`), and
   `|ζ'/ζ(2+iT)| ≤ Σ Λ(n)/n²`.
5. **Assembly** (`Density/Main.lean`): under RH, `ζ(s) ≠ 0` for `Re s > 1/2`, `Im s ≠ 0`, so
   `N(σ, T) = 0` for `σ > 1/2`. At `σ = 1/2` the exponent is `1 + ε`, and Step 3 with
   `log T ≤ T^ε/ε` gives `N(1/2, T) ≤ (C/ε) T^{1+ε}`.

## Layout

| File | Content |
|---|---|
| `Density/Statement.lean` | Target definitions (fixed; copied from formal-conjectures) |
| `Density/ZeroCount/Jensen.lean` | Step 1 |
| `Density/ZeroCount/Xi.lean` | Step 2 |
| `Density/ZeroCount/Global.lean` | Step 3 |
| `Density/ZeroCount/Local.lean` | Step 4 |
| `Density/ZeroCount.lean` | The zero-counting library (imports Steps 1–4) |
| `Density/Main.lean` | Step 5: `densityHypothesis_of_RH` |
| `Density/AxiomCheck.lean` | `#guard_msgs` allow-list of the headline axioms |
| `Unconditional/DensityUnconditional.lean` | One-line discharge from riemann-hypothesis |

### Using the zero-counting library

Import `Density.ZeroCount` (lake dependency `https://github.com/senamakel/density-rh.git`). The
stable statements are `Density.zeroCountOn_le_of_jensen`,
`Density.zeroCountOn_riemannZeta_eq_xiZeta`, `Density.zeroCountOn_xiZeta_le`,
`Density.zeroCountOn_riemannZeta_le_of_subset_strip`,
`Density.zeroCountOn_riemannZeta_le_of_subset_box`, and `Density.xiZeta_zero_re_mem`. Counts
use `Complex.zeroCountOn` from `Density/Statement.lean`; do not redefine it downstream.

## Deviations from the literature

None in the statement. The constants in Steps 3 and 4 are not explicit: they come from the
non-explicit constant in erdos-985's `xiZeta_growth` and from `Σ m_ρ/|ρ|²` and `ξ'/ξ(2)`, which
are not evaluated. The local bound is stated for the box `|γ - T| ≤ 1` (which contains
`T < γ ≤ T + 1`) with `log(|T| + 2)`, so it holds for every real `T`.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`).

```
lake exe cache get
lake build            # target `Density`
```

From a warm Mathlib cache, erdos-985's analytic modules (Hadamard factorisation, digamma series)
take about 110 s wall time (300 CPU-seconds) on the first build. Each module of this library
elaborates in under 15 CPU-seconds (`Local` about 11 s, `Global` and `Jensen` about 9 s). There
is no `native_decide`.

## Unconditional version

`Unconditional/DensityUnconditional.lean` imports riemann-hypothesis and closes the hypothesis in
one line:

| Theorem | Statement | Axioms |
|---|---|---|
| `density_hypothesis` | `DensityHypothesis.Statement` | `propext`, `Classical.choice`, `Quot.sound` |

Checked against riemann-hypothesis commit `507a75d91d` on 2026-11-24 with

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

which printed (about 20 min wall time, mostly waiting on the import):

```
riemann-hypothesis at 507a75d91d131d627b380df4e32f6e9fb21dd067
'density_hypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `prlimit --nofile=2000000:2000000`).

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

- `Density/Statement.lean`: definitions and statement copied from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at
  commit `86a2f58a4d7a3a0637d15d5b2ce627592b54b956`, Apache-2.0; see [`NOTICE.md`](NOTICE.md).
- No other file is vendored here. The Hadamard factorisation used in Step 4 is erdos-985's, which
  vendors PrimeNumberTheoremAnd under `Vendor/PNT` (Apache-2.0, see its `NOTICE.md`).
