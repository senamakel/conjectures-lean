# Schoenfeld's bounds for ψ, θ and π − li under RH in Lean

Schoenfeld (*Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
(1976), 337–360, Theorem 10 and Corollary 1) proved that the Riemann hypothesis implies

* `|ψ(x) − x| < √x log² x / (8π)` for `x ≥ 73.2`,
* `|θ(x) − x| < √x log² x / (8π)` for `x ≥ 599`,
* `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`,

with `li` the principal-value logarithmic integral. These are explicit forms of von Koch's
1901 theorem `π(x) = li(x) + O(√x log x)` under RH. Unconditionally the best known error terms
are of the form `x exp(−c (log x)^{3/5} (log log x)^{−1/5})`.

This repository proves, in Lean, that RH implies explicit bounds of this form at Schoenfeld's
thresholds, with constants `1/8` for ψ, `1/4` for θ and `9/20` for `π − li`. `Unconditional/`
proves the three bounds unconditionally in Lean, with RH supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
Schoenfeld's constant is `1/(8π)` in all three (see "Deviations from the literature").

**Literature status: RH-consequence** (von Koch 1901; Schoenfeld 1976). The Lean proof follows
von Koch and Schoenfeld. Since a bound `ψ(x) − x = O(√x log² x)` is equivalent to RH, these
theorems are RH in another form.

```lean
theorem Schoenfeld.psiBound_of_RH (hRH : RiemannHypothesis) : PsiBound (1 / 8) 73.2
theorem Schoenfeld.thetaBound_of_RH (hRH : RiemannHypothesis) : ThetaBound (1 / 4) 599
theorem Schoenfeld.piBound_of_RH (hRH : RiemannHypothesis) : PiBound (9 / 20) 2657
theorem Schoenfeld.schoenfeld_weak_of_RH (hRH : RiemannHypothesis) :
    PsiBound (1 / 8) 73.2 ∧ ThetaBound (1 / 4) 599 ∧ PiBound (9 / 20) 2657
```

where (`Schoenfeld/Statement.lean`)

```lean
def PsiBound (C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → |ψ x - x| < C * (√x * Real.log x ^ 2)
def ThetaBound (C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → |θ x - x| < C * (√x * Real.log x ^ 2)
def PiBound (C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < C * (√x * Real.log x)
def SchoenfeldPsi : Prop := PsiBound (1 / (8 * π)) 73.2
def SchoenfeldTheta : Prop := ThetaBound (1 / (8 * π)) 599
def SchoenfeldPi : Prop := PiBound (1 / (8 * π)) 2657
def SchoenfeldStatement : Prop := SchoenfeldPsi ∧ SchoenfeldTheta ∧ SchoenfeldPi
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `Schoenfeld.psiBound_of_RH`, `thetaBound_of_RH`, `piBound_of_RH`, `schoenfeld_weak_of_RH` | C | `RiemannHypothesis` (Mathlib's definition, used as is) |
| `psi_bound`, `theta_bound`, `pi_bound` (`Unconditional/`) | U | none; RH from riemann-hypothesis |

Both tiers hold for the constants `1/8`, `1/4` and `9/20`. Schoenfeld's exact
`SchoenfeldStatement` (constant `1/(8π)`) is the fixed target and is not proved; see
"Deviations from the literature".

`Real.logIntegral` (principal-value `li`, `li(x) = li(2) + ∫₂ˣ dt/log t`) is copied verbatim
from formal-conjectures (`FormalConjecturesForMathlib/Analysis/SpecialFunctions/LogIntegral.lean`).
formal-conjectures has no statement of Schoenfeld's bounds (checked 2026-11-24), so
`PsiBound`, `ThetaBound` and `PiBound` are this repository's own. There are no cited
hypotheses (tier H), no `native_decide` and no finite computation: the range above each
threshold is covered analytically.

## Axioms

`lake env lean` on a file with `import Schoenfeld` and `#print axioms`:

```
'Schoenfeld.schoenfeld_weak_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.psiBound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.thetaBound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.piBound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Proof outline

Full blueprint with every constant: [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).

1. Zeros under RH (`ZeroSums.lean`): `Σ_ρ m/|ρ|² = 2 + γ − log 4π < 1/20`, so `|ρ|² ≥ 20`.
   Hadamard's product for erdos-985's `ξ` at real `s = a + 1/2` gives the Poisson-kernel sum
   `Σ_ρ m a/(a² + γ²) = Re ξ'/ξ(a + 1/2) ≤ ½ log a − ½ log 2π + (12/5)/a` for `a ≥ 2`. This is
   the zero-density input (in place of an explicit `N(T)`).
2. The zero sum (`Density.lean`): `F(T) = Σ_ρ m min(1/|ρ|, T/|ρ|²)` is at most `T/20`, and
   at most `0.9 Jb(10T) + 2 Vb(T) + 2.75 Vb(5) ≈ 0.225 log² T` by writing `1/|γ|` as
   `0.9 ∫₂^{10T} da/(a² + γ²)` and exchanging sum and integral.
3. Differenced explicit formula (`PsiInt.lean`): erdos-985's weighted explicit formula for
   `Ψ₁(x) = Σ_{n ≤ x} Λ(n)(x − n)` at integers; for `b = a + h`,
   `h ψ(a) ≤ Ψ₁(b) − Ψ₁(a) ≤ h ψ(b)` and `|b^{ρ+1} − a^{ρ+1}| ≤ min(|ρ+1| h √b, 2 b^{3/2})` give
   `|ψ(x) − x| ≤ h/2 + 3.6 + 1.5/h + √(x+h) F(2(x+h)/h)`.
4. ψ (`Psi.lean`): for `73.2 ≤ x ≤ 2^18`, `F(T) ≤ T/20` with `h ≈ 0.447 x^{3/4}` on 15
   intervals (worst ratio to `√x log² x/8`: `0.98`). For `x ≥ 2^18`, step 2 with `h = ⌈4√x⌉`
   reduces to a quadratic inequality in `log x` (ratio `0.82` at `2^18`).
5. θ (`Theta.lean`): Costa Pereira's `ψ − θ ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})` and
   `ψ(y) ≤ log 4 · y + 2√y log y` (both in Mathlib) give `ψ − θ ≤ √x log² x/8` for `x ≥ 599`.
6. π (`Pi.lean`): partial summation (Mathlib) and integration by parts for `li`:
   `π(x) − li(x) = (θ(x) − x)/log x + ∫₂ˣ (θ(t) − t)/(t log² t) dt + 2/log 2 − li(2)`, with
   `|∫₂^599| ≤ 33`, `|∫_599^x| ≤ √x/2` and `0 ≤ li(2) ≤ 2`.

## Layout

| File | Content |
|---|---|
| `Schoenfeld/LogIntegral.lean` | `Real.logIntegral`, vendored from formal-conjectures |
| `Schoenfeld/Statement.lean` | Target statements `PsiBound`, `ThetaBound`, `PiBound`, `SchoenfeldStatement` |
| `Schoenfeld/ZeroSums.lean` | RH for `ξ`, `Σ m/\|ρ\|²`, the Poisson-kernel bound |
| `Schoenfeld/Density.lean` | The zero sum `F(T)`: trivial and log² bounds |
| `Schoenfeld/Psi1.lean` | `Ψ₁` and monotone differencing (from robin-rh) |
| `Schoenfeld/PsiInt.lean` | Explicit formula for `Ψ₁`, `ψ` at integers and real `x` |
| `Schoenfeld/Psi.lean` | `psiBound_of_RH` |
| `Schoenfeld/Theta.lean` | Costa Pereira bound for `ψ − θ`, `thetaBound_of_RH` |
| `Schoenfeld/Pi.lean` | `li` by parts, `piBound_of_RH` |
| `Schoenfeld/Main.lean` | `schoenfeld_weak_of_RH` |
| `Unconditional/SchoenfeldUnconditional.lean` | RH discharged by riemann-hypothesis |

## Deviations from the literature

The thresholds are Schoenfeld's; the constants are larger: `1/8 = π · 1/(8π)` for ψ,
`1/4 = 2π · 1/(8π)` for θ, `9/20 ≈ 11.3 · 1/(8π)` for π − li.

* ψ: Schoenfeld uses Rosser's explicit zero-counting formula
  `N(T) = (T/2π) log(T/2πe) + 7/8 + O(log T)` with explicit error and the numerically
  verified low zeros. Neither is available in Mathlib or erdos-985, so zero density enters
  here through the Poisson-kernel sum of step 1, which costs a factor `≈ 1.41` in the leading
  term and large lower-order terms. The method's ratio to `√x log² x/8` is `0.98` near
  `x = 73`, `0.82` at `2^18` and tends to `0.45`; its asymptotic constant is about `0.056`,
  versus `1/(8π) ≈ 0.0398`. Reaching `1/(8π)` from `x = 73.2` requires formalising an explicit
  `N(T)` (argument principle and Backlund's bound for `arg ζ(1/2 + iT)`) and a verified list
  of the first zeros.
* θ: `θ = ψ − (ψ − θ)` adds the bound `ψ − θ ≤ √x log² x/8` to ψ's `1/8`. The true
  `ψ − θ` is about `√x`, so θ inherits ψ's constant for large `x`, but not uniformly from `599`
  with these estimates.
* π: inherits θ's constant `1/4`, plus `2 · (1/4)/log x` from the tail integral and
  `∫₂^599 dt/log² t ≈ 26` (bounded by 33): `0.40` at `x = 2657`, rounded up to `9/20`.

## Building

```bash
lake exe cache get
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 `9538edb`. On top of the Mathlib and erdos-985
caches the library takes about 2.5 CPU-minutes; per module (user CPU): `Schoenfeld.Psi` 44 s
(the 15-interval case split), `Theta` 23 s, `Pi` 19 s, `Density` 15 s, `PsiInt` 14 s,
`ZeroSums` 10 s, the rest under 6 s each.

## Unconditional version

`Unconditional/SchoenfeldUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the hypothesis with its `riemannHypothesis`. The theorems below have no hypothesis:

| Theorem | Statement | Axioms |
|---|---|---|
| `psi_bound` | `Schoenfeld.PsiBound (1 / 8) 73.2` | standard three |
| `theta_bound` | `Schoenfeld.ThetaBound (1 / 4) 599` | standard three |
| `pi_bound` | `Schoenfeld.PiBound (9 / 20) 2657` | standard three |

Checked 2026-11-24 with `scripts/check-unconditional.sh` against riemann-hypothesis
`507a75d91d` (library at commit `a72aed5`): the build succeeded and `#print axioms` printed

```
'psi_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'theta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'pi_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The run took 44.5 min wall (200 s user CPU), dominated by importing riemann-hypothesis on a
loaded machine.

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on Linux raise
`nofile` (for example `sudo prlimit --pid $$ --nofile=2000000:2000000`); on macOS:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

* `Schoenfeld/LogIntegral.lean`: from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
  `FormalConjecturesForMathlib/Analysis/SpecialFunctions/LogIntegral.lean` at commit
  `86a2f58a4d7a3a0637d15d5b2ce627592b54b956`, Apache License 2.0, © 2026 The Formal
  Conjectures Authors. Change: module-system header replaced by `import Mathlib` (noted in
  the file).
* `Schoenfeld/Psi1.lean`: `psi1` and its differencing lemmas copied from
  [senamakel/robin-rh](https://github.com/senamakel/robin-rh) (`Robin/Defs.lean`,
  `Robin/RH/Psi1.lean`), same author.
* The explicit formula, Hadamard factorisation and gamma-factor bounds come from
  [senamakel/erdos-985](https://github.com/senamakel/erdos-985) (lake dependency).
