# Schoenfeld's bounds for ψ, θ and π − li under RH in Lean

Schoenfeld (*Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
(1976), 337–360, Theorem 10 and Corollary 1) proved that the Riemann hypothesis implies

* `|ψ(x) − x| < √x log² x / (8π)` for `x ≥ 73.2`,
* `|θ(x) − x| < √x log² x / (8π)` for `x ≥ 599`,
* `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`,

with `li` the principal-value logarithmic integral. These are explicit forms of von Koch's
1901 theorem `π(x) = li(x) + O(√x log x)` under RH. Unconditionally the best known error terms
are of the form `x exp(−c (log x)^{3/5} (log log x)^{−1/5})`.

**Literature status: RH-consequence** (von Koch 1901; Schoenfeld 1976). This repository is a
complete Lean proof that RH implies these bounds, following von Koch and Schoenfeld; a bound
`ψ(x) − x = O(√x log² x)` is RH in another form. It contains two results:

* from RH alone, all three bounds with Schoenfeld's thresholds and the constants `1/8`, `1/4`,
  `9/20`;
* Schoenfeld's exact statement, constant `1/(8π)` and his thresholds, from RH and one cited
  input, Rosser's explicit zero count (Rosser 1941, Theorem 19). The other numerical inputs
  are proved here by proved-sound checkers run with `native_decide`: PsiCert
  (`|ψ(x) − x| ≤ (4/5)√x` on `[1500, 10¹⁰]`, an exact segmented sieve over every integer up to
  `10¹⁰`) and the target itself on the three finite ranges `[73.2, 1500]`, `[599, 3·10⁴]`,
  `[2657, 4·10⁵]`.

```lean
theorem Schoenfeld.psiBound_of_RH (hRH : RiemannHypothesis) : PsiBound (1 / 8) 73.2
theorem Schoenfeld.thetaBound_of_RH (hRH : RiemannHypothesis) : ThetaBound (1 / 4) 599
theorem Schoenfeld.piBound_of_RH (hRH : RiemannHypothesis) : PiBound (9 / 20) 2657
theorem Schoenfeld.schoenfeld_weak_of_RH (hRH : RiemannHypothesis) :
    PsiBound (1 / 8) 73.2 ∧ ThetaBound (1 / 4) 599 ∧ PiBound (9 / 20) 2657

theorem Schoenfeld.schoenfeldPsi_of_RH (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) (hS : PsiSmallRange) : SchoenfeldPsi
theorem Schoenfeld.schoenfeldTheta_of_RH (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) (hS : ThetaSmallRange) : SchoenfeldTheta
theorem Schoenfeld.schoenfeldPi_of_RH (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) (hSθ : ThetaSmallRange) (hSπ : PiSmallRange) : SchoenfeldPi
theorem Schoenfeld.schoenfeld_of_RH (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) (hSψ : PsiSmallRange) (hSθ : ThetaSmallRange) (hSπ : PiSmallRange) :
    SchoenfeldStatement

theorem Schoenfeld.Check.psiSmallRange : PsiSmallRange
theorem Schoenfeld.Check.thetaSmallRange : ThetaSmallRange
theorem Schoenfeld.Check.piSmallRange : PiSmallRange
theorem Schoenfeld.psiCert : PsiCert

theorem Schoenfeld.schoenfeldPsi_of_RH_of_rosser (hRH : RiemannHypothesis)
    (hR : RosserZeroCount) : SchoenfeldPsi
theorem Schoenfeld.schoenfeldTheta_of_RH_of_rosser (hRH : RiemannHypothesis)
    (hR : RosserZeroCount) : SchoenfeldTheta
theorem Schoenfeld.schoenfeldPi_of_RH_of_rosser (hRH : RiemannHypothesis)
    (hR : RosserZeroCount) : SchoenfeldPi
theorem Schoenfeld.schoenfeld_of_RH_of_rosser (hRH : RiemannHypothesis)
    (hR : RosserZeroCount) : SchoenfeldStatement
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

and the inputs (`Schoenfeld/Inputs.lean`, `Schoenfeld/SmallRange.lean`)

```lean
noncomputable def positiveZeroCount (T : ℝ) : ℝ := by
  classical
  exact ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0
def RosserZeroCount : Prop :=
  ∀ T : ℝ, 2 ≤ T →
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588
def PsiCert : Prop :=
  ∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x
def PsiSmallRange : Prop :=
  ∀ x : ℝ, 73.2 ≤ x → x ≤ 1500 → |ψ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2)
def ThetaSmallRange : Prop :=
  ∀ x : ℝ, 599 ≤ x → x ≤ 30000 → |θ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2)
def PiSmallRange : Prop :=
  ∀ x : ℝ, 2657 ≤ x → x ≤ 400000 →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < 1 / (8 * π) * (√x * Real.log x)
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `psiBound_of_RH`, `thetaBound_of_RH`, `piBound_of_RH` (constants `1/8`, `1/4`, `9/20`) | C | RH |
| `Check.psiSmallRange`, `Check.thetaSmallRange`, `Check.piSmallRange` | D | none |
| `psiCert` (`PsiCert`) | D | none |
| `schoenfeldPsi_of_RH_of_rosser` (`1/(8π)`, `x ≥ 73.2`) | C + H | RH, `RosserZeroCount` |
| `schoenfeldTheta_of_RH_of_rosser` (`1/(8π)`, `x ≥ 599`) | C + H | RH, `RosserZeroCount` |
| `schoenfeldPi_of_RH_of_rosser` (`1/(8π)`, `x ≥ 2657`) | C + H | RH, `RosserZeroCount` |
| `schoenfeld_of_RH_of_rosser` (`SchoenfeldStatement`) | C + H | RH, `RosserZeroCount` |
| `schoenfeld_of_RH` (the same with all five inputs as arguments) | C + H | RH and the five inputs |

In `Unconditional/` RH is discharged by riemann-hypothesis: the first row becomes tier U and the
`_of_rosser` rows U + H. The one input still cited is `RosserZeroCount`.

* `RiemannHypothesis` is Mathlib's definition, used as is.
* `RosserZeroCount` is Rosser's explicit Riemann–von Mangoldt formula (J. B. Rosser, *Explicit
  bounds for some functions of prime numbers*, Amer. J. Math. 63 (1941), 211–232, Theorem 19).
  `positiveZeroCount` and the statement are copied verbatim from
  `TernaryGoldbach.RSBounds.Rosser1941` in [teorth/IEANTN](https://github.com/teorth/IEANTN),
  where `Rosser1941.zero_count_bounds` proves it with no hypothesis (Lean `v4.34.0-rc2`).
* `PsiCert` is copied verbatim from `Goals.Schoenfeld1976.PsiCert` in
  [Garald1/RSBounds](https://github.com/Garald1/RSBounds), where a kernel-checked campaign also
  proves it (Lean `v4.35.0`). It is proved here (`Schoenfeld.psiCert`) by our own checker; no
  code is taken from RSBounds.
* `PsiSmallRange`, `ThetaSmallRange`, `PiSmallRange` are Schoenfeld's three bounds restricted to
  `[73.2, 1500]`, `[599, 3·10⁴]` and `[2657, 4·10⁵]` (Schoenfeld checks these ranges with
  Gram's, the Rosser–Walker and the Appel–Rosser tables). They are proved here
  (`Schoenfeld/Check/`).
* `Real.logIntegral` (principal-value `li`, `li(x) = li(2) + ∫₂ˣ dt/log t`) is copied verbatim
  from formal-conjectures (`FormalConjecturesForMathlib/Analysis/SpecialFunctions/LogIntegral.lean`).
  formal-conjectures has no statement of Schoenfeld's bounds (checked 2026-11-24), so
  `PsiBound`, `ThetaBound`, `PiBound` are written here.
* `native_decide`: 24 calls, each evaluating a checker whose soundness is proved in Lean (see
  Axioms). The RH-only theorems and `schoenfeld_of_RH` use none.

## Axioms

`lake env lean` on a file with `import Schoenfeld` and `#print axioms`:

```
'Schoenfeld.schoenfeld_weak_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.psiBound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.thetaBound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.piBound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.schoenfeld_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.schoenfeldPsi_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.schoenfeldTheta_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.schoenfeldPi_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
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


The constant `1/(8π)` (steps 6–10):

6. **Zero count** (`ZeroCount.lean`). In `Im s > 0`, `ζ` and `ξ` have the same orders, so
   `positiveZeroCount T` is erdos-985's `Σ_{0<γ≤T} m`. `ρ ↦ 1 − ρ` preserves orders and negates
   `γ` under RH, so `F(T) ≤ 2 G(T)`, `G(T) = Σ_{γ>0} m min(1/γ, T/γ²)`.
7. **`G(T)` from `N(t)`** (`CountSum.lean`). `G(T) = ∫_{4.4}^T N/t² + 2T ∫_T^∞ N/t³` (sum and
   integral exchanged), Rosser's bound with `log log t ≤ log t/e`, and closed-form integrals:
   `G(T) ≤ log² T/(4π) + (1 − log 2π) log T/(2π) + 0.65`.
8. **ψ** (`PsiSharp.lean`, `Sharp.lean`). Step 3 with `h = ⌈2√8 √x⌉`:
   `|ψ(x) − x| ≤ √x (u²/(8π) − 0.2985 u + 4.62)` for `x ≥ 10¹⁰`, `u = log x` (ratio `0.90` to
   the target at `10¹⁰`). PsiCert covers `[1500, 10¹⁰]` and `PsiSmallRange` `[73.2, 1500]`.
9. **θ** (`ThetaSharp.lean`). `ψ − θ ≤ 1.047 √x` for `x ≥ 10¹⁰` (PsiCert and step 8 for
   `ψ(√x)`, `ψ(x^{1/3})`), so `|θ(x) − x| ≤ √x (u²/(8π) − 0.2985 u + 5.667)`; on
   `[3·10⁴, 10¹⁰]`, PsiCert gives `|θ(x) − x| ≤ 3.9252 √x`; `ThetaSmallRange` covers
   `[599, 3·10⁴]`.
10. **π** (`PiSharp.lean`). Step 6's decomposition with `|∫₂^599| ≤ 33`,
    `|∫_599^{3·10⁴}| ≤ 14`, `|∫_{3·10⁴}^{10¹⁰}| ≤ 2448`, and for `x ≥ 10¹⁰` the antiderivative
    `2√t (1/(8π) − 0.2985/ℓ + 6.2/ℓ²)` for the tail. What is left,
    `√x ((2/(8π) − 0.2985) + 5.07/u + 12.4/u²) < 5148`, is checked on four ranges of `u`.
    `[4·10⁵, 10¹⁰]` uses `3.9252 √x` throughout; `PiSmallRange` covers `[2657, 4·10⁵]`.

The finite inputs (steps 11–13), each a checker with a soundness proof, run by `native_decide`:

11. **ψ and θ on the small ranges** (`Check/Step.lean`, `Check/PsiTheta.lean`). `checkA` walks
    the integers; between consecutive jumps `a < b` of the step function (prime powers for ψ,
    primes for θ) the value `c` is constant, and since the right-hand side `F` is increasing it
    suffices that `c − a < F(a)` and `b − c < F(a)`. `c` is carried as a rational enclosure,
    `log p` from Mathlib's series for `log(1 − y)` (40 terms, rounded to `2^{-64}`), `√a` from
    `Nat.sqrt`, `π < 3.141593`. Smallest margins (floating point): `0.033` (ψ, cell `[89, 97)`), `0.23` (θ).
12. **π − li on `[2657, 4·10⁵]`** (`Check/Li.lean`, `Check/Pi.lean`). `li(2657)` is enclosed in
    `[399.553, 399.640]` (true value 399.597): `li(2) = ∫₀¹ (1/log(1+u) + 1/log(1−u)) du`
    (the vendored definition) on a mesh of 3,327 cells, each bounded by the monotonicity of
    `1/log(1+u)` and `1/log(1/(1−u))`, and `∫₂^{2657} dt/log t` on 10,545 cells. `checkB` then
    walks the primes, advancing `li` by `(b−a)/log b ≤ ∫ₐᵇ dt/log t ≤ (b−a)/log a`. Smallest
    margin (floating point) `0.32`, at `x → 2659⁻`.
13. **PsiCert** (`SchoenfeldCompute/Psi.lean`, `PsiCert/`). `[1500, 10⁶]`: `checkA` with
    `F(x) = (4/5)√x` (step 11). `(10⁶, 10¹⁰]`: an exact segmented sieve over every integer up
    to `10¹⁰ + 3.4·10⁶`, in segments of `2^{20}`, with the primes up to `131072` as sieving
    primes and a second array holding the exponent `k` of each proper prime power `p^k`. It is
    cut into blocks `(a, b]` of length `2^{⌊log₂ a⌋/2 − 8}` (about `√a/256`), on which
    `Λ(n) ∈ [log a/k, log b/k]` gives enclosures of `ψ(b)` at scale `2^{96}`, and
    `log b = log a + log(1 + (b−a)/a)` comes from the `artanh` series. For `x ∈ [a, b]`,
    monotonicity gives `ψ(x) − x ≤ ψ(b) − a` and `x − ψ(x) ≤ b − ψ(a)`; both are checked to be
    `≤ (4/5)√a` in integer arithmetic. Proved: the sieve is exact (`sieveSeg_spec`: an entry is
    unmarked iff its number is prime), the exponent array is exact (`ppMark_sound`,
    `ppMark_complete`), the logarithms are sound, and the guards imply the bound
    (`blockStep_sound`, `runSegs_sound`). The run is split into 20 chunks of 477 segments; the
    20 intermediate states (`PsiCert/Data.lean`) are untrusted data, and each transition is one
    `native_decide`. Smallest margin (a floating-point replay in C) `67`, i.e. `0.0064 √a`, at
    `a ≈ 1.1·10⁸`.

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
| `Schoenfeld/Inputs.lean` | `positiveZeroCount`, `RosserZeroCount`, `PsiCert` (tier H, verbatim) |
| `Schoenfeld/SmallRange.lean` | `PsiSmallRange`, `ThetaSmallRange`, `PiSmallRange` (tier H) |
| `Schoenfeld/ZeroCount.lean` | `ζ`/`ξ` orders, `positiveZeroCount = cnt`, `F(T) ≤ 2 G(T)` |
| `Schoenfeld/CountSum.lean` | `G(T)` as an integral of `N(t)`, `Gsum_le_Ub` |
| `Schoenfeld/PsiSharp.lean` | `psi_explicit`, `psi_sharp_large` |
| `Schoenfeld/ThetaSharp.lean` | `theta_explicit`, `theta_mid_abs`, `theta_sharp_large` |
| `Schoenfeld/Sharp.lean` | `schoenfeldPsi_of_RH`, `schoenfeldTheta_of_RH` |
| `Schoenfeld/PiSharp.lean` | the `π − li` integrals, `schoenfeldPi_of_RH`, `schoenfeld_of_RH` |
| `Schoenfeld/Check/Basic.lean` | Rational enclosures of `log`, `√`, `1/x` and the right-hand sides, with soundness |
| `Schoenfeld/Check/Step.lean` | `checkA`, the cell checker for a step function against an increasing `F`, and `checkA_sound` |
| `Schoenfeld/Check/PsiTheta.lean` | `psiSmallRange`, `thetaSmallRange` (2 `native_decide`) |
| `Schoenfeld/Check/Li.lean` | Mesh folds, the enclosure of `li(2657)` |
| `Schoenfeld/Check/Pi.lean` | `checkB`, `piSmallRange` (1 `native_decide`) |
| `Schoenfeld/Ranges.lean` | `schoenfeld_of_RH_of_cited` (ranges discharged) |
| `SchoenfeldCompute/Psi.lean` | PsiCert computation, Lean core only, precompiled |
| `Schoenfeld/PsiCert/Log.lean` | Soundness of the fixed-point logarithms (from robin-rh) |
| `Schoenfeld/PsiCert/Sieve.lean` | The segmented sieve is exact |
| `Schoenfeld/PsiCert/Pp.lean` | Prime-power exponents; the base primes |
| `Schoenfeld/PsiCert/Run.lean` | Block, segment and run soundness |
| `Schoenfeld/PsiCert/Small.lean` | PsiCert on `[1500, 10⁶]` (1 `native_decide`) |
| `Schoenfeld/PsiCert/Data.lean`, `Chunks/C00`–`C19`, `Chain.lean` | Chunk states and the 20 transitions (20 `native_decide`) |
| `Schoenfeld/PsiCert/Final.lean` | `psiCert` |
| `Schoenfeld/WithRosser.lean` | `schoenfeld_of_RH_of_rosser` and its three parts |
| `scripts/Axioms.lean` | `#print axioms` for every headline theorem |
| `Unconditional/SchoenfeldUnconditional.lean` | RH discharged by riemann-hypothesis |

## Deviations from the literature

**From RH alone** the thresholds are Schoenfeld's and the constants larger: `1/8 = π · 1/(8π)`
for ψ, `1/4 = 2π · 1/(8π)` for θ, `9/20 ≈ 11.3 · 1/(8π)` for π − li. Zero density enters there
through a Poisson-kernel sum, which costs a factor `≈ 1.41` in the leading term; that method's
asymptotic constant for ψ is about `0.056`.

**With Rosser's zero count** the constant is Schoenfeld's `1/(8π)` and the thresholds are his
(`73.2`, `599`, `2657`). The route differs from his in where the analysis takes over:

| | Schoenfeld 1976 | here |
|---|---|---|
| analytic range | `x ≥ e^{16}` (ψ, θ), `x ≥ 2.3·10⁹` (π) | `x ≥ 10¹⁰` (ψ, θ, π) |
| zero input | Rosser's `N(T)` and Rosser–Schoenfeld 1975, Lemmas 8 and 9 | Rosser's `N(T)` only (`RosserZeroCount`) |
| `[1500, 10¹⁰]` | Rosser–Schoenfeld 1975 Theorems 18, 19, 24 | PsiCert, proved here by a sieve to `10¹⁰` |
| finite ranges | Gram, Rosser–Walker, Appel–Rosser, Brent tables | `PsiSmallRange`, `ThetaSmallRange`, `PiSmallRange`, proved here |

The constant needs no list of zeros: Rosser's count is used from `t = 4.4` (`|ρ|² ≥ 20`), and its
error term `0.137 log t + 0.443 log log t + 1.588`, integrated against `dt/t²`, adds a constant
multiple of `√x`, which the `−0.2985 u √x` term absorbs from `x = 10¹⁰` on. The π bound has the
least slack, smallest near `x ≈ e^{25}` (the four-range check in step 10).

**Not proved here: `RosserZeroCount`.** It is proved in Lean in teorth/IEANTN
(`Rosser1941.zero_count_bounds`, Lean `v4.34.0-rc2`), whose import closure is 219 files and
about 95,000 lines: about 25,000 lines for `T ≥ 100` (Backlund's argument) and about 70,000 for
the 29 zero certificates below height 100. A sample of 14 of its files (4,375 lines, from the
Lean `v4.35.0` originals in Garald1/RSBounds and calr3/ternary-goldbach) compiled against this
Mathlib pin with 6 files needing a one- or two-line fix each; the full port is estimated at one
to two weeks. The proof here only uses the upper half of Rosser's bound, and only through a
constant. A floating-point model of the error budget (not a Lean proof) indicates that any
explicit count `N(T) ≤ (T/2π) log(T/2π) − T/2π + 7/8 + a log T + b` valid for all
`T ≥ 4.4` with `2.48 a + b ≤ 3.31` would do (Rosser's uses `2.33`); the binding constraint is
the π bound just above `10¹⁰`.

## Building

```bash
lake exe cache get
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 `9538edb`. On top of the Mathlib and erdos-985
caches the library takes about 4.5 CPU-minutes; per module (user CPU): `Schoenfeld.Psi` 44 s
(the 15-interval case split), `ThetaSharp` 34 s, `PsiSharp` 34 s, `PiSharp` 31 s, `Theta` 23 s,
`Pi` 19 s, `Density` 15 s, `CountSum` 15 s, `PsiInt` 14 s, `ZeroSums` 10 s, the rest under 7 s
each. The round-5 modules were timed with `lake env lean` on a loaded machine.

## Unconditional version

`Unconditional/SchoenfeldUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the RH hypothesis with its `riemannHypothesis` (Alpöge's
proof). The first three bounds are then proved unconditionally in Lean; the `1/(8π)` bounds are
proved from the cited inputs alone.

| Theorem | Statement | Axioms |
|---|---|---|
| `psi_bound` | `Schoenfeld.PsiBound (1 / 8) 73.2` | standard three |
| `theta_bound` | `Schoenfeld.ThetaBound (1 / 4) 599` | standard three |
| `pi_bound` | `Schoenfeld.PiBound (9 / 20) 2657` | standard three |
| `schoenfeld_psi` | `RosserZeroCount → PsiCert → PsiSmallRange → SchoenfeldPsi` | standard three |
| `schoenfeld_theta` | `RosserZeroCount → PsiCert → ThetaSmallRange → SchoenfeldTheta` | standard three |
| `schoenfeld_pi` | `RosserZeroCount → PsiCert → ThetaSmallRange → PiSmallRange → SchoenfeldPi` | standard three |
| `schoenfeld_statement` | the five inputs `→ SchoenfeldStatement` | standard three |

Checked 2026-11-24 with `scripts/check-unconditional.sh` against riemann-hypothesis
`507a75d91d` (library at commit `6d7e828`): the build succeeded and `#print axioms` printed

```
'psi_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'theta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'pi_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The run took 13.8 min wall (146 s user CPU), dominated by importing riemann-hypothesis.

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on Linux raise
`nofile` (for example `sudo prlimit --pid $$ --nofile=2000000:2000000`); on macOS:
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the
Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh).
This check links against the community build cache and does not repeat those kernel checks.

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
* `SchoenfeldCompute/Psi.lean`: the fixed-point logarithms (`logLoS`, `logUpS`) and the sieve
  loops (`markLoop`, `sieveLoop`, `sieveSeg`) are copied from robin-rh
  (`RobinCompute/Core.lean` at `343518c`, same authors); `Schoenfeld/PsiCert/Log.lean` and the
  soundness half of `Schoenfeld/PsiCert/Sieve.lean` copy their proofs (`Robin/Compute/Log.lean`,
  `Robin/Compute/Sieve.lean`). The log enclosures in `Schoenfeld/Check/Basic.lean` follow
  nicolas-rh's `Nicolas/Check` (same authors).
* The block reduction for PsiCert (check `ψ(b) − a` and `b − ψ(a)` at block ends) is the idea of
  Garald1/RSBounds' `PsiSieveBlockReduction`; the code here is independent of theirs.
* The explicit formula, Hadamard factorisation and gamma-factor bounds come from
  [senamakel/erdos-985](https://github.com/senamakel/erdos-985) (lake dependency).
* `Schoenfeld/Inputs.lean`: the definition `positiveZeroCount` and the statement of
  `RosserZeroCount` are copied verbatim from [teorth/IEANTN](https://github.com/teorth/IEANTN)
  (`Solutions/Schoenfeld1976Numerics.v1/Proof/RSBounds/RosserCountDefinition.lean`,
  `Rosser1941.lean`, commit `cd9c2dd`), Apache License 2.0. The statement of `PsiCert` is copied
  verbatim from [Garald1/RSBounds](https://github.com/Garald1/RSBounds)
  (`RSBounds/Schoenfeld1976TargetsExtra.lean`, commit `82d7a55`), Apache License 2.0. No proof
  is copied from either. See [`NOTICE`](NOTICE).
