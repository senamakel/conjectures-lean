# Schoenfeld's 1/(8π) bounds for ψ, θ and π − li from RH in Lean

This repository proves Schoenfeld's explicit bounds under the Riemann hypothesis, with his
constant `1/(8π)` and his thresholds:

* `|ψ(x) − x| < √x log² x / (8π)` for `x ≥ 73.2`,
* `|θ(x) − x| < √x log² x / (8π)` for `x ≥ 599`,
* `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`,

where `li` is the principal-value logarithmic integral (L. Schoenfeld, *Sharper bounds for the
Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30 (1976), 337–360, Theorem 10 and
Corollary 1). `Schoenfeld.schoenfeld_of_RH : RiemannHypothesis → SchoenfeldStatement` takes RH
as its only hypothesis: every numerical input is proved in Lean in this repository.
`Unconditional/` closes RH with the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
so `schoenfeld_statement : SchoenfeldStatement` is proved unconditionally in Lean.

**Literature status: RH-consequence** (von Koch 1901; Schoenfeld 1976). The three bounds are
explicit forms of von Koch's 1901 theorem `π(x) = li(x) + O(√x log x)` under RH, and a bound
`ψ(x) − x = O(√x log² x)` is RH in another form. The main library is a complete Lean proof that
RH implies Schoenfeld's Theorem 10 and Corollary 1, following Schoenfeld. The proof of RH is
L. Alpöge's (2026), certified by the Lean FRO and the Mathlib Initiative on 2026-11-21. Without
RH the best known error terms have the form `x exp(−c (log x)^{3/5} (log log x)^{−1/5})`.

`schoenfeld_of_RH` rests on five inputs, all proved here:

* Rosser's explicit zero count (J. B. Rosser 1941, Theorem 19), `rosserZeroCount`, from the
  vendored Lean proof of Garald1/RSBounds, calr3/ternary-goldbach and teal-sea/zeta-lab in
  `Vendor/Rosser/`;
* `psiCert`, the bound `|ψ(x) − x| ≤ (4/5)√x` on `[1500, 10¹⁰]`, from an exact segmented sieve
  over every integer up to `10¹⁰`;
* Schoenfeld's three bounds on the finite ranges `[73.2, 1500]`, `[599, 3·10⁴]` and
  `[2657, 4·10⁵]`.

`psiCert` and the three finite ranges are proved-sound checkers evaluated with `native_decide`
(24 calls in all). A second theorem, `schoenfeld_weak_of_RH`, gives the three bounds at
Schoenfeld's thresholds with the larger constants `1/8`, `1/4` and `9/20`, from RH with no
computation.

```lean
-- Schoenfeld/Rosser.lean
theorem Schoenfeld.schoenfeld_of_RH (hRH : RiemannHypothesis) : SchoenfeldStatement
theorem Schoenfeld.schoenfeldPsi_of_RH (hRH : RiemannHypothesis) : SchoenfeldPsi
theorem Schoenfeld.schoenfeldTheta_of_RH (hRH : RiemannHypothesis) : SchoenfeldTheta
theorem Schoenfeld.schoenfeldPi_of_RH (hRH : RiemannHypothesis) : SchoenfeldPi

-- Unconditional/SchoenfeldUnconditional.lean
theorem schoenfeld_statement : Schoenfeld.SchoenfeldStatement :=
  Schoenfeld.schoenfeld_of_RH riemannHypothesis

-- the inputs, each proved with no hypothesis
theorem Schoenfeld.rosserZeroCount : RosserZeroCount
theorem Schoenfeld.psiCert : PsiCert
theorem Schoenfeld.Check.psiSmallRange : PsiSmallRange
theorem Schoenfeld.Check.thetaSmallRange : ThetaSmallRange
theorem Schoenfeld.Check.piSmallRange : PiSmallRange

-- larger constants, no computation
theorem Schoenfeld.psiBound_of_RH (hRH : RiemannHypothesis) : PsiBound (1 / 8) 73.2
theorem Schoenfeld.thetaBound_of_RH (hRH : RiemannHypothesis) : ThetaBound (1 / 4) 599
theorem Schoenfeld.piBound_of_RH (hRH : RiemannHypothesis) : PiBound (9 / 20) 2657
theorem Schoenfeld.schoenfeld_weak_of_RH (hRH : RiemannHypothesis) :
    PsiBound (1 / 8) 73.2 ∧ ThetaBound (1 / 4) 599 ∧ PiBound (9 / 20) 2657

-- the same statement with inputs as arguments, for reuse with other inputs
theorem Schoenfeld.schoenfeld_of_RH_of_inputs (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) (hSψ : PsiSmallRange) (hSθ : ThetaSmallRange) (hSπ : PiSmallRange) :
    SchoenfeldStatement
theorem Schoenfeld.schoenfeld_of_RH_of_cited (hRH : RiemannHypothesis) (hR : RosserZeroCount)
    (hC : PsiCert) : SchoenfeldStatement
theorem Schoenfeld.schoenfeld_of_RH_of_rosser (hRH : RiemannHypothesis)
    (hR : RosserZeroCount) : SchoenfeldStatement
```

`schoenfeld_of_RH_of_rosser` has the parts `schoenfeldPsi_of_RH_of_rosser`,
`schoenfeldTheta_of_RH_of_rosser` and `schoenfeldPi_of_RH_of_rosser`, with the same hypotheses.
The statements (`Schoenfeld/Statement.lean`):

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

The inputs (`Schoenfeld/Inputs.lean`, `Schoenfeld/SmallRange.lean`):

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
| `schoenfeld_statement` (`SchoenfeldStatement`, `Unconditional/`) | U | none |
| `schoenfeld_of_RH` (`SchoenfeldStatement`) | C | RH |
| `schoenfeldPsi_of_RH` (`1/(8π)`, `x ≥ 73.2`) | C | RH |
| `schoenfeldTheta_of_RH` (`1/(8π)`, `x ≥ 599`) | C | RH |
| `schoenfeldPi_of_RH` (`1/(8π)`, `x ≥ 2657`) | C | RH |
| `rosserZeroCount` (`RosserZeroCount`) | D | none |
| `psiCert` (`PsiCert`) | D | none |
| `Check.psiSmallRange`, `Check.thetaSmallRange`, `Check.piSmallRange` | D | none |
| `psiBound_of_RH`, `thetaBound_of_RH`, `piBound_of_RH` (constants `1/8`, `1/4`, `9/20`) | C | RH |
| `schoenfeld_of_RH_of_rosser` and its parts | C + H | RH, `RosserZeroCount` |
| `schoenfeld_of_RH_of_inputs` and its parts (all five inputs as arguments) | C + H | RH and the five inputs |

In `Unconditional/` the riemann-hypothesis repository discharges RH, and every `_of_RH` row
becomes tier U. The `_of_rosser`, `_of_cited` and `_of_inputs` versions stay available for use
with other inputs.

* `RiemannHypothesis` is Mathlib's definition, used as is.
* `RosserZeroCount` is Rosser's explicit Riemann–von Mangoldt formula (J. B. Rosser, *Explicit
  bounds for some functions of prime numbers*, Amer. J. Math. 63 (1941), 211–232, Theorem 19).
  `positiveZeroCount` and the statement are copied verbatim from
  `TernaryGoldbach.RSBounds.Rosser1941` in [teorth/IEANTN](https://github.com/teorth/IEANTN).
  `Schoenfeld.rosserZeroCount` (`Schoenfeld/Rosser.lean`) proves it with
  `TernaryGoldbach.RSBounds.Rosser1941.zero_count_bounds`, vendored with its whole import
  closure (216 files, about 95,000 lines) from the Lean `v4.35.0` originals in
  [Garald1/RSBounds](https://github.com/Garald1/RSBounds) `82d7a55`. Its
  `RosserCountDefinition.lean` has the same `positiveZeroCount`, so the two statements are the
  same term. See [`Vendor/Rosser/README.md`](Vendor/Rosser/README.md).
* `PsiCert` is copied verbatim from `Goals.Schoenfeld1976.PsiCert` in
  [Garald1/RSBounds](https://github.com/Garald1/RSBounds), where a kernel-checked campaign also
  proves it (Lean `v4.35.0`). `Schoenfeld.psiCert` proves it with this repository's own
  checker; no code is taken from RSBounds.
* `PsiSmallRange`, `ThetaSmallRange` and `PiSmallRange` are Schoenfeld's three bounds restricted
  to `[73.2, 1500]`, `[599, 3·10⁴]` and `[2657, 4·10⁵]`. Schoenfeld checked these ranges with
  Gram's, the Rosser–Walker and the Appel–Rosser tables; here `Schoenfeld/Check/` proves them.
* `Real.logIntegral` (principal-value `li`, `li(x) = li(2) + ∫₂ˣ dt/log t`) is copied verbatim
  from formal-conjectures (`FormalConjecturesForMathlib/Analysis/SpecialFunctions/LogIntegral.lean`).
  formal-conjectures has no statement of Schoenfeld's bounds (checked 2026-11-24), so
  `PsiBound`, `ThetaBound` and `PiBound` are written here.
* `native_decide`: 24 calls, each evaluating a checker whose soundness is proved in Lean (see
  Axioms). `schoenfeld_weak_of_RH`, `rosserZeroCount` and `schoenfeld_of_RH_of_inputs` use
  none, and the vendored Rosser proof has none.

## Axioms

`lake env lean scripts/Axioms.lean` (2026-11-24, at the commit of this README):

```
'Schoenfeld.schoenfeld_weak_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.schoenfeld_of_RH_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.Check.psiSmallRange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1]
'Schoenfeld.Check.thetaSmallRange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1]
'Schoenfeld.Check.piSmallRange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1]
'Schoenfeld.psiCert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeld_of_RH_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeldPsi_of_RH_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeldTheta_of_RH_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeldPi_of_RH_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeld_of_RH_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.rosserZeroCount' depends on axioms: [propext, Classical.choice, Quot.sound]
'Schoenfeld.schoenfeldPsi_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeldTheta_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeldPi_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Schoenfeld.schoenfeld_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
```

`schoenfeld_weak_of_RH`, `rosserZeroCount` and `schoenfeld_of_RH_of_inputs` use the standard
three axioms only. The finite inputs add 24 `native_decide` axioms to `schoenfeld_of_RH`, each the
evaluation of a checker proved sound in Lean:

| `native_decide` | Checks | Soundness | Time |
|---|---|---|---|
| `checkA_psi` | ψ on `[73.2, 1500]` against `√x log² x/(8π)` | `checkA_sound` | seconds |
| `checkA_theta` | θ on `[599, 3·10⁴]` | `checkA_sound` | seconds |
| `checkB_pi` | `li(2657)` enclosure, then `π − li` on `[2657, 4·10⁵]` | `liAnchor_sound`, `checkB_sound` | under a minute (whole module) |
| `checkA_psiCert` | ψ on `[1500, 10⁶]` against `(4/5)√x` | `checkA_sound` | 71 s (whole module) |
| `chunk00` to `chunk19` | the segmented sieve over `(1, 1.00034·10¹⁰]`, 477 segments each | `runSegs_sound` | 13.9 CPU-min in all (`chunk00` 130 s, the others 22 to 80 s) |

The first four run in Lean's interpreter. The chunks call `SchoenfeldCompute`, compiled to
native code (`precompileModules`). Times are single-core user CPU on a loaded machine.
## Proof outline

The full blueprint, with every constant, is [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md). Steps 1
to 6 give the bounds with the constants `1/8`, `1/4` and `9/20`. Steps 7 to 11 sharpen them to
`1/(8π)`, steps 12 to 14 are the finite inputs, and step 15 is Rosser's zero count.

1. Zeros under RH (`ZeroSums.lean`): `Σ_ρ m/|ρ|² = 2 + γ − log 4π < 1/20`, so `|ρ|² ≥ 20`.
   Hadamard's product for erdos-985's `ξ` at real `s = a + 1/2` gives the Poisson-kernel sum
   `Σ_ρ m a/(a² + γ²) = Re ξ'/ξ(a + 1/2) ≤ ½ log a − ½ log 2π + (12/5)/a` for `a ≥ 2`. This is
   the zero-density input for the weaker constants.
2. The zero sum (`Density.lean`): `F(T) = Σ_ρ m min(1/|ρ|, T/|ρ|²)` is at most `T/20`, and
   at most `0.9 Jb(10T) + 2 Vb(T) + 2.75 Vb(5) ≈ 0.225 log² T`, by writing `1/|γ|` as
   `0.9 ∫₂^{10T} da/(a² + γ²)` and exchanging sum and integral.
3. Differenced explicit formula (`PsiInt.lean`): erdos-985's weighted explicit formula for
   `Ψ₁(x) = Σ_{n ≤ x} Λ(n)(x − n)` at integers. For `b = a + h`,
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
7. Zero count (`ZeroCount.lean`). In `Im s > 0`, `ζ` and `ξ` have the same orders, so
   `positiveZeroCount T` is erdos-985's `Σ_{0<γ≤T} m`. The map `ρ ↦ 1 − ρ` preserves orders and
   negates `γ` under RH, so `F(T) ≤ 2 G(T)` with `G(T) = Σ_{γ>0} m min(1/γ, T/γ²)`.
8. `G(T)` from `N(t)` (`CountSum.lean`). `G(T) = ∫_{4.4}^T N/t² + 2T ∫_T^∞ N/t³` (sum and
   integral exchanged). Rosser's bound with `log log t ≤ log t/e` and closed-form integrals give
   `G(T) ≤ log² T/(4π) + (1 − log 2π) log T/(2π) + 0.65`.
9. ψ (`PsiSharp.lean`, `Sharp.lean`). Step 3 with `h = ⌈2√8 √x⌉` gives
   `|ψ(x) − x| ≤ √x (u²/(8π) − 0.2985 u + 4.62)` for `x ≥ 10¹⁰`, `u = log x` (ratio `0.90` to
   the target at `10¹⁰`). PsiCert covers `[1500, 10¹⁰]` and `PsiSmallRange` covers `[73.2, 1500]`.
10. θ (`ThetaSharp.lean`). `ψ − θ ≤ 1.047 √x` for `x ≥ 10¹⁰` (PsiCert and step 9 for
    `ψ(√x)`, `ψ(x^{1/3})`), so `|θ(x) − x| ≤ √x (u²/(8π) − 0.2985 u + 5.667)`. On
    `[3·10⁴, 10¹⁰]`, PsiCert gives `|θ(x) − x| ≤ 3.9252 √x`, and `ThetaSmallRange` covers
    `[599, 3·10⁴]`.
11. π (`PiSharp.lean`). The decomposition of step 6 with `|∫₂^599| ≤ 33`,
    `|∫_599^{3·10⁴}| ≤ 14`, `|∫_{3·10⁴}^{10¹⁰}| ≤ 2448`, and for `x ≥ 10¹⁰` the antiderivative
    `2√t (1/(8π) − 0.2985/ℓ + 6.2/ℓ²)` for the tail. What is left,
    `√x ((2/(8π) − 0.2985) + 5.07/u + 12.4/u²) < 5148`, is checked on four ranges of `u`.
    `[4·10⁵, 10¹⁰]` uses `3.9252 √x` throughout, and `PiSmallRange` covers `[2657, 4·10⁵]`.
12. ψ and θ on the small ranges (`Check/Step.lean`, `Check/PsiTheta.lean`). `checkA` walks
    the integers. Between consecutive jumps `a < b` of the step function (prime powers for ψ,
    primes for θ) the value `c` is constant, and since the right-hand side `F` is increasing it
    suffices that `c − a < F(a)` and `b − c < F(a)`. `c` is carried as a rational enclosure,
    with `log p` from Mathlib's series for `log(1 − y)` (40 terms, rounded to `2^{-64}`), `√a`
    from `Nat.sqrt` and `π < 3.141593`. Smallest margins (floating point): `0.033` for ψ (cell
    `[89, 97)`), `0.23` for θ.
13. π − li on `[2657, 4·10⁵]` (`Check/Li.lean`, `Check/Pi.lean`). `li(2657)` is enclosed in
    `[399.553, 399.640]` (true value 399.597): `li(2) = ∫₀¹ (1/log(1+u) + 1/log(1−u)) du`
    (the vendored definition) on a mesh of 3,327 cells, each bounded by the monotonicity of
    `1/log(1+u)` and `1/log(1/(1−u))`, and `∫₂^{2657} dt/log t` on 10,545 cells. `checkB` then
    walks the primes, advancing `li` by `(b−a)/log b ≤ ∫ₐᵇ dt/log t ≤ (b−a)/log a`. Smallest
    margin (floating point) `0.32`, at `x → 2659⁻`.
14. PsiCert (`SchoenfeldCompute/Psi.lean`, `PsiCert/`). On `[1500, 10⁶]`, `checkA` with
    `F(x) = (4/5)√x` (step 12). On `(10⁶, 10¹⁰]`, an exact segmented sieve over every integer up
    to `10¹⁰ + 3.4·10⁶`, in segments of `2^{20}`, with the primes up to `131072` as sieving
    primes and a second array holding the exponent `k` of each proper prime power `p^k`. It is
    cut into blocks `(a, b]` of length `2^{⌊log₂ a⌋/2 − 8}` (about `√a/256`), on which
    `Λ(n) ∈ [log a/k, log b/k]` gives enclosures of `ψ(b)` at scale `2^{96}`, and
    `log b = log a + log(1 + (b−a)/a)` comes from the `artanh` series. For `x ∈ [a, b]`,
    monotonicity gives `ψ(x) − x ≤ ψ(b) − a` and `x − ψ(x) ≤ b − ψ(a)`, and both are checked to
    be `≤ (4/5)√a` in integer arithmetic. Proved: the sieve is exact (`sieveSeg_spec`: an entry
    is unmarked iff its number is prime), the exponent array is exact (`ppMark_sound`,
    `ppMark_complete`), the logarithms are sound, and the guards imply the bound
    (`blockStep_sound`, `runSegs_sound`). The run is split into 20 chunks of 477 segments. The
    20 intermediate states (`PsiCert/Data.lean`) are untrusted data, and each transition is one
    `native_decide`. Smallest margin (a floating-point replay in C) `67`, that is `0.0064 √a`,
    at `a ≈ 1.1·10⁸`.
15. Rosser's zero count (`Rosser.lean`, `Vendor/Rosser/`). `rosserZeroCount` is the vendored
    `Rosser1941.zero_count_bounds`. For `T ≥ 100` it uses Backlund's argument
    (`RSBounds/BacklundHighCount.lean`: the argument principle on the rectangle with corners
    `1/2`, `5/4`, `5/4 + iT`, `1/2 + iT`, Jensen's formula on circles centred on `σ = 5/4` for
    the variation of `arg ζ`, Stirling for the Gamma factor and an Euler–Maclaurin bound for `ζ`).
    For `T ≤ 100` it uses zeta-lab's certificate that the 29 zeros of height at most 100 are
    simple and lie in explicit rational brackets on the critical line (`RHHeight100/`,
    `HardyTenZeros/`, `RSBounds/BacklundLowCount.lean`), so `N(T)` is known exactly below 100.

The proof uses only the upper half of Rosser's count, and only through a constant. A
floating-point model of the error budget (not a Lean proof) indicates that any explicit count
`N(T) ≤ (T/2π) log(T/2π) − T/2π + 7/8 + a log T + b` valid for all `T ≥ 4.4` with
`2.48 a + b ≤ 3.31` would also do (Rosser's uses `2.33`). The binding constraint is the π bound
just above `10¹⁰`.

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
| `Schoenfeld/Inputs.lean` | `positiveZeroCount`, `RosserZeroCount`, `PsiCert` (input statements, verbatim) |
| `Schoenfeld/SmallRange.lean` | `PsiSmallRange`, `ThetaSmallRange`, `PiSmallRange` (input statements) |
| `Schoenfeld/ZeroCount.lean` | `ζ`/`ξ` orders, `positiveZeroCount = cnt`, `F(T) ≤ 2 G(T)` |
| `Schoenfeld/CountSum.lean` | `G(T)` as an integral of `N(t)`, `Gsum_le_Ub` |
| `Schoenfeld/PsiSharp.lean` | `psi_explicit`, `psi_sharp_large` |
| `Schoenfeld/ThetaSharp.lean` | `theta_explicit`, `theta_mid_abs`, `theta_sharp_large` |
| `Schoenfeld/Sharp.lean` | `schoenfeldPsi_of_RH_of_inputs`, `schoenfeldTheta_of_RH_of_inputs` |
| `Schoenfeld/PiSharp.lean` | the `π − li` integrals, `schoenfeldPi_of_RH_of_inputs`, `schoenfeld_of_RH_of_inputs` |
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
| `Schoenfeld/PsiCert/Data.lean`, `Chunks/C00` to `C19`, `Chain.lean` | Chunk states and the 20 transitions (20 `native_decide`) |
| `Schoenfeld/PsiCert/Final.lean` | `psiCert` |
| `Schoenfeld/WithRosser.lean` | `schoenfeld_of_RH_of_rosser` and its three parts |
| `Schoenfeld/Rosser.lean` | `rosserZeroCount`; `schoenfeld_of_RH` and its three parts |
| `Vendor/Rosser/` | the vendored proof of Rosser's count (216 files; `README.md`, `PORTING.md`, `licenses/`) |
| `scripts/Axioms.lean` | `#print axioms` for every headline theorem |
| `Unconditional/SchoenfeldUnconditional.lean` | RH discharged by riemann-hypothesis |
## Deviations from the literature

None in the statement: `SchoenfeldStatement` has Schoenfeld's constant `1/(8π)` and his
thresholds `73.2`, `599` and `2657`, and `schoenfeld_of_RH` assumes RH only. The route differs
from his in where the analysis takes over:

| | Schoenfeld 1976 | here |
|---|---|---|
| analytic range | `x ≥ e^{16}` (ψ, θ), `x ≥ 2.3·10⁹` (π) | `x ≥ 10¹⁰` (ψ, θ, π) |
| zero input | Rosser's `N(T)` and Rosser–Schoenfeld 1975, Lemmas 8 and 9 | Rosser's `N(T)` only (`RosserZeroCount`) |
| `[1500, 10¹⁰]` | Rosser–Schoenfeld 1975 Theorems 18, 19, 24 | PsiCert, proved here by a sieve to `10¹⁰` |
| finite ranges | Gram, Rosser–Walker, Appel–Rosser, Brent tables | `PsiSmallRange`, `ThetaSmallRange`, `PiSmallRange`, proved here |

The constant needs no list of zeros. Rosser's count is used from `t = 4.4` (`|ρ|² ≥ 20`), and
its error term `0.137 log t + 0.443 log log t + 1.588`, integrated against `dt/t²`, adds a
constant multiple of `√x`, which the `−0.2985 u √x` term absorbs from `x = 10¹⁰` on. The π bound
has the least slack, near `x ≈ e^{25}` (the four-range check in step 11).

The secondary theorems `psiBound_of_RH`, `thetaBound_of_RH` and `piBound_of_RH` have
Schoenfeld's thresholds and larger constants: `1/8 = π · 1/(8π)` for ψ, `1/4 = 2π · 1/(8π)` for
θ and `9/20 ≈ 11.3 · 1/(8π)` for π − li. They use no zero count: zero density enters through a
Poisson-kernel sum, which costs a factor of about `1.41` in the leading term, and that method's
asymptotic constant for ψ is about `0.056`.

## Building

```bash
lake exe cache get
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 `9538edb`. On top of the Mathlib and erdos-985
caches the analytic library takes about 4.5 CPU-minutes; per module (user CPU):
`Schoenfeld.Psi` 44 s (the 15-interval case split), `ThetaSharp` 34 s, `PsiSharp` 34 s,
`PiSharp` 31 s, `Theta` 23 s, `Pi` 19 s, `Density` 15 s, `CountSum` 15 s, `PsiInt` 14 s,
`ZeroSums` 10 s, the rest under 7 s each. The finite checks add about 17 CPU-minutes:
`Schoenfeld.PsiCert.Chunks.C00` to `C19` 13.9 min (each about 20 to 130 s), `PsiCert.Small` 71 s,
`Check.Pi` about 50 s, and the soundness proofs (`PsiCert.Run`, `Check.Li` and the rest) under 20 s each.
Build the chunks one at a time on a shared machine (`lake build Schoenfeld.PsiCert.Chunks.C00`
and so on).

The vendored proof of Rosser's count (`Vendor/Rosser/`, six `lean_lib`s in `lakefile.toml`)
took about 3 CPU-hours from a cold `.lake` (10,700 s user CPU reported by `lake build`, 8.5 min
wall with `LEAN_NUM_THREADS=12` on a loaded 95-core machine). It is dominated by zeta-lab's
height-100 certificate: the 28 `RHHeight100` modules take about 2,800 s of elaboration in all
(the largest `Box*` modules up to 200 s each), `HardyTenZeros` about 600 s, `HardyFirstZero` about
250 s, and the Backlund half (`RSBounds/`, `TernaryGoldbach/`) about 330 s.

The chunk states in `Schoenfeld/PsiCert/Data.lean` were produced by running
`runSegs basePrimes 477` from `init` twenty times with the compiled code. They are data, and
each transition is re-checked when its chunk module builds.

## Unconditional version

`Unconditional/SchoenfeldUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the RH hypothesis with its `riemannHypothesis` (Alpöge's
proof). Every bound is then proved unconditionally in Lean, Schoenfeld's `1/(8π)` bounds
included: `schoenfeld_statement` has no hypothesis.

| Theorem | Statement | Axioms |
|---|---|---|
| `schoenfeld_statement` | `Schoenfeld.SchoenfeldStatement` | standard three + 24 `native_decide` |
| `schoenfeld_psi` | `Schoenfeld.SchoenfeldPsi` | standard three + 22 `native_decide` |
| `schoenfeld_theta` | `Schoenfeld.SchoenfeldTheta` | standard three + 22 `native_decide` |
| `schoenfeld_pi` | `Schoenfeld.SchoenfeldPi` | standard three + 23 `native_decide` |
| `psi_bound` | `Schoenfeld.PsiBound (1 / 8) 73.2` | standard three |
| `theta_bound` | `Schoenfeld.ThetaBound (1 / 4) 599` | standard three |
| `pi_bound` | `Schoenfeld.PiBound (9 / 20) 2657` | standard three |
| `schoenfeld_statement_of_rosser` | `RosserZeroCount → SchoenfeldStatement` | standard three + 24 `native_decide` |
| `schoenfeld_statement_of_cited` | `RosserZeroCount → PsiCert → SchoenfeldStatement` | standard three + 3 `native_decide` |
| `schoenfeld_statement_of_inputs` | the five inputs `→ SchoenfeldStatement` | standard three |

(and the parts `schoenfeld_*_of_rosser`, `schoenfeld_*_of_cited`, `schoenfeld_*_of_inputs`).
So Schoenfeld's Theorem 10 and Corollary 1, with his constant `1/(8π)` and his thresholds, are
proved unconditionally in Lean. Checked 2026-11-24 with `scripts/check-unconditional.sh` against
riemann-hypothesis `507a75d91d`: the build succeeded, no `sorryAx` appeared, and
`#print axioms` printed

```
'psi_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'theta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'pi_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_psi_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_theta_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_pi_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_statement_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'schoenfeld_psi_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1]
'schoenfeld_theta_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1]
'schoenfeld_pi_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1]
'schoenfeld_statement_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1]
'schoenfeld_psi_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'schoenfeld_theta_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'schoenfeld_pi_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'schoenfeld_statement_of_rosser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'schoenfeld_psi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'schoenfeld_theta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'schoenfeld_pi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'schoenfeld_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psi._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
```

The run took 11.2 min wall (130 s user CPU) on a loaded machine, dominated by importing
riemann-hypothesis.

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
  [senamakel/robin-rh](../robin-rh/) (`Robin/Defs.lean`,
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
  [senamakel/erdos-985](../erdos-985/) (lake dependency).
* `Schoenfeld/Inputs.lean`: the definition `positiveZeroCount` and the statement of
  `RosserZeroCount` are copied verbatim from [teorth/IEANTN](https://github.com/teorth/IEANTN)
  (`Solutions/Schoenfeld1976Numerics.v1/Proof/RSBounds/RosserCountDefinition.lean`,
  `Rosser1941.lean`, commit `cd9c2dd`), Apache License 2.0. The statement of `PsiCert` is copied
  verbatim from [Garald1/RSBounds](https://github.com/Garald1/RSBounds)
  (`RSBounds/Schoenfeld1976TargetsExtra.lean`, commit `82d7a55`), Apache License 2.0. See
  [`NOTICE`](NOTICE).
* `Vendor/Rosser/` (216 files): the proof of Rosser's zero count, vendored with its import closure.
  Every file starts with a comment naming its source repository, commit and path, and keeps its
  author and licence header.
  * `Vendor/Rosser/RSBounds/` (82 files): [Garald1/RSBounds](https://github.com/Garald1/RSBounds)
    at `82d7a55f02e52cd071cd8ed800cc889a23ad3e61`, Apache License 2.0 (eleven files MIT, as their
    headers say); RSBounds itself adapts code from teorth/IEANTN, gersh/ternary-goldbach-lean,
    calr3/ternary-goldbach and Mathlib, as its `THIRD_PARTY_NOTICES.md` records.
  * `Vendor/Rosser/TernaryGoldbach/` (35 files):
    [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach) at
    `192ca57362fa3ee737cd83205cb9ea99526c4553`, Apache License 2.0, © 2026 Charlie Reams (with
    material from PrimeNumberTheoremAnd, Apache License 2.0).
  * `Vendor/Rosser/{Zeta23,ZetaLean,RHHeight,RHHeight100,HardyFirstZero,HardyTenZeros}/`
    (99 files): RSBounds' `vendor/rh100/`, the closure of `RHHeight100.Main100` from
    [teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab) at
    `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534` with RSBounds' documented adaptations; MIT, ©
    2026 Thomas Lince, with the Zeta23 files under Apache License 2.0.

  The licence texts and notices are in `Vendor/Rosser/licenses/`. 28 files were edited to compile
  at this Lean and Mathlib pin (proof repairs only, no statement changed); every edit is listed
  in [`Vendor/Rosser/PORTING.md`](Vendor/Rosser/PORTING.md).
