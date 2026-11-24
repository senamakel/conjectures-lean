# Speiser's theorem above height 8 under RH in Lean

**Literature status: RH-equivalent.** Speiser (*Geometrisches zur Riemannschen Zetafunktion*,
Math. Ann. **110** (1934), 514–521) proved that the Riemann hypothesis is equivalent to
`ζ'(s) ≠ 0` for `0 < Re s < 1/2`. Levinson and Montgomery (*Zeros of the derivatives of the
Riemann zeta-function*, Acta Math. **133** (1974), 49–65, Theorem 1 and its corollary) gave an
analytic proof and a quantitative form; the direction RH ⇒ `ζ'` zero-free was rediscovered by
Spira (1965). Because the statement is equivalent to RH, an unconditional version says nothing
beyond the RH claim. Unconditionally, Levinson–Montgomery show that `ζ` and `ζ'` have the same
number of zeros in `0 < Re s < 1/2` up to height `T`, up to `O(log T)`. Nothing here is new
mathematics.

The main library is a Lean proof that RH implies `ζ'(s) ≠ 0` for `0 < Re s < 1/2` and
`|Im s| ≥ 8`, following the Re ζ'/ζ argument of Levinson–Montgomery §2. **The full target (every
height) is not proved**: the band `|Im s| < 8` enters as an explicit hypothesis (see
"Deviations from the literature").

```lean
theorem Speiser.speiserAbove_of_RH (hRH : RiemannHypothesis) : Speiser.SpeiserAbove 8

theorem Speiser.speiser_of_RH_of_below (hRH : RiemannHypothesis) (hB : Speiser.SpeiserBelow 8) :
    Speiser.SpeiserStatement
```

The targets, fixed in `Speiser/Statement.lean`:

```lean
def SpeiserStatement : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → deriv riemannZeta s ≠ 0

def SpeiserAbove (T₀ : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → T₀ ≤ |s.im| → deriv riemannZeta s ≠ 0

def SpeiserBelow (T₀ : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → |s.im| < T₀ → deriv riemannZeta s ≠ 0
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `speiserAbove_of_RH` | C | `RiemannHypothesis` |
| `speiser_of_RH_of_below` | C + H | `RiemannHypothesis`, `SpeiserBelow 8` |
| `speiser_above` (`Unconditional/`) | U | none |
| `speiser_of_below` (`Unconditional/`) | U + H | `SpeiserBelow 8` |

`RiemannHypothesis` is Mathlib's. formal-conjectures has no statement of Speiser's theorem
(searched 2026-11-24 for "Speiser" and `deriv riemannZeta`), so `SpeiserStatement` and its two
halves are this repo's own. `SpeiserBelow 8` is the target restricted to the bounded box
`0 < σ < 1/2`, `|t| < 8`; the literature settles that box with numerical information on the low
zeros of `ζ` (Levinson–Montgomery use that `β = 1/2` for `|γ| < 1000` and explicit `N(T)`
bounds).

## Axioms

From `lake env lean scripts/Axioms.lean`:

```
'Speiser.speiserAbove_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.speiser_of_RH_of_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.re_logDeriv_xiZeta_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.re_archimedean_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standard three only: no `native_decide`, no `sorry`, no `axiom`.

## Proof outline

Suppose `ζ'(s) = 0` with `0 < σ < 1/2`, `|t| ≥ 8`. Under RH `ζ(s) ≠ 0`, so `ξ(s) ≠ 0`, where
`ξ(s) = s(s-1)Λ(s)` is erdos-985's `xiZeta`.

1. `Speiser/Xi.lean`, `logDeriv_xiZeta_of_deriv_eq_zero`: near `s`,
   `ξ = s(s-1) Γℝ(s) ζ(s)`, and `ζ'(s) = 0` gives
   `ξ'/ξ(s) = 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2)`.
2. `Speiser/Xi.lean`, `re_logDeriv_xiZeta_nonpos`: Hadamard (erdos-985 `hadamard_logDeriv`)
   gives `ξ'/ξ(z) = b + Σ_ρ m_ρ (1/(z-ρ) + 1/ρ)`. At `z = 0` the sum vanishes, so `b = ξ'(0)`;
   `ξ(1-s) = ξ(s)` gives `ξ'(1) = -ξ'(0)`, hence `-2b = Σ_ρ m_ρ (1/(1-ρ) + 1/ρ)`. Under RH,
   `1 - ρ = conj ρ`, so `Re ξ'/ξ(z) = Σ_ρ m_ρ (Re z - 1/2)/|z-ρ|² ≤ 0` for `Re z ≤ 1/2`.
3. `Speiser/Gamma.lean`, `re_archimedean_pos`: with `ψ(s/2) = ψ(1+s/2) - 2/s` the right side of
   step 1 is `1/(s-1) - (1/2) log π + (1/2) ψ(1+s/2)`. The series
   `ψ(w) - ψ(1) = Σ_k (1/(k+1) - 1/(k+w))` (erdos-985) has terms of real part `≥ 0` and
   `≥ 1/n - (n + 1/4)/(n² + 16)`; the first 20 sum to more than `1.87`. With `γ < 2/3`,
   `log π < 1.163` and `Re 1/(s-1) ≥ -1/64`, the real part is `> 0.005`.
4. `Speiser/Main.lean`: steps 2 and 3 contradict each other.

## Deviations from the literature

The fixed target `SpeiserStatement` is **not proved**: only `|Im s| ≥ 8` is. The real-part
argument cannot reach lower: the archimedean part `H(s) = 1/(s-1) - (1/2)log π + (1/2)ψ(1+s/2)`
has `Re H < 0` somewhere in the strip for every `|t| < 6.52` (at `σ = 0`), and on the real
segment `Re ζ'/ζ > 0`. Below that height the proof needs the positions of actual zeros of `ζ`:

- For `|t| ≲ 1.5`, `Im H < 0` while (if every zero has `γ² > t² + 1/4`) `Im ξ'/ξ(s) > 0`; this
  needs a lower bound for the first zero ordinate, which erdos-985's Hadamard sum gives
  (`γ₁ ≳ 4.4` from `Re ξ'/ξ(2)` and `ζ'/ζ(2) ≤ -log 2/4`), plus the real segment by a size bound.
  Not formalised.
- For `1.5 ≲ |t| < 6.52`, `H(s)` and `ξ'/ξ(s)` both lie in the upper-left quadrant, and neither
  a sign nor a cone argument separates them (a two-sided cone test would need `γ₁ > 200`). A
  size bound on `|ξ'/ξ(s)|` needs the low zeros themselves: even knowing `γ₁ ≥ 14` and
  `Σ 1/γ² = 0.046`, the crude bound gives `|ξ'/ξ(s)| ≤ 0.86` against `|H(s)| ≈ 0.5`. This is
  a rigorous numerical computation of `ζ` near the critical line, which Levinson–Montgomery
  also use.
- The threshold `8` rather than `6.52` comes from the crude bounds in step 3 (`Re 1/(s-1) ≥ -1/t²`,
  the `+1/4` in each term, `γ < 2/3`).

## Layout

| File | Content |
|---|---|
| `Speiser/Statement.lean` | Fixed targets `SpeiserStatement`, `SpeiserAbove`, `SpeiserBelow` |
| `Speiser/Xi.lean` | `ξ(1-s) = ξ(s)`, zeros of `ξ` on the line under RH, `Re ξ'/ξ ≤ 0`, `ξ'/ξ` at a critical point of `ζ` |
| `Speiser/Gamma.lean` | `Re` of the archimedean part `> 0` for `0 < σ ≤ 1/2`, `|t| ≥ 8` |
| `Speiser/Main.lean` | `speiserAbove_of_RH`, `speiser_of_RH_of_below` |
| `Unconditional/SpeiserUnconditional.lean` | One-line discharges with `riemannHypothesis` |
| `scripts/Axioms.lean` | `#print axioms` for the headline theorems |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 at `9538edb`.

```
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

The four `Speiser` modules take about 15 s each. The erdos-985 modules they import
(`Hadamard`, `XiGrowth`, `Principal.Identity.Zeros`, `StepA.GammaFactor`,
`Bounds.DigammaSeries`) took about 5 minutes wall on first build.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `speiser_above` | `Speiser.SpeiserAbove 8` | `propext`, `Classical.choice`, `Quot.sound` |
| `speiser_of_below` | `Speiser.SpeiserBelow 8 → Speiser.SpeiserStatement` | `propext`, `Classical.choice`, `Quot.sound` |

Checked against riemann-hypothesis `507a75d91d` with

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

which needs about 93 GB of cache, about 19 GB of RAM and an open-file limit of about 900k
(`sudo prlimit --pid $$ --nofile=2000000:2000000`). Output on 2026-11-24 (37 min wall on a
loaded box, mostly restoring the riemann-hypothesis cache):

```
'speiser_above' depends on axioms: [propext, Classical.choice, Quot.sound]
'speiser_of_below' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`speiser_above` is `ζ'(s) ≠ 0` for `0 < Re s < 1/2`, `|Im s| ≥ 8`, given the Lean proof of RH
in leanprover-community/riemann-hypothesis, which has not been independently verified; since
Speiser's statement is equivalent to RH, this says nothing beyond the RH claim.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

No vendored files. `mem_strip_of_xiZeta_eq_zero` in `Speiser/Xi.lean` follows the lemma of the
same name in senamakel/li-criterion-rh. The Hadamard factorisation, `xiZeta`, its growth bound,
the `Γℝ` derivative and the digamma series come from senamakel/erdos-985 (a lake dependency).
