# Speiser's theorem under RH in Lean, outside the band 5/2 ≤ |Im s| < 7

**Literature status: RH-equivalent.** Speiser (*Geometrisches zur Riemannschen Zetafunktion*,
Math. Ann. **110** (1934), 514–521) proved that the Riemann hypothesis is equivalent to
`ζ'(s) ≠ 0` for `0 < Re s < 1/2`. Levinson and Montgomery (*Zeros of the derivatives of the
Riemann zeta-function*, Acta Math. **133** (1974), 49–65, Theorem 1 and its corollary) gave an
analytic proof and a quantitative form; the direction RH ⇒ `ζ'` zero-free was rediscovered by
Spira (1965). Because the statement is equivalent to RH, an unconditional version says nothing
beyond the RH claim. Unconditionally, Levinson–Montgomery show that `ζ` and `ζ'` have the same
number of zeros in `0 < Re s < 1/2` up to height `T`, up to `O(log T)`. Nothing here is new
mathematics.

The main library is a Lean proof that RH implies `ζ'(s) ≠ 0` for `0 < Re s < 1/2` with
`|Im s| ≥ 7` (the real-part argument of Levinson–Montgomery §2) and with `|Im s| < 5/2` (a size
argument on the same Hadamard sum, real segment included). **The full target is not proved**:
the band `5/2 ≤ |Im s| < 7` enters as an explicit hypothesis. It needs a certified computation
of `ζ'`, designed and sized in [`docs/BAND.md`](docs/BAND.md) (see "Deviations from the
literature").

```lean
theorem Speiser.speiserAbove_of_RH (hRH : RiemannHypothesis) : Speiser.SpeiserAbove 7

theorem Speiser.speiserBelow_of_RH (hRH : RiemannHypothesis) : Speiser.SpeiserBelow (5 / 2)

theorem Speiser.speiser_of_RH_of_band (hRH : RiemannHypothesis)
    (hM : Speiser.SpeiserBand (5 / 2) 7) : Speiser.SpeiserStatement

theorem Speiser.speiser_of_RH_of_below (hRH : RiemannHypothesis) (hB : Speiser.SpeiserBelow 7) :
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

def SpeiserBand (a b : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → a ≤ |s.im| → |s.im| < b → deriv riemannZeta s ≠ 0
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `speiserAbove_of_RH` | C | `RiemannHypothesis` |
| `speiserBelow_of_RH` | C | `RiemannHypothesis` |
| `speiser_of_RH_of_band` | C + H | `RiemannHypothesis`, `SpeiserBand (5/2) 7` |
| `speiser_of_RH_of_below` | C + H | `RiemannHypothesis`, `SpeiserBelow 7` (superseded by the band form) |
| `speiser_above`, `speiser_below` (`Unconditional/`) | U | none |
| `speiser_of_band` (`Unconditional/`) | U + H | `SpeiserBand (5/2) 7` |
| `speiser_of_below` (`Unconditional/`) | U + H | `SpeiserBelow 7` |

`RiemannHypothesis` is Mathlib's. formal-conjectures has no statement of Speiser's theorem
(searched 2026-11-24 for "Speiser" and `deriv riemannZeta`), so `SpeiserStatement` and its two
halves are this repo's own. `SpeiserBand (5/2) 7` is the target restricted to the bounded band
`0 < σ < 1/2`, `5/2 ≤ |t| < 7`; the literature settles the low region with numerical information on the low
zeros of `ζ` (Levinson–Montgomery use that `β = 1/2` for `|γ| < 1000` and explicit `N(T)`
bounds).

## Axioms

From `lake env lean scripts/Axioms.lean`:

```
'Speiser.speiserAbove_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.speiser_of_RH_of_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.re_logDeriv_xiZeta_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.re_archimedean_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.speiserBelow_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.speiser_of_RH_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standard three only: no `native_decide`, no `sorry`, no `axiom`.

## Proof outline

Suppose `ζ'(s) = 0` with `0 < σ < 1/2`, `|t| ≥ 7`. Under RH `ζ(s) ≠ 0`, so `ξ(s) ≠ 0`, where
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
   `≥ cTerm k = 1/n - max_{u ∈ [n, n+1/4]} u/(u² + 49/4)`; the first 20 sum to more than
   `1.799`. With `γ < 0.5851` (`H₆₄ - 6 log 2`), `log π < 1.1455` and `Re 1/(s-1) ≥ -1/50`,
   the real part is `> 0.014`.
4. `Speiser/Main.lean`: steps 2 and 3 contradict each other, so `SpeiserAbove 7`.

Below height `5/2` (`Speiser/Low.lean`, `speiserBelow_of_RH`):

5. `ξ'(1) = Λ₀(1) = 1 + (γ - log 4π)/2 < 0.0295` (`γ < 0.5851`, `log π > 1.14`). Step 2 at
   `z = 1` reads `Re ξ'/ξ(1) = Σ_ρ m_ρ (1/2)/(1/4 + γ_ρ²)`, so a single term gives `γ_ρ² ≥ 16`
   for every zero (`im_sq_ge_of_RH`).
6. For `|t| ≤ 5/2`, `|γ| ≥ 4` and `a = 1/2 - σ ∈ [0, 1/2]`:
   `a/(a² + (t-γ)²) ≤ (65/9)(1/2)/(1/4 + γ²)`, since `(65/9)(|γ| - 5/2)² ≥ 1/4 + γ²` for
   `|γ| ≥ 4`. Summing, `Re ξ'/ξ(s) ≥ -(65/9) Re ξ'/ξ(1) > -0.214`.
7. The archimedean side is `< -0.38`: `Re 1/(s-1) ≤ -1/13`, and each series term is at most
   `dTerm k` (the exact minimum of `u/(u² + 25/16)` on `[n, n+1/4]`), and at most `(15/8)/n²`
   for `n ≥ 2`. Ten terms plus `(15/8)(π²/6 - Σ_{n≤10} 1/n²)` give `< 1.105`, with `γ > 0.57688`
   and `log π > 1.14`. This contradicts step 6.

## Deviations from the literature

The fixed target `SpeiserStatement` is **not proved**: the band `5/2 ≤ |Im s| < 7` is the
hypothesis `SpeiserBand (5/2) 7`.

- **Above 7.** The archimedean part `H(s) = 1/(s-1) - (1/2)log π + (1/2)ψ(1+s/2)` has
  `Re H < 0` somewhere in the strip for every `|t| < 6.52` (at `σ = 0`), so the sign argument
  stops there. The threshold `7` rather than `6.52` comes from bounding each series term by its
  worst case over `σ ∈ [0, 1/2]` and from the truncation. With 40 terms `6.8` would go through
  (margin `0.004`); `6.6` fails even with 200 terms.
- **Below 5/2.** The size argument needs `−Re H(s)` to beat `(65/9)·0.0295`. With the exact
  `ξ'(1) = 0.0231` and the zero bound `γ₁ ≥ 4.6` that it gives, the same argument would reach
  `|t| ≈ 3`; it cannot reach the band, because `Re H → 0` as `|t| → 6.5` while the zero-sum
  bound grows as `|t|` approaches the (unproved) first zero.
- **The band.** There `H(s)` and `ξ'/ξ(s)` both lie in the upper-left quadrant, and neither a sign
  nor a cone argument separates them (a two-sided cone test would need `γ₁ > 200`). A size bound
  needs the low zeros themselves (even `γ₁ ≥ 14` and `Σ 1/γ² = 0.046` give `|ξ'/ξ(s)| ≤ 0.86`
  against `|H(s)| ≈ 0.5`). Levinson–Montgomery also use computation here. The band is done by a
  certified evaluation of `ζ'`; see [`docs/BAND.md`](docs/BAND.md) for the design and sizing.

## Layout

| File | Content |
|---|---|
| `Speiser/Statement.lean` | Fixed targets `SpeiserStatement`, `SpeiserAbove`, `SpeiserBelow`, `SpeiserBand` |
| `Speiser/Xi.lean` | `ξ(1-s) = ξ(s)`, zeros of `ξ` on the line under RH, `Re ξ'/ξ ≤ 0`, `ξ'/ξ` at a critical point of `ζ` |
| `Speiser/Gamma.lean` | `Re` of the archimedean part `> 0` for `0 < σ ≤ 1/2`, `|t| ≥ 7` |
| `Speiser/Low.lean` | `ξ'(1)`, `γ² ≥ 16` for every zero, the size argument: `speiserBelow_of_RH` |
| `Speiser/Main.lean` | `speiserAbove_of_RH`, `speiser_of_RH_of_band`, `speiser_of_RH_of_below` |
| `Unconditional/SpeiserUnconditional.lean` | One-line discharges with `riemannHypothesis` |
| `scripts/Axioms.lean` | `#print axioms` for the headline theorems |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 at `9538edb`.

```
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

The five `Speiser` modules take under 20 s each. The erdos-985 modules they import
(`Hadamard`, `XiGrowth`, `Principal.Identity.Zeros`, `StepA.GammaFactor`,
`Bounds.DigammaSeries`) took about 5 minutes wall on first build.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `speiser_above` | `Speiser.SpeiserAbove 7` | `propext`, `Classical.choice`, `Quot.sound` |
| `speiser_of_below` | `Speiser.SpeiserBelow 7 → Speiser.SpeiserStatement` | `propext`, `Classical.choice`, `Quot.sound` |
| `speiser_below` | `Speiser.SpeiserBelow (5 / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `speiser_of_band` | `Speiser.SpeiserBand (5 / 2) 7 → Speiser.SpeiserStatement` | `propext`, `Classical.choice`, `Quot.sound` |

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
'speiser_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'speiser_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`speiser_above` and `speiser_below` are `ζ'(s) ≠ 0` for `0 < Re s < 1/2` with `|Im s| ≥ 7`, respectively `|Im s| < 5/2`, given the Lean proof of RH
in leanprover-community/riemann-hypothesis, which has not been independently verified. Since
Speiser's statement is equivalent to RH, this says nothing beyond the RH claim.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

No vendored files. `mem_strip_of_xiZeta_eq_zero` in `Speiser/Xi.lean` follows the lemma of the
same name in senamakel/li-criterion-rh. The Hadamard factorisation, `xiZeta`, its growth bound,
the `Γℝ` derivative and the digamma series come from senamakel/erdos-985 (a lake dependency).
