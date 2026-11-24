# Speiser's theorem under RH in Lean

**Literature status: RH-equivalent.** Speiser (*Geometrisches zur Riemannschen Zetafunktion*,
Math. Ann. **110** (1934), 514–521) proved that the Riemann hypothesis is equivalent to
`ζ'(s) ≠ 0` for `0 < Re s < 1/2`. Levinson and Montgomery (*Zeros of the derivatives of the
Riemann zeta-function*, Acta Math. **133** (1974), 49–65, Theorem 1 and its corollary) gave an
analytic proof and a quantitative form. The direction RH ⇒ `ζ'` zero-free was rediscovered by
Spira (1965). Because the statement is equivalent to RH, an unconditional version says nothing
beyond the RH claim. Unconditionally, Levinson–Montgomery show that `ζ` and `ζ'` have the same
number of zeros in `0 < Re s < 1/2` up to height `T`, up to `O(log T)`. Nothing here is new
mathematics.

The main library is a Lean proof that RH implies `ζ'(s) ≠ 0` throughout `0 < Re s < 1/2`,
following Levinson–Montgomery's real-part argument for large `|Im s|`. The strip is covered in
three pieces:

* `|Im s| ≥ 7`: the real-part argument, under RH;
* `|Im s| < 5/2`: a size argument on the same Hadamard sum, under RH, real segment included;
* `5/2 ≤ |Im s| < 7`: a verified computation with Euler–Maclaurin and disc arithmetic, which needs
  no hypothesis.

```lean
theorem Speiser.speiser_of_RH (hRH : RiemannHypothesis) : Speiser.SpeiserStatement

theorem Speiser.Band.speiserBand : Speiser.SpeiserBand (5 / 2) 7

theorem Speiser.speiserAbove_of_RH (hRH : RiemannHypothesis) : Speiser.SpeiserAbove 7

theorem Speiser.speiserBelow_of_RH (hRH : RiemannHypothesis) : Speiser.SpeiserBelow (5 / 2)
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
| `speiser_of_RH` | C | `RiemannHypothesis` |
| `speiserAbove_of_RH`, `speiserBelow_of_RH` | C | `RiemannHypothesis` |
| `Band.speiserBand` | D | none (verified computation) |
| `speiser` (`Unconditional/`) | U | none |
| `speiser_above`, `speiser_below` (`Unconditional/`) | U | none |

`speiser_of_RH_of_band` and `speiser_of_RH_of_below` (the previous milestones, which take the
missing region as a hypothesis) are kept; `speiser_of_RH` supersedes them.

`RiemannHypothesis` is Mathlib's. formal-conjectures has no statement of Speiser's theorem
(searched 2026-11-24 for "Speiser" and `deriv riemannZeta`), so the targets are this repo's own.

## Axioms

From `lake env lean scripts/Axioms.lean`:

```
'Speiser.speiserAbove_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.speiser_of_RH_of_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.re_logDeriv_xiZeta_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.re_archimedean_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.speiserBelow_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.speiser_of_RH_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'Speiser.Band.speiserBand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Speiser.Band.coverOK_lower._native.native_decide.ax_1_1,
 Speiser.Band.coverOK_upper._native.native_decide.ax_1_1]
'Speiser.speiser_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Speiser.Band.coverOK_lower._native.native_decide.ax_1_1,
 Speiser.Band.coverOK_upper._native.native_decide.ax_1_1]
```

There are 2 `native_decide` calls, `coverOK_upper` and `coverOK_lower` (`Speiser/Band/Run.lean`).
Each runs the checker `SpeiserCompute.coverOK` on one half of the band: the box
`[0, 1/2] × [5/2, 7]` or its mirror image. The checker bisects the box, at most 40 levels, until
every piece passes `cellOK` (71,223 pieces per half). Together they take 186 s of CPU. The
checker is proved sound in `Speiser/Band/Check.lean` and `Speiser/Band/Main.lean`
(`deriv_ne_zero_of_cellOK`, `deriv_ne_zero_of_coverOK`). Nothing else uses `native_decide`, and
there is no `sorry` or `axiom` anywhere.

## Proof outline

Write `ξ(s) = s(s-1)Λ(s)` (erdos-985's `xiZeta`). Under RH, `ζ(s) ≠ 0` in the strip, so a zero
of `ζ'` would give `ξ'/ξ(s) = E(s) := 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2)`
(`Speiser/Xi.lean`, `logDeriv_xiZeta_of_deriv_eq_zero`).

1. `Speiser/Xi.lean`, `hasSum_re_logDeriv_xiZeta`: Hadamard (erdos-985 `hadamard_logDeriv`)
   gives `ξ'/ξ(z) = b + Σ_ρ m_ρ (1/(z-ρ) + 1/ρ)`. At `z = 0` the sum vanishes, so `b = ξ'(0)`.
   The functional equation gives `ξ'(1) = -ξ'(0)`. Under RH, `1 - ρ = conj ρ`, so
   `Re ξ'/ξ(z) = Σ_ρ m_ρ (Re z - 1/2)/|z-ρ|²`.
2. **`|t| ≥ 7`** (`Speiser/Gamma.lean`, `re_archimedean_pos`). `Re E(s) > 0.014`, from 20 terms of
   `ψ(w) - ψ(1) = Σ_k (1/(k+1) - 1/(k+w))`, each bounded by the exact maximum of
   `u/(u² + 49/4)` on `[n, n+1/4]`, together with `γ < 0.5851` (`H₆₄ - 6 log 2`),
   `log π < 1.1455` and `Re 1/(s-1) ≥ -1/50`. Step 1 gives `Re ξ'/ξ(s) ≤ 0`, a contradiction.
3. **`|t| < 5/2`** (`Speiser/Low.lean`). `ξ'(1) = Λ₀(1) = 1 + (γ - log 4π)/2 < 0.0295`. Step 1 at
   `z = 1` gives `Σ_ρ m_ρ (1/2)/(1/4 + γ_ρ²) < 0.0295`, so every zero has `γ_ρ² ≥ 16`. For
   `|t| ≤ 5/2` this gives `Re ξ'/ξ(s) ≥ -(65/9)·0.0295 > -0.214`, while `Re E(s) < -0.38`
   (ten series terms, each at most the exact minimum of `u/(u² + 25/16)`, plus a
   `(15/8)(π²/6 - Σ_{n≤10} 1/n²)` tail).
4. **`5/2 ≤ |t| < 7`** (`Speiser/Band/`, no RH):
   - `EulerMaclaurin.lean`: for `f(x) = x^{-s}`, one fundamental-theorem-of-calculus step with
     the positive kernel `K(u) = u²(1-u)²/24` gives
     `r_n(s) := (f(n)+f(n+1))/2 - ∫_n^{n+1} f - (f'(n+1)-f'(n))/12 = -∫₀¹ K f''''(n+u) du`, so
     `|r_n| ≤ |s(s+1)(s+2)(s+3)| n^{-σ-4}/384`.
   - `Zeta.lean`: `ζ(s) = Σ_{n<9} n^{-s} + 9^{-s}/2 + 9^{1-s}/(s-1) + s 9^{-s-1}/12 + Σ_{n≥9} r_n(s)`,
     first for `Re s > 1` by telescoping. The identity theorem then carries it to the boxes
     `{-1 < σ < 2, 1 < ±t < 10}`.
   - `Deriv.lean`: hence `ζ' = M1 + T'` with `M1` explicit and `M1' = M2` explicit. Cauchy's
     estimate gives `‖T'(s)‖ ≤ P(‖s‖+ρ)/(147456ρ)`, where `P(a) = a(a+1)(a+2)(a+3)` and
     `ρ = 2/5`.
   - `SpeiserCompute/Core.lean` (Lean core only, `precompileModules`): fixed-point disc
     arithmetic at `2^-64`. `exp` is computed by Taylor series (16 terms) and six squarings,
     `log 2, 3, 5, 7` are enclosed to `5·10⁻¹²`, and a cell `D(c, r)` is accepted when
     `|M1(c)| > rad + r·sup|M2| + sup|T'|`.
   - `Sound.lean`, `Logs.lean`, `Check.lean`: every disc operation maps members to members, and
     an accepted cell contains no zero of `ζ'`. The proofs use the mean value inequality for
     `M1` and the Cauchy bound for `T'`.

Design and sizing of the computation, and the options rejected: [`docs/BAND.md`](docs/BAND.md).

## Deviations from the literature

None in the statement: `SpeiserStatement` is proved in full under RH. The route differs from
Levinson–Montgomery's in the bounded region. They use known numerical facts about the low zeros
(`β = 1/2` for `|γ| < 1000`, explicit `N(T)`). Here the low zeros are never located: below
`|t| = 5/2` a lower bound `γ² ≥ 16` on every zero, read off from `ξ'(1)`, is enough, and the band
`5/2 ≤ |t| < 7` is a direct certified computation of `ζ'`.

The thresholds come from the arguments:
- The real-part argument stops at `|t| ≈ 6.52`, where `Re E` first vanishes (at `σ = 0`). `7`
  comes from bounding each series term by its worst case over `σ`.
- The size argument would reach about `|t| ≈ 3` with the exact `ξ'(1)`.

## Layout

| File | Content |
|---|---|
| `Speiser/Statement.lean` | Fixed targets `SpeiserStatement`, `SpeiserAbove`, `SpeiserBelow`, `SpeiserBand` |
| `Speiser/Xi.lean` | `ξ(1-s) = ξ(s)`, zeros of `ξ` on the line under RH, `Re ξ'/ξ` as a sum over zeros, `ξ'/ξ` at a critical point of `ζ` |
| `Speiser/Gamma.lean` | The archimedean part is positive for `|t| ≥ 7` |
| `Speiser/Low.lean` | `ξ'(1)`, `γ² ≥ 16`, and the size argument for `|t| < 5/2` |
| `Speiser/Main.lean` | `speiserAbove_of_RH` and the combinations with hypotheses |
| `Speiser/Band/EulerMaclaurin.lean` | One Euler–Maclaurin step with a positive kernel, and its bound |
| `Speiser/Band/Zeta.lean` | Euler–Maclaurin for `ζ` on convex boxes, by the identity theorem |
| `Speiser/Band/Deriv.lean` | `ζ' = M1 + T'`, `M1' = M2`, the tail bound, Cauchy, mean value |
| `Speiser/Band/Sound.lean` | Soundness of the disc arithmetic and of `exp` |
| `Speiser/Band/Logs.lean` | `log 2, 3, 5, 7` to `5·10⁻¹²` |
| `Speiser/Band/Check.lean` | `M1(c)` and `sup ‖M2‖` enclosures; `deriv_ne_zero_of_cellOK` |
| `Speiser/Band/Run.lean` | The two `native_decide` runs |
| `Speiser/Band/Main.lean` | `deriv_ne_zero_of_coverOK`, `speiserBand` |
| `Speiser/Final.lean` | `speiser_of_RH` |
| `SpeiserCompute/Core.lean` | The executable checker (Lean core only) |
| `Unconditional/SpeiserUnconditional.lean` | One-line discharges with `riemannHypothesis` |
| `scripts/Axioms.lean` | `#print axioms` for the headline theorems |

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`, erdos-985 at `9538edb`.

```
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

`Speiser.Band.Run` (the two `native_decide` runs) takes about 186 s of CPU on one core. Every
other `Speiser` module builds in under 30 s. The erdos-985 modules imported (`Hadamard`,
`XiGrowth`, `Principal.Identity.Zeros`, `StepA.GammaFactor`, `Bounds.DigammaSeries`) took about
5 minutes wall on first build.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `speiser` | `Speiser.SpeiserStatement` | standard three + the 2 `native_decide` above |
| `speiser_above` | `Speiser.SpeiserAbove 7` | `propext`, `Classical.choice`, `Quot.sound` |
| `speiser_below` | `Speiser.SpeiserBelow (5 / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `speiser_of_band` | `Speiser.SpeiserBand (5 / 2) 7 → Speiser.SpeiserStatement` | `propext`, `Classical.choice`, `Quot.sound` |
| `speiser_of_below` | `Speiser.SpeiserBelow 7 → Speiser.SpeiserStatement` | `propext`, `Classical.choice`, `Quot.sound` |

Checked against riemann-hypothesis `507a75d91d` with

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

which needs about 93 GB of cache, about 19 GB of RAM and an open-file limit of about 900k
(`sudo prlimit --pid $$ --nofile=2000000:2000000`). Output on 2026-11-24:

```
'speiser' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Speiser.Band.coverOK_lower._native.native_decide.ax_1_1,
 Speiser.Band.coverOK_upper._native.native_decide.ax_1_1]
'speiser_above' depends on axioms: [propext, Classical.choice, Quot.sound]
'speiser_of_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'speiser_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'speiser_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`speiser` is `ζ'(s) ≠ 0` for `0 < Re s < 1/2`, given the Lean proof of RH in
leanprover-community/riemann-hypothesis, which has not been independently verified. Since
Speiser's statement is equivalent to RH, this says nothing beyond the RH claim.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

No vendored files. `mem_strip_of_xiZeta_eq_zero` in `Speiser/Xi.lean` follows the lemma of the
same name in senamakel/li-criterion-rh. The Hadamard factorisation, `xiZeta`, its growth bound,
the `Γℝ` derivative and the digamma series come from senamakel/erdos-985 (a lake dependency).
The pattern of a core-only compiled checker with a separate soundness proof follows
senamakel/robin-rh.
