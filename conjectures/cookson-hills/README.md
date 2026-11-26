# The Cookson Hills series converges, from μ(π) = 2, in Lean

This package proves that the Cookson Hills series

  `Σ_{n ≥ 1} sec² n / n³ = Σ_{n ≥ 1} 1 / (n³ cos² n)`  (angles in radians)

converges, in the form that
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) states as
`FlintCooksonHills.cookson_hills_series_converges` (there `@[category research open]`, with
`sorry`). `FlintCooksonHills.cookson_hills_series_converges` here is a complete Lean proof from the
standard three axioms; it also gives the Flint Hills series `Σ 1/(n³ sin² n)` in the
formal-conjectures form.

The premise is that the irrationality exponent of `π` is 2, proved by OpenAI in *The
irrationality exponent of π is 2* (September 24, 2026, `preprints/` of
[openai/math](https://github.com/openai/math)) and formalised in Lean in the same repository as
`OAI.PiExponent.pi_eventual_lower_bound`. Their paper derives the Flint Hills series from it
(Corollary 1.2), following Alekseyev's criterion (*On convergence of the Flint Hills series*,
arXiv:1104.5100, 2011). Label: **consequence of μ(π) = 2 (OpenAI 2026)**. The OpenAI paper does
not mention the Cookson Hills series. The step from Flint Hills to Cookson Hills used here is
`sin 2n = 2 sin n cos n`; we did not find it written down in a source we read, and it is
elementary, so we claim no novelty for it.

## Main theorems

```lean
-- CooksonHills/Main.lean
theorem FlintCooksonHills.cookson_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.cos (n + 1)^2)))

theorem FlintCooksonHills.flint_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.sin (n + 1)^2)))

-- CooksonHills/OfPiExponent.lean
theorem FlintCooksonHills.cookson_hills_of_piEventualLowerBound
    (h : OAI.PiExponent.PiEventualLowerBound) : CooksonHillsStatement

-- CooksonHills/OfFlint.lean
theorem FlintCooksonHills.cookson_hills_of_flint_hills
    (h : FlintHillsStatement) : CooksonHillsStatement
```

with, from `Vendor/OAI/NumberTheory/PiExponent/Statement.lean`:

```lean
def EventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

def PiEventualLowerBound : Prop := EventualLowerBound Real.pi
```

## Tier and provenance

Tiers are those of the conjectures-lean workspace (`AGENTS.md`).

| Theorem | Tier | Hypotheses |
|---|---|---|
| `cookson_hills_of_flint_hills` | C | the Flint Hills statement |
| `cookson_hills_of_piEventualLowerBound` | C | `PiEventualLowerBound` (μ(π) = 2) |
| `cookson_hills_series_converges` | D | none |
| `flint_hills_series_converges` | D | none |

- `FlintHillsStatement` and `CooksonHillsStatement` in `CooksonHills/Statement.lean` are the
  statements of `FlintCooksonHills.flint_hills_series_converges` and
  `FlintCooksonHills.cookson_hills_series_converges` in
  `FormalConjectures/Wikipedia/FlintCooksonHills.lean`, commit `9097e2f`, copied word for word.
  The two headline theorems restate those types in full rather than through the definitions.
- `PiEventualLowerBound` is OpenAI's definition, vendored unchanged.
- Tier D: no riemann-hypothesis import and no hypothesis. The proof of `μ(π) = 2` is OpenAI's
  Lean code, vendored under `Vendor/` (869 files) and built here on this workspace's pin.

## Axioms

AXIOMS_PLACEHOLDER

## Proof outline

1. **μ(π) = 2** (`Vendor/OAI/NumberTheory/PiExponent/Main.lean`,
   `OAI.PiExponent.pi_eventual_lower_bound`): for every `ν > 2`, `|π − p/q| ≥ q^(−ν)` for all
   large `q`. This is OpenAI's proof, unchanged in substance (see "Porting" below).
2. **Flint Hills** (`Vendor/.../Analysis/FlintConsequence.lean`, OpenAI): with `ν = 9/4`,
   `‖qπ‖ ≥ c q^(−5/4)`; each `n ≥ 2` is assigned `q = round(n/π)`, at most four `n` share a `q`,
   `|sin n| ≥ (2/π)‖qπ‖` and `q ≤ n`, so `Σ 1/(n³ sin² n) ≤ 16 Σ_q 1/(q³ ‖qπ‖²)`, which
   converges by a dyadic spacing count (`DyadicSpacing.lean`).
3. **Cookson Hills from Flint Hills** (`CooksonHills/OfFlint.lean`): `sin² 2x = 4 sin² x cos² x
   ≤ 4 cos² x`, so `1/(x³ cos² x) ≤ 32 / ((2x)³ sin² 2x)` whenever `sin 2x ≠ 0` (true at every
   positive integer, as `π` is irrational; if `cos x = 0` the Lean term is `0`). The `n`-th
   Cookson Hills term is therefore at most 32 times the Flint Hills term at index `2n + 1`
   (0-indexed), and a subseries of a convergent series of nonnegative terms converges.
4. **Headline** (`CooksonHills/Main.lean`): steps 2 and 3 applied to step 1.

## Layout

| File | Content |
|---|---|
| `CooksonHills/Statement.lean` | The two formal-conjectures statements. Fixed |
| `CooksonHills/OfFlint.lean` | Flint Hills implies Cookson Hills (Mathlib only) |
| `CooksonHills/OfPiExponent.lean` | Both series from `PiEventualLowerBound` (imports 8 vendored modules) |
| `CooksonHills/Main.lean` | The headline theorems |
| `Vendor/OAI/NumberTheory/PiExponent/` | OpenAI's μ(π) = 2 proof, 869 files, ported to this pin |
| `Vendor/LICENSE`, `NOTICE` | Apache-2.0 licence and attribution |

## Deviations from the literature

None in the statements. Our proof of the Flint Hills half is OpenAI's.

## Porting

OpenAI's tree targets Lean `v4.34.1` and Mathlib `d13f23b7`; this package is on Lean `v4.36.0`
and Mathlib `fc4f59e5` (1486 Mathlib commits later). The vendored files are unchanged except for
the edits that port forced, each marked with a comment where it is more than a token:

PORTING_PLACEHOLDER

## Building

```
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5`, with the workspace's shared `.lake/packages`.
BUILD_PLACEHOLDER

## This result stays tier D

There is no unconditional version to add: the headline imports nothing from riemann-hypothesis
and has no hypothesis.

## Credits

- `Vendor/OAI/NumberTheory/PiExponent/` is from [openai/math](https://github.com/openai/math),
  `lean/OAI/NumberTheory/PiExponent/`, commit `3344da59991ed94f9ba711217b29c1d760badfa6`,
  Apache-2.0 (`Vendor/LICENSE`). See `NOTICE` for the list of modified files.
- The statements in `CooksonHills/Statement.lean` are from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
  commit `9097e2f`, Apache-2.0, Copyright 2026 The Formal Conjectures Authors.
- The Lean proof that connects them was built by OpenHuman agents.
