# Hironaka's resolution of singularities in characteristic 0 in Lean

Hironaka (*Resolution of singularities of an algebraic variety over a field of characteristic
zero*, Ann. of Math. 79 (1964), 109–326) proved that every variety `X` over a field of
characteristic 0 has a resolution: a smooth variety `Y` with a proper birational morphism
`Y → X`. In positive characteristic this is known in dimension at most three and open beyond.

**Status in the literature: known.** This is a Lean formalisation of a theorem proved in 1964.
It is not new mathematics, and it has nothing to do with the Riemann hypothesis.

This repository proves the statement of the theorem that
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) carries as
`resolution_of_singularities_of_charZero`, where it is stated with `sorry`. It does not formalise
Hironaka's argument. The resolution algorithm is imported from
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
which proves it on the way to something else. What is proved here is the passage from that
theorem to the formal-conjectures statement.

## Main theorems

```lean
-- Hironaka/Main.lean
theorem Hironaka.hironaka_of_smoothModification (h : SmoothModification.{u}) :
    HironakaStatement.{u}

-- Unconditional/HironakaUnconditional.lean
theorem Hironaka.Unconditional.smoothModification : SmoothModification.{u}
theorem Hironaka.Unconditional.resolution_of_singularities_of_charZero : HironakaStatement.{u}
```

with, from `Hironaka/Statement.lean`:

```lean
def HasResolution {S X : Scheme.{u}} (sX : X ⟶ S) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
    IsIntegral Y ∧ IsProper f ∧ Smooth (f ≫ sX) ∧ Scheme.BirationalOver f (𝟙 X)

def HironakaStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsSeparated sX],
    HasResolution sX

def SmoothModification : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X],
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X),
      Smooth (π ≫ f) ∧ IsProper π ∧ IsIso (morphismRestrict π f.smoothLocus) ∧
        Dense (π.base ⁻¹' (f.smoothLocus : Set X))
```

## Tier and provenance

Tiers are those of the [conjectures](https://github.com/senamakel/conjectures) workspace.

| Theorem | Tier | Hypotheses |
|---|---|---|
| `hironaka_of_smoothModification` | H | `SmoothModification` |
| `Unconditional.resolution_of_singularities_of_charZero` | U₀ | none |

- `HasResolution` and `HironakaStatement` are `AlgebraicGeometry.Scheme.HasResolution` and the
  statement of `resolution_of_singularities_of_charZero` in formal-conjectures,
  `FormalConjectures/Wikipedia/ResolutionOfSingularities.lean`, at commit `86a2f58a4d`, copied
  word for word apart from the namespace. formal-conjectures marks the theorem
  `research solved`.
- `SmoothModification` is the one input the main library does not prove. It is the first four
  clauses of `FunctorialResolution.IsResolutionRuleCharZero` in riemann-hypothesis
  (`src/Development/ResolutionOfSingularities/Statements.lean`), with the tower of blowups
  forgotten. It mentions Mathlib objects only, so any other proof of Hironaka's theorem can
  discharge it.
- Tier U₀ means the theorem imports riemann-hypothesis for a lemma that does not depend on the
  Riemann hypothesis. No RH or GRH theorem is used anywhere in this repository.

## Axioms

Main library, `#print axioms Hironaka.hironaka_of_smoothModification` (2026-11-24):

```
'Hironaka.hironaka_of_smoothModification' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unconditional/HironakaUnconditional.lean` (2026-11-24, riemann-hypothesis `507a75d91d`):

```
'Hironaka.Unconditional.smoothModification' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hironaka.Unconditional.resolution_of_singularities_of_charZero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

There is no `sorry`, no `native_decide` and no `axiom` declaration.

## Proof outline

Given `X` integral, separated and of finite type over a field `k` of characteristic 0, with
structure morphism `sX`, and `π : Y ⟶ X` from `SmoothModification`:

1. **The smooth locus `U` of `X` is dense.** Mathlib's generic smoothness over a perfect field,
   `Scheme.Hom.dense_smoothLocus_of_perfectField` (`Hironaka/Main.lean`).
2. **`Y` is irreducible.** `π ⁻¹ᵁ U` is isomorphic to `U`, an open subscheme of the integral `X`,
   so it is irreducible. It is dense in `Y`, so `Y` is irreducible (`Hironaka/Main.lean`).
3. **`Y` is reduced.** A scheme smooth over an integral scheme is reduced,
   `isReduced_of_smooth_of_isIntegral` (`Hironaka/SmoothReduced.lean`). Mathlib at the pin lacks
   this. The proof takes a standard smooth chart, which is étale over a polynomial ring;
   `isReduced_of_etale_of_isDomain` shows an étale algebra over a domain is reduced, by embedding
   it into its base change to the fraction field.
4. **`Y` is integral**, by Mathlib's `isIntegral_of_irreducibleSpace_of_isReduced`.
5. **`π` is birational over `X`.** The `Scheme.PartialIso` has source `π ⁻¹ᵁ U`, target `U` and
   the isomorphism `π ∣_ U`.

Properness and smoothness of `Y` over `k` come straight from the input.

## Layout

| File | Content |
|---|---|
| `Hironaka/Statement.lean` | The target and the input. Fixed |
| `Hironaka/SmoothReduced.lean` | Smooth over an integral scheme implies reduced |
| `Hironaka/Main.lean` | `hironaka_of_smoothModification` |
| `Unconditional/HironakaUnconditional.lean` | The input from riemann-hypothesis, and the closed theorem |
| `scripts/check-unconditional.sh` | Builds both and prints the axioms |

## Deviations from the literature

None in the statement. The input `SmoothModification` asks for less than Hironaka proved: it
drops the blowup structure, the centres over the singular locus and the normal-crossings
exceptional divisor, because the formal-conjectures statement does not mention them.

## Building

```
lake exe cache get && lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5`. A build with Mathlib from cache takes about 1 minute of wall
time; `Hironaka/Main.lean` is the slow module (about 150 s of CPU).

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `Hironaka.Unconditional.smoothModification` | `SmoothModification` | `propext`, `Classical.choice`, `Quot.sound` |
| `Hironaka.Unconditional.resolution_of_singularities_of_charZero` | `HironakaStatement` | `propext`, `Classical.choice`, `Quot.sound` |

Checked against riemann-hypothesis commit `507a75d91d`:

```
scripts/check-unconditional.sh [RH_DIR]
```

Only one riemann-hypothesis module is imported,
`Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing`. The
`lean` step takes about 45 s and 6.2 GB of RAM. Restoring that repository's cache with
`lake exe cache get` needs about 93 GB of disk and a high open-file limit.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the resolution-of-singularities proof,
whose independent verification is still pending. `RH_FULL_BUILD=1` rebuilds the imported
riemann-hypothesis modules from source instead; that has not been run.

A second source exists. [resolutionorg/hironaka](https://github.com/resolutionorg/hironaka)
(Apache-2.0, 420,000 lines) proves `AlgebraicGeometry.exists_isBlowUpAlong_smooth`, which gives
three of the four clauses of `SmoothModification` for integral separated schemes directly.
Discharging the input from it would make the closed theorem tier D. It is on Lean `v4.35.0`,
835 Mathlib commits behind this repository's pin, and has not been ported.

## Credits

- The definition `HasResolution` and the statement `HironakaStatement` are from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
  commit `86a2f58a4d`, Apache-2.0, Copyright 2026 The Formal Conjectures Authors. See `NOTICE`.
- riemann-hypothesis is imported, not copied. It was published without a licence.
