# Vendored: Rosser's zero count (Rosser 1941, Theorem 19)

This directory holds the exact import closure of
`TernaryGoldbach.RSBounds.Rosser1941.zero_count_bounds`, the unconditional Lean proof of
Rosser's explicit Riemann–von Mangoldt formula

`|N(T) − (T/2π) log(T/2π) + T/2π − 7/8| < 0.137 log T + 0.443 log log T + 1.588` for `T ≥ 2`,

which `Schoenfeld/Rosser.lean` uses to prove `Schoenfeld.rosserZeroCount`. The closure is
216 Lean files (about 95,000 lines), computed by following `import` lines from
`RSBounds/Rosser1941.lean`. Nothing outside the closure is vendored. The proof has no `sorry`,
`axiom` or `native_decide`.

| Directory | Files | Lines | Source |
|---|---|---|---|
| `RSBounds/` | 82 | 13,027 | [Garald1/RSBounds](https://github.com/Garald1/RSBounds) `82d7a55f02e52cd071cd8ed800cc889a23ad3e61`, path `RSBounds/` (Apache-2.0; eleven files MIT, see their headers) |
| `TernaryGoldbach/` | 35 | 12,743 | [calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach) `192ca57362fa3ee737cd83205cb9ea99526c4553`, path `TernaryGoldbach/` (Apache-2.0) |
| `Zeta23/`, `ZetaLean/`, `RHHeight/`, `RHHeight100/`, `HardyFirstZero/`, `HardyTenZeros/` | 99 | 69,276 | Garald1/RSBounds `82d7a55`, path `vendor/rh100/`, which is the closure of `RHHeight100.Main100` from [teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab) `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534` with RSBounds' documented adaptations (zeta-lab: MIT, Thomas Lince; Zeta23 files: Apache-2.0) |

The proof splits at height 100 (`Rosser1941.lean`): Backlund's argument (Jensen's formula,
the Gamma-factor phase by Stirling, an Euler–Maclaurin bound for ζ) for `T ≥ 100`
(`RSBounds/BacklundHighCount.lean`, 110 files of the closure, Mathlib only), and for
`T ≤ 100` the zeta-lab certificate that the 29 zeros of height at most 100 are simple, lie on
the critical line, and sit in explicit rational brackets (`RSBounds/BacklundLowCount.lean`).

## Provenance and licences

Every file begins with a comment naming its source repository, commit and path. Files keep
their original module names, namespaces and author/licence headers. The licence texts and
notices of the three sources are in `licenses/`:

* `RSBounds-LICENSE` (Apache-2.0), `RSBounds-licenses-*` (the MIT text for RSBounds' MIT
  files and the licences of the projects RSBounds adapts: IEANTN, gersh/ternary-goldbach-lean,
  PrimeNumberTheoremAnd, calr3/ternary-goldbach, Zeta23) and `RSBounds-THIRD_PARTY_NOTICES.md`
  (RSBounds' attribution of every adapted file);
* `ternary-goldbach-LICENSE` (Apache-2.0) and `ternary-goldbach-NOTICE`;
* `zeta-lab-LICENSE-MIT`, `Zeta23-LICENSE-Apache-2.0` and `rh100-README.md` (RSBounds'
  description of the height-100 replay and its adaptations).

## Build

`lakefile.toml` registers six libraries (`RosserTG`, `RosserRSBounds`, `RosserZeta23`,
`RosserZetaLean`, `RosserRHHeight`, `RosserHardy`), all with `srcDir = "Vendor/Rosser"`. Each
keeps the Lean options of the project it came from: the upstream packages leave `autoImplicit` at
Lean's default (`true`), and zeta-lab's `RHHeight` libraries turn it off.

Changes made to port the files from Lean `v4.35.0` / Mathlib `v4.35.0` to this repository's
Lean `v4.36.0` / Mathlib `fc4f59e5` are listed, file by file, in [`PORTING.md`](PORTING.md).
No statement was changed and no hypothesis added.
