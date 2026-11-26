# Vendored from PrimeNumberTheoremAnd

Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd (Apache-2.0, see `LICENSE`).

Files keep their original relative paths under `Vendor/PNT/`, so module
`PrimeNumberTheoremAnd.X` becomes `Vendor.PNT.PrimeNumberTheoremAnd.X`.
Every file carries the line "Modified for erdos-985: ported to Lean v4.36.0 / Mathlib fc4f59e5."
Changes: import paths rewritten to the `Vendor.PNT.` prefix, and the minimal API-drift fixes
needed to compile against Lean v4.36.0 / Mathlib fc4f59e5. No statements were weakened.

## Entries

- Hadamard factorization (general, finite order) and its dependency closure:
  `PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization{,/Growth,/Order,/Summability}.lean`,
  `Divisor*.lean`, `WeierstrassFactor.lean`, `CanonicalProduct.lean`, `Cartan*.lean`, `ExpPoly{,/Growth}.lean`,
  `AbsMax.lean`, `BorelCaratheodory.lean`, `LocallyUniformLimit.lean`, `Norm.lean`,
  `ValueDistribution/LogCounting/{Basic,Growth}.lean`, `Analysis/Meromorphic/Divisor{Holomorphic,Support}.lean`,
  `Analysis/SpecialFunctions/{Exp,Complex/LogBounds,Log/Dyadic,Log/ExpGrowth,Log/PosLog}.lean`,
  `Topology/MetricSpace/Annulus.lean`, `Analysis/Calculus/Deriv/Polynomial.lean`.
  Source commit: a4fb6989b07e9c76b511807ae93e33e25b820e9b (Lean v4.35.0). Vendored by the Hadamard agent.
