# Notice

`Density/Statement.lean` contains definitions and a theorem statement copied word for word from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
at commit `86a2f58a4d7a3a0637d15d5b2ce627592b54b956`:

- `Complex.zeroCountOn`, `Complex.analyticOrderNatAt_eq_zero_of_ne_zero` and
  `Complex.zeroCountOn_eq_zero_of_forall_ne_zero` from
  `FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean`;
- `DensityHypothesis.zetaZeroCount` and the statements of
  `DensityHypothesis.density_hypothesis_zeta_zeros` and `DensityHypothesis.guth_maynard_zero_density`
  (as the bodies of `DensityHypothesis.Statement` and `DensityHypothesis.GuthMaynardStatement`) from `FormalConjectures/Wikipedia/DensityHypothesis.lean`.

Copyright 2026 The Formal Conjectures Authors. Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The changes are listed in the module docstring of
`Density/Statement.lean`: the `module` header, the `public`/`@[expose]` section markers and the
`@[category …, AMS …]` attributes are dropped, and the two theorem statements are made `Prop`s.
