# The Lindelöf hypothesis from RH, in Lean

`Lindelof/Statement.lean` fixes the target statements; its definitions must not change. The
project has no `sorry` on the path to the main theorem (the Dirichlet L-function version in
`Lindelof/Dirichlet.lean` is an open stretch goal).

The [Lindelöf hypothesis](https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis) says that
`ζ(1/2 + it) = O(t^ε)` for every `ε > 0`. Littlewood (1912) proved that it follows from the Riemann
hypothesis (Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §14.2). This project
formalizes that implication:

```lean
theorem Lindelof.lindelof_of_RH (hRH : RiemannHypothesis) : Lindelof.LindelofHypothesis
```

`RiemannHypothesis` is Mathlib's statement. RH itself is supplied by
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
which proves it as `riemannHypothesis : RiemannHypothesis`. The main library takes RH as a
hypothesis and does not import that repository. `Unconditional/LindelofUnconditional.lean` imports
both and closes the hypothesis in one line; `scripts/check-unconditional.sh` builds and checks it:

```lean
theorem lindelof_hypothesis : Lindelof.LindelofHypothesis :=
  Lindelof.lindelof_of_RH riemannHypothesis
-- 'lindelof_hypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Checked against riemann-hypothesis commit `507a75d91d`. The riemann-hypothesis proof brings in no
axioms of its own; the result is exactly as trustworthy as that proof.

The analytic toolkit (Hadamard factorization of `ξ`, growth of `ξ`) comes from
[erdos-985](https://github.com/senamakel/erdos-985), required as a lake dependency.

The proof plan is in [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).
