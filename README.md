# Artin's primitive root conjecture under Hooley's hypothesis, in Lean

Work in progress.

The target is Hooley's 1967 theorem, as stated in
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean):

```lean
theorem conditional_artin_primitive_roots.parts.i (a : ℤ) (ha : ¬IsSquare a) (ha' : a ≠ -1)
    (h : HooleyHypothesis a) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime}
```

That is: if `a` is not a square and not `-1`, and RH holds for the Dedekind zeta functions of
the Kummer fields `ℚ(ζ_k, a^{1/k})` with `k` squarefree, then a positive proportion of primes
`p` have `a` as a primitive root.

## This result stays conditional

[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
proves RH for ζ and GRH for Dirichlet L-functions. The Kummer fields are not abelian over ℚ,
so their zeta functions are not products of Dirichlet L-functions, and that repository does
not supply `HooleyHypothesis`. Unlike [erdos-985](https://github.com/senamakel/erdos-985),
this project has no unconditional version. The erdos-985 analytic library also covers only
Dirichlet characters, so the Chebotarev and Kummer-field parts have to be built here.

## Layout

| File | Content |
|---|---|
| `Artin/Statement.lean` | definitions copied word for word from formal-conjectures; do not change |
| `Artin/Interfaces.lean` | the split: analytic half and sieve half, joined by `EffectiveKummerChebotarev` |
| `Artin/Main.lean` | the target theorem, from the two halves |
| `docs/BLUEPRINT.md` | the plan, step by step |

## Building

Uses Lean v4.36.0 and the same Mathlib as erdos-985 (`fc4f59e5`), which it requires as a lake
dependency. `.lake/packages` is a symlink to the shared package directory
`../lean-grh-shared/packages`, which other projects also use: don't run `lake update`,
`lake clean` or `lake exe cache get` against it. Build one module at a time:

```bash
lake build Artin.Main
```
