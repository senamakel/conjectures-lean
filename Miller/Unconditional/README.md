# Connecting to GRH

`Miller.BachSubgroupBound` is copied verbatim from `Ankeny.BachSubgroupBound`, so the two are the
same term. `ankeny-grh` (a lake dependency, pinned in `lakefile.toml`) proves
`Ankeny.bach_of_GRH : DirichletLNonvanishingRightOfHalf → BachSubgroupBound (21 / 5)`, and
`Miller/GRH.lean` plugs it in:

```lean
theorem Miller.miller_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Miller.MillerStatement (21 / 5) :=
  Miller.miller_of_bach (Ankeny.bach_of_GRH hGRH)
```

To make this unconditional, apply it to `LFunction_ne_zero_of_half_lt_re` from
leanprover-community/riemann-hypothesis. Its statement is identical to
`Erdos985.DirichletLNonvanishingRightOfHalf`; see erdos-985's `Unconditional/` for the pattern.
