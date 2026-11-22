# Connecting to the GRH proof of Bach's bound

Everything in this repository is unconditional: `Miller.miller_of_bach` and
`Miller.prime_iff_of_bach` take `BachSubgroupBound c` as a hypothesis.

`Miller.BachSubgroupBound` is copied verbatim from `Ankeny.BachSubgroupBound` in the
`ankeny-grh` repository, so the two are the same term. Once `ankeny-grh` proves

```lean
theorem Ankeny.bach_of_GRH (hGRH : GRH) : Ankeny.BachSubgroupBound 2
```

the GRH version of Miller's theorem and of the deterministic test is one line each:

```lean
theorem Miller.miller_of_GRH (hGRH : GRH) : Miller.MillerStatement 2 :=
  Miller.miller_of_bach (Ankeny.bach_of_GRH hGRH)

theorem Miller.millerTest_iff_prime_of_GRH (hGRH : GRH) {n : ℕ} (hn : Odd n) (h1 : 1 < n) :
    Miller.millerTest n = true ↔ n.Prime :=
  Miller.millerTest_iff_prime (Ankeny.bach_of_GRH hGRH) hn h1
```

The dependency on `ankeny-grh` is deliberately not added yet. If the definitions turn out to be
syntactically different after an upstream change, `Iff.rfl`/`id` should still close the gap as
long as they unfold to the same proposition.
