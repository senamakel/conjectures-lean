# Discharging the Erdős #142 / #140 hypothesis inside openai/math

`Implications.Erdos142.FromQuantitativeDensity` proves formal-conjectures
`erdos_142.variants.lower` and our all-`k` statement of Erdős #140 from
`Erdos142.OAI.QuantitativeDensityTheorem`, a verbatim copy of openai/math's
`OAI.Erdos3.QuantitativeDensityTheorem` (`lean/OAI/Combinatorics/Progressions/Model.lean`,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`). openai/math proves it as
`OAI.Erdos3.manuscriptQuantitativeDensityTheorem`
(`lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean`).

openai/math is on Lean `v4.34.1` and Mathlib `d13f23b7`, and its progressions library alone has
4,774 files, so the Implications library does not import it. [`Discharge.lean`](Discharge.lean)
is the discharge that would close the hypothesis inside openai/math's own toolchain:

```lean
theorem Erdos142.OAI.quantitativeDensityTheorem : Erdos142.OAI.QuantitativeDensityTheorem :=
  OAI.Erdos3.manuscriptQuantitativeDensityTheorem
```

followed by one-line applications of `variantsLower_of_quantitativeDensity` and
`allK_of_quantitativeDensity`. Our copies live in the namespace `Erdos142.OAI` rather than
`OAI.Erdos3`, so both can be imported together. The two definitions have identical bodies, so
the first line goes through by unfolding.

## Status: not typechecked

No openai/math build cache exists on the build box (2026-11-26), and the `v4.34.1` toolchain is
not installed. A cold build of the progressions tree would take hours, so it was not started.
To check it: in openai/math's `lean/`, run `lake exe cache get`, copy
`Implications/Erdos142/Statement.lean` and `FromQuantitativeDensity.lean` under the same
paths, add them to the library's globs, and run `lake env lean Discharge.lean`. Those two files
use only Mathlib and should compile at `d13f23b7`; that has not been tried.

The progressions tree at `adc7f12` imports only Mathlib and its own modules. A source search of
it finds no `axiom`, `sorry`, `native_decide`, `opaque`, `implemented_by` or `extern`. That is a
text search, not `#print axioms`. openai/math's Comparator config (`ErdosReciprocal.json`,
permitted axioms: the standard three) covers only `manuscriptReciprocalProgressionTheorem`.
`lean/docs/159.md` says that the quantitative bound "is outside this selected statement", so
openai/math has not certified `manuscriptQuantitativeDensityTheorem` itself, although
`Conclusions.lean` proves both theorems from the same lemma, `manuscript_main_theorems`.
