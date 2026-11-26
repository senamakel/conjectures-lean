import CooksonHills.OfFlint
import OAI.NumberTheory.PiExponent.Analysis.FlintConsequence

/-!
# Flint Hills and Cookson Hills from the irrationality-exponent bound for `π`

`OAI.PiExponent.PiEventualLowerBound` says that for every `ν > 2`, `|π - p/q| ≥ q^(-ν)` once
`q` is large (definition in `Vendor/OAI/NumberTheory/PiExponent/Statement.lean`). From it the
vendored `flintHills_positive_summable_of_eventual_lower_bound` gives the Flint Hills series, and
`cookson_hills_of_flint_hills` turns that into the Cookson Hills series.

This file imports only the analytic part of the vendored tree (eight modules), not the proof of
the bound itself.
-/

namespace FlintCooksonHills

/-- The Flint Hills series converges if `μ(π) = 2` in the form `PiEventualLowerBound`. -/
theorem flint_hills_of_piEventualLowerBound (h : OAI.PiExponent.PiEventualLowerBound) :
    FlintHillsStatement := by
  have := OAI.PiExponent.flintHills_positive_summable_of_eventual_lower_bound h
  unfold FlintHillsStatement
  simpa only [Nat.cast_add, Nat.cast_one] using this

/-- The Cookson Hills series converges if `μ(π) = 2` in the form `PiEventualLowerBound`. -/
theorem cookson_hills_of_piEventualLowerBound (h : OAI.PiExponent.PiEventualLowerBound) :
    CooksonHillsStatement :=
  cookson_hills_of_flint_hills (flint_hills_of_piEventualLowerBound h)

end FlintCooksonHills
