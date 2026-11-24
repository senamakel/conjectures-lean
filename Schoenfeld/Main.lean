import Schoenfeld.Pi

/-!
# Main theorems (conditional on RH)

Under Mathlib's `RiemannHypothesis`:

* `psiBound_of_RH : PsiBound (1/8) 73.2`: `|ψ(x) − x| < √x log² x / 8` for `x ≥ 73.2`;
* `thetaBound_of_RH : ThetaBound (1/2) 599`: `|θ(x) − x| < √x log² x / 2` for `x ≥ 599`;
* `piBound_of_RH : PiBound (3/5) 2657`: `|π(x) − li(x)| < (3/5) √x log x` for `x ≥ 2657`.

These are Schoenfeld's three bounds with the same thresholds and larger constants
(`1/8 = π · 1/(8π)`, `1/2 = 4π · 1/(8π)`, `3/5 ≈ 15 · 1/(8π)`); Schoenfeld's exact statement
`SchoenfeldStatement` stays the fixed target. See `docs/BLUEPRINT.md`.
-/

namespace Schoenfeld

/-- Schoenfeld's three bounds under RH, with the constants `1/8`, `1/2`, `3/5`. -/
theorem schoenfeld_weak_of_RH (hRH : RiemannHypothesis) :
    PsiBound (1 / 8) 73.2 ∧ ThetaBound (1 / 2) 599 ∧ PiBound (3 / 5) 2657 :=
  ⟨psiBound_of_RH hRH, thetaBound_of_RH hRH, piBound_of_RH hRH⟩

end Schoenfeld
