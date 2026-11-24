import Mathlib

/-!
# Target statements for speiser-rh

**Speiser's theorem** (A. Speiser, *Geometrisches zur Riemannschen Zetafunktion*,
Math. Ann. 110 (1934), 514–521): the Riemann hypothesis is equivalent to `ζ'(s) ≠ 0` for
`0 < Re s < 1/2`. Levinson and Montgomery (*Zeros of the derivatives of the Riemann
zeta-function*, Acta Math. 133 (1974), 49–65) gave an analytic proof and a quantitative form.

Only the direction **RH ⇒ `ζ'` has no zeros in `0 < Re s < 1/2`** is targeted here.
formal-conjectures has no statement of Speiser's theorem (searched 2026-11-24 for "Speiser" and
for `deriv riemannZeta`), so these definitions are this repo's own. `RiemannHypothesis` is
Mathlib's.

These statements are fixed: do not edit them to make a proof go through.
-/

namespace Speiser

/-- **The target** (forward direction of Speiser's theorem, as a conclusion): `ζ'(s) ≠ 0`
throughout the open strip `0 < Re s < 1/2`. -/
def SpeiserStatement : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → deriv riemannZeta s ≠ 0

/-- `ζ'(s) ≠ 0` for `0 < Re s < 1/2` and `|Im s| ≥ T₀` (the part of the strip above height
`T₀`). -/
def SpeiserAbove (T₀ : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → T₀ ≤ |s.im| → deriv riemannZeta s ≠ 0

/-- `ζ'(s) ≠ 0` for `0 < Re s < 1/2` and `|Im s| < T₀` (the bounded part of the strip). -/
def SpeiserBelow (T₀ : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → |s.im| < T₀ → deriv riemannZeta s ≠ 0

/-- The two regions together give the target. -/
theorem speiserStatement_of_above_of_below {T₀ : ℝ} (hA : SpeiserAbove T₀)
    (hB : SpeiserBelow T₀) : SpeiserStatement := fun s h0 h1 =>
  (le_or_gt T₀ |s.im|).elim (hA s h0 h1) (hB s h0 h1)

end Speiser
