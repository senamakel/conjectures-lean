import Polya.Check

/-!
# Von Sterneck's conjecture is false

`M(7725038629) = 43947`, and `4 · 43947² = 7725355236 > 7725038629`, so `|M(x)| < ½ √x` fails at
`x = 7725038629 > 200`.

One `native_decide` (`Polya.Check.mertens_7725038629_check`): it fills the tables of `M` at the
`2·87892` points `y ≤ 87892` and `⌊7725038629/a⌋`, checks the identity
`∑_{k ≤ y} M(⌊y/k⌋) = 1` at each of them, and reads off `M(7725038629)`. Soundness:
`runMertens_sound`, the same theorem as for Pólya's conjecture at a different argument.
-/

namespace Polya

namespace Check

/-- The table check for `M(7725038629) = 43947`. Uses `native_decide`. -/
theorem mertens_7725038629_check : runMertens 7725038629 43947 = true := by
  native_decide

end Check

/-- `M(7725038629) = 43947`. -/
theorem mertens_7725038629 : mertens 7725038629 = 43947 :=
  Check.runMertens_sound Check.mertens_7725038629_check (by norm_num)

/-- Von Sterneck's conjecture is false, squared form: `4 M(x)² ≥ x` at `x = 7725038629`. -/
theorem vonSterneck_conjecture_int_false : ¬ VonSterneckConjectureInt := by
  intro h
  have := h 7725038629 (by norm_num)
  rw [mertens_7725038629] at this
  exact absurd this (by norm_num)

/-- Von Sterneck's conjecture is false: `|M(x)| ≥ ½ √x` at `x = 7725038629`. -/
theorem vonSterneck_conjecture_false : ¬ VonSterneckConjecture := by
  intro h
  have h1 := h 7725038629 (by norm_num)
  rw [mertens_7725038629] at h1
  have h2 : Real.sqrt (7725038629 : ℝ) ≤ 87894 := by
    rw [show (87894 : ℝ) = Real.sqrt (87894 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  norm_num at h1
  linarith

end Polya
