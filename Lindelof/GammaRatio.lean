import Mathlib

/-!
# Step 3: a ratio bound for `Γ` on vertical lines

`|Γ(b + iy)| ≤ C |y|^{b-a} |Γ(a + iy)|` for `1/4 ≤ a ≤ b ≤ 1`, `|y| ≥ 1`, with `C` absolute.
See `docs/BLUEPRINT.md`, Step 3 (Gauss product `Complex.GammaSeq_tendsto_Gamma`).
-/

namespace Lindelof

open Complex

theorem norm_Gamma_le_rpow_mul :
    ∃ C : ℝ, ∀ a b y : ℝ, 1 / 4 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ |y| →
      ‖Gamma (b + y * I)‖ ≤ C * |y| ^ (b - a) * ‖Gamma (a + y * I)‖ := by
  sorry

end Lindelof
