import BachSharp.Basic
import BachSharp.Sound
import BachSharp.Tail
import BachSharp.Compute.L0
import BachSharp.Compute.L1

/-!
# The sharp bound for `m ≥ 5 · 2^49`, under GRH

With constant `1.657 ≤ 2 / log² 3`: `5 · 2^49 ≤ q < 2^7400` by the parametrised lls-grh checker
(`BachSharp/Compute/L0.lean`, `L1.lean`; every block passes the GRH budget uniform in `q`), and
`q ≥ 2^7400` by the polynomial tail `goodQ_tailS`.
-/

set_option exponentiation.threshold 8000

namespace BachSharp

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- **Bach's subgroup bound with constant `1.657` for `q ≥ 5 · 2^49`, under GRH.** -/
theorem bach1657_large_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (q : ℕ) [NeZero q]
    (hq : 5 * 2 ^ 49 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 1657 / 1000 * Real.log q ^ 2 := by
  have hc : ((1657 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) = 1657 / 1000 := by norm_num
  rcases Nat.lt_or_ge q (2 ^ 100) with h | h
  · have := Check.checkChunkC_sound chunk_ok_L0 q hq h
    rw [hc] at this
    exact bach_of_goodC hGRH q this H hH
  rcases Nat.lt_or_ge q (2 ^ 7400) with h' | h'
  · have := Check.checkChunkC_sound chunk_ok_L1 q h h'
    rw [hc] at this
    exact bach_of_goodC hGRH q this H hH
  · exact LLS.bach_of_goodQ hGRH q (goodQ_tailS q h') H hH

/-- **The sharp bound for every modulus `q ≥ 5 · 2^49`, under GRH.** -/
theorem sharp_large_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (q : ℕ) [NeZero q]
    (hq : 5 * 2 ^ 49 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ sharpConst * Real.log q ^ 2 := by
  obtain ⟨a, ha, hle⟩ := bach1657_large_of_GRH hGRH q hq H hH
  exact ⟨a, ha, hle.trans (mul_le_mul_of_nonneg_right c1657_le_sharpConst (sq_nonneg _))⟩

end BachSharp
