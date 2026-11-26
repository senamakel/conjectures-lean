import Mathlib

/-!
# Green's problem 76 and the weak ε-net question ⇒ the constant form of Green 76

The statements are copied word for word from formal-conjectures (commit `9097e2f`),
`FormalConjectures/GreensOpenProblems/76.lean`, with the definition `Green76.HitsRichRectangles`
from the same file (Apache-2.0, © 2026 The Formal Conjectures Authors):

* `Green76.green_76` (research open), stated here as `Green76Statement`;
* `Green76.green_76.variants.weak_net` (research open), stated here as `Green76WeakNet`;
* `Green76.green_76.variants.exists_constant` (research open), stated here as
  `Green76ExistsConstant`.

The docstring of `exists_constant` says "Each of `green_76` and `green_76.variants.weak_net`
implies this." The first is a specialisation (`k = 1000`). For the second, given the constant `C`
of the weak net, take `k = ⌈2C⌉₊ + 1`: then `C · n / k ≤ n / 2`, and a natural number at most
`n / 2` (a real) is at most `⌊n / 2⌋`.
-/

open scoped Finset

namespace Implications.Combinatorics.Green76

/-- Verbatim from formal-conjectures `9097e2f`, `Green76.HitsRichRectangles`: every closed
axis-parallel rectangle that contains at least `k` points of `A` also contains a point of `A'`. -/
def HitsRichRectangles (k : ℕ) (A A' : Finset (ℝ × ℝ)) : Prop :=
  ∀ a b : ℝ × ℝ, k ≤ #{p ∈ A | p ∈ Set.Icc a b} → ∃ p ∈ A', p ∈ Set.Icc a b

/-- Verbatim from formal-conjectures `9097e2f`, `Green76.green_76`. -/
def Green76Statement : Prop :=
    ∀ A : Finset (ℝ × ℝ), ∃ A', #A' ≤ #A / 2 ∧ HitsRichRectangles 1000 A A'

/-- Verbatim from formal-conjectures `9097e2f`, `Green76.green_76.variants.exists_constant`. -/
def Green76ExistsConstant : Prop :=
    ∃ k : ℕ, ∀ A : Finset (ℝ × ℝ), ∃ A', #A' ≤ #A / 2 ∧ HitsRichRectangles k A A'

/-- Verbatim from formal-conjectures `9097e2f`, `Green76.green_76.variants.weak_net`. -/
def Green76WeakNet : Prop :=
    ∃ C : ℝ, ∀ k : ℕ, 0 < k → ∀ A : Finset (ℝ × ℝ),
      ∃ A', #A' ≤ C * #A / k ∧ HitsRichRectangles k A A'

/-- **Green 76 ⇒ Green 76 with some constant** (take `k = 1000`). -/
theorem green76ExistsConstant_of_green76 (h : Green76Statement) : Green76ExistsConstant :=
  ⟨1000, h⟩

/-- **Weak ε-nets of size `O(1/ε)` ⇒ Green 76 with some constant.** -/
theorem green76ExistsConstant_of_weakNet (h : Green76WeakNet) : Green76ExistsConstant := by
  obtain ⟨C, hC⟩ := h
  set k : ℕ := ⌈2 * C⌉₊ + 1 with hk
  have hkpos : 0 < k := Nat.succ_pos _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have h2C : 2 * C ≤ (k : ℝ) := by
    have := Nat.le_ceil (2 * C)
    rw [hk]; push_cast; linarith
  refine ⟨k, fun A => ?_⟩
  obtain ⟨A', hcard, hhit⟩ := hC k hkpos A
  refine ⟨A', ?_, hhit⟩
  have hn : (0 : ℝ) ≤ #A := Nat.cast_nonneg _
  have hle : (#A' : ℝ) ≤ (#A : ℝ) / 2 := by
    refine hcard.trans ?_
    rw [div_le_div_iff₀ hkR (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  -- `#A' ≤ #A / 2` in `ℝ` gives `2 * #A' ≤ #A` in `ℕ`.
  have h2 : 2 * #A' ≤ #A := by
    have : (2 : ℝ) * #A' ≤ #A := by linarith
    exact_mod_cast this
  omega

end Implications.Combinatorics.Green76
