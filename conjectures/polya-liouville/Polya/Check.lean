import Polya.Identities

/-!
# A checker for `M(x)` and `L(x)`, proved sound

The trusted computation is a check of tables, not the computation that fills them.

* `blockSum f x n` evaluates `∑_{k=n}^{x} f ⌊x/k⌋` in `O(√x)` steps, grouping the `k` on which
  `⌊x/k⌋` is constant (`blockSum_eq`).
* A candidate for `M` is any function `f : ℕ → ℤ`, read here from two arrays (`tableFn`): `f y`
  for `y ≤ T`, and `f ⌊X/a⌋` for `⌊X/a⌋ > T`.
* `tablesOK X T f` checks the identity `∑_{k=1}^{y} f ⌊y/k⌋ = 1` at every `y` of the set
  `V = {1 ≤ y ≤ T} ∪ {⌊X/a⌋ : a ≥ 1}`. `V` is closed under `y ↦ ⌊y/k⌋`, and the identity
  determines `M` (`sum_mertens_div`), so a passing check forces `f = M` on `V` (`tables_sound`),
  whatever arrays are supplied.
* `L(X) = ∑_{d ≤ √X} M(⌊X/d²⌋)` (`liouvilleSum_eq_sum_mertens`) and every `⌊X/d²⌋` lies in `V`.

The arrays are filled by `buildSmall` and `buildBig`, the usual `O(X^{3/4})` recursion. Nothing
about them is proved and nothing needs to be: the check is run on whatever they return.
-/

namespace Polya.Check

open Finset

/-! ## Block sums -/

theorem le_div_div {x n : ℕ} (h : n ≤ x) : n ≤ x / (x / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hq : 0 < x / n := Nat.div_pos h hn
  rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm]
  exact Nat.mul_div_le x n

/-- `blockSum f x n = ∑_{k=n}^{x} f ⌊x/k⌋`, summed over the blocks `[n, ⌊x/⌊x/n⌋⌋]` on which
`⌊x/k⌋` is constant. -/
def blockSum (f : ℕ → ℤ) (x n : ℕ) : ℤ :=
  if h : x < n then 0 else
    ((x / (x / n) + 1 - n : ℕ) : ℤ) * f (x / n) + blockSum f x (x / (x / n) + 1)
termination_by x + 1 - n
decreasing_by
  have := le_div_div (Nat.le_of_not_lt h)
  omega

end Polya.Check
