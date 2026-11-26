import Mathlib

/-!
# Minoli–Bear implies infinitely many non-perfect hyperperfect numbers

Source: `FormalConjectures/Wikipedia/HyperperfectNumber.lean`, formal-conjectures `9097e2f`.
`IsHyperperfect` (with its `DecidableRel` instance), the premise
`HyperperfectNumber.minoli_bear_hyperperfect_conjecture` and the conclusion
`HyperperfectNumber.infinitely_many_hyperperfect_numbers` (both research open) are copied
verbatim.

The deduction is the one in the formal-conjectures docstring (Guy 2004, §B2): for `n > 1`,
`n - 1 = k (s(n) - 1)` with `n - 1 > 0` fixes `k`, so a choice of one `k`-hyperperfect number for
each `k ≥ 2` is injective.
-/

namespace Implications.Misc.Hyperperfect

/-- Source: `FormalConjectures/Wikipedia/HyperperfectNumber.lean`,
`HyperperfectNumber.IsHyperperfect`, formal-conjectures `9097e2f`, verbatim.

Predicate asserting that $n > 1$ is $k$-hyperperfect ($k \ge 1$):
$n = 1 + k \cdot (s(n) - 1)$ where $s(n)$ sums the proper divisors of $n$. -/
def IsHyperperfect (k n : ℕ) : Prop :=
  0 < k ∧ 1 < n ∧ n = 1 + k * ((∑ d ∈ n.properDivisors, d) - 1)

instance instDecidableRelIsHyperperfect : DecidableRel IsHyperperfect := fun k n ↦ by
  unfold IsHyperperfect
  infer_instance

/-- Source: `HyperperfectNumber.minoli_bear_hyperperfect_conjecture`, formal-conjectures
`9097e2f` (research open); the statement, verbatim.

Minoli and Bear's conjecture (1975; Guy 2004, §B2, pp. 74–75): for every integer $k \ge 1$, at
least one $k$-hyperperfect integer exists. -/
def MinoliBearConjecture : Prop :=
    ∀ k ≥ 1, ∃ n, IsHyperperfect k n

/-- Source: `HyperperfectNumber.infinitely_many_hyperperfect_numbers`, formal-conjectures
`9097e2f` (research open); the statement, verbatim. -/
def InfinitelyManyHyperperfect : Prop :=
    {n : ℕ | ∃ k ≥ 2, IsHyperperfect k n}.Infinite

/-- A number `n` is `k`-hyperperfect for at most one `k`. -/
theorem IsHyperperfect.unique {k j n : ℕ} (hk : IsHyperperfect k n) (hj : IsHyperperfect j n) :
    k = j := by
  obtain ⟨-, hn, e1⟩ := hk
  obtain ⟨-, -, e2⟩ := hj
  set S := (∑ d ∈ n.properDivisors, d) - 1
  have h0 : k * S ≠ 0 := by omega
  have hS : 0 < S := Nat.pos_of_ne_zero (fun h => h0 (by simp [h]))
  exact Nat.eq_of_mul_eq_mul_right hS (by omega)

/-- **Minoli–Bear implies infinitely many non-perfect hyperperfect numbers.** -/
theorem infinitely_many_hyperperfect_of_minoli_bear (h : MinoliBearConjecture) :
    InfinitelyManyHyperperfect := by
  have hc : ∀ k : ℕ, ∃ n, 1 ≤ k → IsHyperperfect k n := by
    intro k
    by_cases hk : 1 ≤ k
    · obtain ⟨n, hn⟩ := h k hk; exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h' => absurd h' hk⟩
  choose f hf using hc
  have hinj : Set.InjOn f (Set.Ici 2) := fun k hk j hj e =>
    (hf k (by simp at hk; omega)).unique (e ▸ hf j (by simp at hj; omega))
  refine ((Set.Ici_infinite 2).image hinj).mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, hk, hf k (by simp at hk; omega)⟩

end Implications.Misc.Hyperperfect
