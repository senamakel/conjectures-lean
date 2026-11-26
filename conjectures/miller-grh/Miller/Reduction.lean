import Miller.Liars

/-!
# Bach's subgroup bound implies Miller's theorem

The statements are the ones fixed in the scaffold (moved here from `Miller/Statement.lean`).
-/

namespace Miller

/-- For odd composite `n`, Bach's bound gives a unit outside the liar subgroup: a non-liar base
`a` with `0 < a < n` and `a ≤ c log² n`. -/
theorem exists_witness_of_bach {c : ℝ} (h : BachSubgroupBound c) {n : ℕ} (hn : Odd n)
    (h1 : 1 < n) (hnp : ¬ n.Prime) :
    ∃ a : ℕ, 0 < a ∧ a < n ∧ (a : ℝ) ≤ c * Real.log n ^ 2 ∧ ¬ IsStrongProbablePrime n a := by
  have : NeZero n := ⟨by omega⟩
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  obtain ⟨H, hH, hliar⟩ := exists_proper_subgroup_liars hn h1 hnp
  obtain ⟨u, huH, hu⟩ := h n H hH
  refine ⟨(u : ZMod n).val, Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero),
    ZMod.val_lt _, hu, fun hspp => huH (hliar u ?_)⟩
  exact (isStrongProbablePrime_val_iff u).mp hspp

/-- Unconditional group theory: the main deliverable of this repository. -/
theorem miller_of_bach {c : ℝ} (h : BachSubgroupBound c) : MillerStatement c := by
  intro n hn h1 hnp
  obtain ⟨a, ha0, -, hac, ha⟩ := exists_witness_of_bach h hn h1 hnp
  exact ⟨a, ha0, hac, ha⟩

/-- The resulting primality test is correct: for odd `n > 1`, `n` is prime iff it is a strong
probable prime to every base `1 ≤ a ≤ c log² n` with `a < n`. -/
theorem prime_iff_of_bach {c : ℝ} (h : BachSubgroupBound c) (n : ℕ) (hn : Odd n) (h1 : 1 < n) :
    n.Prime ↔ ∀ a : ℕ, 0 < a → a < n → (a : ℝ) ≤ c * Real.log n ^ 2 → IsStrongProbablePrime n a := by
  refine ⟨fun hp a ha0 han _ => isStrongProbablePrime_of_prime hp ha0 han, fun hall => ?_⟩
  by_contra hnp
  obtain ⟨a, ha0, han, hac, ha⟩ := exists_witness_of_bach h hn h1 hnp
  exact ha (hall a ha0 han hac)

end Miller
