import BachCorollaries.EulerLiars

/-!
# Bach's subgroup bound implies a deterministic Solovay–Strassen test

For odd composite `n` the Euler liars form a proper subgroup (`eulerLiars_ne_top`), so
`Ankeny.BachSubgroupBound c` gives a unit `u` outside it with residue `≤ c log² n`: an Euler
witness prime to `n`. For an odd prime `p`, every base passes (Euler's criterion).
-/

namespace BachCorollaries

/-- Euler's criterion: an odd prime `p` is an Euler probable prime to every base. -/
theorem isEulerProbablePrime_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    IsEulerProbablePrime p a := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  unfold IsEulerProbablePrime
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow, Int.cast_natCast]
  congr 1
  omega

/-- For odd composite `n`, Bach's bound gives an Euler witness `0 < a < n`, `a ≤ c log² n`,
prime to `n`. -/
theorem exists_euler_witness_of_bach {c : ℝ} (h : Ankeny.BachSubgroupBound c) {n : ℕ}
    (hn : Odd n) (h1 : 1 < n) (hnp : ¬ n.Prime) :
    ∃ a : ℕ, 0 < a ∧ a < n ∧ (a : ℝ) ≤ c * Real.log n ^ 2 ∧ a.Coprime n ∧
      ¬ IsEulerProbablePrime n a := by
  have : NeZero n := ⟨by omega⟩
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  obtain ⟨u, huH, hu⟩ := h n (eulerLiars n) (eulerLiars_ne_top hn h1 hnp)
  exact ⟨(u : ZMod n).val, Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero),
    ZMod.val_lt _, hu, ZMod.val_coe_unit_coprime u,
    fun he => huH ((mem_eulerLiars_iff u).mpr he)⟩

/-- **Deterministic Solovay–Strassen from Bach's bound.** -/
theorem solovayStrassen_of_bach {c : ℝ} (h : Ankeny.BachSubgroupBound c) :
    SolovayStrassenStatement c := by
  intro n hn h1 hnp
  obtain ⟨a, ha0, -, hac, hcop, ha⟩ := exists_euler_witness_of_bach h hn h1 hnp
  exact ⟨a, ha0, hac, hcop, ha⟩

/-- The resulting primality criterion: an odd `n > 1` is prime iff every base `0 < a < n` with
`a ≤ c log² n` is prime to `n` and passes Euler's criterion. -/
theorem prime_iff_euler_of_bach {c : ℝ} (h : Ankeny.BachSubgroupBound c) {n : ℕ} (hn : Odd n)
    (h1 : 1 < n) :
    n.Prime ↔ ∀ a : ℕ, 0 < a → a < n → (a : ℝ) ≤ c * Real.log n ^ 2 →
      a.Coprime n ∧ IsEulerProbablePrime n a := by
  refine ⟨fun hp a ha0 han _ => ⟨?_, isEulerProbablePrime_of_prime hp ?_ a⟩, fun hall => ?_⟩
  · exact Nat.Coprime.symm ((Nat.coprime_of_lt_prime ha0.ne' han hp))
  · rintro rfl; exact absurd hn (by decide)
  · by_contra hnp
    obtain ⟨a, ha0, han, hac, -, ha⟩ := exists_euler_witness_of_bach h hn h1 hnp
    exact ha (hall a ha0 han hac).2

end BachCorollaries
