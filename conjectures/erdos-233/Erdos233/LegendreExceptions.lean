import Erdos233.AlmostAll

/-!
# Exceptional square intervals and prime gaps

This file starts the quantitative Legendre consequence of the RH large-gap
bound. A prime-free square interval sits inside one consecutive-prime gap.
-/

namespace Erdos233

open Nat

/-- The integer points in the half-open square interval `[n^2, (n+1)^2)`. -/
def squareInterval (n : ℕ) : Finset ℕ := Finset.Ico (n ^ 2) ((n + 1) ^ 2)

/-- The Legendre failure predicate: no prime lies strictly between consecutive squares. -/
def legendreFailure (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (n ^ 2 < p ∧ p < (n + 1) ^ 2)

lemma squareInterval_card (n : ℕ) : (squareInterval n).card = 2 * n + 1 := by
  simp [squareInterval]
  have h : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  omega

lemma squareInterval_disjoint {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (squareInterval m) (squareInterval n) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [squareInterval, Finset.mem_Ico] at hx₁ hx₂
  rcases lt_or_gt_of_ne hmn with h | h
  · have hs : (m + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt h) 2
    omega
  · have hs : (n + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt h) 2
    omega

/-- A failed square interval is contained in the gap between its surrounding primes. -/
lemma legendreFailure_gap {n : ℕ} (hn : 2 ≤ n) (hbad : legendreFailure n) :
    let k := idx (n ^ 2) - 1
    (n + 1) ^ 2 ≤ (k + 1).nth Nat.Prime ∧
      k.nth Nat.Prime < n ^ 2 ∧ 2 * n + 1 ≤ primeGap k := by
  let k := idx (n ^ 2) - 1
  have hsq_gt : 2 < n ^ 2 := by nlinarith
  have hkpos : idx (n ^ 2) ≠ 0 := by
    intro hz
    have hle : n ^ 2 ≤ 2 := by
      simpa [idx] using (Nat.primeCounting'_eq_zero_iff.mp hz)
    omega
  have hsucc : k + 1 = idx (n ^ 2) := by
    dsimp [k]
    omega
  have hprev : k < idx (n ^ 2) := by omega
  have hpk : k.nth Nat.Prime < n ^ 2 := nth_lt_of_lt_idx hprev
  have hnextle : n ^ 2 ≤ (k + 1).nth Nat.Prime := by
    rw [hsucc]
    exact le_nth_of_idx_le le_rfl
  have hsq_not_prime : ¬ (n ^ 2).Prime := by
    rw [pow_two]
    exact Nat.not_prime_mul (by omega) (by omega)
  have hnextgt : n ^ 2 < (k + 1).nth Nat.Prime := by
    have hp := Nat.prime_nth_prime (k + 1)
    have hneq : (k + 1).nth Nat.Prime ≠ n ^ 2 := by
      intro heq
      apply hsq_not_prime
      simpa [heq] using hp
    omega
  have hupper : (n + 1) ^ 2 ≤ (k + 1).nth Nat.Prime := by
    by_contra h
    have hlt : (k + 1).nth Nat.Prime < (n + 1) ^ 2 := by omega
    exact hbad ((k + 1).nth Nat.Prime) (Nat.prime_nth_prime _) ⟨hnextgt, hlt⟩
  have hpow : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  refine ⟨hupper, hpk, ?_⟩
  have hsum : n ^ 2 + (2 * n + 1) ≤ (k + 1).nth Nat.Prime := by
    rw [← hpow]
    exact hupper
  unfold primeGap
  omega

lemma squareInterval_subset_gap {n k : ℕ}
    (hleft : k.nth Nat.Prime ≤ n ^ 2)
    (hright : (n + 1) ^ 2 ≤ (k + 1).nth Nat.Prime) :
    squareInterval n ⊆ Finset.Ico (k.nth Nat.Prime) ((k + 1).nth Nat.Prime) := by
  intro x hx
  simp only [squareInterval, Finset.mem_Ico] at hx ⊢
  exact ⟨hleft.trans hx.1, lt_of_lt_of_le hx.2 hright⟩

end Erdos233
