import FormalConjectures.OEIS.«100474»

/-! Restrict the first-prime search in A100474 to even indices. -/

namespace A100474Parity

open OeisA100474 Finset
open scoped BigOperators

private theorem triangular_succ (n : ℕ) : triangular (n + 1) = triangular n + (n + 1) := by
  unfold triangular
  rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring]
  exact Nat.add_mul_div_left _ _ (by decide)

private theorem triangular_ge (n : ℕ) : n ≤ triangular n := by
  induction n with
  | zero => decide
  | succ n ih => rw [triangular_succ]; omega

private noncomputable def primeAt (i : ℕ) : ℕ := Nat.nth Nat.Prime i

private theorem primeAt_prime (i : ℕ) : (primeAt i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i

private noncomputable def block (k : ℕ) : ℕ :=
  ∏ i ∈ Ico (triangular (k + 1) - 1) (triangular (k + 2) - 1), primeAt i

private theorem block_range (k : ℕ) :
    block k = ∏ i ∈ range (k + 2), primeAt ((triangular (k + 1) - 1) + i) := by
  unfold block
  rw [prod_Ico_eq_prod_range]
  have ht : triangular (k + 2) = triangular (k + 1) + (k + 2) :=
    triangular_succ (k + 1)
  have hlen : triangular (k + 2) - 1 - (triangular (k + 1) - 1) = k + 2 := by
    have := triangular_ge (k + 1)
    omega
  rw [hlen]

private theorem block_large (k : ℕ) : 4 ≤ block k := by
  rw [block_range]
  calc
    4 ≤ 2 ^ (k + 2) := by
      simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ k + 2 by omega))
    _ = ∏ _i ∈ range (k + 2), (2 : ℕ) := by simp
    _ ≤ _ := prod_le_prod (by simp) (fun i _ => (primeAt_prime _).two_le)

private theorem block_double (k : ℕ) : 2 * block k ≤ block (k + 1) := by
  simp only [block_range]
  have htri : triangular (k + 2) = triangular (k + 1) + (k + 2) :=
    triangular_succ (k + 1)
  let f (i : ℕ) := primeAt (triangular (k + 1) - 1 + i)
  let g (i : ℕ) := primeAt (triangular (k + 2) - 1 + i)
  change 2 * (∏ i ∈ range (k + 2), f i) ≤ ∏ i ∈ range (k + 3), g i
  rw [prod_range_succ g (k + 2), mul_comm 2]
  apply Nat.mul_le_mul
  · exact prod_le_prod (by simp) fun i _ =>
      (Nat.nth_monotone Nat.infinite_setOfPred_prime) (by omega)
  · exact (primeAt_prime _).two_le

private theorem a_block (k : ℕ) : a (k + 2) = block k - a (k + 1) := rfl

private theorem block_odd (k : ℕ) : Odd (block (k + 1)) := by
  rw [block_range]
  have hterm (i : ℕ) : Odd (primeAt ((triangular (k + 2) - 1) + i)) := by
    apply (primeAt_prime _).odd_of_ne_two
    have htri := triangular_ge (k + 2)
    have hpos : 0 < (triangular (k + 2) - 1) + i := by omega
    have hh := Nat.nth_strictMono Nat.infinite_setOfPred_prime hpos
    rw [Nat.nth_prime_zero_eq_two] at hh
    exact ne_of_gt hh
  have hall (s : Finset ℕ) : Odd (∏ i ∈ s, primeAt ((triangular (k + 2) - 1) + i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [prod_insert hi]; exact (hterm i).mul ih
  exact hall _

private theorem a_sum_block (k : ℕ) : a (k + 3) + a (k + 2) = block (k + 1) := by
  change block (k + 1) - a (k + 2) + a (k + 2) = block (k + 1)
  apply Nat.sub_add_cancel
  have h1 : a (k + 2) ≤ block k := by rw [a_block]; exact Nat.sub_le _ _
  have h2 := block_double k
  omega

theorem a_mod_two (k : ℕ) : a (k + 2) % 2 = (k + 1) % 2 := by
  induction k with
  | zero => rw [a_2]
  | succ k ih =>
    change a (k + 3) % 2 = (k + 2) % 2
    have hs := a_sum_block k
    have ho := (Nat.odd_iff.mp (block_odd k))
    omega

theorem prime_index_even {n : ℕ} (hn : 2 < n) (hp : (a n).Prime) : Even n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hsize : 2 < a (k + 3) := by
    have h1 : a (k + 2) ≤ block k := by rw [a_block]; exact Nat.sub_le _ _
    have h2 := block_double k
    have h3 := block_large k
    have hs := a_sum_block k
    omega
  have ha := Nat.odd_iff.mp (hp.odd_of_ne_two (ne_of_gt hsize))
  have hmod := a_mod_two (k + 1)
  change a (k + 3) % 2 = (k + 2) % 2 at hmod
  exact Nat.even_iff.mpr (by omega)

end A100474Parity

#print axioms A100474Parity.prime_index_even
