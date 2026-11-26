import Implications.Dickson.Linear

/-!
# Erdős Problem 647, windowed variant, from Dickson's conjecture

Source: `FormalConjectures/ErdosProblems/647.lean`, `Erdos647.erdos_647.variants.infinite`,
formal-conjectures `9097e2f` (research open). The conclusion below is verbatim:
for every `k` there are infinitely many `n` with `m + τ(m) ≤ n + 2` for all `n - k < m < n`.

Erdős [Er79d] (as quoted on erdosproblems.com/647) says this "seems certain"; erdosproblems.com
says it would follow from Schinzel's hypothesis H. No proof is written in the formal-conjectures
file, and the construction below is ours.

Take `L = k!` and the forms `(L/j) X - 1` for `1 ≤ j < k`. Their constant term is `-1`, so they
meet the Schinzel condition at `X = 0`, and Dickson gives infinitely many `t` with every
`q_j = (L/j) t - 1` prime. Keep `t > k`. For `n = L t` and `n - k < m < n`, put `j = n - m`, so
`1 ≤ j < k` and `m = j q_j`. As `q_j ≥ t - 1 ≥ k > j`, `q_j ∤ j`, so `τ(m) = 2 τ(j)`, and
`τ(j) ≤ j/2 + 1` because every divisor of `j` other than `j` is at most `j/2`. Hence
`m + τ(m) ≤ m + j + 2 = n + 2`.
-/

open Polynomial

namespace Implications.Dickson

open Finset

/-- `2 τ(j) ≤ j + 2` for `j ≥ 1`: every divisor of `j` other than `j` is at most `j / 2`. -/
theorem two_mul_card_divisors_le (j : ℕ) (hj : 0 < j) : 2 * j.divisors.card ≤ j + 2 := by
  have hsub : j.divisors ⊆ insert j (Icc 1 (j / 2)) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨e, he⟩, -⟩ := hd
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e
      · omega
      · simp [he]
    · apply mem_insert_of_mem
      rw [mem_Icc]
      have hd0 : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · subst h0; omega
        · exact h0
      refine ⟨hd0, ?_⟩
      rw [Nat.le_div_iff_mul_le two_pos]
      calc d * 2 ≤ d * e := Nat.mul_le_mul_left d h
        _ = j := he.symm
  have := (card_le_card hsub).trans (card_insert_le _ _)
  simp only [Nat.card_Icc] at this
  omega

theorem card_divisors_mul_prime (j q : ℕ) (hq : q.Prime) (hqj : j < q) :
    (j * q).divisors.card = 2 * j.divisors.card := by
  have hcop : j.Coprime q :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr
      (fun h => by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          omega
        · exact absurd (Nat.le_of_dvd h0 h) (by omega)))
  rw [Nat.Coprime.card_divisors_mul hcop, hq.divisors, card_pair hq.one_lt.ne, mul_comm]

open Filter ArithmeticFunction.sigma in
/-- Source: `FormalConjectures/ErdosProblems/647.lean`, `Erdos647.erdos_647.variants.infinite`,
formal-conjectures `9097e2f` (research open); conclusion verbatim, under Dickson's conjecture. -/
theorem erdos_647_variants_infinite_of_dickson (hdickson : DicksonConjecture) :
    ∀ k, { n | ⨆ m : Set.Ioo (n - k) n, ↑m + σ 0 m ≤ n + 2 }.Infinite := by
  intro k
  set L := k.factorial with hL
  have hL0 : 0 < L := Nat.factorial_pos k
  have hdvd : ∀ j, 1 ≤ j → j < k → j ∣ L := fun j h1 h2 => Nat.dvd_factorial h1 h2.le
  have hLj : ∀ j, 1 ≤ j → j < k → 0 < L / j := fun j h1 h2 =>
    Nat.div_pos (Nat.le_of_dvd hL0 (hdvd j h1 h2)) h1
  let fs : Finset ℤ[X] := (Ico 1 k).image (fun j => C ((L / j : ℕ) : ℤ) * X + C (-1))
  have H := hdickson fs ?_ ?_
  · rw [Set.infinite_coe_iff] at H
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨t, ht, hta⟩ := H.exists_gt (a + k)
    have htL : t ≤ L * t := Nat.le_mul_of_pos_left t hL0
    refine ⟨L * t, ?_, by omega⟩
    show ⨆ m : Set.Ioo (L * t - k) (L * t), (↑m + σ 0 ↑m) ≤ L * t + 2
    apply ciSup_le'
    rintro ⟨m, hm1, hm2⟩
    obtain ⟨j, hjm⟩ : ∃ j, m + j = L * t := ⟨L * t - m, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hjk : j < k := by omega
    have hLj' := hLj j hj1 hjk
    have hq := ht (C ((L / j : ℕ) : ℤ) * X + C (-1)) (mem_image_of_mem _ (mem_Ico.mpr ⟨hj1, hjk⟩))
    simp only [eval_add, eval_mul, eval_C, eval_X] at hq
    have hpos : 1 ≤ L / j * t := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [show ((L / j : ℕ) : ℤ) * (t : ℤ) + -1 = ((L / j * t - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hpos]; ring, Int.natAbs_natCast] at hq
    have hqt : t ≤ L / j * t := Nat.le_mul_of_pos_left t hLj'
    have hmq : m = j * (L / j * t - 1) := by
      rw [Nat.mul_sub, ← mul_assoc, Nat.mul_div_cancel' (hdvd j hj1 hjk)]
      omega
    simp only [ArithmeticFunction.sigma_zero_apply]
    rw [hmq, card_divisors_mul_prime j _ hq (by omega)]
    have := two_mul_card_divisors_le j (by omega)
    rw [← hmq]
    omega
  · intro f hf
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hf
    rw [mem_Ico] at hj
    exact linear_degree_bunyakovsky (by exact_mod_cast hLj j hj.1 hj.2)
      (isUnit_neg_one.isRelPrime_left)
  · intro p hp
    refine ⟨0, ?_⟩
    intro f hf
    obtain ⟨j, -, rfl⟩ := mem_image.mp hf
    simp only [eval_add, eval_mul, eval_C, eval_X, Nat.cast_zero, mul_zero, zero_add]
    intro h
    have : (p : ℤ) ∣ 1 := by simpa using h
    exact hp.ne_one (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

end Implications.Dickson
