import Implications.ABC.Radical

/-!
# Erdős 977, factorial variant, under the abc conjecture

`erdos_977.variants.factorial` of formal-conjectures (`FormalConjectures/ErdosProblems/977.lean`,
commit `9097e2f`): `P(n! + 1) / n → ∞`, where `P(m)` is the largest prime factor of `m`.

Deduction (after Murty–Wong 2002, who get the sharper `P(n!+1) > (1 + o(1)) n log n`; we prove
only what the formal statement asks). Apply `ABC.ABCConjecture` at `ε = 1` to `(1, n!, n! + 1)`.
For all but finitely many `n` the triple is not exceptional, so
`n! + 1 ≤ rad(n! (n! + 1))² ≤ (4^n · 4^P)² = 16^(n + P)`, with `P = P(n! + 1)`, using
`rad(n!) ≤ 4^n` (primorial bound) and `rad(m) ≤ 4^{P(m)}` (every prime factor of `m` is at most
`P(m)`). If `P < K n` this gives `n! < (16^(K+1))^n`, false for large `n`. So `P ≥ K n`
eventually, for every `K`.
-/

namespace Implications.Abc

open _root_.ABC Erdos977 Nat Filter

/-- `rad(m) ≤ 4^{P(m)}` for `m ≠ 0`. -/
lemma radical_le_four_pow_maxPrimeFac {m : ℕ} (hm : m ≠ 0) : radical m ≤ 4 ^ m.maxPrimeFac :=
  radical_le_four_pow fun _ hp =>
    Nat.le_maxPrimeFac hm (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- Under abc, `n! + 1 ≤ 16^(n + P(n! + 1))` for all large `n`. -/
lemma eventually_factorial_succ_le (habc : ABCConjecture) :
    ∀ᶠ n in atTop, n ! + 1 ≤ 16 ^ (n + (n ! + 1).maxPrimeFac) := by
  obtain ⟨M, hM⟩ := ((abcSet_finite habc (by norm_num : (0 : ℝ) < 1)).image
    fun x => x.2.2).bddAbove
  refine eventually_atTop.2 ⟨M + 1, fun n hn => ?_⟩
  have hnot : (1, n !, n ! + 1) ∉ abcSet 1 := fun hmem => by
    have : n ! + 1 ≤ M := hM ⟨_, hmem, rfl⟩
    have := Nat.self_le_factorial n
    omega
  have hle : ((n ! + 1 : ℕ) : ℝ) ≤ (radical (1 * n ! * (n ! + 1)) : ℝ) ^ (1 + (1 : ℝ)) := by
    by_contra hlt
    exact hnot ⟨Nat.one_pos, Nat.factorial_pos n, by omega,
      pairwise_coprime_triple (Nat.coprime_one_left _) (Nat.coprime_one_left _)
        (coprime_self_succ _), by ring, lt_of_not_ge hlt⟩
  rw [show (1 + (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hle
  have hle' : n ! + 1 ≤ radical (1 * n ! * (n ! + 1)) ^ 2 := by exact_mod_cast hle
  have hrad : radical (1 * n ! * (n ! + 1)) ≤ 4 ^ n * 4 ^ (n ! + 1).maxPrimeFac := by
    rw [one_mul, radical_mul (coprime_self_succ _)]
    exact Nat.mul_le_mul (radical_factorial_le n) (radical_le_four_pow_maxPrimeFac (by omega))
  calc n ! + 1 ≤ radical (1 * n ! * (n ! + 1)) ^ 2 := hle'
    _ ≤ (4 ^ n * 4 ^ (n ! + 1).maxPrimeFac) ^ 2 := Nat.pow_le_pow_left hrad 2
    _ = 16 ^ (n + (n ! + 1).maxPrimeFac) := by
      rw [← pow_add, ← pow_mul, show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, mul_comm]

/-- Under abc, `P(n! + 1) ≥ K n` for all large `n`, for every `K`. -/
lemma eventually_mul_le_maxPrimeFac (habc : ABCConjecture) (K : ℕ) :
    ∀ᶠ n in atTop, K * n ≤ (n ! + 1).maxPrimeFac := by
  filter_upwards [eventually_factorial_succ_le habc, eventually_pow_lt_factorial (16 ^ (K + 1))]
    with n h1 h2
  by_contra hlt
  push Not at hlt
  have : 16 ^ (n + (n ! + 1).maxPrimeFac) ≤ (16 ^ (K + 1)) ^ n := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega

/-- abc implies `erdos_977.variants.factorial`. -/
theorem erdos_977_factorial_of_abc (habc : ABCConjecture) : Erdos977.Factorial := by
  unfold Erdos977.Factorial
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_mul_le_maxPrimeFac habc ⌈b⌉₊, eventually_ge_atTop 1] with n h hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  calc b * n ≤ (⌈b⌉₊ : ℝ) * n := by gcongr; exact Nat.le_ceil b
    _ ≤ _ := by exact_mod_cast h

/-- The same, stated with formal-conjectures' own `Nat.maxPrimeFac` (copied as
`Erdos977.fcMaxPrimeFac`). -/
theorem erdos_977_factorial_of_abc' (habc : ABCConjecture) :
    Tendsto (fun n : ℕ ↦ (fcMaxPrimeFac (n.factorial + 1) : ℝ) / n) atTop atTop := by
  simp only [fcMaxPrimeFac_eq]
  exact erdos_977_factorial_of_abc habc

end Implications.Abc
