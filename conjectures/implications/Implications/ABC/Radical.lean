import Implications.ABC.Statement

/-!
# Facts about `ABC.radical` used by the abc consequences

* `radical_mul`: the radical is multiplicative on coprime arguments.
* `radical_sq_dvd_of_powerful`: for a powerful `n`, `rad(n)² ∣ n`.
* `radical_le_four_pow`: if every prime factor of `n` is at most `B`, then `rad(n) ≤ 4^B`
  (through `primorial_le_four_pow`).
* `mem_abc_of_cube_lt_sq`: an admissible triple with `rad(abc)³ < c²` is in the exceptional set
  of `ABC.ABCConjecture` at `ε = 1/2`.
* `eventually_of_abc`: the shape of argument used for Erdős 936. A finite exceptional set bounds
  `c`, so a family with `n ≤ c n` leaves it eventually.
-/

namespace Implications.Abc

open _root_.ABC Finset

lemma radical_pos (n : ℕ) : 0 < radical n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma radical_one : radical 1 = 1 := by simp [radical]

lemma radical_mul {a b : ℕ} (h : Nat.Coprime a b) : radical (a * b) = radical a * radical b := by
  unfold radical
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]

lemma radical_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : radical (p ^ k) = p := by
  simp [radical, Nat.primeFactors_prime_pow hk hp]

lemma radical_sq_dvd_of_powerful {n : ℕ} (hn : n ≠ 0) (h : n.Powerful) : radical n ^ 2 ∣ n := by
  unfold radical
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact pow_dvd_pow _ ((hpp.pow_dvd_iff_le_factorization hn).1 (h p hp))

lemma radical_sq_le_of_powerful {n : ℕ} (hn : n ≠ 0) (h : n.Powerful) : radical n ^ 2 ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (radical_sq_dvd_of_powerful hn h)

lemma radical_le_four_pow {n B : ℕ} (h : ∀ p ∈ n.primeFactors, p ≤ B) : radical n ≤ 4 ^ B := by
  refine le_trans ?_ (primorial_le_four_pow B)
  rw [primorial_eq_prod_primesLE]
  unfold radical
  refine Nat.le_of_dvd (Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primesLE hp).pos)
    (Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_)
  exact Nat.mem_primesLE.2 ⟨h p hp, Nat.prime_of_mem_primeFactors hp⟩

lemma radical_factorial_le (n : ℕ) : radical n.factorial ≤ 4 ^ n :=
  radical_le_four_pow fun _ hp =>
    (Nat.Prime.dvd_factorial (Nat.prime_of_mem_primeFactors hp)).1 (Nat.dvd_of_mem_primeFactors hp)

lemma pairwise_coprime_triple {a b c : ℕ} (hab : Nat.Coprime a b) (hac : Nat.Coprime a c)
    (hbc : Nat.Coprime b c) : ({a, b, c} : Set ℕ).Pairwise Nat.Coprime := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | assumption
    | exact Nat.Coprime.symm ‹_›

lemma coprime_pred_self {m : ℕ} (hm : 0 < m) : Nat.Coprime (m - 1) m := by
  have : m = (m - 1) + 1 := by omega
  conv_rhs => rw [this]
  exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)

lemma coprime_self_succ (m : ℕ) : Nat.Coprime m (m + 1) :=
  Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)

/-- The exceptional set of `ABC.ABCConjecture` at a given `ε`. -/
def abcSet (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}

lemma abcSet_finite (habc : ABCConjecture) {ε : ℝ} (hε : 0 < ε) : (abcSet ε).Finite :=
  habc ε hε

/-- `x^(3/2) < c` follows from `x³ < c²`. -/
lemma rpow_three_halves_lt {x c : ℕ} (h : x ^ 3 < c ^ 2) :
    ((x : ℝ)) ^ (1 + (1 / 2 : ℝ)) < c := by
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy : (0 : ℝ) ≤ (x : ℝ) ^ (1 + (1 / 2 : ℝ)) := Real.rpow_nonneg hx _
  have hsq : ((x : ℝ) ^ (1 + (1 / 2 : ℝ))) ^ 2 = (x : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have h' : ((x : ℝ) ^ (1 + (1 / 2 : ℝ))) ^ 2 < (c : ℝ) ^ 2 := by
    rw [hsq]; exact_mod_cast h
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg c) h'

lemma mem_abcSet_of_cube_lt_sq {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) (hsum : a + b = c)
    (h : radical (a * b * c) ^ 3 < c ^ 2) : (a, b, c) ∈ abcSet (1 / 2) :=
  ⟨ha, hb, by omega, pairwise_coprime_triple hab hac hbc, hsum, rpow_three_halves_lt h⟩

/-- A finite exceptional set bounds the third coordinate. -/
lemma eventually_of_abcSet_finite {ε : ℝ} (hfin : (abcSet ε).Finite) (P : ℕ → Prop)
    (t : ℕ → ℕ × ℕ × ℕ) (N₀ : ℕ) (hmem : ∀ n ≥ N₀, P n → t n ∈ abcSet ε)
    (hc : ∀ n, n ≤ (t n).2.2) : ∀ᶠ n in Filter.atTop, ¬ P n := by
  obtain ⟨M, hM⟩ := (hfin.image fun x => x.2.2).bddAbove
  refine Filter.eventually_atTop.2 ⟨max N₀ (M + 1), fun n hn hP => ?_⟩
  have h1 : (t n).2.2 ≤ M := hM ⟨t n, hmem n (le_of_max_le_left hn) hP, rfl⟩
  have h2 := hc n
  have h3 := le_of_max_le_right hn
  omega

/-- Arithmetic core for 936: if `r² ≤ c` and `64 < c` then `(2r)³ < c²`. -/
lemma two_mul_cube_lt_sq {r c : ℕ} (hr : r ^ 2 ≤ c) (hc : 64 < c) : (2 * r) ^ 3 < c ^ 2 := by
  -- (8 r³)² = 64 r⁶ ≤ 64 c³ < c⁴
  have h6 : (r ^ 2) ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hr 3
  have : ((2 * r) ^ 3) ^ 2 < (c ^ 2) ^ 2 := by
    have e1 : ((2 * r) ^ 3) ^ 2 = 64 * (r ^ 2) ^ 3 := by ring
    have e2 : (c ^ 2) ^ 2 = c * c ^ 3 := by ring
    rw [e1, e2]
    have hc3 : 0 < c ^ 3 := by positivity
    calc 64 * (r ^ 2) ^ 3 ≤ 64 * c ^ 3 := Nat.mul_le_mul_left _ h6
      _ < c * c ^ 3 := Nat.mul_lt_mul_of_pos_right hc hc3
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this

/-- Arithmetic core for the factorial cases: if `r² ≤ c` and `(4^n)^6 < c` then
`(4^n r)³ < c²`. -/
lemma four_pow_mul_cube_lt_sq {r c n : ℕ} (hr : r ^ 2 ≤ c) (hc : (4 ^ n) ^ 6 < c) :
    (4 ^ n * r) ^ 3 < c ^ 2 := by
  have h6 : (r ^ 2) ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hr 3
  have : ((4 ^ n * r) ^ 3) ^ 2 < (c ^ 2) ^ 2 := by
    have e1 : ((4 ^ n * r) ^ 3) ^ 2 = (4 ^ n) ^ 6 * (r ^ 2) ^ 3 := by ring
    have e2 : (c ^ 2) ^ 2 = c * c ^ 3 := by ring
    rw [e1, e2]
    have hc3 : 0 < c ^ 3 := by
      have : 0 < c := lt_of_le_of_lt (Nat.zero_le _) hc
      positivity
    calc (4 ^ n) ^ 6 * (r ^ 2) ^ 3 ≤ (4 ^ n) ^ 6 * c ^ 3 := Nat.mul_le_mul_left _ h6
      _ < c * c ^ 3 := Nat.mul_lt_mul_of_pos_right hc hc3
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this

/-- `K^n < n!` for all large `n`. -/
lemma eventually_pow_lt_factorial (K : ℕ) : ∀ᶠ n in Filter.atTop, K ^ n < n.factorial := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (K : ℝ)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [h] with n hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_lt_one hf] at hn
  exact_mod_cast hn

end Implications.Abc
