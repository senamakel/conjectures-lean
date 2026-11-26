import Implications.ABC.Radical

/-!
# The abc conjecture and its constant and quality forms

formal-conjectures (`FormalConjectures/Wikipedia/ABC.lean`, commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, Apache-2.0) states abc in three ways:
`ABC.abc` (copied as `ABC.ABCConjecture` in `Implications.ABC.Statement`),
`ABC.abc.variants.lt_constant_mul` and `ABC.abc.variants.quality`. All three are open there and
no implication between them is proved. This module proves that the three are equivalent.

* `abcConstantMul_of_abc`: take `K = 1 + max c` over the finite exceptional set.
* `abc_of_abcConstantMul`: use the constant form at `ε/2`. An exceptional triple has
  `rad^(1+ε) < c < K rad^(1+ε/2)`, so `rad^(ε/2) < K`; this bounds `rad`, then `c`, then `a, b`.
* `abcQuality_iff_abc`: the two exceptional sets are equal for every `ε`, because
  `rad(abc) ≥ 2` for an admissible triple (`c = a + b ≥ 2`), so `log rad > 0`.

The module also holds the toolkit the other abc modules use: `rad(n)^k ≤ n` for a `k`-full `n`,
`rad(ab) ≤ rad a · rad b`, and `mem_abcSet_of_pow_lt` (an admissible triple with
`rad(abc)^(k+1) < c^k` is exceptional at `ε = 1/k`), with `finite_of_abc` to turn it into a
finiteness statement.
-/

namespace ABC

/-- Copied verbatim from `FormalConjectures/Wikipedia/ABC.lean`, `ABC.quality`.

Quality `q(a, b, c)` of the triple `(a, b, c)` is defined as `q(a,b,c) = log (c) / log (rad(abc))`.
-/
noncomputable def quality (a b c : ℕ) : ℝ := (c : ℝ).log / (radical <| a * b * c : ℝ).log

/-- `ABC.abc.variants.lt_constant_mul` (`FormalConjectures/Wikipedia/ABC.lean`), statement
verbatim:
For every positive real number ε, there exists a constant `K_ε` such that for all triples (a, b, c)
of coprime positive integers, with a + b = c we have `c < K_ε rad(abc)^(1+ε)`. -/
def ABCConstantMul : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ K,
    ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime → a + b = c →
    c < K * (radical <| a * b * c : ℝ)^(1 + ε)

/-- `ABC.abc.variants.quality` (`FormalConjectures/Wikipedia/ABC.lean`), statement verbatim:
For every positive real number ε, there exist only finitely many triples `(a, b, c)` of coprime
positive integers with `a + b = c` such that `q(a, b, c) > 1 + ε`. -/
def ABCQuality : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε),
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ quality a b c > (1 + ε)}.Finite

end ABC

namespace Implications.Abc

open _root_.ABC

/-! ### Radical toolkit -/

lemma one_le_radical (n : ℕ) : 1 ≤ radical n := radical_pos n

lemma radical_pow {m k : ℕ} (hk : k ≠ 0) : radical (m ^ k) = radical m := by
  simp [radical, Nat.primeFactors_pow _ hk]

lemma radical_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    radical (a * b) ≤ radical a * radical b := by
  refine Nat.le_of_dvd (Nat.mul_pos (radical_pos a) (radical_pos b)) ?_
  unfold radical
  rw [Nat.primeFactors_mul ha hb]
  exact Dvd.intro _ Finset.prod_union_inter

lemma two_le_radical {n : ℕ} (hn : 2 ≤ n) : 2 ≤ radical n := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 (by omega : 1 < n)
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact hpp.two_le.trans (Nat.le_of_dvd (radical_pos n) (Finset.dvd_prod_of_mem id hp))

/-- For a `k`-full `n ≠ 0`, `rad(n)^k ∣ n`. -/
lemma radical_pow_dvd_of_full {n k : ℕ} (hn : n ≠ 0) (h : (k).Full n) : radical n ^ k ∣ n := by
  unfold radical
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact pow_dvd_pow _ ((hpp.pow_dvd_iff_le_factorization hn).1 (h p hp))

lemma radical_pow_le_of_full {n k : ℕ} (hn : n ≠ 0) (h : (k).Full n) : radical n ^ k ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (radical_pow_dvd_of_full hn h)

/-- A nonzero square is powerful. -/
lemma powerful_sq (m : ℕ) : (m ^ 2).Powerful := by
  intro p hp
  have hpm : p ∣ m := (Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow
    (Nat.dvd_of_mem_primeFactors hp)
  exact pow_dvd_pow_of_dvd hpm 2

/-! ### Entering the exceptional set at `ε = 1/k` -/

/-- `x^(1 + 1/k) < c` follows from `x^(k+1) < c^k`. -/
lemma rpow_one_add_inv_lt {x c k : ℕ} (hk : 0 < k) (h : x ^ (k + 1) < c ^ k) :
    ((x : ℝ)) ^ (1 + 1 / (k : ℝ)) < c := by
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpow : ((x : ℝ) ^ (1 + 1 / (k : ℝ))) ^ k = (x : ℝ) ^ (k + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast]
    congr 1
    field_simp
    push_cast
    ring
  have h' : ((x : ℝ) ^ (1 + 1 / (k : ℝ))) ^ k < (c : ℝ) ^ k := by
    rw [hpow]; exact_mod_cast h
  exact lt_of_pow_lt_pow_left₀ k (Nat.cast_nonneg c) h'

/-- An admissible triple with `rad(abc) ≤ X` and `X^(k+1) < c^k` is exceptional at `ε = 1/k`. -/
lemma mem_abcSet_of_pow_lt {a b c X k : ℕ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) (hsum : a + b = c)
    (hX : radical (a * b * c) ≤ X) (h : X ^ (k + 1) < c ^ k) :
    (a, b, c) ∈ abcSet (1 / (k : ℝ)) :=
  ⟨ha, hb, by omega, pairwise_coprime_triple hab hac hbc, hsum,
    rpow_one_add_inv_lt hk (lt_of_le_of_lt (Nat.pow_le_pow_left hX _) h)⟩

/-- Finiteness form of `eventually_of_abcSet_finite`. -/
lemma finite_of_abc (habc : ABCConjecture) {ε : ℝ} (hε : 0 < ε) (P : ℕ → Prop)
    (t : ℕ → ℕ × ℕ × ℕ) (N₀ : ℕ) (hmem : ∀ n ≥ N₀, P n → t n ∈ abcSet ε)
    (hc : ∀ n, n ≤ (t n).2.2) : {n | P n}.Finite := by
  have hev := eventually_of_abcSet_finite (abcSet_finite habc hε) P t N₀ hmem hc
  by_contra hinf
  exact (Nat.frequently_atTop_iff_infinite.2 hinf) hev

/-! ### The three forms are equivalent -/

/-- abc implies its constant form `ABC.abc.variants.lt_constant_mul`. -/
theorem abcConstantMul_of_abc (habc : ABCConjecture) : ABCConstantMul := by
  intro ε hε
  obtain ⟨M, hM⟩ := ((habc ε hε).image fun x => x.2.2).bddAbove
  refine ⟨(M : ℝ) + 1, fun a b c ha hb hc hcop hsum => ?_⟩
  set r : ℝ := (radical (a * b * c) : ℝ) ^ (1 + ε)
  have hr : (1 : ℝ) ≤ r :=
    Real.one_le_rpow (by exact_mod_cast one_le_radical _) (by linarith)
  by_cases hmem : r < c
  · have hcM : c ≤ M := hM ⟨(a, b, c), ⟨ha, hb, hc, hcop, hsum, hmem⟩, rfl⟩
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc (c : ℝ) ≤ M := by exact_mod_cast hcM
      _ < (M : ℝ) + 1 := by linarith
      _ ≤ ((M : ℝ) + 1) * r := le_mul_of_one_le_right (by linarith) hr
  · push Not at hmem
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    calc (c : ℝ) ≤ r := hmem
      _ < ((M : ℝ) + 1) * r := by nlinarith

/-- The constant form `ABC.abc.variants.lt_constant_mul` implies abc. -/
theorem abc_of_abcConstantMul (hK : ABCConstantMul) : ABCConjecture := by
  intro ε hε
  obtain ⟨K, hK⟩ := hK (ε / 2) (by linarith)
  -- the bound on `rad` and on `c`
  set R : ℝ := K ^ (2 / ε)
  set B : ℝ := K * R ^ (1 + ε / 2)
  refine (((Set.finite_Iic ⌈B⌉₊).prod (Set.finite_Iic ⌈B⌉₊)).prod
    (Set.finite_Iic ⌈B⌉₊) |>.image fun x : (ℕ × ℕ) × ℕ => (x.1.1, x.1.2, x.2)).subset ?_
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hcop, hsum, hlt⟩
  have hup := hK a b c ha hb hc hcop hsum
  set r : ℝ := (radical (a * b * c) : ℝ)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast one_le_radical _
  have hr0 : (0 : ℝ) < r := by linarith
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]; ring_nf
  have hpos : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  -- `r^(ε/2) < K`
  have hrK : r ^ (ε / 2) < K := by
    have : r ^ (1 + ε / 2) * r ^ (ε / 2) < K * r ^ (1 + ε / 2) := by
      rw [← hsplit]; exact hlt.trans hup
    nlinarith
  have hK0 : 0 < K := lt_of_le_of_lt (Real.rpow_nonneg hr0.le _) hrK
  -- `r < R`
  have hrR : r < R := by
    have h1 : (r ^ (ε / 2)) ^ (2 / ε) < K ^ (2 / ε) :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hr0.le _) hrK (by positivity)
    rwa [← Real.rpow_mul hr0.le, show ε / 2 * (2 / ε) = 1 by field_simp, Real.rpow_one] at h1
  have hcB : (c : ℝ) < B := by
    calc (c : ℝ) < K * r ^ (1 + ε / 2) := hup
      _ ≤ K * R ^ (1 + ε / 2) := by
        gcongr
  have hcN : c ≤ ⌈B⌉₊ := by
    have := Nat.le_ceil B
    exact_mod_cast (hcB.le.trans this)
  refine ⟨((a, b), c), ⟨⟨?_, ?_⟩, hcN⟩, rfl⟩ <;> simp only [Set.mem_Iic] <;> omega

/-- abc is equivalent to its constant form. -/
theorem abc_iff_abcConstantMul : ABCConjecture ↔ ABCConstantMul :=
  ⟨abcConstantMul_of_abc, abc_of_abcConstantMul⟩

/-- For an admissible triple, `q(a, b, c) > 1 + ε` iff `rad(abc)^(1+ε) < c`. -/
lemma quality_gt_iff {a b c : ℕ} {ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hsum : a + b = c) :
    quality a b c > 1 + ε ↔ (radical (a * b * c) : ℝ) ^ (1 + ε) < c := by
  have hr2 : 2 ≤ radical (a * b * c) := two_le_radical (by
    have : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc 2 ≤ c := by omega
      _ = 1 * c := (one_mul c).symm
      _ ≤ a * b * c := Nat.mul_le_mul_right _ this)
  set r : ℝ := (radical (a * b * c) : ℝ)
  have hr : (1 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    linarith
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  unfold quality
  rw [gt_iff_lt, lt_div_iff₀ hlogr, ← Real.log_rpow (by linarith),
    Real.log_lt_log_iff (Real.rpow_pos_of_pos (by linarith) _) hc0]

/-- abc is equivalent to its quality form `ABC.abc.variants.quality`: for every `ε` the two
exceptional sets coincide. -/
theorem abcQuality_iff_abc : ABCQuality ↔ ABCConjecture := by
  have hset : ∀ ε : ℝ,
      {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
        a + b = c ∧ quality a b c > (1 + ε)} =
      {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
        a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c} := by
    intro ε
    ext ⟨a, b, c⟩
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨ha, hb, hc, hcop, hsum, hq⟩
      exact ⟨ha, hb, hc, hcop, hsum, (quality_gt_iff ha hb hsum).1 hq⟩
    · rintro ⟨ha, hb, hc, hcop, hsum, hq⟩
      exact ⟨ha, hb, hc, hcop, hsum, (quality_gt_iff ha hb hsum).2 hq⟩
  constructor
  · intro h ε hε; rw [← hset]; exact h ε hε
  · intro h ε hε; rw [hset]; exact h ε hε

/-- The constant form is equivalent to the quality form. -/
theorem abcConstantMul_iff_abcQuality : ABCConstantMul ↔ ABCQuality :=
  abc_iff_abcConstantMul.symm.trans abcQuality_iff_abc.symm

end Implications.Abc
