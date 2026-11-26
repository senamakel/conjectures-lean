import Artin.Kummer.Conductor

/-!
# Positivity of the Artin density (blueprint step B6)

`kummerDensity a = ∑ₖ μ(k) / [K_k : ℚ]` is the density that Hooley's sieve produces. For `a` not a
perfect power we prove that the series converges absolutely and that its sum is positive.

Write `w(k) = 1 / (k φ(k)) = ∏_{p ∣ k} 1 / (p (p - 1))` for squarefree `k`. By
`kummerDegree_mul_kummerEps`, `μ(k) / [K_k : ℚ] = μ(k) ε(k) w(k)` with `ε(k) ∈ {1, 2}`, `ε(k) = 1`
for odd `k` and `ε(2) = 1`. Pairing `k = j` with `k = 2j` for odd squarefree `j` gives
`μ(j) w(j) (1 - ε(2j)/2)`, which is `1/2` at `j = 1` and at least `-w(j)/2` otherwise. Since
`∑_{j odd squarefree, j > 1} w(j) ≤ ∏_{p ≥ 3} (1 + 1/(p(p-1))) - 1 ≤ e^{1/2} - 1 < 1`, the sum is
positive. No information about the conductor of `ℚ(√a)` is needed for positivity.

**General `a` (perfect powers included).** `kummerDensity_pos_of_not_isSquare` proves `δ(a) > 0`
for every `a` that is not a square and not `-1`. The crude bound above fails once `a = ± b^h` with
`h` divisible by several small odd primes, so this uses the exact degree
`[K_k : ℚ] m(k) = k φ(k)` (`kummerDegree_mul_kummerM`) and the conductor of `ℚ(√a)`
(`exists_sq_cyclotomicField_iff`). For squarefree `k`,
`μ(k) / [K_k : ℚ] = ε(k) ∏_{q ∣ k} (-x_q)` with `x_q = m_q / (q (q - 1))`, `m_q = q` if `a` is a
`q`-th power in `ℤ` and `1` otherwise (`moebius_div_kummerDegree_eq_prod`). Pairing `j` with `2j`
gives `δ(a) = ½ ∑_j g(j)`, where `g(j) = h(j) = ∏_{q ∣ j} (-x_q)` on odd squarefree `j`, except
that `g(j) = 0` when `a₀ ≡ 1 (mod 4)` and `D = |a₀| ∣ j` (`a = a₀ c²`, `a₀` squarefree). Removing
the finitely many primes `q` with `x_q ≠ 1/(q(q-1))` one at a time (`coprimeSum_hw_peel`) and the
multiples of `D` (`tsum_dvd_hw`) writes `∑ g` as
`∏ (1 - x_q) · (∏_{q ∣ D} (1 - x_q) - h(D)) · ∑_{(j, M) = 1} μ(j) w(j)`; every `x_q ≤ 1/2` with
equality only at `q = 3` (`dfactor_pos`), and the last sum is positive by the crude bound
(`coprimeSum_hw_pos`).
-/

namespace Artin.Kummer

open ArithmeticFunction Finset

/-! ### Euler-product bounds for `∑ 1/(k φ(k))` over squarefree `k` -/

/-- `w(k) = ∏_{p ∣ k} 1/(p(p-1))` for squarefree `k`, and `0` otherwise. -/
noncomputable def sqfreeWeight (k : ℕ) : ℝ :=
  if Squarefree k then ∏ p ∈ k.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ else 0

lemma inv_mul_pred_nonneg {p : ℕ} (hp : 1 ≤ p) : 0 ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact inv_nonneg.2 (mul_nonneg (by linarith) (by linarith))

lemma sqfreeWeight_nonneg (k : ℕ) : 0 ≤ sqfreeWeight k := by
  unfold sqfreeWeight
  split_ifs
  · exact prod_nonneg fun p hp => inv_mul_pred_nonneg (Nat.prime_of_mem_primeFactors hp).one_le
  · exact le_rfl

lemma sqfreeWeight_one : sqfreeWeight 1 = 1 := by simp [sqfreeWeight]

/-- `w(k) = 1/(k φ(k))` for squarefree `k`. -/
lemma sqfreeWeight_eq {k : ℕ} (hk : Squarefree k) :
    sqfreeWeight k = ((k : ℝ) * k.totient)⁻¹ := by
  have hk0 : k ≠ 0 := hk.ne_zero
  have hprod := Nat.prod_primeFactors_of_squarefree hk
  have htot : k.totient = ∏ p ∈ k.primeFactors, (p - 1) := by
    have h := Nat.totient_mul_prod_primeFactors k
    rw [hprod] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hk0) (by rw [h, mul_comm])
  have e1 : (k : ℝ) = ∏ p ∈ k.primeFactors, (p : ℝ) := by rw [← Nat.cast_prod, hprod]
  have e2 : (k.totient : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    rw [htot, Nat.cast_prod]
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  simp only [sqfreeWeight, hk, ↓reduceIte]
  rw [e1, e2, ← prod_mul_distrib, prod_inv_distrib]

/-- Expanding `∏_{p ∈ P} (1 + x_p)` dominates any sum of `∏_{p ∣ k} x_p` over distinct squarefree
`k` supported on `P`. -/
lemma sum_prod_le_prod_one_add {s P : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ p, 0 ≤ x p)
    (hs : ∀ k ∈ s, Squarefree k ∧ k.primeFactors ⊆ P) :
    ∑ k ∈ s, ∏ p ∈ k.primeFactors, x p ≤ ∏ p ∈ P, (1 + x p) := by
  rw [prod_one_add]
  have hinj : Set.InjOn Nat.primeFactors s := by
    intro k hk l hl hkl
    rw [← Nat.prod_primeFactors_of_squarefree (hs k hk).1,
      ← Nat.prod_primeFactors_of_squarefree (hs l hl).1, hkl]
  rw [← sum_image (f := fun t => ∏ p ∈ t, x p) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => prod_nonneg fun p _ => hx p
  intro t ht
  obtain ⟨k, hk, rfl⟩ := mem_image.1 ht
  exact mem_powerset.2 (hs k hk).2

lemma prod_one_add_le_exp {P : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ p, 0 ≤ x p) :
    ∏ p ∈ P, (1 + x p) ≤ Real.exp (∑ p ∈ P, x p) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun p _ => by linarith [hx p])
    fun p _ => by have := Real.add_one_le_exp (x p); linarith

/-- Telescoping: `∑_{m ≤ n < m + j} 1/(n(n-1)) = 1/(m-1) - 1/(m+j-1)`. -/
lemma sum_Ico_inv_mul_pred {m : ℕ} (hm : 2 ≤ m) (j : ℕ) :
    ∑ n ∈ Ico m (m + j), ((n : ℝ) * ((n : ℝ) - 1))⁻¹
      = ((m : ℝ) - 1)⁻¹ - ((m + j : ℕ) - 1 : ℝ)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
    have h1 : (2 : ℝ) ≤ (m + j : ℕ) := by exact_mod_cast (show 2 ≤ m + j by omega)
    have h2 : ((m + j : ℕ) : ℝ) - 1 ≠ 0 := by linarith
    have h3 : ((m + j : ℕ) : ℝ) ≠ 0 := by linarith
    have key : (((m + j : ℕ) : ℝ) * (((m + j : ℕ) : ℝ) - 1))⁻¹
        = (((m + j : ℕ) : ℝ) - 1)⁻¹ - (((m + j : ℕ) : ℝ))⁻¹ := by
      field_simp; ring
    rw [key]
    push_cast
    ring

lemma sum_inv_mul_pred_le {P : Finset ℕ} {m : ℕ} (hm : 2 ≤ m) (hP : ∀ p ∈ P, m ≤ p) :
    ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ ((m : ℝ) - 1)⁻¹ := by
  set j := P.sup id + 1
  have hsub : P ⊆ Ico m (m + j) := by
    intro p hp
    have : p ≤ P.sup id := le_sup (f := id) hp
    exact mem_Ico.2 ⟨hP p hp, by omega⟩
  calc ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹
      ≤ ∑ n ∈ Ico m (m + j), ((n : ℝ) * ((n : ℝ) - 1))⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ =>
          inv_mul_pred_nonneg (by have := (mem_Ico.1 hn).1; omega)
    _ = ((m : ℝ) - 1)⁻¹ - ((m + j : ℕ) - 1 : ℝ)⁻¹ := sum_Ico_inv_mul_pred hm j
    _ ≤ ((m : ℝ) - 1)⁻¹ := by
        have : (1 : ℝ) ≤ ((m + j : ℕ) : ℝ) - 1 := by
          have : (2 : ℝ) ≤ ((m + j : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m + j by omega)
          linarith
        linarith [inv_nonneg.2 (show (0 : ℝ) ≤ ((m + j : ℕ) : ℝ) - 1 by linarith)]

/-- Finite sums of `w(k)` over all `k` are at most `e`. -/
lemma sum_sqfreeWeight_le (s : Finset ℕ) : ∑ k ∈ s, sqfreeWeight k ≤ Real.exp 1 := by
  set P := (range (s.sup id + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, 2 ≤ p := fun p hp => (mem_filter.1 hp).2.two_le
  calc ∑ k ∈ s, sqfreeWeight k
      = ∑ k ∈ s.filter Squarefree, ∏ p ∈ k.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        rw [sum_filter]; rfl
    _ ≤ ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
        refine sum_prod_le_prod_one_add (fun p => ?_) fun k hk => ⟨(mem_filter.1 hk).2, ?_⟩
        · rcases Nat.eq_zero_or_pos p with rfl | hp
          · simp
          · exact inv_mul_pred_nonneg hp
        · intro p hp
          have hp' := Nat.mem_primeFactors.1 hp
          have hks : k ≤ s.sup id := le_sup (f := id) (mem_filter.1 hk).1
          exact mem_filter.2 ⟨mem_range.2 (by
            have := Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1; omega), hp'.1⟩
    _ ≤ Real.exp (∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
        refine prod_one_add_le_exp fun p => ?_
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · simp
        · exact inv_mul_pred_nonneg hp
    _ ≤ Real.exp 1 := by
        refine Real.exp_le_exp.2 ((sum_inv_mul_pred_le le_rfl hP).trans ?_)
        norm_num

/-- `w(k)` restricted to odd `k > 1`. -/
noncomputable def oddWeight (k : ℕ) : ℝ := if Odd k ∧ k ≠ 1 then sqfreeWeight k else 0

lemma oddWeight_nonneg (k : ℕ) : 0 ≤ oddWeight k := by
  unfold oddWeight; split_ifs
  · exact sqfreeWeight_nonneg k
  · exact le_rfl

/-- Finite sums of `w(k)` over odd `k > 1` are at most `e^{1/2} - 1`. -/
lemma sum_oddWeight_le (s : Finset ℕ) : ∑ k ∈ s, oddWeight k ≤ Real.exp (1 / 2) - 1 := by
  set s' := s.filter fun k => Squarefree k ∧ Odd k ∧ k ≠ 1
  set P := (range (s.sup id + 1)).filter fun p => Nat.Prime p ∧ 3 ≤ p
  set x : ℕ → ℝ := fun p => ((p : ℝ) * ((p : ℝ) - 1))⁻¹
  have hx : ∀ p, 0 ≤ x p := fun p => by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [x]
    · exact inv_mul_pred_nonneg hp
  have h1 : (1 : ℕ) ∉ s' := by simp [s']
  have heq : ∑ k ∈ s, oddWeight k = ∑ k ∈ s', ∏ p ∈ k.primeFactors, x p := by
    rw [sum_filter]
    refine sum_congr rfl fun k _ => ?_
    simp only [oddWeight, sqfreeWeight, x]
    by_cases hsq : Squarefree k <;> by_cases ho : Odd k <;> by_cases h1 : k = 1 <;>
      simp [hsq, ho, h1]
  have hle : ∑ k ∈ insert 1 s', ∏ p ∈ k.primeFactors, x p ≤ ∏ p ∈ P, (1 + x p) := by
    refine sum_prod_le_prod_one_add hx fun k hk => ?_
    rcases mem_insert.1 hk with rfl | hk
    · exact ⟨squarefree_one, by simp⟩
    · have hk' := mem_filter.1 hk
      refine ⟨hk'.2.1, fun p hp => ?_⟩
      have hp' := Nat.mem_primeFactors.1 hp
      have hks : k ≤ s.sup id := le_sup (f := id) hk'.1
      have hp3 : 3 ≤ p := by
        rcases hp'.1.eq_two_or_odd' with h2 | hodd
        · subst h2
          exact absurd (even_iff_two_dvd.2 hp'.2.1) (Nat.not_even_iff_odd.2 hk'.2.2.1)
        · have := hp'.1.two_le
          rcases Nat.lt_or_ge p 3 with h | h
          · interval_cases p; exact absurd hodd (by decide)
          · exact h
      exact mem_filter.2 ⟨mem_range.2 (by
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1; omega), hp'.1, hp3⟩
  rw [sum_insert h1, Nat.primeFactors_one, prod_empty] at hle
  have hexp : ∏ p ∈ P, (1 + x p) ≤ Real.exp (1 / 2) := by
    refine (prod_one_add_le_exp hx).trans (Real.exp_le_exp.2 ?_)
    refine (sum_inv_mul_pred_le (m := 3) (by norm_num)
      fun p hp => (mem_filter.1 hp).2.2).trans ?_
    norm_num
  rw [heq]
  linarith

lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

lemma summable_sqfreeWeight : Summable sqfreeWeight :=
  summable_of_sum_le sqfreeWeight_nonneg sum_sqfreeWeight_le

lemma summable_oddWeight : Summable oddWeight :=
  summable_of_sum_le oddWeight_nonneg sum_oddWeight_le

lemma tsum_oddWeight_lt_one : ∑' k, oddWeight k < 1 := by
  have := Real.tsum_le_of_sum_le oddWeight_nonneg sum_oddWeight_le
  linarith [exp_half_lt_two]

/-! ### The density -/

/-- The Artin density `δ(a) = ∑ₖ μ(k) / [K_k : ℚ]` (terms with `k` not squarefree vanish). -/
noncomputable def kummerDensity (a : ℤ) : ℝ :=
  ∑' k : ℕ, (moebius k : ℝ) / kummerDegree a k

variable {a : ℤ}

lemma moebius_div_kummerDegree_of_squarefree (hpp : NotPerfectPower a) {k : ℕ}
    (hk : Squarefree k) :
    (moebius k : ℝ) / kummerDegree a k = moebius k * kummerEps a k * sqfreeWeight k := by
  have h := kummerDegree_mul_kummerEps hpp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk.ne_zero
  have ht0 : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hk.ne_zero)
  have hdeg : (kummerDegree a k : ℝ) * kummerEps a k = k * k.totient := by exact_mod_cast h
  have hd0 : (kummerDegree a k : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdeg; nlinarith
  rw [sqfreeWeight_eq hk, ← hdeg]
  field_simp
  have he : (kummerEps a k : ℝ) ≠ 0 := by
    rcases kummerEps_eq_one_or_two (a := a) (k := k) with h | h <;> rw [h] <;> norm_num
  field_simp

lemma moebius_div_kummerDegree_of_not_squarefree {k : ℕ} (hk : ¬ Squarefree k) :
    (moebius k : ℝ) / kummerDegree a k = 0 := by
  simp [moebius_eq_zero_of_not_squarefree hk]

lemma abs_moebius_div_kummerDegree_le (hpp : NotPerfectPower a) (k : ℕ) :
    |(moebius k : ℝ) / kummerDegree a k| ≤ 2 * sqfreeWeight k := by
  by_cases hk : Squarefree k
  · rw [moebius_div_kummerDegree_of_squarefree hpp hk, abs_mul, abs_mul,
      abs_of_nonneg (sqfreeWeight_nonneg k)]
    have hμ : |(moebius k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have hε : |(kummerEps a k : ℝ)| ≤ 2 := by
      rcases kummerEps_eq_one_or_two (a := a) (k := k) with h | h <;> rw [h] <;> norm_num
    calc |(moebius k : ℝ)| * |(kummerEps a k : ℝ)| * sqfreeWeight k
        ≤ (1 * 2) * sqfreeWeight k :=
          mul_le_mul_of_nonneg_right (mul_le_mul hμ hε (abs_nonneg _) zero_le_one)
            (sqfreeWeight_nonneg k)
      _ = 2 * sqfreeWeight k := by ring
  · rw [moebius_div_kummerDegree_of_not_squarefree hk, abs_zero]
    exact mul_nonneg zero_le_two (sqfreeWeight_nonneg k)

/-- The series defining `δ(a)` converges absolutely. -/
theorem summable_moebius_div_kummerDegree (hpp : NotPerfectPower a) :
    Summable fun k : ℕ => (moebius k : ℝ) / kummerDegree a k :=
  Summable.of_norm_bounded (summable_sqfreeWeight.mul_left 2)
    fun k => by rw [Real.norm_eq_abs]; exact abs_moebius_div_kummerDegree_le hpp k

lemma not_squarefree_two_mul_of_even {j : ℕ} (hj : Even j) : ¬ Squarefree (2 * j) := by
  obtain ⟨i, rfl⟩ := hj
  intro h
  have := h 2 ⟨i, by ring⟩
  exact absurd this (by decide)

lemma squarefree_two_mul {j : ℕ} (hj : Odd j) (hsq : Squarefree j) : Squarefree (2 * j) :=
  Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_two_left.2 hj), Nat.squarefree_two, hsq⟩

lemma sqfreeWeight_two_mul {j : ℕ} (hj : Odd j) (hsq : Squarefree j) :
    sqfreeWeight (2 * j) = sqfreeWeight j / 2 := by
  rw [sqfreeWeight_eq (squarefree_two_mul hj hsq), sqfreeWeight_eq hsq,
    Nat.totient_mul (Nat.coprime_two_left.2 hj), Nat.totient_two]
  push_cast
  field_simp

lemma moebius_two_mul {j : ℕ} (hj : Odd j) : (moebius (2 * j) : ℝ) = - moebius j := by
  rw [isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_two_left.2 hj),
    moebius_apply_prime Nat.prime_two]
  push_cast; ring

/-- The pairing of `k = j` and `k = 2j` is bounded below by `[j = 1]/2 - w'(j)/2`. -/
lemma pair_lower_bound (hpp : NotPerfectPower a) (j : ℕ) :
    (if j = 1 then (1 / 2 : ℝ) else 0) - oddWeight j / 2 ≤
      (moebius (2 * j) : ℝ) / kummerDegree a (2 * j) +
        (if Odd j then (moebius j : ℝ) / kummerDegree a j else 0) := by
  by_cases hgood : Odd j ∧ Squarefree j
  · obtain ⟨hj, hsq⟩ := hgood
    simp only [hj, ↓reduceIte]
    rw [moebius_div_kummerDegree_of_squarefree hpp (squarefree_two_mul hj hsq),
      moebius_div_kummerDegree_of_squarefree hpp hsq, kummerEps_of_odd (Nat.not_even_iff_odd.2 hj
        ∘ even_iff_two_dvd.2), sqfreeWeight_two_mul hj hsq, moebius_two_mul hj]
    have hw := sqfreeWeight_nonneg j
    have hμ : |(moebius j : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    rw [abs_le] at hμ
    by_cases h1 : j = 1
    · subst h1
      simp only [↓reduceIte, mul_one, sqfreeWeight_one, moebius_apply_one, Int.cast_one,
        kummerEps_two hpp, oddWeight]
      norm_num
    · simp only [h1, ↓reduceIte]
      have hodd : oddWeight j = sqfreeWeight j := by simp [oddWeight, hj, h1]
      rw [hodd]
      rcases kummerEps_eq_one_or_two (a := a) (k := 2 * j) with h | h <;> rw [h] <;> push_cast <;>
        nlinarith
  · have hj1 : j ≠ 1 := by rintro rfl; exact hgood ⟨odd_one, squarefree_one⟩
    have h2j : ¬ Squarefree (2 * j) := by
      intro h
      by_cases hj : Odd j
      · exact hgood ⟨hj, h.squarefree_of_dvd (dvd_mul_left j 2)⟩
      · exact not_squarefree_two_mul_of_even (Nat.not_odd_iff_even.1 hj) h
    rw [moebius_div_kummerDegree_of_not_squarefree h2j]
    simp only [hj1, ↓reduceIte]
    have : (if Odd j then (moebius j : ℝ) / kummerDegree a j else 0) = 0 := by
      split_ifs with hj
      · exact moebius_div_kummerDegree_of_not_squarefree fun h => hgood ⟨hj, h⟩
      · rfl
    rw [this]
    linarith [oddWeight_nonneg j]

/-- **Positivity of the Artin density (B6)** for `a` not a perfect power. -/
theorem kummerDensity_pos (hpp : NotPerfectPower a) : 0 < kummerDensity a := by
  set f : ℕ → ℝ := fun k => (moebius k : ℝ) / kummerDegree a k with hf_def
  have hf : Summable f := summable_moebius_div_kummerDegree hpp
  have hs_e : Summable fun j => f (2 * j) :=
    hf.comp_injective (mul_right_injective₀ two_ne_zero)
  have hs_o : Summable fun j => f (2 * j + 1) :=
    hf.comp_injective fun x y h => by simpa using h
  set ind : ℕ → ℝ := fun j => if Odd j then f j else 0
  have hs_i : Summable ind :=
    Summable.of_norm_bounded hf.norm fun j => by
      simp only [ind]; split_ifs <;> simp
  have hind : ∑' j, ind j = ∑' j, f (2 * j + 1) := by
    rw [← tsum_even_add_odd (hs_i.comp_injective (mul_right_injective₀ two_ne_zero))
      (hs_i.comp_injective fun x y h => by simpa using h)]
    have he : ∀ j, ind (2 * j) = 0 := fun j => by simp [ind]
    have ho : ∀ j, ind (2 * j + 1) = f (2 * j + 1) := fun j => by simp [ind]
    simp only [he, ho, tsum_zero, zero_add]
  have hsum : kummerDensity a = ∑' j, (f (2 * j) + ind j) := by
    rw [kummerDensity, ← hf_def, ← tsum_even_add_odd hs_e hs_o, ← hind, hs_e.tsum_add hs_i]
  have hlow : Summable fun j : ℕ => (if j = 1 then (1 / 2 : ℝ) else 0) - oddWeight j / 2 :=
    ((summable_of_ne_finset_zero (s := {1}) fun j hj => by
      rw [Finset.mem_singleton] at hj; simp [hj])).sub (summable_oddWeight.div_const 2)
  have hle := hlow.tsum_le_tsum (fun j => pair_lower_bound hpp j) (hs_e.add hs_i)
  rw [hsum]
  refine lt_of_lt_of_le ?_ hle
  rw [Summable.tsum_sub (summable_of_ne_finset_zero (s := {1}) fun j hj => by
      rw [Finset.mem_singleton] at hj; simp [hj]) (summable_oddWeight.div_const 2),
    tsum_ite_eq 1 (fun _ => (1 / 2 : ℝ)), tsum_div_const]
  linarith [tsum_oddWeight_lt_one]


/-- For every `a ∉ {0, ±1}` (perfect powers included) the series for `δ(a)` converges absolutely,
by the lower bound `k φ(k) ≤ 4^|a| [K_k : ℚ]`. -/
theorem summable_moebius_div_kummerDegree_of_ne (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ -1) :
    Summable fun k : ℕ => (moebius k : ℝ) / kummerDegree a k := by
  refine Summable.of_norm_bounded (summable_sqfreeWeight.mul_left ((4 : ℝ) ^ a.natAbs)) fun k => ?_
  rw [Real.norm_eq_abs]
  by_cases hk : Squarefree k
  · have hle : (k * k.totient : ℝ) ≤ 4 ^ a.natAbs * kummerDegree a k := by
      exact_mod_cast mul_totient_le_kummerDegree ha0 ha1 ha2 hk
    have hpos : (0 : ℝ) < k * k.totient := by
      have := Nat.pos_of_ne_zero hk.ne_zero
      have := Nat.totient_pos.2 this
      positivity
    have hdeg : (0 : ℝ) < kummerDegree a k := by
      by_contra h; push Not at h; nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) a.natAbs]
    rw [abs_div, abs_of_pos hdeg, sqfreeWeight_eq hk, div_le_iff₀ hdeg]
    have hμ : |(moebius k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    calc |(moebius k : ℝ)| ≤ 1 := hμ
      _ = 4 ^ a.natAbs * ((k : ℝ) * k.totient)⁻¹ * (4 ^ a.natAbs)⁻¹ * ((k : ℝ) * k.totient) := by
        field_simp; exact (div_self hpos.ne').symm
      _ ≤ 4 ^ a.natAbs * ((k : ℝ) * k.totient)⁻¹ * (4 ^ a.natAbs)⁻¹ *
          (4 ^ a.natAbs * kummerDegree a k) := by gcongr
      _ = 4 ^ a.natAbs * ((k : ℝ) * k.totient)⁻¹ * kummerDegree a k := by field_simp
  · rw [moebius_div_kummerDegree_of_not_squarefree hk, abs_zero]
    exact mul_nonneg (by positivity) (sqfreeWeight_nonneg k)

/-! ### The conductor of `ℚ(√a)` -/

/-- **Conductor of `ℚ(√a)`.** For `a = a₀ c²` not a square, `a₀` squarefree, and `k` squarefree:
`√a ∈ ℚ(ζ_k)` iff `a₀ ≡ 1 (mod 4)` and `|a₀| ∣ k` (`Artin/Kummer/Conductor.lean`). -/
theorem exists_sq_cyclotomicField_iff {a₀ c : ℤ} (ha : ¬ IsSquare a) (h₀ : Squarefree a₀)
    (hac : a = a₀ * c ^ 2) {k : ℕ} (hk : Squarefree k) :
    (∃ β : CyclotomicField k ℚ, β ^ 2 = a) ↔ a₀ % 4 = 1 ∧ a₀.natAbs ∣ k := by
  have hc : c ≠ 0 := by
    rintro rfl; exact ha ⟨0, by simp [hac]⟩
  have hc' : (c : CyclotomicField k ℚ) ≠ 0 := by exact_mod_cast hc
  constructor
  · rintro ⟨β, hβ⟩
    refine mod_four_and_dvd_of_exists_sq hk h₀ (β := β / c) ?_
    rw [div_pow, hβ, hac]; push_cast; field_simp
  · rintro ⟨h4, hdvd⟩
    obtain ⟨β, hβ⟩ := exists_sq_of_mod_four hk.ne_zero h₀ h4 hdvd
    exact ⟨β * c, by rw [mul_pow, hβ, hac]; push_cast; ring⟩

/-! ### Positivity in general (perfect powers included) -/

section Weights

variable (P : ℕ → Prop) [DecidablePred P]

/-- The local weight `x_p = m_p / (p (p - 1))`, `m_p = p` if `P p` and `1` otherwise. -/
noncomputable def xw (p : ℕ) : ℝ := (if P p then (p : ℝ) else 1) * ((p : ℝ) * ((p : ℝ) - 1))⁻¹

/-- `h(j) = ∏_{p ∣ j} (-x_p)` on odd squarefree `j`, and `0` otherwise. -/
noncomputable def hw (j : ℕ) : ℝ :=
  if Odd j ∧ Squarefree j then ∏ p ∈ j.primeFactors, -xw P p else 0

/-- `∑_{(j, D) = 1} g(j)`. -/
noncomputable def coprimeSum (g : ℕ → ℝ) (D : ℕ) : ℝ := ∑' j, if Nat.Coprime j D then g j else 0

variable {P}

lemma xw_pos {p : ℕ} (hp : p.Prime) : 0 < xw P p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold xw
  apply mul_pos
  · split_ifs <;> linarith
  · apply inv_pos.2; nlinarith

lemma xw_le {p : ℕ} (hp : p.Prime) : xw P p ≤ ((p : ℝ) - 1)⁻¹ := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  unfold xw
  calc (if P p then (p : ℝ) else 1) * ((p : ℝ) * ((p : ℝ) - 1))⁻¹
      ≤ p * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        split_ifs <;> linarith
    _ = ((p : ℝ) - 1)⁻¹ := by field_simp

lemma xw_le_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : xw P p ≤ 1 / 2 := by
  have h3 : (3 : ℝ) ≤ p := by have := hp.two_le; exact_mod_cast (by omega : 3 ≤ p)
  refine (xw_le hp).trans ?_
  calc ((p : ℝ) - 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 1 / 2 := by norm_num

lemma xw_lt_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : xw P p < 1 / 2 := by
  have h5 : (5 : ℝ) ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    exact_mod_cast (by omega : 5 ≤ p)
  refine (xw_le hp).trans_lt ?_
  calc ((p : ℝ) - 1)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ < 1 / 2 := by norm_num

lemma xw_two (hP2 : ¬ P 2) : xw P 2 = 1 / 2 := by
  simp [xw, hP2]; norm_num

lemma hw_one : hw P 1 = 1 := by simp [hw]

lemma hw_of_not_odd {j : ℕ} (hj : ¬ Odd j) : hw P j = 0 := by simp [hw, hj]

lemma hw_eq_prod {j : ℕ} (hj : Odd j) (hsq : Squarefree j) :
    hw P j = ∏ p ∈ j.primeFactors, -xw P p := by simp [hw, hj, hsq]

lemma hw_mul_prime {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : ¬ p ∣ j) :
    hw P (p * j) = -xw P p * hw P j := by
  have hj0 : j ≠ 0 := by rintro rfl; exact hj (dvd_zero p)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcop : Nat.Coprime p j := (Nat.Prime.coprime_iff_not_dvd hp).2 hj
  have hodd : Odd (p * j) ↔ Odd j := by rw [Nat.odd_mul]; simp [hpodd]
  have hsq : Squarefree (p * j) ↔ Squarefree j := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨fun h => h.2.2, fun h => ⟨hcop, hp.prime.squarefree, h⟩⟩
  unfold hw
  by_cases h : Odd j ∧ Squarefree j
  · rw [ite_eq_left ⟨hodd.2 h.1, hsq.2 h.2⟩, ite_eq_left h, Nat.primeFactors_mul hp.ne_zero hj0,
      hp.primeFactors, Finset.singleton_union,
      Finset.prod_insert (fun h' => hj (Nat.dvd_of_mem_primeFactors h'))]
  · rw [ite_eq_right (fun h' => h ⟨hodd.1 h'.1, hsq.1 h'.2⟩), ite_eq_right h, mul_zero]

lemma hw_mul_prime_of_dvd {p j : ℕ} (hp : p.Prime) (hj : p ∣ j) : hw P (p * j) = 0 := by
  unfold hw
  rw [ite_eq_right]
  rintro ⟨-, hsq⟩
  obtain ⟨i, rfl⟩ := hj
  have := hsq p ⟨i, by ring⟩
  exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)

lemma hw_mul_of_coprime {m j : ℕ} (h : Nat.Coprime m j) : hw P (m * j) = hw P m * hw P j := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hw]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hw]
  have hsq : Squarefree (m * j) ↔ Squarefree m ∧ Squarefree j := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨fun h' => ⟨h'.2.1, h'.2.2⟩, fun h' => ⟨h, h'.1, h'.2⟩⟩
  unfold hw
  by_cases h1 : Odd m ∧ Squarefree m <;> by_cases h2 : Odd j ∧ Squarefree j
  · rw [ite_eq_left ⟨Nat.odd_mul.2 ⟨h1.1, h2.1⟩, hsq.2 ⟨h1.2, h2.2⟩⟩, ite_eq_left h1, ite_eq_left h2,
      Nat.primeFactors_mul hm.ne' hj.ne', Finset.prod_union h.disjoint_primeFactors]
  · rw [ite_eq_right (fun h' => h2 ⟨(Nat.odd_mul.1 h'.1).2, (hsq.1 h'.2).2⟩), ite_eq_right h2, mul_zero]
  · rw [ite_eq_right (fun h' => h1 ⟨(Nat.odd_mul.1 h'.1).1, (hsq.1 h'.2).1⟩), ite_eq_right h1, zero_mul]
  · rw [ite_eq_right (fun h' => h1 ⟨(Nat.odd_mul.1 h'.1).1, (hsq.1 h'.2).1⟩), ite_eq_right h1, zero_mul]

lemma hw_mul_of_not_coprime {m j : ℕ} (h : ¬ Nat.Coprime m j) : hw P (m * j) = 0 := by
  unfold hw
  rw [ite_eq_right]
  rintro ⟨-, hsq⟩
  exact h (Nat.squarefree_mul_iff.1 hsq).1

end Weights

section Peel

lemma summable_coprime {g : ℕ → ℝ} (hg : Summable g) (D : ℕ) :
    Summable fun j => if Nat.Coprime j D then g j else 0 :=
  Summable.of_norm_bounded hg.norm fun j => by split_ifs <;> simp

/-- Removing one prime `p` from the support: if `g(p j) = c g(j)` for `p ∤ j` and `g(p j) = 0`
for `p ∣ j`, then `∑_{(j,D)=1} g = (1 + c) ∑_{(j,pD)=1} g`. -/
lemma coprimeSum_peel {g : ℕ → ℝ} (hg : Summable g) {p D : ℕ} (hp : p.Prime) (hpD : ¬ p ∣ D)
    {c : ℝ} (hmul : ∀ j, ¬ p ∣ j → g (p * j) = c * g j) (hsq : ∀ j, p ∣ j → g (p * j) = 0) :
    coprimeSum g D = (1 + c) * coprimeSum g (p * D) := by
  set A : ℕ → ℝ := fun j => if Nat.Coprime j D then g j else 0 with hA_def
  set B : ℕ → ℝ := fun j => if Nat.Coprime j (p * D) then g j else 0 with hB_def
  set C : ℕ → ℝ := fun j => if p ∣ j then A j else 0 with hC_def
  have hA : Summable A := summable_coprime hg D
  have hB : Summable B := summable_coprime hg (p * D)
  have hC : Summable C :=
    Summable.of_norm_bounded hA.norm fun j => by simp only [C]; split_ifs <;> simp
  have hcopD : Nat.Coprime p D := (Nat.Prime.coprime_iff_not_dvd hp).2 hpD
  have hiff : ∀ j, Nat.Coprime j p ↔ ¬ p ∣ j := fun j =>
    Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  have hsplit : A = B + C := by
    funext j
    simp only [A, B, C, Pi.add_apply, Nat.coprime_mul_iff_right, hiff]
    by_cases hj : p ∣ j <;> simp [hj]
  have hCsum : ∑' j, C j = c * ∑' j, B j := by
    have hsupp : Function.support C ⊆ Set.range (p * ·) := by
      intro j hj
      simp only [Function.mem_support, C] at hj
      split_ifs at hj with h
      · obtain ⟨i, rfl⟩ := h; exact ⟨i, rfl⟩
      · exact absurd rfl hj
    rw [← (mul_right_injective₀ hp.ne_zero).tsum_eq hsupp, ← tsum_mul_left]
    congr 1; funext i
    simp only [C, A, B, dvd_mul_right, ite_true, Nat.coprime_mul_iff_left,
      Nat.coprime_mul_iff_right, hiff]
    by_cases hi : p ∣ i
    · simp [hsq i hi, hi]
    · simp only [hmul i hi, hi, not_false_eq_true]
      by_cases hc : i.Coprime D
      · rw [ite_eq_left ⟨hcopD, hc⟩, ite_eq_left ⟨trivial, hc⟩]
      · rw [ite_eq_right (fun h => hc h.2), ite_eq_right (fun h => hc h.2), mul_zero]
  unfold coprimeSum
  change ∑' j, A j = (1 + c) * ∑' j, B j
  rw [hsplit, show ∑' j, (B + C) j = ∑' j, (B j + C j) from rfl, hB.tsum_add hC, hCsum]; ring

variable {P : ℕ → Prop} [DecidablePred P]

/-- Removing a finite set `S` of odd primes from the support of `h`. -/
lemma coprimeSum_hw_peel (hs : Summable (hw P)) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    {D : ℕ} (hSD : ∀ p ∈ S, ¬ p ∣ D) :
    coprimeSum (hw P) D = (∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p) := by
  induction S using Finset.induction_on generalizing D with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self p S)
    rw [ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      (fun q hq => hSD q (Finset.mem_insert_of_mem hq))]
    have hpD' : ¬ p ∣ D * ∏ q ∈ S, q := by
      intro h
      rcases (Nat.Prime.dvd_mul hp.1).1 h with h | h
      · exact hSD p (Finset.mem_insert_self p S) h
      · obtain ⟨q, hq, hpq⟩ := (hp.1.prime.dvd_finsetProd_iff _).1 h
        have := (Nat.prime_dvd_prime_iff_eq hp.1 (hS q (Finset.mem_insert_of_mem hq)).1).1 hpq
        exact hpS (this ▸ hq)
    rw [coprimeSum_peel hs hp.1 hpD' (c := -xw P p) (fun j hj => hw_mul_prime hp.1 hp.2 hj)
      (fun j hj => hw_mul_prime_of_dvd hp.1 hj), Finset.prod_insert hpS, Finset.prod_insert hpS,
      show p * (D * ∏ q ∈ S, q) = D * (p * ∏ q ∈ S, q) by ring]
    ring

/-- The sum of `h` over multiples of `D`. -/
lemma tsum_dvd_hw (D : ℕ) (hD : D ≠ 0) :
    ∑' j, (if D ∣ j then hw P j else 0) = hw P D * coprimeSum (hw P) D := by
  have hsupp : Function.support (fun j => if D ∣ j then hw P j else 0) ⊆ Set.range (D * ·) := by
    intro j hj
    simp only [Function.mem_support] at hj
    split_ifs at hj with h
    · obtain ⟨i, rfl⟩ := h; exact ⟨i, rfl⟩
    · exact absurd rfl hj
  rw [← (mul_right_injective₀ hD).tsum_eq hsupp, coprimeSum, ← tsum_mul_left]
  congr 1; funext i
  simp only [dvd_mul_right, ite_true]
  by_cases hi : Nat.Coprime i D
  · rw [ite_eq_left hi, hw_mul_of_coprime hi.symm]
  · rw [ite_eq_right hi, hw_mul_of_not_coprime (fun h => hi h.symm), mul_zero]

/-- `∑_{(j, M) = 1} h(j) > 0` once every prime with `P p` divides `M`: then `h(j) = μ(j) w(j)` on
the support and the crude bound applies. -/
lemma coprimeSum_hw_pos (hs : Summable (hw P)) {M : ℕ} (hM : ∀ p, p.Prime → P p → p ∣ M) :
    0 < coprimeSum (hw P) M := by
  have hlow : ∀ j, (if j = 1 then (1 : ℝ) else 0) - oddWeight j ≤
      if Nat.Coprime j M then hw P j else 0 := by
    intro j
    by_cases h1 : j = 1
    · subst h1; simp [hw_one, oddWeight]
    simp only [h1, ↓reduceIte, zero_sub]
    by_cases hgood : Nat.Coprime j M ∧ Odd j ∧ Squarefree j
    · obtain ⟨hc, ho, hsq⟩ := hgood
      rw [ite_eq_left hc, hw_eq_prod ho hsq]
      have hw' : oddWeight j = ∏ p ∈ j.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        simp [oddWeight, sqfreeWeight, ho, h1, hsq]
      have hx : ∀ p ∈ j.primeFactors, xw P p = ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        intro p hp
        have hp' := Nat.mem_primeFactors.1 hp
        have hnP : ¬ P p := fun hP =>
          hp'.1.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hp'.2.1 hc)
            (hM p hp'.1 hP))
        simp [xw, hnP]
      have hprod : ∏ p ∈ j.primeFactors, -xw P p =
          ∏ p ∈ j.primeFactors, -((p : ℝ) * ((p : ℝ) - 1))⁻¹ :=
        Finset.prod_congr rfl fun p hp => by rw [hx p hp]
      have habs : |∏ p ∈ j.primeFactors, -((p : ℝ) * ((p : ℝ) - 1))⁻¹| =
          ∏ p ∈ j.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        rw [Finset.abs_prod]
        exact Finset.prod_congr rfl fun p hp => by
          rw [abs_neg, abs_of_nonneg (inv_mul_pred_nonneg (Nat.prime_of_mem_primeFactors hp).one_le)]
      rw [hw', hprod]
      linarith [neg_abs_le (∏ p ∈ j.primeFactors, -((p : ℝ) * ((p : ℝ) - 1))⁻¹)]
    · have : (if Nat.Coprime j M then hw P j else 0) = 0 := by
        split_ifs with hc
        · unfold hw; rw [ite_eq_right (fun h => hgood ⟨hc, h⟩)]
        · rfl
      rw [this]; linarith [oddWeight_nonneg j]
  have hs1 : Summable fun j : ℕ => (if j = 1 then (1 : ℝ) else 0) - oddWeight j :=
    (summable_of_ne_finset_zero (s := {1}) fun j hj => by
      rw [Finset.mem_singleton] at hj; simp [hj]).sub summable_oddWeight
  have hs2 := summable_coprime hs M
  have hle := hs1.tsum_le_tsum hlow hs2
  rw [Summable.tsum_sub (summable_of_ne_finset_zero (s := {1}) fun j hj => by
      rw [Finset.mem_singleton] at hj; simp [hj]) summable_oddWeight,
    tsum_ite_eq 1 (fun _ => (1 : ℝ))] at hle
  unfold coprimeSum
  linarith [tsum_oddWeight_lt_one]

end Peel

section Main

variable {P : ℕ → Prop} [DecidablePred P]

/-- The factor `∏_{p ∣ D} (1 - x_p) - h(D)` coming from `√a ∈ ℚ(ζ_{2j}) ⟺ D ∣ j` is positive: all
`x_p ≤ 1/2`, with equality only at `p = 3`. -/
lemma dfactor_pos {D : ℕ} (hD : Squarefree D) (hodd : Odd D) (hD1 : D ≠ 1) :
    0 < ∏ p ∈ D.primeFactors, (1 - xw P p) - hw P D := by
  rw [hw_eq_prod hodd hD]
  have hp2 : ∀ p ∈ D.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))⟩
  by_cases h : ∃ p ∈ D.primeFactors, p ≠ 3
  · have hlt : ∏ p ∈ D.primeFactors, xw P p < ∏ p ∈ D.primeFactors, (1 - xw P p) := by
      refine Finset.prod_lt_prod₀ (fun p hp => xw_pos (hp2 p hp).1) (fun p hp => ?_) ?_
      · linarith [xw_le_half (P := P) (hp2 p hp).1 (hp2 p hp).2]
      · obtain ⟨p, hp, hp3⟩ := h
        exact ⟨p, hp, by linarith [xw_lt_half (P := P) (hp2 p hp).1 (hp2 p hp).2 hp3]⟩
    have habs : |∏ p ∈ D.primeFactors, -xw P p| = ∏ p ∈ D.primeFactors, xw P p := by
      rw [Finset.abs_prod]
      exact Finset.prod_congr rfl fun p hp => by rw [abs_neg, abs_of_pos (xw_pos (hp2 p hp).1)]
    linarith [le_abs_self (∏ p ∈ D.primeFactors, -xw P p)]
  · push Not at h
    have hne : D.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by
      have := hD.ne_zero; omega)
    have h3 : D.primeFactors = {3} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, h⟩
      obtain ⟨p, hp⟩ := hne
      exact h p hp ▸ hp
    rw [h3]; simp

open Classical in
/-- For squarefree `k`: `μ(k) / [K_k : ℚ] = ε(k) ∏_{q ∣ k} (-x_q)`, with `x_q` built from
`P q = (a is a q-th power in ℤ)`. -/
lemma moebius_div_kummerDegree_eq_prod (ha0 : a ≠ 0) (hP2 : ¬ ∃ c : ℤ, c ^ 2 = a)
    {k : ℕ} (hk : Squarefree k) :
    (moebius k : ℝ) / kummerDegree a k =
      kummerEps a k * ∏ q ∈ k.primeFactors, -xw (fun q => ∃ c : ℤ, c ^ q = a) q := by
  set P : ℕ → Prop := fun q => ∃ c : ℤ, c ^ q = a with hP
  have hk0 : k ≠ 0 := hk.ne_zero
  have hM : (kummerM a k : ℝ) =
      kummerEps a k * ∏ q ∈ k.primeFactors, (if P q then (q : ℝ) else 1) := by
    unfold kummerM
    rw [Finset.prod_filter]
    push_cast
    by_cases h2 : 2 ∣ k
    · have h2m : 2 ∈ k.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2, hk0⟩
      rw [← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ h2m]
      have hB : (if P 2 then ((2 : ℕ) : ℝ) else 1) = 1 := ite_eq_right hP2
      rw [hB, one_mul]
      unfold kummerEps
      simp only [↓reduceIte, h2, true_and]
      congr 1
      · split_ifs <;> simp
      · refine Finset.prod_congr rfl fun x hx => ?_
        have hx2 := Finset.ne_of_mem_erase hx
        simp only [hx2, ↓reduceIte, P]
    · rw [kummerEps_of_odd h2, Nat.cast_one, one_mul]
      refine Finset.prod_congr rfl fun x hx => ?_
      have hx2 : x ≠ 2 := by rintro rfl; exact h2 (Nat.dvd_of_mem_primeFactors hx)
      simp only [hx2, ↓reduceIte, P]
  have hdegR : (kummerDegree a k : ℝ) * kummerM a k = k * k.totient := by
    exact_mod_cast kummerDegree_mul_kummerM ha0 hk
  have hpos : (0 : ℝ) < k * k.totient := by
    have := Nat.pos_of_ne_zero hk0
    have := Nat.totient_pos.2 this
    positivity
  have hdeg0 : (kummerDegree a k : ℝ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hdegR; linarith
  have hM0 : (kummerM a k : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hdegR; linarith
  have hf : (moebius k : ℝ) / kummerDegree a k = moebius k * kummerM a k * sqfreeWeight k := by
    rw [sqfreeWeight_eq hk, ← hdegR]; field_simp
  have hμ : (moebius k : ℝ) = ∏ q ∈ k.primeFactors, (-1 : ℝ) := by
    rw [moebius_apply_of_squarefree hk, Finset.prod_const,
      ← (cardDistinctFactors_eq_cardFactors_iff_squarefree hk0).2 hk,
      cardDistinctFactors_eq_card_primeFactors]
    push_cast; ring
  have hw : sqfreeWeight k = ∏ q ∈ k.primeFactors, ((q : ℝ) * ((q : ℝ) - 1))⁻¹ := by
    simp [sqfreeWeight, hk]
  rw [hf, hμ, hM, hw, Finset.prod_congr rfl (fun q _ => show -xw P q =
    (-1) * (if P q then (q : ℝ) else 1) * ((q : ℝ) * ((q : ℝ) - 1))⁻¹ by unfold xw; ring),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring


lemma prod_one_sub_xw_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    0 < ∏ p ∈ S, (1 - xw P p) :=
  Finset.prod_pos fun p hp => by linarith [xw_le_half (P := P) (hS p hp).1 (hS p hp).2]

/-- **Positivity of the Artin density (B6) in general**: `δ(a) > 0` for every `a` that is not a
square and not `-1`, perfect powers included. -/
theorem kummerDensity_pos_of_not_isSquare (ha : ¬ IsSquare a) (ha' : a ≠ -1) :
    0 < kummerDensity a := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact ha ⟨1, by simp⟩
  obtain ⟨a₀, c, h₀, hac⟩ : ∃ a₀ c : ℤ, Squarefree a₀ ∧ a = a₀ * c ^ 2 := by
    obtain ⟨c, b, hbc, hb⟩ := exists_sq_mul_squarefree a.natAbs
    rcases Int.natAbs_eq a with h | h
    · exact ⟨b, c, Int.squarefree_natCast.2 hb, by rw [h, ← hbc]; push_cast; ring⟩
    · exact ⟨-b, c, Int.squarefree_natAbs.1 (by simpa using hb), by rw [h, ← hbc]; push_cast; ring⟩
  have hc0 : c ≠ 0 := by rintro rfl; exact ha ⟨0, by simp [hac]⟩
  set P : ℕ → Prop := fun q => ∃ c : ℤ, c ^ q = a with hP
  have hP2 : ¬ ∃ c : ℤ, c ^ 2 = a := fun ⟨c, hc⟩ => ha ⟨c, by rw [← hc]; ring⟩
  have hPle : ∀ q, P q → q ≤ a.natAbs := fun q ⟨c, hc⟩ => le_natAbs_of_pow_eq c hc ha0 ha1 ha'
  set D : ℕ := a₀.natAbs with hD
  have hDsq : Squarefree D := Int.squarefree_natAbs.2 h₀
  have hDodd : a₀ % 4 = 1 → Odd D := fun h => by
    rw [hD, Int.natAbs_odd]; exact Int.odd_iff.2 (by omega)
  have hD0 : D ≠ 0 := hDsq.ne_zero
  set f : ℕ → ℝ := fun k => (moebius k : ℝ) / kummerDegree a k with hf_def
  have hf : Summable f := summable_moebius_div_kummerDegree_of_ne ha0 ha1 ha'
  have hform : ∀ k, Squarefree k → f k = kummerEps a k * ∏ q ∈ k.primeFactors, -xw P q :=
    fun k hk => moebius_div_kummerDegree_eq_prod ha0 hP2 hk
  have hf0 : ∀ k, ¬ Squarefree k → f k = 0 := fun k hk =>
    moebius_div_kummerDegree_of_not_squarefree hk
  have hodd_eq : ∀ j, Odd j → f j = hw P j := by
    intro j hj
    by_cases hsq : Squarefree j
    · rw [hform j hsq, kummerEps_of_odd (fun h => (Nat.not_even_iff_odd.2 hj)
        (even_iff_two_dvd.2 h)), hw_eq_prod hj hsq]
      simp
    · rw [hf0 j hsq]; simp [hw, hsq]
  have hs : Summable (hw P) := Summable.of_norm_bounded hf.norm fun j => by
    by_cases hj : Odd j
    · rw [hodd_eq j hj]
    · rw [hw_of_not_odd hj]; simp
  set g : ℕ → ℝ := fun j => if a₀ % 4 = 1 ∧ D ∣ j then 0 else hw P j with hg_def
  -- pairing `k = j` with `k = 2 j`
  have hpair : ∀ j, f (2 * j) + (if Odd j then f j else 0) = g j / 2 := by
    intro j
    by_cases hgood : Odd j ∧ Squarefree j
    · obtain ⟨hj, hsq⟩ := hgood
      have h2sq : Squarefree (2 * j) := squarefree_two_mul hj hsq
      rw [ite_eq_left hj, hodd_eq j hj]
      have h2j : (2 : ℕ) ∉ j.primeFactors := fun h =>
        (Nat.not_even_iff_odd.2 hj) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors h))
      have hf2 : f (2 * j) = kummerEps a (2 * j) * (-(1 / 2)) * hw P j := by
        rw [hform _ h2sq, Nat.primeFactors_mul two_ne_zero hsq.ne_zero,
          Nat.prime_two.primeFactors, Finset.singleton_union, Finset.prod_insert h2j,
          xw_two hP2, hw_eq_prod hj hsq]
        ring
      have hiff : (2 ∣ 2 * j ∧ ∃ β : CyclotomicField (2 * j) ℚ, β ^ 2 = a) ↔
          (a₀ % 4 = 1 ∧ D ∣ j) := by
        rw [exists_sq_cyclotomicField_iff ha h₀ hac h2sq]
        constructor
        · rintro ⟨-, h4, hdvd⟩
          exact ⟨h4, (Nat.Coprime.dvd_mul_left (Nat.coprime_two_right.2 (hDodd h4))).1 hdvd⟩
        · rintro ⟨h4, hdvd⟩; exact ⟨dvd_mul_right 2 j, h4, hdvd.mul_left 2⟩
      have hε : kummerEps a (2 * j) = if a₀ % 4 = 1 ∧ D ∣ j then 2 else 1 := by
        unfold kummerEps
        by_cases h : a₀ % 4 = 1 ∧ D ∣ j
        · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
        · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h]
      rw [hf2, hε]
      simp only [g]
      split_ifs <;> push_cast <;> ring
    · have h2 : ¬ Squarefree (2 * j) := by
        intro h
        by_cases hj : Odd j
        · exact hgood ⟨hj, h.squarefree_of_dvd (dvd_mul_left j 2)⟩
        · exact not_squarefree_two_mul_of_even (Nat.not_odd_iff_even.1 hj) h
      have h1 : (if Odd j then f j else 0) = 0 := by
        split_ifs with hj
        · exact hf0 j fun h => hgood ⟨hj, h⟩
        · rfl
      have hg0 : g j = 0 := by
        simp only [g]
        split_ifs
        · rfl
        · unfold hw; rw [ite_eq_right hgood]
      rw [hf0 _ h2, h1, hg0]; ring
  -- `δ(a) = (∑ g) / 2`
  have hs_e : Summable fun j => f (2 * j) :=
    hf.comp_injective (mul_right_injective₀ two_ne_zero)
  have hs_o : Summable fun j => f (2 * j + 1) :=
    hf.comp_injective fun x y h => by simpa using h
  set ind : ℕ → ℝ := fun j => if Odd j then f j else 0
  have hs_i : Summable ind :=
    Summable.of_norm_bounded hf.norm fun j => by
      simp only [ind]; split_ifs <;> simp
  have hind : ∑' j, ind j = ∑' j, f (2 * j + 1) := by
    rw [← tsum_even_add_odd (hs_i.comp_injective (mul_right_injective₀ two_ne_zero))
      (hs_i.comp_injective fun x y h => by simpa using h)]
    have he : ∀ j, ind (2 * j) = 0 := fun j => by simp [ind]
    have ho : ∀ j, ind (2 * j + 1) = f (2 * j + 1) := fun j => by simp [ind]
    simp only [he, ho, tsum_zero, zero_add]
  have hsum : kummerDensity a = ∑' j, g j / 2 := by
    rw [kummerDensity, ← hf_def, ← tsum_even_add_odd hs_e hs_o, ← hind, ← hs_e.tsum_add hs_i]
    exact tsum_congr hpair
  rw [hsum, tsum_div_const]
  refine div_pos ?_ two_pos
  -- the bad primes
  set H : Finset ℕ := (Finset.range (a.natAbs + 1)).filter fun q => q.Prime ∧ q ≠ 2 ∧ P q
  have hH : ∀ p ∈ H, p.Prime ∧ p ≠ 2 := fun p hp => by
    have := (Finset.mem_filter.1 hp).2; exact ⟨this.1, this.2.1⟩
  have hPmem : ∀ p, p.Prime → P p → p ∈ H := by
    intro p hp hPp
    have hp2 : p ≠ 2 := by rintro rfl; exact hP2 hPp
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hPle p hPp)), hp, hp2, hPp⟩
  have hcs1 : ∑' j, hw P j = coprimeSum (hw P) 1 := by
    unfold coprimeSum; simp
  by_cases hE : a₀ % 4 = 1
  · have hD1 : D ≠ 1 := by
      intro h1
      rcases Int.natAbs_eq a₀ with h | h <;> rw [← hD, h1] at h
      · exact ha ⟨c, by rw [hac, h]; ring⟩
      · rw [h] at hE; norm_num at hE
    have hDo := hDodd hE
    have hpfD : ∀ p ∈ D.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 hDo) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))⟩
    have hgeq : g = fun j => hw P j - if D ∣ j then hw P j else 0 := by
      funext j
      simp only [g, hE, true_and]
      split_ifs <;> ring
    have hsD : Summable fun j => if D ∣ j then hw P j else 0 :=
      Summable.of_norm_bounded hs.norm fun j => by split_ifs <;> simp
    have h1 : coprimeSum (hw P) 1 =
        (∏ p ∈ D.primeFactors, (1 - xw P p)) * coprimeSum (hw P) D := by
      rw [coprimeSum_hw_peel hs D.primeFactors hpfD (D := 1) (fun p hp h =>
        (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.1 h)), one_mul,
        Nat.prod_primeFactors_of_squarefree hDsq]
    set S := H \ D.primeFactors
    have hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := fun p hp => hH p (Finset.mem_sdiff.1 hp).1
    have hSD : ∀ p ∈ S, ¬ p ∣ D := fun p hp h =>
      (Finset.mem_sdiff.1 hp).2 (Nat.mem_primeFactors.2 ⟨(hS p hp).1, h, hD0⟩)
    have h2 := coprimeSum_hw_peel hs S hS hSD
    have hpos : 0 < coprimeSum (hw P) (D * ∏ p ∈ S, p) := by
      refine coprimeSum_hw_pos hs fun p hp hPp => ?_
      by_cases hpD : p ∈ D.primeFactors
      · exact (Nat.dvd_of_mem_primeFactors hpD).trans (dvd_mul_right _ _)
      · exact (Finset.dvd_prod_of_mem (fun q : ℕ => q)
          (Finset.mem_sdiff.2 ⟨hPmem p hp hPp, hpD⟩)).trans (dvd_mul_left _ _)
    rw [hgeq]
    show 0 < ∑' j, (hw P j - if D ∣ j then hw P j else 0)
    rw [hs.tsum_sub hsD, tsum_dvd_hw D hD0, hcs1, h1, h2]
    have hfac := dfactor_pos (P := P) hDsq hDo hD1
    have hSpos := prod_one_sub_xw_pos (P := P) hS
    have heq : (∏ p ∈ D.primeFactors, (1 - xw P p)) *
          ((∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p)) -
        hw P D * ((∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p)) =
        (∏ p ∈ D.primeFactors, (1 - xw P p) - hw P D) *
          ((∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p)) := by ring
    rw [heq]
    exact mul_pos hfac (mul_pos hSpos hpos)
  · have hgeq : g = hw P := by
      funext j; simp only [g, hE, false_and, ↓reduceIte]
    rw [hgeq, hcs1, coprimeSum_hw_peel hs H hH (D := 1) (fun p hp h =>
      (hH p hp).1.one_lt.ne' (Nat.dvd_one.1 h)), one_mul]
    refine mul_pos (prod_one_sub_xw_pos hH) (coprimeSum_hw_pos hs fun p hp hPp => ?_)
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) (hPmem p hp hPp)

end Main

end Artin.Kummer
