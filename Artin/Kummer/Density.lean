import Artin.Kummer.Degree

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

/-! ### What remains (stated, not proved)

The two statements below are what the rest of the project needs beyond the non-perfect-power case.

1. **Conductor of `ℚ(√a)`.** For squarefree `k`, `√a ∈ ℚ(ζ_k)` exactly when the discriminant of
   `ℚ(√a)` divides `k`. With `a = a₀ c²`, `a₀` squarefree, that discriminant is `a₀` if
   `a₀ ≡ 1 (mod 4)` and `4 a₀` otherwise, and `4 a₀` never divides a squarefree `k`. This turns
   `kummerEps` into Hooley's explicit `ε(k)` and gives the closed form
   `δ(a) = A (1 - μ(|a₀|) ∏_{q ∣ a₀} 1/(q² - q - 1))` for `a₀ ≡ 1 (mod 4)` (and `δ(a) = A`
   otherwise), `A` = Artin's constant, when `a` is not a perfect power. Positivity above does
   not need it. The `⇐` direction is a Gauss-sum computation (`gaussSum_sq`); the `⇒` direction
   needs ramification in cyclotomic fields (or `ℚ(ζ_m) ∩ ℚ(ζ_n) = ℚ(ζ_{gcd(m,n)})`), which our
   Mathlib pin does not provide.

2. **Positivity for perfect powers.** For `a = ± b^h` with `h > 1` the exact degree is
   `[K_k : ℚ] = k φ(k) / m(k)` with `m(k)` the largest divisor of `k` for which `a` is an
   `m(k)`-th power in `ℚ(ζ_k)` (the proof of `exists_structure` gives this), and the odd part of
   `m(k)` is `∏ q` over odd primes `q ∣ gcd(k, h)` with `a` a `q`-th power in `ℤ`. The crude bound
   used in `kummerDensity_pos` fails once `h` has several small odd prime factors (e.g.
   `h = 105`: the weights `q / (q (q - 1))` at `q = 3, 5, 7` push the comparison sum past `1`), so
   the general case needs the exact set of `j` with `√a ∈ ℚ(ζ_{2j})`, i.e. item 1.
-/

/-- **Not proved: conductor of `ℚ(√a)`.** See item 1 above. -/
theorem exists_sq_cyclotomicField_iff {a₀ c : ℤ} (ha : ¬ IsSquare a) (h₀ : Squarefree a₀)
    (hac : a = a₀ * c ^ 2) {k : ℕ} (hk : Squarefree k) :
    (∃ β : CyclotomicField k ℚ, β ^ 2 = a) ↔ a₀ % 4 = 1 ∧ a₀.natAbs ∣ k := by
  sorry

/-- **Not proved: positivity of `δ(a)` in general** (Hooley's hypothesis on `a` in the target
theorem). Proved above (`kummerDensity_pos`) when `a` is not a perfect power. See item 2. -/
theorem kummerDensity_pos_of_not_isSquare (ha : ¬ IsSquare a) (ha' : a ≠ -1) :
    0 < kummerDensity a := by
  sorry

end Artin.Kummer
