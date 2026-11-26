import PsiGRH.Primitive

/-!
# From a character to the primitive character inducing it

A character `χ` mod `N` and its primitive character `χ*` (mod the conductor) agree on every `n`
coprime to `N`, and `χ(n) = 0` otherwise. So `ψ(u, χ)` and `ψ(u, χ*)` differ by at most
`Σ_{n ≤ u, (n, N) > 1} Λ(n) ≤ ω(N) log u` (`norm_psiChar_sub_primitive_le`), and
`ω(N) log 2 ≤ log N` (`card_primeFactors_mul_log_two_le`). The principal character is the only
one whose primitive character is trivial (`primitiveCharacter_eq_one_iff`), so the main terms
agree.
-/

namespace PsiGRH

open DirichletCharacter ArithmeticFunction

/-- `ω(N) log 2 ≤ log N`. -/
lemma card_primeFactors_mul_log_two_le {N : ℕ} (hN : N ≠ 0) :
    (N.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log N := by
  have h1 : 2 ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ N.primeFactors, p ≤ N :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)
  have h3 : ((2 ^ N.primeFactors.card : ℕ) : ℝ) ≤ N := by exact_mod_cast h1.trans h2
  rw [← Real.log_pow]
  push_cast at h3
  exact Real.log_le_log (by positivity) h3

/-- `Σ_{n ≤ u, (n, N) > 1} Λ(n) ≤ ω(N) log u`. -/
lemma sum_vonMangoldt_not_coprime_le {N : ℕ} (hN : N ≠ 0) {u : ℝ} (hu : 1 ≤ u) :
    ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n => ¬ n.Coprime N), Λ n ≤
      N.primeFactors.card * Real.log u := by
  classical
  set M := ⌊u⌋₊ with hMdef
  have hM : M ≠ 0 := (Nat.floor_pos.mpr hu).ne'
  set P := N.primeFactors.sigma (fun p => Finset.Icc 1 (Nat.log p M)) with hP
  have h1 : ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ n.Coprime N), Λ n ≤
      ∑ n ∈ P.image (fun x => x.1 ^ x.2), Λ n := by
    rw [← Finset.sum_filter_ne_zero]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => vonMangoldt_nonneg)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨-, hnM⟩, hcop⟩, hΛ⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hpN : p ∣ N := by
      by_contra h
      exact hcop (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr h))
    rw [Finset.mem_image]
    refine ⟨⟨p, k⟩, ?_, rfl⟩
    rw [hP, Finset.mem_sigma, Nat.mem_primeFactors, Finset.mem_Icc]
    exact ⟨⟨hp, hpN, hN⟩, hk, Nat.le_log_of_pow_le hp.one_lt hnM⟩
  have h2 : ∑ n ∈ P.image (fun x => x.1 ^ x.2), Λ n ≤ ∑ x ∈ P, Λ (x.1 ^ x.2) :=
    Finset.sum_image_le_of_nonneg fun _ _ => vonMangoldt_nonneg
  have h3 : ∑ x ∈ P, Λ (x.1 ^ x.2) ≤ ∑ p ∈ N.primeFactors, Real.log u := by
    rw [hP, Finset.sum_sigma]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    calc ∑ k ∈ Finset.Icc 1 (Nat.log p M), Λ (p ^ k)
        = ∑ k ∈ Finset.Icc 1 (Nat.log p M), Real.log p := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hpp]
      _ = (Nat.log p M : ℝ) * Real.log p := by simp
      _ = Real.log ((p ^ Nat.log p M : ℕ) : ℝ) := by
          push_cast; rw [Real.log_pow]
      _ ≤ Real.log u := by
          have h := Nat.pow_log_le_self p hM
          have hpos : (0 : ℝ) < ((p ^ Nat.log p M : ℕ) : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero _ hpp.ne_zero)
          refine Real.log_le_log hpos ?_
          exact (Nat.cast_le.mpr h).trans (Nat.floor_le (by linarith))
  refine h1.trans (h2.trans (h3.trans (le_of_eq ?_)))
  simp

/-- `χ*` is trivial exactly when `χ` is principal. -/
lemma primitiveCharacter_eq_one_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    calc χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
          χ.changeLevel_primitiveCharacter.symm
      _ = changeLevel χ.conductor_dvd_level 1 := by rw [h]
      _ = 1 := map_one _
  · rintro rfl
    exact primitiveCharacter_one

lemma mainTerm_primitiveCharacter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : ℝ) :
    mainTerm χ.primitiveCharacter u = mainTerm χ u := by
  unfold mainTerm
  by_cases h : χ = 1
  · rw [if_pos h, if_pos ((primitiveCharacter_eq_one_iff χ).mpr h)]
  · rw [if_neg h, if_neg (mt (primitiveCharacter_eq_one_iff χ).mp h)]

/-- `|ψ(u, χ) − ψ(u, χ*)| ≤ ω(N) log u`. -/
theorem norm_psiChar_sub_primitive_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {u : ℝ}
    (hu : 1 ≤ u) :
    ‖psiChar χ u - psiChar χ.primitiveCharacter u‖ ≤ N.primeFactors.card * Real.log u := by
  classical
  unfold psiChar
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not _ (fun n => n.Coprime N)]
  have hcop : ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n => n.Coprime N),
      ((Λ n : ℂ) * χ n - (Λ n : ℂ) * χ.primitiveCharacter n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.mpr hn.2)
    simp only [Int.cast_natCast] at h
    rw [h, sub_self]
  rw [hcop, zero_add]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans
    (sum_vonMangoldt_not_coprime_le (NeZero.ne N) hu))
  rw [Finset.mem_filter] at hn
  have hχ0 : χ n = 0 := by
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    exact hn.2
  rw [hχ0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg]
  have h1 := DirichletCharacter.norm_le_one χ.primitiveCharacter (n : ZMod χ.conductor)
  have h0 : 0 ≤ Λ n := vonMangoldt_nonneg
  calc Λ n * ‖χ.primitiveCharacter n‖ ≤ Λ n * 1 := by gcongr
    _ = Λ n := mul_one _

end PsiGRH
