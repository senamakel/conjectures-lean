import LLS.Key

/-!
# The prime powers `p^k ≤ s²`, `k ≥ 2`

`Σ_{n ≤ s², n = p^k, k ≥ 2} Λ(n) log(s²/n) ≤ 2 Σ_{m ≤ s} Λ(m) log(s/m) + 2 Σ_{m ≤ N} Λ(m) log(N/m)`
whenever `s² ≤ 2N²`. Write `n = p^k`, `m = p^⌊k/2⌋`: for even `k`, `n = m²` and the term is
`2Λ(m) log(s/m)`; for odd `k`, `n = m²p` with `p ≥ 2`, and the term is at most `2Λ(m) log(N/m)`.
Both maps `n ↦ m` are injective.
-/

namespace LLS.Thm14

open Finset ArithmeticFunction

/-- `p^⌊k/2⌋` for `n = p^k`. -/
def halfPow (n : ℕ) : ℕ := n.minFac ^ (n.factorization n.minFac / 2)

lemma pp_repr {n : ℕ} (h : IsPrimePow n) :
    n.minFac.Prime ∧ 0 < n.factorization n.minFac ∧ n.minFac ^ n.factorization n.minFac = n := by
  obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
  rw [Nat.Prime.pow_minFac hr hk.ne', hr.factorization_pow, Finsupp.single_eq_same]
  exact ⟨hr, hk, rfl⟩

lemma two_le_exp {n : ℕ} (h : IsPrimePow n) (hnp : ¬ n.Prime) : 2 ≤ n.factorization n.minFac := by
  obtain ⟨hp, hk, he⟩ := pp_repr h
  by_contra h2
  have : n.factorization n.minFac = 1 := by omega
  rw [this, pow_one] at he
  exact hnp (he ▸ hp)

lemma vonMangoldt_pow_eq {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    (Λ (p ^ j) : ℝ) = Real.log p := by
  rw [vonMangoldt_apply_pow hj, vonMangoldt_apply_prime hp]

lemma minFac_halfPow {n : ℕ} (h : IsPrimePow n) (hnp : ¬ n.Prime) :
    (halfPow n).minFac = n.minFac := by
  obtain ⟨hp, -, -⟩ := pp_repr h
  have := two_le_exp h hnp
  exact Nat.Prime.pow_minFac hp (by omega)

lemma halfPow_even {n : ℕ} (h : IsPrimePow n) (he : Even (n.factorization n.minFac)) :
    halfPow n ^ 2 = n := by
  obtain ⟨-, -, hn⟩ := pp_repr h
  obtain ⟨j, hj⟩ := he
  conv_rhs => rw [← hn]
  unfold halfPow
  rw [← pow_mul, hj]
  congr 1
  omega

lemma halfPow_odd {n : ℕ} (h : IsPrimePow n) (he : ¬ Even (n.factorization n.minFac)) :
    halfPow n ^ 2 * n.minFac = n := by
  obtain ⟨-, -, hn⟩ := pp_repr h
  obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.1 he
  conv_rhs => rw [← hn]
  unfold halfPow
  rw [← pow_mul, ← pow_succ, hj]
  congr 1
  omega

theorem sum_sq_pp_le (s N : ℕ) (hs : 1 ≤ s) (hN : s ^ 2 ≤ 2 * N ^ 2) :
    ∑ n ∈ (range (s ^ 2 + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        (Λ n : ℝ) * Real.log (((s ^ 2 : ℕ) : ℝ) / n)
      ≤ 2 * ∑ m ∈ range (s + 1), (Λ m : ℝ) * Real.log ((s : ℝ) / m)
        + 2 * ∑ m ∈ range (N + 1), (Λ m : ℝ) * Real.log ((N : ℝ) / m) := by
  classical
  set S := (range (s ^ 2 + 1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
  set f : ℕ → ℝ := fun n => (Λ n : ℝ) * Real.log (((s ^ 2 : ℕ) : ℝ) / n)
  set h1 : ℕ → ℝ := fun m => 2 * ((Λ m : ℝ) * Real.log ((s : ℝ) / m))
  set h2 : ℕ → ℝ := fun m => 2 * ((Λ m : ℝ) * Real.log ((N : ℝ) / m))
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have memS : ∀ n ∈ S, n ≤ s ^ 2 ∧ IsPrimePow n ∧ ¬ n.Prime := fun n hn => by
    simp only [S, mem_filter, mem_range] at hn
    exact ⟨Nat.lt_succ_iff.1 hn.1, hn.2⟩
  have hpos : ∀ n ∈ S, 0 < halfPow n := fun n hn => by
    obtain ⟨-, hpp, -⟩ := memS n hn
    exact pow_pos (pp_repr hpp).1.pos _
  have hj : ∀ n ∈ S, n.factorization n.minFac / 2 ≠ 0 := fun n hn => by
    obtain ⟨-, hpp, hnp⟩ := memS n hn
    have := two_le_exp hpp hnp
    omega
  have hΛ : ∀ n ∈ S, (Λ n : ℝ) = Λ (halfPow n) := fun n hn => by
    obtain ⟨-, hpp, hnp⟩ := memS n hn
    obtain ⟨hp, hk, he⟩ := pp_repr hpp
    unfold halfPow
    rw [vonMangoldt_pow_eq hp (hj n hn)]
    conv_lhs => rw [← he]
    rw [vonMangoldt_pow_eq hp hk.ne']
  rw [← sum_filter_add_sum_filter_not S (fun n => Even (n.factorization n.minFac))]
  gcongr
  · -- even exponents
    set Se := S.filter (fun n => Even (n.factorization n.minFac))
    have hinj : Set.InjOn halfPow Se := fun a ha b hb hab => by
      simp only [Se, coe_filter, Set.mem_ofPred_eq] at ha hb
      rw [← halfPow_even (memS a ha.1).2.1 ha.2, ← halfPow_even (memS b hb.1).2.1 hb.2, hab]
    have hle : ∀ n ∈ Se, f n ≤ h1 (halfPow n) := fun n hn => by
      have hn' := (mem_filter.1 hn)
      obtain ⟨-, hpp, -⟩ := memS n hn'.1
      have e := halfPow_even hpp hn'.2
      have hm0 : (0 : ℝ) < halfPow n := by exact_mod_cast hpos n hn'.1
      have e' : (n : ℝ) = (halfPow n : ℝ) ^ 2 := by exact_mod_cast e.symm
      simp only [f, h1]
      rw [hΛ n hn'.1, e']
      push_cast
      rw [show (s : ℝ) ^ 2 / (halfPow n : ℝ) ^ 2 = ((s : ℝ) / halfPow n) ^ 2 by ring,
        Real.log_pow]
      ring_nf; exact le_rfl
    calc ∑ n ∈ Se, f n ≤ ∑ n ∈ Se, h1 (halfPow n) := sum_le_sum hle
      _ = ∑ m ∈ Se.image halfPow, h1 m := (sum_image hinj).symm
      _ ≤ ∑ m ∈ range (s + 1), h1 m := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun m hm _ => ?_
          · intro m hm
            obtain ⟨n, hn, rfl⟩ := mem_image.1 hm
            have hn' := mem_filter.1 hn
            obtain ⟨hns, hpp, -⟩ := memS n hn'.1
            have e := halfPow_even hpp hn'.2
            rw [mem_range, Nat.lt_succ_iff]
            have : halfPow n ^ 2 ≤ s ^ 2 := by rw [e]; exact hns
            exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
          · have := mem_range.1 hm
            exact mul_nonneg (by norm_num) (mul_nonneg vonMangoldt_nonneg
              (log_div_nonneg (Nat.lt_succ_iff.1 this)))
      _ = 2 * ∑ m ∈ range (s + 1), (Λ m : ℝ) * Real.log ((s : ℝ) / m) := by
          simp only [h1]; rw [mul_sum]
  · -- odd exponents
    set So := S.filter (fun n => ¬ Even (n.factorization n.minFac))
    have hinj : Set.InjOn halfPow So := fun a ha b hb hab => by
      simp only [So, coe_filter, Set.mem_ofPred_eq] at ha hb
      obtain ⟨-, hpa, hna⟩ := memS a ha.1
      obtain ⟨-, hpb, hnb⟩ := memS b hb.1
      rw [← halfPow_odd hpa ha.2, ← halfPow_odd hpb hb.2, ← minFac_halfPow hpa hna,
        ← minFac_halfPow hpb hnb, hab]
    have hm2 : ∀ n ∈ So, halfPow n ^ 2 ≤ N ^ 2 := fun n hn => by
      have hn' := mem_filter.1 hn
      obtain ⟨hns, hpp, -⟩ := memS n hn'.1
      have e := halfPow_odd hpp hn'.2
      have hp2 := (pp_repr hpp).1.two_le
      nlinarith
    have hle : ∀ n ∈ So, f n ≤ h2 (halfPow n) := fun n hn => by
      have hn' := (mem_filter.1 hn)
      obtain ⟨-, hpp, -⟩ := memS n hn'.1
      have e := halfPow_odd hpp hn'.2
      have hp2 : (2 : ℝ) ≤ n.minFac := by exact_mod_cast (pp_repr hpp).1.two_le
      have hm0 : (0 : ℝ) < halfPow n := by exact_mod_cast hpos n hn'.1
      have hNm : halfPow n ≤ N := (Nat.pow_le_pow_iff_left (by norm_num)).1 (hm2 n hn)
      have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hm0 (by exact_mod_cast hNm)
      have e' : (n : ℝ) = (halfPow n : ℝ) ^ 2 * (n.minFac : ℝ) := by exact_mod_cast e.symm
      simp only [f, h2]
      rw [hΛ n hn'.1, e']
      have hl : Real.log (((s ^ 2 : ℕ) : ℝ) / ((halfPow n : ℝ) ^ 2 * (n.minFac : ℝ)))
          ≤ 2 * Real.log ((N : ℝ) / halfPow n) := by
        rw [← Real.log_rpow (by positivity), Real.rpow_two]
        refine Real.log_le_log (by positivity) ?_
        have hsN : ((s : ℝ)) ^ 2 ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast hN
        push_cast
        have hp0 : (0 : ℝ) < n.minFac := by linarith
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (halfPow n : ℝ), mul_le_mul_of_nonneg_left hp2
          (sq_nonneg ((N : ℝ)))]
      have := mul_le_mul_of_nonneg_left hl (vonMangoldt_nonneg (n := halfPow n))
      linarith
    calc ∑ n ∈ So, f n ≤ ∑ n ∈ So, h2 (halfPow n) := sum_le_sum hle
      _ = ∑ m ∈ So.image halfPow, h2 m := (sum_image hinj).symm
      _ ≤ ∑ m ∈ range (N + 1), h2 m := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun m hm _ => ?_
          · intro m hm
            obtain ⟨n, hn, rfl⟩ := mem_image.1 hm
            rw [mem_range, Nat.lt_succ_iff]
            exact (Nat.pow_le_pow_iff_left (by norm_num)).1 (hm2 n hn)
          · have := mem_range.1 hm
            exact mul_nonneg (by norm_num) (mul_nonneg vonMangoldt_nonneg
              (log_div_nonneg (Nat.lt_succ_iff.1 this)))
      _ = 2 * ∑ m ∈ range (N + 1), (Λ m : ℝ) * Real.log ((N : ℝ) / m) := by
          simp only [h2]; rw [mul_sum]

end LLS.Thm14
