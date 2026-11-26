import BachSorenson.Two.ZeroSum
import Erdos985.Analytic.ExplicitFormula.Bounds.GammaPart

/-!
# `L'/L` at `s = 1 + a`, summed over the characters mod `q`

With `ld χ s = L'/L(s, χ)` and `σ = 1 + a > 1`:

* `Σ_χ Re ld(χ, σ) ≤ 0` over all characters mod `q`, because `−Σ_χ L'/L(σ, χ) =
  φ(q) Σ_{n ≡ 1} Λ(n) n^{-σ} ≥ 0` (`sum_re_ld_nonpos`). This is Bach–Sorenson's use of
  `ζ_E'/ζ_E(1 + a) ≤ 0` (proof of their Lemma 4.6) for the cyclotomic field, written with
  characters;
* `−Re ld(χ, σ) ≤ Σ_n Λ(n) n^{-σ} ≤ 1640` for `a = 1/20` (`neg_re_ld_le`, `tsum_vonMangoldt_le`);
* for `ψ` mod `f ∣ q` and `χ = ψ` lifted to `q`,
  `Re ld(ψ, σ) ≤ Re ld(χ, σ) + Σ_{p ∣ q, p ∤ f} log p/(p − 1)` (`re_ld_le_changeLevel`);
* `Re Γ'/Γ`-part `≤ −0.7` at `σ = 21/20` (`re_gammaLogDeriv_le`).
-/

namespace BachSorenson.Two

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic Erdos985.Analytic.BoundsAux LLS Finset

/-- `L'/L(s, χ)`. -/
noncomputable def ld {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

lemma ld_eq_neg_LSeries {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    ld χ s = -LSeries (fun n => χ n * (Λ n : ℂ)) s := by
  unfold ld
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  simp only [Pi.mul_def] at h
  rw [h, neg_div, neg_neg]

/-! ### A `p`-series bound -/

lemma rpow_step {m : ℝ} (hm : 1 ≤ m) {b : ℝ} (hb : 0 < b) :
    1 / (m + 1) ^ (1 + b) ≤ (1 / b) * (m ^ (-b) - (m + 1) ^ (-b)) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m + 1 := by linarith
  set X := (m + 1) ^ (-b) with hX
  have hX0 : 0 < X := Real.rpow_pos_of_pos hm1 _
  set r := (m + 1) / m with hr
  have hr0 : 0 < r := by positivity
  have hlog : 1 / (m + 1) ≤ Real.log r := by
    have := Real.one_sub_inv_le_log_of_pos hr0
    have e : 1 - r⁻¹ = 1 / (m + 1) := by rw [hr]; field_simp; ring
    linarith
  have hrb : 1 + b * (1 / (m + 1)) ≤ r ^ b := by
    rw [Real.rpow_def_of_pos hr0]
    have := Real.add_one_le_exp (Real.log r * b)
    nlinarith
  have hmX : m ^ (-b) = X * r ^ b := by
    rw [hX, hr, Real.div_rpow hm1.le hm0.le, Real.rpow_neg hm1.le, Real.rpow_neg hm0.le]
    have : (0 : ℝ) < (m + 1) ^ b := Real.rpow_pos_of_pos hm1 _
    field_simp
  have hpow : 1 / (m + 1) ^ (1 + b) = X * (1 / (m + 1)) := by
    rw [hX, Real.rpow_add hm1, Real.rpow_one, Real.rpow_neg hm1.le]
    field_simp
  rw [hpow, hmX]
  have hk : b * (1 / (m + 1)) ≤ r ^ b - 1 := by linarith
  calc X * (1 / (m + 1)) = (1 / b) * (X * (b * (1 / (m + 1)))) := by field_simp
    _ ≤ (1 / b) * (X * (r ^ b - 1)) := by gcongr
    _ = (1 / b) * (X * r ^ b - X) := by ring

lemma sum_range_rpow_le {b : ℝ} (hb : 0 < b) (M : ℕ) :
    ∑ i ∈ range (M + 2), 1 / (i : ℝ) ^ (1 + b)
      ≤ 1 + (1 / b) * (1 - ((M : ℝ) + 1) ^ (-b)) := by
  induction M with
  | zero =>
    simp [Finset.sum_range_succ, Real.zero_rpow (by linarith : (1 + b) ≠ 0)]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have h := rpow_step (m := (M : ℝ) + 1) (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)]) hb
    push_cast
    have e : ((M : ℝ) + 1 + 1) = (M + 2 : ℕ) := by push_cast; ring
    rw [e] at h ⊢
    push_cast at h ⊢
    nlinarith

lemma tsum_rpow_le {b : ℝ} (hb : 0 < b) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + b) ≤ 1 + 1 / b := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun n => ?_
  have h1 := sum_range_rpow_le hb n
  have h0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-b) := by positivity
  have hsub : ∑ i ∈ range n, 1 / (i : ℝ) ^ (1 + b) ≤ ∑ i ∈ range (n + 2), 1 / (i : ℝ) ^ (1 + b) :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun _ _ _ => by positivity
  have : (1 / b) * (1 - ((n : ℝ) + 1) ^ (-b)) ≤ 1 / b := by
    have : 0 < 1 / b := by positivity
    nlinarith
  linarith

lemma log_le_rpow (n : ℕ) {b : ℝ} (hb : 0 < b) : Real.log n ≤ (1 / b) * (n : ℝ) ^ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hb.ne']
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn0 b)
    rw [Real.log_rpow hn0] at h
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hb]
    nlinarith

/-- `Σ_n Λ(n) n^{-(1 + a)} ≤ (2/a)(1 + 2/a)`, from `Λ(n) ≤ log n ≤ (2/a) n^{a/2}`. -/
theorem vonMangoldt_rpow_summable_le {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (1 + a)) ∧
      ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (1 + a) ≤ (2 / a) * (1 + 2 / a) := by
  have hb : 0 < a / 2 := by linarith
  have hle : ∀ n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (1 + a) ≤ (2 / a) * (1 / (n : ℝ) ^ (1 + a / 2)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (by linarith : (1 + a / 2) ≠ 0)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hΛ : (Λ n : ℝ) ≤ Real.log n := vonMangoldt_le_log
    have hl := log_le_rpow n hb
    have e : (n : ℝ) ^ (1 + a) = (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (1 + a / 2) := by
      rw [← Real.rpow_add hn0]; ring_nf
    have hp : 0 < (n : ℝ) ^ (a / 2) := Real.rpow_pos_of_pos hn0 _
    have hq : 0 < (n : ℝ) ^ (1 + a / 2) := Real.rpow_pos_of_pos hn0 _
    rw [e, div_le_iff₀ (by positivity)]
    have : 1 / (a / 2) = 2 / a := by field_simp
    rw [this] at hl
    calc (Λ n : ℝ) ≤ 2 / a * (n : ℝ) ^ (a / 2) := hΛ.trans hl
      _ = _ := by field_simp
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + a / 2)) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  have hs : Summable (fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (1 + a)) :=
    Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) hle
      (hsum.mul_left _)
  refine ⟨hs, ?_⟩
  calc ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (1 + a)
      ≤ ∑' n : ℕ, (2 / a) * (1 / (n : ℝ) ^ (1 + a / 2)) :=
        hs.tsum_le_tsum hle (hsum.mul_left _)
    _ = (2 / a) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + a / 2) := tsum_mul_left
    _ ≤ (2 / a) * (1 + 1 / (a / 2)) := by gcongr; exact tsum_rpow_le hb
    _ = _ := by field_simp

/-! ### Bounds for `ld` -/

lemma norm_term_le {M : ℕ} (χ : DirichletCharacter ℂ M) {a : ℝ} (n : ℕ) :
    ‖LSeries.term (fun n => χ n * (Λ n : ℂ)) (((1 + a : ℝ)) : ℂ) n‖
      ≤ (Λ n : ℝ) / (n : ℝ) ^ (1 + a) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq]
    simp only [hn, ↓reduceIte, norm_mul, ofReal_re]
    have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    have : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    gcongr
    nlinarith

/-- `−Re L'/L(1 + a, χ) ≤ Σ_n Λ(n) n^{-(1+a)}`. -/
theorem neg_re_ld_le {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {a : ℝ} (ha : 0 < a) :
    -(ld χ ((1 + a : ℝ) : ℂ)).re ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (1 + a) := by
  have hs : 1 < (((1 + a : ℝ)) : ℂ).re := by simp; linarith
  rw [ld_eq_neg_LSeries χ hs, neg_re, neg_neg]
  refine (Complex.re_le_norm _).trans ?_
  unfold LSeries
  exact tsum_of_norm_bounded (vonMangoldt_rpow_summable_le ha).1.hasSum fun n => norm_term_le χ n

/-- `Σ_χ Re L'/L(1 + a, χ) ≤ 0` over all characters mod `q`. -/
theorem sum_re_ld_nonpos {q : ℕ} [NeZero q] {a : ℝ} (ha : 0 < a) :
    ∑ χ : DirichletCharacter ℂ q, (ld χ ((1 + a : ℝ) : ℂ)).re ≤ 0 := by
  set s : ℂ := ((1 + a : ℝ) : ℂ) with hsdef
  have hs : 1 < s.re := by simp [s]; linarith
  have hsumm : ∀ χ : DirichletCharacter ℂ q,
      Summable (LSeries.term (fun n => χ n * (Λ n : ℂ)) s) := fun χ => by
    have := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    simpa [LSeriesSummable, Pi.mul_def] using this
  have e1 : ∑ χ : DirichletCharacter ℂ q, (ld χ s).re
      = -(∑' n, ∑ χ : DirichletCharacter ℂ q, LSeries.term (fun n => χ n * (Λ n : ℂ)) s n).re := by
    rw [Summable.tsum_finsetSum (fun χ _ => hsumm χ), Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [ld_eq_neg_LSeries χ hs, neg_re]
    rfl
  rw [e1, neg_nonpos]
  have hS : Summable fun n => ∑ χ : DirichletCharacter ℂ q,
      LSeries.term (fun n => χ n * (Λ n : ℂ)) s n := summable_sum fun χ _ => hsumm χ
  have hre := hS.hasSum.mapL Complex.reCLM
  refine hre.nonneg fun n => ?_
  simp only [Function.comp_apply, Complex.reCLM_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [LSeries.term, hn, ↓reduceIte]
    have e : ∑ χ : DirichletCharacter ℂ q, χ n * (Λ n : ℂ) / (n : ℂ) ^ s
        = (∑ χ : DirichletCharacter ℂ q, χ n) * ((Λ n : ℂ) / (n : ℂ) ^ s) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun χ _ => by ring
    rw [e, DirichletCharacter.sum_characters_eq]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc : (n : ℂ) ^ s = (((n : ℝ) ^ (1 + a) : ℝ) : ℂ) := by
      rw [hsdef, Complex.ofReal_cpow hn0]; simp
    rw [hc]
    split_ifs
    · rw [show ((q.totient : ℂ)) * ((Λ n : ℂ) / (((n : ℝ) ^ (1 + a) : ℝ) : ℂ))
          = (((q.totient : ℝ) * ((Λ n : ℝ) / (n : ℝ) ^ (1 + a)) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg vonMangoldt_nonneg (by positivity))
    · simp

/-- `Σ_{χ ≠ 1} (Re L'/L(1 + a, χ) + Re L'/L(1 + a, χ⁻¹)) ≤ 2 Σ_n Λ(n) n^{-(1+a)}`. -/
theorem sum_erase_re_ld_le {q : ℕ} [NeZero q] {a : ℝ} (ha : 0 < a) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ((ld χ ((1 + a : ℝ) : ℂ)).re + (ld χ⁻¹ ((1 + a : ℝ) : ℂ)).re)
      ≤ 2 * ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (1 + a) := by
  set s : ℂ := ((1 + a : ℝ) : ℂ)
  set F : DirichletCharacter ℂ q → ℝ := fun χ => (ld χ s).re
  have hall := sum_re_ld_nonpos (q := q) ha
  have hinv : ∑ χ : DirichletCharacter ℂ q, F χ⁻¹ = ∑ χ : DirichletCharacter ℂ q, F χ :=
    Equiv.sum_comp (Equiv.inv _) F
  have h1 := neg_re_ld_le (1 : DirichletCharacter ℂ q) ha
  have e1 : ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, F χ
      = ∑ χ : DirichletCharacter ℂ q, F χ - F 1 := by
    rw [← Finset.add_sum_erase _ _ (mem_univ 1)]; ring
  have e2 : ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, F χ⁻¹
      = ∑ χ : DirichletCharacter ℂ q, F χ⁻¹ - F 1⁻¹ := by
    rw [← Finset.add_sum_erase _ _ (mem_univ 1)]; ring
  rw [inv_one] at e2
  rw [Finset.sum_add_distrib]
  change ∑ χ ∈ _, F χ + ∑ χ ∈ _, F χ⁻¹ ≤ _
  rw [e1, e2, hinv]
  change -F 1 ≤ _ at h1
  linarith

/-! ### Imprimitive characters -/

/-- The prime-power part `Σ_{k ≥ 1} Λ(p^k)/p^k` of a prime. -/
noncomputable def hp (p n : ℕ) : ℝ := if IsPrimePow n ∧ n.minFac = p then (Λ n : ℝ) / n else 0

lemma hp_nonneg (p n : ℕ) : 0 ≤ hp p n := by
  unfold hp; split_ifs
  · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  · exact le_rfl

lemma hasSum_hp {p : ℕ} (hp' : p.Prime) : HasSum (hp p) (Real.log p / (p - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  have hg : Function.Injective (fun k : ℕ => p ^ (k + 1)) := fun i j h => by
    have := Nat.pow_right_injective hp'.two_le h
    simpa using this
  have hsupp : ∀ n ∉ Set.range (fun k : ℕ => p ^ (k + 1)), hp p n = 0 := by
    intro n hn
    unfold hp
    split_ifs with h
    · exfalso
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 h.1
      have : r = p := by rw [← h.2, Nat.Prime.pow_minFac hr hk.ne']
      subst this
      exact hn ⟨k - 1, by simp; congr 1; omega⟩
    · rfl
  rw [← hg.hasSum_iff hsupp]
  have hval : ∀ k : ℕ, hp p (p ^ (k + 1)) = Real.log p * ((1 / (p : ℝ)) * (1 / (p : ℝ)) ^ k) := by
    intro k
    unfold hp
    have hpp : IsPrimePow (p ^ (k + 1)) := (hp'.isPrimePow).pow (by omega)
    rw [if_pos ⟨hpp, Nat.Prime.pow_minFac hp' (by omega)⟩, vonMangoldt_apply_pow (by omega),
      vonMangoldt_apply_prime hp']
    push_cast
    rw [div_pow, one_pow, pow_succ]
    field_simp
  simp only [Function.comp_def, hval]
  have hr : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hG := ((hasSum_geometric_of_lt_one hr hr1).mul_left (1 / (p : ℝ))).mul_left (Real.log p)
  convert hG using 1
  field_simp

/-- For `ψ` mod `f ∣ q`, `Re L'/L(σ, ψ) ≤ Re L'/L(σ, ψ lifted to q) + Σ_{p ∣ q, p ∤ f} log p/(p − 1)`. -/
theorem re_ld_le_changeLevel {f q : ℕ} [NeZero f] [NeZero q] (hfq : f ∣ q) (hq : q ≠ 0) (ψ : DirichletCharacter ℂ f)
    {a : ℝ} (ha : 0 < a) :
    (ld ψ ((1 + a : ℝ) : ℂ)).re ≤ (ld (DirichletCharacter.changeLevel hfq ψ) ((1 + a : ℝ) : ℂ)).re
      + ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f), Real.log p / (p - 1) := by
  classical
  set s : ℂ := ((1 + a : ℝ) : ℂ) with hsdef
  set χ := DirichletCharacter.changeLevel hfq ψ with hχdef
  set R := q.primeFactors.filter (fun p => ¬ p ∣ f) with hR
  have hs : 1 < s.re := by simp [s]; linarith
  have hsum : ∀ {M : ℕ} (φ : DirichletCharacter ℂ M),
      Summable (LSeries.term (fun n => φ n * (Λ n : ℂ)) s) := fun φ => by
    have := DirichletCharacter.LSeriesSummable_twist_vonMangoldt φ hs
    simpa [LSeriesSummable, Pi.mul_def] using this
  have hdiff : ld ψ s - ld χ s = ∑' n, (LSeries.term (fun n => χ n * (Λ n : ℂ)) s n
      - LSeries.term (fun n => ψ n * (Λ n : ℂ)) s n) := by
    rw [ld_eq_neg_LSeries ψ hs, ld_eq_neg_LSeries χ hs, (hsum χ).tsum_sub (hsum ψ)]
    unfold LSeries; ring
  have hHas : HasSum (fun n => ∑ p ∈ R, hp p n) (∑ p ∈ R, Real.log p / (p - 1)) :=
    hasSum_sum fun p hpR => hasSum_hp (Nat.prime_of_mem_primeFactors (mem_filter.1 hpR).1)
  have hbound : ∀ n, ‖LSeries.term (fun n => χ n * (Λ n : ℂ)) s n
      - LSeries.term (fun n => ψ n * (Λ n : ℂ)) s n‖ ≤ ∑ p ∈ R, hp p n := by
    intro n
    have h0 : 0 ≤ ∑ p ∈ R, hp p n := sum_nonneg fun p _ => hp_nonneg p n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using h0
    simp only [LSeries.term, hn, ↓reduceIte]
    by_cases hc : n.Coprime q
    · have hval : χ n = ψ n := by
        have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hfq (a := (n : ℤ))
          (Nat.isCoprime_iff_coprime.2 hc)
        simpa [hχdef] using this
      rw [hval, sub_self, norm_zero]; exact h0
    have hχ0 : χ n = 0 :=
      MulChar.map_nonunit χ (fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h))
    rw [hχ0, zero_mul, zero_div, zero_sub, norm_neg]
    by_cases hψ : ψ n = 0
    · rw [hψ]; simpa using h0
    by_cases hΛ : (Λ n : ℝ) = 0
    · rw [show (Λ n : ℂ) = ((Λ n : ℝ) : ℂ) from rfl, hΛ]; simpa using h0
    have hpp : IsPrimePow n := by
      by_contra h; exact hΛ (vonMangoldt_eq_zero_iff.2 h)
    obtain ⟨r, k, hr, hk, hrk⟩ := (isPrimePow_nat_iff n).1 hpp
    have hmin : n.minFac = r := by rw [← hrk, Nat.Prime.pow_minFac hr hk.ne']
    have hcopf : n.Coprime f := by
      have hu : IsUnit (n : ZMod f) := by
        by_contra h; exact hψ (MulChar.map_nonunit ψ h)
      exact (ZMod.isUnit_iff_coprime n f).1 hu
    have hrR : r ∈ R := by
      simp only [hR, mem_filter, Nat.mem_primeFactors]
      refine ⟨⟨hr, ?_, hq⟩, ?_⟩
      · by_contra hd
        exact hc (hrk ▸ Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
      · intro hd
        have : r.Coprime f := Nat.Coprime.coprime_dvd_left (hrk ▸ dvd_pow_self r hk.ne') hcopf
        exact (Nat.Prime.coprime_iff_not_dvd hr).1 this hd
    refine le_trans ?_ (single_le_sum (fun p _ => hp_nonneg p n) hrR)
    have hhp : hp r n = (Λ n : ℝ) / n := by unfold hp; rw [if_pos ⟨hpp, hmin⟩]
    rw [hhp, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hnorm : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (1 + a) := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp [s]
    rw [hnorm]
    have hψ1 : ‖ψ n‖ ≤ 1 := DirichletCharacter.norm_le_one ψ n
    have hp1 : (n : ℝ) ≤ (n : ℝ) ^ (1 + a) := by
      conv_lhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hΛ0 : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    calc ‖ψ n‖ * (Λ n : ℝ) / (n : ℝ) ^ (1 + a) ≤ 1 * (Λ n : ℝ) / n := by
          apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hp1
      _ = _ := by ring
  have hnorm := tsum_of_norm_bounded hHas hbound
  rw [← hdiff] at hnorm
  have := Complex.re_le_norm (ld ψ s - ld χ s)
  rw [sub_re] at this
  linarith

/-! ### The gamma factor at `σ = 21/20` -/

/-- `Re Γ'/Γ`-part of `Λ'/Λ` at `21/20`: `Re gammaLogDeriv χ (21/20) ≤ −0.7`. -/
theorem re_gammaLogDeriv_le {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (gammaLogDeriv χ ((1 + 1 / 20 : ℝ) : ℂ)).re ≤ -(7 / 10) := by
  set σ : ℝ := 1 + 1 / 20 with hσ
  have hs : 1 < ((σ : ℝ) : ℂ).re := by norm_num [σ]
  have H := Complex.reCLM.hasSum (hasSum_gammaLogDeriv χ hs)
  set κ : ℕ := parity χ with hκ
  have hterm : ∀ k : ℕ, Complex.reCLM (1 / (2 + ((2 * k + κ : ℕ) : ℂ))
      - 1 / ((σ : ℂ) + ((2 * k + κ : ℕ) : ℂ))) = 1 / (2 + ((2 * k + κ : ℕ) : ℝ))
        - 1 / (σ + ((2 * k + κ : ℕ) : ℝ)) := by
    intro k
    rw [Complex.reCLM_apply]
    rw [show (1 / (2 + ((2 * k + κ : ℕ) : ℂ)) - 1 / ((σ : ℂ) + ((2 * k + κ : ℕ) : ℂ)))
        = (((1 / (2 + ((2 * k + κ : ℕ) : ℝ)) - 1 / (σ + ((2 * k + κ : ℕ) : ℝ))) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  simp only [hterm] at H
  set g : ℕ → ℝ := fun k => if k = 0 then 1 / (2 + (κ : ℝ)) - 1 / (σ + κ) else 0
  have hg : HasSum g (1 / (2 + (κ : ℝ)) - 1 / (σ + κ)) := hasSum_ite_eq 0 _
  have hle := hasSum_le (fun k => ?_) H hg
  · rw [Complex.reCLM_apply, sub_re] at hle
    have hl2 := Real.log_two_lt_d9
    have hl2' := Real.log_two_gt_d9
    have hγ := DigammaAux.eulerMascheroniConstant_gt
    have hlpi : 1.13 < Real.log Real.pi := by
      rw [Real.lt_log_iff_exp_lt Real.pi_pos]
      have h2 := Real.exp_bound' (x := 0.13) (by norm_num) (by norm_num) (n := 3) (by norm_num)
      simp [Finset.sum_range_succ, Nat.factorial] at h2
      have e : Real.exp 1.13 = Real.exp 1 * Real.exp 0.13 := by rw [← Real.exp_add]; norm_num
      rw [e]
      have h3 := Real.exp_one_lt_d9
      have h4 := Real.pi_gt_d4
      have h5 : 0 < Real.exp 0.13 := Real.exp_pos _
      nlinarith
    have hκ1 : κ = 0 ∨ κ = 1 := Nat.le_one_iff_eq_zero_or_eq_one.1 (parity_le_one χ)
    unfold gammaLogDeriv at hle ⊢
    rw [← hκ] at hle ⊢
    rcases hκ1 with h0 | h1
    · rw [h0] at hle ⊢
      have e2 : ((2 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 1 := by norm_num
      rw [e2, Complex.digamma_one] at hle
      simp only [Nat.cast_zero, add_zero] at hle ⊢
      have e3 : (-(1 / 2) * (Real.log Real.pi : ℂ) + 1 / 2 * -(Real.eulerMascheroniConstant : ℂ)).re
          = -(1 / 2) * Real.log Real.pi - 1 / 2 * Real.eulerMascheroniConstant := by simp; ring
      rw [e3] at hle
      norm_num [σ] at hle ⊢
      linarith
    · rw [h1] at hle ⊢
      have e2 : ((2 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 3 / 2 := by norm_num
      rw [e2] at hle
      have e3 : (-(1 / 2) * (Real.log Real.pi : ℂ) + 1 / 2 * Complex.digamma (3 / 2)).re
          = -(1 / 2) * Real.log Real.pi + 1 / 2 * (2 - 2 * Real.log 2
            - Real.eulerMascheroniConstant) := by
        rw [add_re, ← re_digamma_three_halves]; simp
      rw [e3] at hle
      norm_num [σ] at hle ⊢
      linarith
  · by_cases hk : k = 0
    · subst hk; simp [g]
    · simp only [g, hk, ↓reduceIte]
      have hm : (0 : ℝ) ≤ ((2 * k + κ : ℕ) : ℝ) := Nat.cast_nonneg _
      have : 1 / (2 + ((2 * k + κ : ℕ) : ℝ)) ≤ 1 / (σ + ((2 * k + κ : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le (by norm_num [σ]; linarith) (by norm_num [σ])
      linarith

end BachSorenson.Two
