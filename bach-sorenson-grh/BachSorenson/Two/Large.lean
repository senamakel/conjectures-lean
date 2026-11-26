import BachSorenson.Two.Character
import BachSorenson.Two.PrimePowers
import BachSorenson.Large
import LLS.Analytic.Principal
import LLS.Key

/-!
# One modulus, constant `2`, given a numerical inequality

Let `x = ⌊2 (q log q)²⌋` and `T(a, x) = Σ_{n ≤ x, n ≡ a} Λ(n) log(x/n)`. Orthogonality gives
`φ(q) T(a, x) = Σ_χ χ(a⁻¹) S(x, χ)`. Under GRH:

* principal character: `S(x, χ₀) ≥ x − (3/20)√x − 3 log x − 3 − ω(q) log² x`
  (`LLS.psiLog_ge` minus the `n` not prime to `q`);
* every other character: `‖S(x, χ)‖ ≤ (√x + 1 + log x) Z₂(ψ_χ) + (log q + 2.52) log x
  + (log² x/2 + 5 log x + 2) + 2 ω(q) log² x` (`norm_logSum_prim_le`,
  `norm_logSum_changeLevel_sub_le`);
* the zero sums together: `Σ_{χ ≠ 1} Z₂(ψ_χ) ≤ (11/10)((φ(q) − 1)(log q + log 2 − 7/5) + 3280)`
  (`Z2_prim_le`, `sum_erase_re_ld_le`, `vonMangoldt_rpow_summable_le`).

If no prime `p < x` is `≡ a`, then `T(a, x) ≤ PPl x`; `NumericOK2 q` says these are
incompatible.
-/

namespace BachSorenson.Two

open Complex ArithmeticFunction Finset Erdos985 LLS
open scoped Classical

/-- `T(a, x) = Σ_{n ≤ x, n ≡ a (mod q)} Λ(n) log(x/n)`. -/
noncomputable def logClassSum (q : ℕ) (a : ZMod q) (x : ℕ) : ℝ :=
  ∑ n ∈ (range (x + 1)).filter (fun n : ℕ => (n : ZMod q) = a), (Λ n : ℝ) * Real.log ((x : ℝ) / n)

lemma logClassSum_orthogonality {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (x : ℕ) :
    ((q.totient : ℂ)) * (logClassSum q a x : ℂ)
      = ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * logSum χ x := by
  simp only [logSum, mul_sum]
  rw [sum_comm]
  simp only [logClassSum, sum_filter]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun n _ => ?_
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
  have e : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ((Λ n : ℂ) * χ n * (Real.log ((x : ℝ) / n) : ℂ))
      = (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n) * ((Λ n : ℂ) * (Real.log ((x : ℝ) / n) : ℂ)) := by
    rw [sum_mul]; refine sum_congr rfl fun χ _ => by ring
  rw [e, h]
  by_cases han : (n : ZMod q) = a
  · simp [han]
  · have : a ≠ (n : ZMod q) := fun h => han h.symm
    simp [han, this]

lemma log_div_nonneg' {x n : ℕ} (hn : n ≤ x) : 0 ≤ Real.log ((x : ℝ) / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (by exact_mod_cast hn0)]
    simpa using (show (n : ℝ) ≤ x by exact_mod_cast hn)

/-- `Σ_{n ≤ x, (n, q) > 1} Λ(n) log(x/n) ≤ ω(q) log² x`. -/
lemma sum_not_coprime_le {q : ℕ} (hq : q ≠ 0) (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ (range (x + 1)).filter (fun n => ¬ n.Coprime q), (Λ n : ℝ) * Real.log ((x : ℝ) / n)
      ≤ q.primeFactors.card * Real.log x ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have h2 := sum_le_sum_ppF x (fun n => ¬ n.Coprime q) q.primeFactors
    (fun n => Real.log ((x : ℝ) / n)) (fun n hn => log_div_nonneg' hn) (fun n _ hc hpp => by
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      rw [Nat.Prime.pow_minFac hr hk.ne', Nat.mem_primeFactors]
      refine ⟨hr, ?_, hq⟩
      by_contra hd
      exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd)))
  have h3 : ∀ p ∈ q.primeFactors, ∑ n ∈ ppF x p, (Λ n : ℝ) * Real.log ((x : ℝ) / n)
      ≤ Real.log x * Real.log x := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    calc ∑ n ∈ ppF x p, (Λ n : ℝ) * Real.log ((x : ℝ) / n)
        ≤ ∑ n ∈ ppF x p, (Λ n : ℝ) * Real.log x := by
          refine sum_le_sum fun n hn => ?_
          simp only [ppF, mem_filter, mem_range] at hn
          have hn0 : 0 < n := hn.2.1.pos
          apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
          apply Real.log_le_log (by positivity)
          rw [div_le_iff₀ (by exact_mod_cast hn0)]
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
          nlinarith
      _ = (∑ n ∈ ppF x p, (Λ n : ℝ)) * Real.log x := by rw [sum_mul]
      _ ≤ Real.log x * Real.log x :=
          mul_le_mul_of_nonneg_right (sum_ppF_le x p hpp hx) hl
  calc _ ≤ _ := h2
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log x * Real.log x := sum_le_sum h3
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- The principal character. -/
lemma re_logSum_one_ge (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (x : ℕ) (hx : 1 ≤ x) :
    (x : ℝ) - 3 / 20 * √(x : ℝ) - 3 * Real.log x - 3 - q.primeFactors.card * Real.log x ^ 2
      ≤ (logSum (1 : DirichletCharacter ℂ q) x).re := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hprin := psiLog_ge hGRH x hx
  have hloss := sum_not_coprime_le hq0 x hx
  have hre : ∑ n ∈ range (x + 1), (Λ n : ℝ) * Real.log ((x : ℝ) / n)
      - ∑ n ∈ (range (x + 1)).filter (fun n => ¬ n.Coprime q), (Λ n : ℝ) * Real.log ((x : ℝ) / n)
      ≤ (logSum (1 : DirichletCharacter ℂ q) x).re := by
    rw [re_logSum_eq, sum_filter, ← sum_sub_distrib]
    refine le_of_eq (sum_congr rfl fun n hn => ?_)
    by_cases hc : n.Coprime q
    · have : ((1 : DirichletCharacter ℂ q) n) = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 hc)
      simp [hc, this]
    · have : ((1 : DirichletCharacter ℂ q) n) = 0 :=
        MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h))
      simp [hc, this]
  linarith

lemma card_dirichletCharacter' (q : ℕ) [NeZero q] :
    (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

/-- All non-principal characters together. -/
theorem sum_norm_logSum_le (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (x : ℕ) (hx : 1 ≤ x) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖logSum χ x‖
      ≤ (√(x : ℝ) + 1 + Real.log x) * (11 / 10 * (((q.totient : ℝ) - 1)
          * (Real.log q + Real.log 2 - 7 / 5) + 3280))
        + ((q.totient : ℝ) - 1) * ((Real.log q + 2.52) * Real.log x
          + (Real.log x ^ 2 / 2 + 5 * Real.log x + 2) + q.primeFactors.card * Real.log x ^ 2) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  set E := (Real.log q + 2.52) * Real.log x + (Real.log x ^ 2 / 2 + 5 * Real.log x + 2)
    + q.primeFactors.card * Real.log x ^ 2 with hE
  set c := √(x : ℝ) + 1 + Real.log x with hc
  have hc0 : 0 ≤ c := by positivity
  -- per character
  have hper : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖logSum χ x‖
      ≤ c * (11 / 10 * (Real.log q + Real.log 2 - 7 / 5 + (ld χ ((1 + 1 / 20 : ℝ) : ℂ)).re + (ld χ⁻¹ ((1 + 1 / 20 : ℝ) : ℂ)).re)) + E := by
    intro χ hχ
    have hχ1 : χ ≠ 1 := (mem_erase.1 hχ).1
    have : NeZero χ.conductor := ⟨fun h => hq0
      (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))⟩
    set ψ := χ.primitiveCharacter
    have hfq : χ.conductor ∣ q := χ.conductor_dvd_level
    have hprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hψ1 : ψ ≠ 1 := fun h => hχ1 (by
      rw [← χ.changeLevel_primitiveCharacter]
      change DirichletCharacter.changeLevel _ ψ = 1
      rw [h, map_one])
    have hlift : DirichletCharacter.changeLevel hfq ψ = χ := χ.changeLevel_primitiveCharacter
    have h1 := norm_logSum_prim_le hGRH hprim hψ1 x hx
    have h2 := norm_logSum_changeLevel_sub_le hfq hq0 ψ x hx
    rw [hlift] at h2
    have h3 := Z2_prim_le hGRH χ hχ1
    have hf : Real.log χ.conductor ≤ Real.log q := Real.log_le_log
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor))
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hfq)
    have htri : ‖logSum χ x‖ ≤ ‖logSum ψ x‖ + ‖logSum χ x - logSum ψ x‖ := by
      have := norm_add_le (logSum ψ x) (logSum χ x - logSum ψ x)
      rwa [add_sub_cancel] at this
    have h4 : c * Z2 ψ ≤ c * (11 / 10 * (Real.log q + Real.log 2 - 7 / 5 + (ld χ ((1 + 1 / 20 : ℝ) : ℂ)).re
        + (ld χ⁻¹ ((1 + 1 / 20 : ℝ) : ℂ)).re)) := mul_le_mul_of_nonneg_left h3 hc0
    have h5 : (Real.log χ.conductor + 2.52) * Real.log x ≤ (Real.log q + 2.52) * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hl
    rw [hE]
    nlinarith
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib, sum_const, ← mul_sum, ← mul_sum]
  have hcard : (((univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) = q.totient - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_dirichletCharacter']
    have : 1 ≤ q.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero hq0)
    push_cast [this]
    ring
  rw [nsmul_eq_mul, hcard]
  have hsum := sum_erase_re_ld_le (q := q) (a := 1 / 20) (by norm_num)
  have hP := (vonMangoldt_rpow_summable_le (a := 1 / 20) (by norm_num)).2
  have hsplit : ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      (Real.log q + Real.log 2 - 7 / 5 + (ld χ ((1 + 1 / 20 : ℝ) : ℂ)).re + (ld χ⁻¹ ((1 + 1 / 20 : ℝ) : ℂ)).re)
      = ((q.totient : ℝ) - 1) * (Real.log q + Real.log 2 - 7 / 5)
        + ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ((ld χ ((1 + 1 / 20 : ℝ) : ℂ)).re + (ld χ⁻¹ ((1 + 1 / 20 : ℝ) : ℂ)).re) := by
    rw [← hcard, ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    refine sum_congr rfl fun χ _ => by ring
  have hmain : 11 / 10 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      (Real.log q + Real.log 2 - 7 / 5 + (ld χ ((1 + 1 / 20 : ℝ) : ℂ)).re + (ld χ⁻¹ ((1 + 1 / 20 : ℝ) : ℂ)).re)
      ≤ 11 / 10 * (((q.totient : ℝ) - 1) * (Real.log q + Real.log 2 - 7 / 5) + 3280) := by
    rw [hsplit]
    have : 2 * ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (1 + 1 / 20 : ℝ) ≤ 3280 := by
      norm_num at hP ⊢; linarith
    nlinarith
  have := mul_le_mul_of_nonneg_left hmain hc0
  linarith

/-- The numerical condition at modulus `q` for the constant `2`. -/
def NumericOK2 (q : ℕ) : Prop :=
  1 ≤ xOf 2 q ∧
    (q : ℝ) * (Real.log 4 * (2 * (xOf 2 q : ℝ) ^ ((2 : ℝ)⁻¹) + 3 * (xOf 2 q : ℝ) ^ ((3 : ℝ)⁻¹)
        + 60 * (xOf 2 q : ℝ) ^ ((4 : ℝ)⁻¹)
        + ((Nat.log 2 (xOf 2 q) : ℕ) : ℝ) ^ 2 * (xOf 2 q : ℝ) ^ ((12 : ℝ)⁻¹)))
      + 3 / 20 * √(xOf 2 q : ℝ) + 3 * Real.log (xOf 2 q) + 3
      + q.primeFactors.card * Real.log (xOf 2 q) ^ 2
      + (√(xOf 2 q : ℝ) + 1 + Real.log (xOf 2 q))
          * (11 / 10 * ((q : ℝ) * (Real.log q + Real.log 2 - 7 / 5) + 3280))
      + (q : ℝ) * ((Real.log q + 2.52) * Real.log (xOf 2 q)
          + (Real.log (xOf 2 q) ^ 2 / 2 + 5 * Real.log (xOf 2 q) + 2)
          + q.primeFactors.card * Real.log (xOf 2 q) ^ 2)
      < (xOf 2 q : ℝ)

theorem exists_prime_of_numericOK2 (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ}
    (hq : 3 ≤ q) (hnum : NumericOK2 q) (a : ℕ) (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ p < xOf 2 q := by
  have : NeZero q := ⟨by omega⟩
  set x := xOf 2 q with hxdef
  obtain ⟨hx1, hnum⟩ := hnum
  rw [← hxdef] at hnum
  by_contra hcon
  have hno : ∀ p < x, p.Prime → ¬ p ≡ a [MOD q] := fun p hp hpp hpa => hcon ⟨p, hpp, hpa, hp⟩
  have hunit : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hl : 0 ≤ Real.log x := Real.log_nonneg hxR
  -- upper bound for the class sum
  have hup : logClassSum q (a : ZMod q) x ≤ PPl x := by
    unfold logClassSum PPl
    rw [sum_filter, sum_filter]
    refine sum_le_sum fun n hn => ?_
    have hnx := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hw := log_div_nonneg' hnx
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    by_cases han : (n : ZMod q) = a
    · by_cases hp : n.Prime
      · have hnx' : n = x := by
          by_contra h
          exact hno n (lt_of_le_of_ne hnx h) hp ((ZMod.natCast_eq_natCast_iff n a q).1 han)
        subst hnx'
        simp [han, hp]
      · simp [han, hp]
    · simp only [han, ↓reduceIte]
      split_ifs <;> positivity
  have hpp := ppl_le x hx1
  -- lower bound from orthogonality
  have horth := congrArg Complex.re (logClassSum_orthogonality hunit x)
  rw [show ((q.totient : ℂ) * (logClassSum q a x : ℂ)) = ((q.totient * logClassSum q a x : ℝ) : ℂ)
    by push_cast; ring, Complex.ofReal_re, Complex.re_sum,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)] at horth
  have hu : IsUnit (a : ZMod q)⁻¹ := by
    obtain ⟨u, hu⟩ := hunit
    rw [← hu, ZMod.inv_coe_unit]; exact Units.isUnit _
  have h1 : ((1 : DirichletCharacter ℂ q) (a : ZMod q)⁻¹) = 1 := MulChar.one_apply hu
  rw [h1, one_mul] at horth
  have hprin := re_logSum_one_ge hGRH (q := q) x hx1
  have hrest : -∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖logSum χ x‖
      ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        ((χ (a : ZMod q)⁻¹) * logSum χ x).re := by
    rw [← sum_neg_distrib]
    refine sum_le_sum fun χ _ => ?_
    have hc : ‖χ (a : ZMod q)⁻¹‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hre := Complex.abs_re_le_norm (χ (a : ZMod q)⁻¹ * logSum χ x)
    rw [norm_mul] at hre
    have : ‖χ (a : ZMod q)⁻¹‖ * ‖logSum χ x‖ ≤ ‖logSum χ x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hc
    rw [abs_le] at hre
    linarith [hre.1]
  have hsum := sum_norm_logSum_le hGRH (q := q) x hx1
  -- totient bounds
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega : 0 < q)
  have hT0 : 0 ≤ logClassSum q (a : ZMod q) x := by
    unfold logClassSum
    exact sum_nonneg fun n hn => mul_nonneg vonMangoldt_nonneg
      (log_div_nonneg' (Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hn).1)))
  have hPP0 : 0 ≤ PPl x := hT0.trans hup
  have hφT : (q.totient : ℝ) * logClassSum q (a : ZMod q) x ≤ q * PPl x :=
    mul_le_mul hφ hup hT0 (by positivity)
  -- `log q ≥ log 3 > 1.09`
  have hL : 1.09 < Real.log q := by
    have h3 : Real.log 3 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    have : (1.09 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      have h2 := Real.exp_bound' (x := 0.09) (by norm_num) (by norm_num) (n := 3) (by norm_num)
      simp [Finset.sum_range_succ, Nat.factorial] at h2
      have e : Real.exp 1.09 = Real.exp 1 * Real.exp 0.09 := by rw [← Real.exp_add]; norm_num
      rw [e]
      have h5 : 0 < Real.exp 0.09 := Real.exp_pos _
      nlinarith
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := Real.log_two_gt_d9
  have hB1 : 0 ≤ Real.log q + Real.log 2 - 7 / 5 := by linarith
  have hω : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  have hB2 : 0 ≤ (Real.log q + 2.52) * Real.log x + (Real.log x ^ 2 / 2 + 5 * Real.log x + 2)
      + q.primeFactors.card * Real.log x ^ 2 := by positivity
  have hc0 : 0 ≤ √(x : ℝ) + 1 + Real.log x := by positivity
  have hm1 : ((q.totient : ℝ) - 1) * (Real.log q + Real.log 2 - 7 / 5)
      ≤ (q : ℝ) * (Real.log q + Real.log 2 - 7 / 5) := mul_le_mul_of_nonneg_right (by linarith) hB1
  have hm2 : ((q.totient : ℝ) - 1) * ((Real.log q + 2.52) * Real.log x
      + (Real.log x ^ 2 / 2 + 5 * Real.log x + 2) + q.primeFactors.card * Real.log x ^ 2)
      ≤ (q : ℝ) * ((Real.log q + 2.52) * Real.log x
      + (Real.log x ^ 2 / 2 + 5 * Real.log x + 2) + q.primeFactors.card * Real.log x ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hB2
  have hm3 : (√(x : ℝ) + 1 + Real.log x) * (11 / 10 * (((q.totient : ℝ) - 1)
      * (Real.log q + Real.log 2 - 7 / 5) + 3280))
      ≤ (√(x : ℝ) + 1 + Real.log x) * (11 / 10 * ((q : ℝ)
      * (Real.log q + Real.log 2 - 7 / 5) + 3280)) := by
    apply mul_le_mul_of_nonneg_left _ hc0; linarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hP : (q : ℝ) * PPl x ≤ (q : ℝ) * (Real.log 4 * (2 * (x : ℝ) ^ ((2 : ℝ)⁻¹)
      + 3 * (x : ℝ) ^ ((3 : ℝ)⁻¹) + 60 * (x : ℝ) ^ ((4 : ℝ)⁻¹)
      + ((Nat.log 2 x : ℕ) : ℝ) ^ 2 * (x : ℝ) ^ ((12 : ℝ)⁻¹))) :=
    mul_le_mul_of_nonneg_left hpp hq0
  linarith

end BachSorenson.Two
