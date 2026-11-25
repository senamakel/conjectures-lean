import LLS.Bach2.Budget
import LLS.Sharp.Principal
import LLS.Thm11.Common

/-!
# The budget for LLS Theorem 1.1 (1)

`LLS.keyP` uses the lower bound `Re Σ_{n ≤ x} Λ(n)ψ(n)/n (1 − n/x) ≥ Pc − Lc_q − Lc_R` for the
Cesàro sum of the primitive character `ψ`. The part of the sum over `n` prime to `q` is also
`≥ 0`, so the bound improves to `max(0, Pc − Lc_q) − Lc_R` (`LLS.Thm11.sum_re_ge_max`). This is
the `max(0, ·)` in LLS's `A(q)`. With it, `LLS.Thm11.budgetM_nonpos` is `LLS.budget_nonpos`
with `2K(Pc − Lc_q)` replaced by `2K max(0, Pc − Lc_q)`, and `LLS.Thm11.budget11` bounds the
prime costs by `ω(q) m(x) + R(x)` and `Lc_q` by `σ(q) = Σ_{p ∣ q} log p/(p − 1)`:

  `base0(x) + 2K max(0, Pc − σ(q)) − κ log q − ω(q) m(x) − R(x) ≤ 0`,

with `m(x) = (log x − ½ log 2)²/2` and `R(x) = (log x − ½ log 2)²/2 + log 2 (K(1 + 1/x) − ½ log x)
+ (log x − ½ log 3)²/2` (the primes `2` and `3`; a prime `p ≥ 5` outside the conductor costs
nothing, by the side condition `R5OK`).
-/

namespace LLS.Thm11

open Real Finset ArithmeticFunction

/-! ### Losses with the `max(0, ·)` -/

theorem sum_re_ge_max {f q : ℕ} (φ : DirichletCharacter ℂ f) (hq : q ≠ 0) (x : ℕ)
    (w : ℕ → ℝ) (hw : ∀ n ≤ x, 0 ≤ w n) (h1 : ∀ n ≤ x, n.Coprime q → φ n = 1) :
    max 0 (∑ n ∈ range (x + 1), (Λ n : ℝ) * w n
        - ∑ p ∈ q.primeFactors, ∑ n ∈ ppF x p, (Λ n : ℝ) * w n)
        - ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f), ∑ n ∈ ppF x p, (Λ n : ℝ) * w n
      ≤ ∑ n ∈ range (x + 1), (Λ n : ℝ) * w n * (φ n).re := by
  classical
  have hcopf : ∀ n : ℕ, φ n ≠ 0 → n.Coprime f := fun n hn => by
    have hu : IsUnit (n : ZMod f) := by
      by_contra h
      exact hn (MulChar.map_nonunit φ h)
    exact (ZMod.isUnit_iff_coprime n f).1 hu
  set C := ∑ n ∈ (range (x + 1)).filter (fun n => n.Coprime q), (Λ n : ℝ) * w n
  set E₁ := ∑ n ∈ (range (x + 1)).filter (fun n => ¬ n.Coprime q), (Λ n : ℝ) * w n
  set E₂ := ∑ n ∈ (range (x + 1)).filter (fun n : ℕ => ¬ n.Coprime q ∧ φ (n : ZMod f) ≠ 0),
    (Λ n : ℝ) * w n
  have hsplit : ∑ n ∈ range (x + 1), (Λ n : ℝ) * w n = C + E₁ :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hC0 : 0 ≤ C := sum_nonneg fun n hn => by
    have hnx : n ≤ x := Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hn).1)
    exact mul_nonneg vonMangoldt_nonneg (hw n hnx)
  have hterm : C - E₂ ≤ ∑ n ∈ range (x + 1), (Λ n : ℝ) * w n * (φ n).re := by
    simp only [C, E₂]
    rw [sum_filter, sum_filter, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    have hnx : n ≤ x := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hlw : 0 ≤ (Λ n : ℝ) * w n := mul_nonneg vonMangoldt_nonneg (hw n hnx)
    by_cases hc : n.Coprime q
    · rw [if_pos hc, if_neg (fun h => h.1 hc), h1 n hnx hc]; simp
    · have hre1 : -1 ≤ (φ n).re := by
        have := Complex.abs_re_le_norm (φ n)
        have := DirichletCharacter.norm_le_one φ n
        rw [abs_le] at *; linarith
      by_cases h0 : φ n = 0
      · simp [hc, h0]
      · simp only [hc, h0, not_false_eq_true, true_and, ne_eq, ite_true, ite_false, zero_sub]
        nlinarith [mul_le_mul_of_nonneg_left hre1 hlw]
  have hE₁ : E₁ ≤ ∑ p ∈ q.primeFactors, ∑ n ∈ ppF x p, (Λ n : ℝ) * w n := by
    refine sum_le_sum_ppF x _ _ w hw fun n _ hc hpp => ?_
    obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    rw [Nat.Prime.pow_minFac hr hk.ne', Nat.mem_primeFactors]
    refine ⟨hr, ?_, hq⟩
    by_contra hd
    exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
  have hE₂ : E₂ ≤ ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f),
      ∑ n ∈ ppF x p, (Λ n : ℝ) * w n := by
    refine sum_le_sum_ppF x _ _ w hw fun n _ hc hpp => ?_
    obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    rw [Nat.Prime.pow_minFac hr hk.ne']
    simp only [mem_filter, Nat.mem_primeFactors]
    refine ⟨⟨hr, ?_, hq⟩, ?_⟩
    · by_contra hd
      exact hc.1 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
    · intro hd
      have hcop := hcopf _ hc.2
      have : r.Coprime f := Nat.Coprime.coprime_dvd_left (dvd_pow_self r hk.ne') hcop
      exact (Nat.Prime.coprime_iff_not_dvd hr).1 this hd
  have hmax : max 0 (∑ n ∈ range (x + 1), (Λ n : ℝ) * w n
      - ∑ p ∈ q.primeFactors, ∑ n ∈ ppF x p, (Λ n : ℝ) * w n) ≤ C :=
    max_le hC0 (by linarith)
  linarith

/-! ### The key inequality with the `max(0, ·)` -/

theorem keyM (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (Pc : ℝ) (hPc : Pc ≤ cesSum x) :
    ∃ lf Z : ℝ, 0 ≤ lf ∧ 0 ≤ Z ∧ ∃ R ⊆ q.primeFactors,
      lf + ∑ p ∈ R, Real.log p ≤ Real.log q ∧
      Z * (1 + 1 / x - 2 / √(x : ℝ)) ≤ lf * (1 - 1 / x)
        - 2 * (max 0 (Pc - ∑ p ∈ q.primeFactors, lcp x p) - ∑ p ∈ R, lcp x p)
        + 2 * Eshift x ∧
      (x : ℝ) - 3 / 20 * √(x : ℝ) - 3 * Real.log x - 3
          - ∑ p ∈ q.primeFactors, llp x p - ∑ p ∈ R, llp x p
        ≤ (√(x : ℝ) + 1) * Z + (lf + Z) / 2 * Real.log x
          - 1 / 2 * Real.log Real.pi * Real.log x + Etil x := by
  classical
  set f := χ.conductor with hf
  have hfq : f ∣ q := χ.conductor_dvd_level
  have hq0 : q ≠ 0 := NeZero.ne q
  have hf0 : f ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hfq))
  have : NeZero f := ⟨hf0⟩
  set ψ := χ.primitiveCharacter
  have hψprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hψ1 : ψ ≠ 1 := fun h => hχ (by
    rw [← χ.changeLevel_primitiveCharacter]
    change DirichletCharacter.changeLevel _ ψ = 1
    rw [h, map_one])
  have hψi1 : ψ⁻¹ ≠ 1 := by simpa using hψ1
  have hψiprim : ψ⁻¹.IsPrimitive := hψprim.inv
  have hψval : ∀ n : ℕ, n.Coprime q → ψ n = χ n := fun n hn => by
    have := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.2 hn)
    simpa using this
  have h1 : ∀ n ≤ x, n.Coprime q → ψ n = 1 := fun n hn hc => by
    rw [hψval n hc, hval n hn hc]
  have h1i : ∀ n ≤ x, n.Coprime q → ψ⁻¹ n = 1 := fun n hn hc => by
    rw [MulChar.inv_apply_eq_inv', h1 n hn hc, inv_one]
  set R := q.primeFactors.filter (fun p => ¬ p ∣ f) with hR
  have hx1 : 1 ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  have lowS : ∀ φ : DirichletCharacter ℂ f, (∀ n ≤ x, n.Coprime q → φ n = 1) →
      (x : ℝ) - 3 / 20 * √(x : ℝ) - 3 * Real.log x - 3
          - ∑ p ∈ q.primeFactors, llp x p - ∑ p ∈ R, llp x p ≤ (logSum φ x).re := by
    intro φ hφ
    have hPL := psiLog_ge hGRH x hx1
    have := sum_re_ge φ hfq hq0 x (fun n => Real.log ((x : ℝ) / n))
      (fun n hn => log_div_nonneg hn) hφ
    rw [re_logSum_eq]
    simp only [llp, hR] at *
    linarith
  have lowC : ∀ φ : DirichletCharacter ℂ f, (∀ n ≤ x, n.Coprime q → φ n = 1) →
      max 0 (Pc - ∑ p ∈ q.primeFactors, lcp x p) - ∑ p ∈ R, lcp x p
        ≤ (cesShift φ x).re := by
    intro φ hφ
    have := sum_re_ge_max φ hq0 x (fun n => 1 / (n : ℝ) * (1 - (n : ℝ) / x))
      (fun n hn => ces_weight_nonneg hn) hφ
    rw [re_cesShift_eq]
    have hm : max 0 (Pc - ∑ p ∈ q.primeFactors, lcp x p)
        ≤ max 0 (cesSum x - ∑ p ∈ q.primeFactors, lcp x p) := max_le_max le_rfl (by linarith)
    simp only [lcp, hR, cesSum] at *
    linarith
  have uS := re_logSum_le hGRH hψprim hψ1 x hx1
  have uSi := re_logSum_le hGRH hψiprim hψi1 x hx1
  have uC := re_cesShift_le hGRH hψprim hψ1 x hx2
  have uCi := re_cesShift_le hGRH hψiprim hψi1 x hx2
  rw [inv_inv] at uSi uCi
  obtain ⟨-, hZ⟩ := Z2_eq hGRH hψprim hψ1
  obtain ⟨-, hZi⟩ := Z2_eq hGRH hψiprim hψi1
  rw [inv_inv] at hZi
  set U := (D ψ 1).re
  set V := (D ψ⁻¹ 1).re
  set Z := Z2 ψ
  have hZZ : Z2 ψ⁻¹ = Z := by rw [hZi, hZ]; ring
  rw [hZZ] at uSi uCi
  set lf := Real.log f
  have hlf : 0 ≤ lf := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hf0)
  refine ⟨lf, Z, hlf, Z2_nonneg ψ, R, filter_subset _ _, log_add_sum_log_le hfq hq0, ?_, ?_⟩
  · have l1 := lowC ψ h1
    have l2 := lowC ψ⁻¹ h1i
    set a := 1 / (x : ℝ)
    set b := 1 / √(x : ℝ)
    have e1 : (lf + V) / (x : ℝ) = (lf + V) * a := by simp [a, div_eq_mul_inv]
    have e2 : (lf + U) / (x : ℝ) = (lf + U) * a := by simp [a, div_eq_mul_inv]
    have e3 : Z / √(x : ℝ) = Z * b := by simp [b, div_eq_mul_inv]
    have e4 : 2 / √(x : ℝ) = 2 * b := by simp [b, div_eq_mul_inv]
    rw [e1, e3] at uC
    rw [e2, e3] at uCi
    rw [e4]
    have hUV : U + V = Z - lf := by rw [hZ]; ring
    have hUVa : U * a + V * a = Z * a - lf * a := by rw [← add_mul, hUV, sub_mul]
    linarith
  · have l1 := lowS ψ h1
    have l2 := lowS ψ⁻¹ h1i
    have hUV : U + V = Z - lf := by rw [hZ]; ring
    have hUVl : U * Real.log x + V * Real.log x = Z * Real.log x - lf * Real.log x := by
      rw [← add_mul, hUV, sub_mul]
    linarith

/-! ### The budget -/

/-- The main terms of the budget without the Cesàro sum. -/
noncomputable def base0 (x : ℝ) : ℝ :=
  x - 3 / 20 * √x - 3 * Real.log x - 3 - 2 * Kc x * Eshift x
    + 1 / 2 * Real.log Real.pi * Real.log x - Etil x

theorem budgetM_nonpos (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (Pc : ℝ) (hPc : Pc ≤ cesSum x) (C : ℝ)
    (hC : ∀ R ⊆ q.primeFactors, ∑ p ∈ q.primeFactors, llp x p
        + ∑ p ∈ R, (llp x p + 2 * Kc x * lcp x p - kap x * Real.log p) ≤ C) :
    base0 x + 2 * Kc x * max 0 (Pc - ∑ p ∈ q.primeFactors, lcp x p)
      - kap x * Real.log q - C ≤ 0 := by
  classical
  obtain ⟨lf, Z, hlf, hZ0, R, hRq, hlog, h1, h2⟩ := keyM hGRH χ hχ x hx hval Pc hPc
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  set s := √(x : ℝ)
  set l := Real.log x
  set den := 1 + 1 / (x : ℝ) - 2 / s
  have hden : 3 / 4 ≤ den := den_pos hxR
  set K := Kc x
  have hKdef : K * den = s + 1 + l / 2 := by
    show Kc x * den = _
    unfold Kc
    exact div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hK0 : 0 < K := Kc_pos hxR
  set M := max 0 (Pc - ∑ p ∈ q.primeFactors, lcp x p)
  set SCR := ∑ p ∈ R, lcp x p
  set SL := ∑ p ∈ q.primeFactors, llp x p
  set SLR := ∑ p ∈ R, llp x p
  set SRlog := ∑ p ∈ R, Real.log p
  have hN : (s + 1 + l / 2) * Z ≤ K * (lf * (1 - 1 / x) - 2 * (M - SCR) + 2 * Eshift x) := by
    rw [← hKdef]
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    nlinarith
  have hS : (x : ℝ) - 3 / 20 * s - 3 * l - 3 - SL - SLR
      ≤ K * (lf * (1 - 1 / x) - 2 * (M - SCR) + 2 * Eshift x) + lf / 2 * l
        - 1 / 2 * Real.log Real.pi * l + Etil x := by
    have : (√(x : ℝ) + 1) * Z + (lf + Z) / 2 * l = (s + 1 + l / 2) * Z + lf / 2 * l := by ring
    linarith
  have hkap0 : 0 ≤ kap x := by
    have h1x : 0 ≤ 1 - 1 / (x : ℝ) := by
      have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    unfold kap; positivity
  have hlf' : K * (lf * (1 - 1 / x)) + lf / 2 * l ≤ kap x * (Real.log q - SRlog) := by
    have : K * (lf * (1 - 1 / x)) + lf / 2 * l = kap x * lf := by simp only [kap, K, l]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hkap0
  have hcost : SL + (SLR + 2 * K * SCR - kap x * SRlog) ≤ C := by
    have := hC R hRq
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at this
    simp only [SL, SLR, SCR, SRlog, K]
    linarith
  unfold base0
  change (x : ℝ) - 3 / 20 * s - 3 * l - 3 - 2 * K * Eshift x
    + 1 / 2 * Real.log Real.pi * l - Etil x + 2 * K * M - kap x * Real.log q - C ≤ 0
  have hexp : K * (lf * (1 - 1 / x) - 2 * (M - SCR) + 2 * Eshift x)
      = K * (lf * (1 - 1 / x)) - 2 * K * M + 2 * K * SCR + 2 * K * Eshift x := by ring
  have hkq : kap x * (Real.log q - SRlog) = kap x * Real.log q - kap x * SRlog := by ring
  nlinarith

/-! ### The cost of the primes dividing `q` -/

/-- `m(x) = (log x − ½ log 2)²/2`, the bound for `llp x p` at every prime `p`. -/
noncomputable def mC (x : ℝ) : ℝ := (Real.log x - Real.log 2 / 2) ^ 2 / 2

/-- The cost of the primes `2` and `3` outside the conductor. -/
noncomputable def RC (x : ℝ) : ℝ :=
  (Real.log x - Real.log 2 / 2) ^ 2 / 2 + Real.log 2 * (Kc x * (1 + 1 / x) - Real.log x / 2)
    + (Real.log x - Real.log 3 / 2) ^ 2 / 2

/-- The side condition making the primes `p ≥ 5` outside the conductor free. -/
def R5OK (x : ℝ) : Prop :=
  (Real.log x - Real.log 5 / 2) ^ 2 / 2 ≤ Real.log 5 * (Kc x / 2 - Kc x / x + Real.log x / 2)

/-- `σ(q) = Σ_{p ∣ q} log p/(p − 1)`. -/
noncomputable def sig (q : ℕ) : ℝ := ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1)

lemma llp_le_mC (x p : ℕ) (hx : 64 ≤ x) (hp : p.Prime) : llp x p ≤ mC x := by
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hl4 := log_ge_four hxR
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  rcases lt_or_ge x p with h | h
  · rw [llp_eq_zero hp h]; unfold mC; positivity
  · have h1 := llp_le x p hp (by omega)
    have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hlpx : Real.log p ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h)
    unfold mC
    have : (Real.log x - Real.log p / 2) ^ 2 ≤ (Real.log x - Real.log 2 / 2) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    linarith

lemma Kc_div_le {x : ℝ} (hx : 64 ≤ x) : Kc x / x ≤ Real.log x / 2 := by
  have hs8 := sqrt_ge_eight hx
  have hl4 := log_ge_four hx
  have hden := den_pos hx
  have hsq : √x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hK : Kc x ≤ (√x + 1 + Real.log x / 2) / (3 / 4) := by
    unfold Kc
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hden
  rw [div_le_iff₀ (by linarith)]
  have : (√x + 1 + Real.log x / 2) / (3 / 4) ≤ Real.log x / 2 * x := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- The cost of one prime outside the conductor. -/
lemma r_cost_le (x p : ℕ) (hx : 64 ≤ x) (hp : p.Prime) (h5 : R5OK x) :
    llp x p + 2 * Kc x * lcp x p - kap x * Real.log p
      ≤ if p = 2 then (Real.log x - Real.log 2 / 2) ^ 2 / 2
          + Real.log 2 * (Kc x * (1 + 1 / x) - Real.log x / 2)
        else if p = 3 then (Real.log x - Real.log 3 / 2) ^ 2 / 2 else 0 := by
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hK := Kc_pos hxR
  have hl4 := log_ge_four hxR
  have hKx := Kc_div_le hxR
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hkap : kap x = Kc x * (1 - 1 / x) + Real.log x / 2 := rfl
  have hKx' : Kc x * (1 / x) = Kc x / x := by ring
  rcases lt_or_ge x p with hpx | hpx
  · rw [llp_eq_zero hp hpx, lcp_eq_zero hp hpx]
    have hk0 : 0 ≤ kap x := by
      rw [hkap]
      have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have hpx' : 5 ≤ p := by
      have : 64 < p := by omega
      omega
    rw [if_neg (show p ≠ 2 by omega), if_neg (show p ≠ 3 by omega)]
    nlinarith
  have h1 := llp_le x p hp (by omega)
  have h2 := lcp_le x p hp (by omega)
  have hlpx : Real.log p ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpx)
  have h2K := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * Kc x)
  split_ifs with h2p h3p
  · subst h2p
    simp only [Nat.cast_ofNat] at h1 h2K
    have e : Real.log 2 / ((2 : ℝ) - 1) = Real.log 2 := by norm_num
    rw [e] at h2K
    rw [hkap]
    have e2 : Real.log 2 * (Kc x * (1 + 1 / x) - Real.log x / 2)
        = 2 * Kc x * Real.log 2 - (Kc x * (1 - 1 / x) + Real.log x / 2) * Real.log 2 := by ring
    simp only [Nat.cast_ofNat]
    linarith
  · subst h3p
    simp only [Nat.cast_ofNat] at h1 h2K
    have e : Real.log 3 / ((3 : ℝ) - 1) = Real.log 3 / 2 := by norm_num
    rw [e] at h2K
    rw [hkap]
    have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have e2 : 2 * Kc x * (Real.log 3 / 2) - (Kc x * (1 - 1 / x) + Real.log x / 2) * Real.log 3
        = Real.log 3 * (Kc x / x - Real.log x / 2) := by ring
    have : Real.log 3 * (Kc x / x - Real.log x / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hl3 (by linarith)
    simp only [Nat.cast_ofNat]
    linarith
  · have hp5 : 5 ≤ p := by
      have := hp.two_le
      by_contra h
      interval_cases p <;> simp_all (config := { decide := true })
    have hl5 : Real.log 5 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp5)
    have hp1 : (4 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      linarith
    have hc : Real.log p / ((p : ℝ) - 1) ≤ Real.log p / 4 :=
      div_le_div_of_nonneg_left hlp0 (by norm_num) hp1
    have hsq : (Real.log x - Real.log p / 2) ^ 2 ≤ (Real.log x - Real.log 5 / 2) ^ 2 := by
      have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    unfold R5OK at h5
    have hbr : 0 ≤ Kc x / 2 - Kc x / x + Real.log x / 2 := by nlinarith
    have : Real.log 5 * (Kc x / 2 - Kc x / x + Real.log x / 2)
        ≤ Real.log p * (Kc x / 2 - Kc x / x + Real.log x / 2) := mul_le_mul_of_nonneg_right hl5 hbr
    rw [hkap]
    nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ 2 * Kc x)]

/-- **The budget for Theorem 1.1 (1).** -/
theorem budget11 (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (Pc : ℝ) (hPc : Pc ≤ cesSum x) (h5 : R5OK x) :
    base0 x + 2 * Kc x * max 0 (Pc - sig q) - kap x * Real.log q
      - (q.primeFactors.card : ℝ) * mC x - RC x ≤ 0 := by
  classical
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hK := Kc_pos hxR
  have hl4 := log_ge_four hxR
  have hKx := Kc_div_le hxR
  -- `Lc_q ≤ σ(q)`
  have hLc : ∑ p ∈ q.primeFactors, lcp x p ≤ sig q := by
    unfold sig
    refine sum_le_sum fun p hp => ?_
    exact lcp_le x p (Nat.prime_of_mem_primeFactors hp) (by omega)
  have hmax : max 0 (Pc - sig q) ≤ max 0 (Pc - ∑ p ∈ q.primeFactors, lcp x p) :=
    max_le_max le_rfl (by linarith)
  have hRC2 : 0 ≤ (Real.log x - Real.log 2 / 2) ^ 2 / 2
      + Real.log 2 * (Kc x * (1 + 1 / x) - Real.log x / 2) := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : Real.log x / 2 ≤ Kc x * (1 + 1 / x) := by
      have := Kc_pos hxR
      have hs := sqrt_ge_eight hxR
      have : Real.log x / 2 ≤ Kc x := by
        have hden := den_pos hxR
        have hlx : Real.log x = 2 * Real.log √(x : ℝ) := by
          rw [← Real.log_rpow (by positivity), Real.rpow_two, Real.sq_sqrt (by positivity)]
        have hls := Real.log_le_sub_one_of_pos (show 0 < √(x : ℝ) by positivity)
        have hd2 : 1 + 1 / (x : ℝ) - 2 / √(x : ℝ) ≤ 2 := by
          have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          have : 0 ≤ 2 / √(x : ℝ) := by positivity
          linarith
        unfold Kc
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      have : 0 ≤ Kc x * (1 / x) := by positivity
      nlinarith
    nlinarith
  have hRC3 : 0 ≤ (Real.log x - Real.log 3 / 2) ^ 2 / 2 := by positivity
  have hC : ∀ R ⊆ q.primeFactors, ∑ p ∈ q.primeFactors, llp x p
      + ∑ p ∈ R, (llp x p + 2 * Kc x * lcp x p - kap x * Real.log p)
        ≤ (q.primeFactors.card : ℝ) * mC x + RC x := by
    intro R hR
    have hA : ∑ p ∈ q.primeFactors, llp x p ≤ (q.primeFactors.card : ℝ) * mC x := by
      have := sum_le_sum fun p (hp : p ∈ q.primeFactors) =>
        llp_le_mC x p hx (Nat.prime_of_mem_primeFactors hp)
      simpa [sum_const, nsmul_eq_mul] using this
    have hB : ∑ p ∈ R, (llp x p + 2 * Kc x * lcp x p - kap x * Real.log p) ≤ RC x := by
      set g : ℕ → ℝ := fun p => if p = 2 then (Real.log x - Real.log 2 / 2) ^ 2 / 2
          + Real.log 2 * (Kc x * (1 + 1 / x) - Real.log x / 2)
        else if p = 3 then (Real.log x - Real.log 3 / 2) ^ 2 / 2 else 0
      have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [g]; split_ifs <;> linarith
      calc ∑ p ∈ R, (llp x p + 2 * Kc x * lcp x p - kap x * Real.log p) ≤ ∑ p ∈ R, g p :=
            sum_le_sum fun p hp => r_cost_le x p hx (Nat.prime_of_mem_primeFactors (hR hp)) h5
        _ ≤ ∑ p ∈ ({2, 3} : Finset ℕ), g p := by
            rw [← sum_filter_ne_zero]
            refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hg0 p
            intro p hp
            simp only [mem_filter] at hp
            simp only [mem_insert, mem_singleton]
            by_contra h
            push Not at h
            apply hp.2
            simp [g, h.1, h.2]
        _ = RC x := by simp [g, RC]
    linarith
  have := budgetM_nonpos hGRH χ hχ x hx hval Pc hPc _ hC
  nlinarith [mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ 2 * Kc x)]

/-! ### The Cesàro lower bound -/

/-- The lower bound used for `Σ_{n ≤ x} Λ(n)/n (1 − n/x)`. -/
noncomputable def PcF (x : ℝ) : ℝ :=
  if 100 ≤ x then Real.log x - 1 - eulerMascheroniConstant - 0.25 / √x - 12 / x
  else Real.log x - 2

theorem PcF_le (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) (x : ℕ) (hx : 64 ≤ x) :
    PcF x ≤ cesSum x := by
  have hces : cesSum x = LLS.P2sum x := by
    unfold cesSum LLS.P2sum
    rw [sum_range_succ, div_self (by positivity : (x : ℝ) ≠ 0)]
    simp only [sub_self, mul_zero, add_zero]
    refine sum_congr rfl fun n _ => by ring
  unfold PcF
  split_ifs with h
  · have hB := LLS.psi1NatBound_of_GRH hGRH
    have hxR : (100 : ℝ) ≤ x := h
    have hx0 : (0 : ℝ) < x := by linarith
    obtain ⟨h1, h2, h3⟩ := Sharp.Hg_inv_bounds hB (x := (x : ℝ)) (by linarith)
    rw [hces, Sharp.P2sum_eq_Hg x (by omega), h1]
    rw [Sharp.rpow_neg_half_eq hx0, Sharp.rpow_neg_one_eq] at h2 h3
    have a1 := (abs_le.mp h2).1
    have a2 := (abs_le.mp h3).2
    have e : 0.25 / √(x : ℝ) + 12 / x = 1 / √(x : ℝ) / 20 + 4 * (1 / x)
        + 2 * (1 / √(x : ℝ) / 10 + 4 * (1 / x)) := by ring
    linarith
  · have hPc := LLS.vonMangoldt_ces_ge x (by omega)
    refine hPc.trans (le_of_eq ?_)
    unfold cesSum
    rw [sum_range_succ, div_self (by positivity : (x : ℝ) ≠ 0)]
    simp only [sub_self, mul_zero, add_zero]
    refine sum_congr rfl fun n _ => by ring

end LLS.Thm11
