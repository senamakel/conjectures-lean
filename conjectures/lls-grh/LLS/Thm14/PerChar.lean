import LLS.Thm14.Prim
import LLS.Numerics.Budget
import LLS.Numerics.Interval
import LLS.L1.Principal
import LLS.Sharp.Principal

/-!
# The bound for one non-principal character, LLS (4.4)–(4.8) with absolute values

For `χ ≠ 1` mod `q`, `s ≥ 31622`, `X = s²`, `l = log X`, `L = log q` and
`A = (s + 1)/(1 − 1/s)²`, `LLS.Thm14.norm_logSum_char` gives

  `|S(X, χ)| ≤ Pc(L, s, l) − 2A Re S'(X, χ)`,

with `S'` the Cesàro sum of LLS Lemma 2.3 and
`Pc = A((1 − 1/X)L − 1.72 + log 2 (1 + 1/X) + log 3/X) + (l − ½ log 2)²/2 + (l − ½ log 3)²/2
  + (0.627 L + 5.93) l + ½ l max(L − 3, l + 2) + 5/4`.

The primitive character `ψ` mod `f` inducing `χ` differs from `χ` only at the prime powers of
the primes `p ∣ q`, `p ∤ f`, where `|ψ| ≤ 1` (no value of `ψ(p)` is assumed). Each such prime
costs `llp + 2A lcp` and saves `A (1 − 1/X) log p` through `log f ≤ log q − Σ log p`; the net
cost is at most the `log 2`, `log 3` terms above, and is negative for `p ≥ 5`.
-/

namespace LLS.Thm14

open Complex ArithmeticFunction Finset Erdos985 Erdos985.Analytic

/-- `A(s) = (s + 1)/(1 − 1/s)²`. -/
noncomputable def Acoef (s : ℝ) : ℝ := (s + 1) / (1 - 1 / s) ^ 2

/-- The per-character bound. -/
noncomputable def Pc (L s l : ℝ) : ℝ :=
  Acoef s * ((1 - 1 / s ^ 2) * L - 1.72 + Real.log 2 * (1 + 1 / s ^ 2) + Real.log 3 / s ^ 2)
    + (l - Real.log 2 / 2) ^ 2 / 2 + (l - Real.log 3 / 2) ^ 2 / 2
    + (0.627 * L + 5.93) * l + (1 / 2 * l * max (L - 3) (l + 2) + 5 / 4)

/-! ### Numerical facts -/

lemma logX_ge {s : ℕ} (hs : 31622 ≤ s) : 20.72 ≤ Real.log ((s ^ 2 : ℕ) : ℝ) := by
  have h := LLS.log_ge_of_pow 999950884 30614 1024 (by norm_num) (by decide +kernel)
  have h2 : Real.log ((999950884 : ℕ) : ℝ) ≤ Real.log ((s ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by nlinarith : 999950884 ≤ s ^ 2))
  norm_num at h h2 ⊢
  linarith

lemma sq_log_le {s : ℕ} (hs : 31622 ≤ s) : Real.log ((s ^ 2 : ℕ) : ℝ) ^ 2 ≤ s := by
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hsR : (31622 : ℝ) ≤ s := by exact_mod_cast hs
  have h1 := Real.log_le_rpow_div hs0 (show (0 : ℝ) < 1 / 4 by norm_num)
  have e : Real.log ((s ^ 2 : ℕ) : ℝ) = 2 * Real.log s := by push_cast; rw [Real.log_pow]; norm_num
  rw [e]
  have hq : ((s : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √(s : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0, Real.sqrt_eq_rpow]; norm_num
  have hsq : √(s : ℝ) * √(s : ℝ) = s := Real.mul_self_sqrt hs0
  have h64 : (64 : ℝ) ≤ √(s : ℝ) := by
    rw [show (64 : ℝ) = √4096 by rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hl0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have h2 : Real.log s ≤ 4 * (s : ℝ) ^ (1 / 4 : ℝ) := by
    have := h1; rw [div_eq_mul_inv] at this; norm_num at this ⊢; linarith
  have h3 : Real.log s ^ 2 ≤ 16 * √(s : ℝ) := by
    rw [← hq]; nlinarith
  nlinarith

lemma EUpar_le (a : ℕ) {x : ℝ} (hx : 10 ^ 8 ≤ x) : LLS.Sharp.EUpar a x ≤ -0.86 := by
  obtain ⟨g1, g2, p1, p2, l1, l2⟩ := LLS.Sharp.consts
  have hx0 : 0 < x := by linarith
  have hinv : 1 / x ≤ 1 / 10 ^ 8 := one_div_le_one_div_of_le (by norm_num) hx
  have hinv0 : 0 ≤ 1 / x := by positivity
  have hlx : Real.log x / x ≤ 1 / 1000 := by
    have hsx := Real.sqrt_nonneg x
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx0)
    rw [Real.log_sqrt hx0.le] at h1
    have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
    have h31 : (10000 : ℝ) ≤ √x := by
      rw [show (10000 : ℝ) = √(10000 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [div_le_iff₀ hx0]
    nlinarith
  have hlx' : 1 / x * Real.log x ≤ 1 / 1000 := by rw [one_div_mul_eq_div]; exact hlx
  unfold LLS.Sharp.EUpar LLS.Sharp.G3par
  split_ifs <;> first | contradiction | nlinarith

lemma gamma100 (a : ℕ) :
    max |LLS.Sharp.ELpar a (100 : ℕ)| |LLS.Sharp.EUpar a (100 : ℕ)| ≤ 1.5 := by
  obtain ⟨g1, g2, p1, p2, l1, l2⟩ := LLS.Sharp.consts
  have h1 := LLS.log_ge_of_pow 100 6803 1024 (by norm_num) (by decide +kernel)
  have h2 := LLS.log_le_of_pow 100 6804 1024 (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at h1 h2 ⊢
  unfold LLS.Sharp.ELpar LLS.Sharp.EUpar LLS.Sharp.G3par
  split_ifs <;> first | contradiction |
    (rw [max_le_iff, abs_le, abs_le]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith)

lemma P2sum100_le (hGRH : DirichletLNonvanishingRightOfHalf) : LLS.P2sum 100 ≤ 3.18 := by
  have h := LLS.Sharp.P2sum_le_sharp (LLS.psi1NatBound_of_GRH hGRH) 100 le_rfl
  obtain ⟨g1, -, -, -, -, -⟩ := LLS.Sharp.consts
  have h2 := LLS.log_le_of_pow 100 6804 1024 (by norm_num) (by norm_num) (by decide +kernel)
  have hs : √((100 : ℕ) : ℝ) = 10 := by
    rw [show ((100 : ℕ) : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs] at h
  push_cast at h h2
  linarith

/-! ### Comparing a character with the primitive character inducing it -/

lemma cesShift_eq_succ {M : ℕ} (φ : DirichletCharacter ℂ M) (x : ℕ) :
    LLS.cesShift φ x = ∑ n ∈ range (x + 1),
      (Λ n : ℂ) * φ n * ((1 / (n : ℝ) * (1 - (n : ℝ) / x) : ℝ) : ℂ) := by
  rw [LLS.cesShift, sum_range_succ]
  have hlast : (Λ x : ℂ) * φ x * ((1 / (x : ℝ) * (1 - (x : ℝ) / x) : ℝ) : ℂ) = 0 := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
      simp [div_self this]
  rw [hlast, add_zero]
  refine sum_congr rfl fun n _ => ?_
  push_cast; ring

theorem norm_diff_le {f q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ f) (hval : ∀ n : ℕ, n.Coprime q → ψ n = χ n) (x : ℕ)
    (w : ℕ → ℝ) (hw : ∀ n ≤ x, 0 ≤ w n) :
    ‖∑ n ∈ range (x + 1), (Λ n : ℂ) * χ n * (w n : ℂ)
        - ∑ n ∈ range (x + 1), (Λ n : ℂ) * ψ n * (w n : ℂ)‖
      ≤ ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ f), ∑ n ∈ ppF x p, (Λ n : ℝ) * w n := by
  classical
  have hq : q ≠ 0 := NeZero.ne q
  have hcopf : ∀ n : ℕ, ψ n ≠ 0 → n.Coprime f := fun n hn => by
    have hu : IsUnit (n : ZMod f) := by
      by_contra h
      exact hn (MulChar.map_nonunit ψ h)
    exact (ZMod.isUnit_iff_coprime n f).1 hu
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ range (x + 1), ‖(Λ n : ℂ) * χ n * (w n : ℂ) - (Λ n : ℂ) * ψ n * (w n : ℂ)‖
      ≤ if (¬ n.Coprime q ∧ ψ (n : ZMod f) ≠ 0) then (Λ n : ℝ) * w n else 0 := by
    intro n hn
    have hnx : n ≤ x := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have hlw : 0 ≤ (Λ n : ℝ) * w n := mul_nonneg vonMangoldt_nonneg (hw n hnx)
    by_cases hc : n.Coprime q
    · rw [if_neg (fun h => h.1 hc), hval n hc, sub_self, norm_zero]
    · have hχ0 : χ n = 0 := by
        have : ¬ IsUnit (n : ZMod q) := fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h)
        exact MulChar.map_nonunit χ this
      by_cases h0 : ψ n = 0
      · rw [if_neg (fun h => h.2 h0), hχ0, h0]; simp
      · rw [if_pos ⟨hc, h0⟩, hχ0]
        have e : (Λ n : ℂ) * 0 * (w n : ℂ) - (Λ n : ℂ) * ψ n * (w n : ℂ)
            = -((((Λ n : ℝ) * w n : ℝ) : ℂ) * ψ n) := by push_cast; ring
        rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlw]
        have := DirichletCharacter.norm_le_one ψ n
        nlinarith
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  refine sum_le_sum_ppF x _ _ w hw fun n _ hc hpp => ?_
  obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
  rw [Nat.Prime.pow_minFac hr hk.ne']
  simp only [mem_filter, Nat.mem_primeFactors]
  refine ⟨⟨hr, ?_, hq⟩, ?_⟩
  · by_contra hd
    exact hc.1 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
  · intro hd
    have hcop := hcopf _ hc.2
    have : r.Coprime f := Nat.Coprime.coprime_dvd_left (dvd_pow_self r hk.ne') hcop
    exact (Nat.Prime.coprime_iff_not_dvd hr).1 this hd

/-! ### The cost of the primes dividing `q` but not the conductor -/

lemma prime_cost (s : ℕ) (hs : 31622 ≤ s) (p : ℕ) (hp : p.Prime) :
    llp (s ^ 2) p + 2 * Acoef s * lcp (s ^ 2) p
        - Acoef s * (1 - 1 / (s : ℝ) ^ 2) * Real.log p
      ≤ (if p = 2 then Acoef s * Real.log 2 * (1 + 1 / (s : ℝ) ^ 2)
            + (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 2 / 2) ^ 2 / 2
          else if p = 3 then Acoef s * Real.log 3 / (s : ℝ) ^ 2
            + (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 3 / 2) ^ 2 / 2
          else 0) := by
  set X := s ^ 2
  set l := Real.log ((X : ℕ) : ℝ)
  have hsR : (31622 : ℝ) ≤ s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) < s := by linarith
  have hA : (s : ℝ) ≤ Acoef s := by
    unfold Acoef
    have h1 : 0 < 1 - 1 / (s : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; exact hs1
    have h2 : (1 - 1 / (s : ℝ)) ^ 2 ≤ 1 := by
      have : 1 / (s : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith [one_div_pos.2 (show (0 : ℝ) < s by linarith)]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hA0 : 0 ≤ Acoef s := by linarith
  have hX : (1 : ℕ) ≤ X := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hl := logX_ge hs
  have hl2 := sq_log_le hs
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hsq1 : 1 / (s : ℝ) ^ 2 ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsq0 : 0 ≤ 1 / (s : ℝ) ^ 2 := by positivity
  have hX2 : ((X : ℕ) : ℝ) = (s : ℝ) ^ 2 := by simp [X]
  have log2 := Real.log_two_gt_d9
  have hid2 : Acoef s * Real.log 2 * (1 + 1 / (s : ℝ) ^ 2)
      + Acoef s * (1 - 1 / (s : ℝ) ^ 2) * Real.log 2 = 2 * Acoef s * Real.log 2 := by ring
  have hid3 : Acoef s * Real.log 3 / (s : ℝ) ^ 2
      + Acoef s * (1 - 1 / (s : ℝ) ^ 2) * Real.log 3 = Acoef s * Real.log 3 := by
    field_simp; ring
  have log2' := Real.log_two_lt_d9
  rcases lt_or_ge X p with hpx | hpx
  · -- no prime power of `p` below `X`
    rw [llp_eq_zero hp hpx, lcp_eq_zero hp hpx]
    have hrhs : 0 ≤ (if p = 2 then Acoef s * Real.log 2 * (1 + 1 / (s : ℝ) ^ 2)
            + (l - Real.log 2 / 2) ^ 2 / 2
          else if p = 3 then Acoef s * Real.log 3 / (s : ℝ) ^ 2 + (l - Real.log 3 / 2) ^ 2 / 2
          else 0) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
      split_ifs <;> positivity
    have : 0 ≤ Acoef s * (1 - 1 / (s : ℝ) ^ 2) * Real.log p := by
      have : 0 ≤ 1 - 1 / (s : ℝ) ^ 2 := by linarith
      positivity
    linarith
  · have hl1 := llp_le X p hp hX
    have hc1 := lcp_le X p hp hX
    have hlpX : Real.log p ≤ l := Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpx)
    have hc2 : 2 * Acoef s * lcp X p ≤ 2 * Acoef s * (Real.log p / ((p : ℝ) - 1)) := by
      have := mul_le_mul_of_nonneg_left hc1 (show 0 ≤ 2 * Acoef s by linarith); linarith
    split_ifs with h2 h3
    · subst h2
      simp only [Nat.cast_ofNat] at *
      norm_num at hc2
      linarith
    · subst h3
      simp only [Nat.cast_ofNat] at *
      norm_num at hc2
      linarith
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        by_contra h
        interval_cases p <;> simp_all <;> exact absurd hp (by decide)
      have hp5R : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have hlog5 : 1.6 ≤ Real.log p := by
        have := LLS.log_ge_of_pow 5 594 256 (by norm_num) (by decide +kernel)
        have h5 : Real.log 5 ≤ Real.log p := Real.log_le_log (by norm_num) hp5R
        push_cast at this; linarith
      have hfrac : Real.log p / ((p : ℝ) - 1) ≤ Real.log p / 4 :=
        div_le_div_of_nonneg_left hlp (by norm_num) (by linarith)
      have hsq : (l - Real.log p / 2) ^ 2 ≤ l ^ 2 := by nlinarith
      have hmul : Acoef s * (1 - 1 / (s : ℝ) ^ 2) * Real.log p
          ≥ Acoef s * (999 / 1000) * Real.log p := by
        have : 999 / 1000 ≤ 1 - 1 / (s : ℝ) ^ 2 := by linarith
        have := mul_le_mul_of_nonneg_left this hA0
        nlinarith
      have hAl : Acoef s * Real.log p ≥ (s : ℝ) * 1.6 := by nlinarith
      nlinarith

theorem bad_cost (s : ℕ) (hs : 31622 ≤ s) (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    ∑ p ∈ R, (llp (s ^ 2) p + 2 * Acoef s * lcp (s ^ 2) p
        - Acoef s * (1 - 1 / (s : ℝ) ^ 2) * Real.log p)
      ≤ Acoef s * Real.log 2 * (1 + 1 / (s : ℝ) ^ 2)
            + (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 2 / 2) ^ 2 / 2
        + (Acoef s * Real.log 3 / (s : ℝ) ^ 2
            + (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 3 / 2) ^ 2 / 2) := by
  classical
  set g : ℕ → ℝ := fun p => if p = 2 then Acoef s * Real.log 2 * (1 + 1 / (s : ℝ) ^ 2)
            + (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 2 / 2) ^ 2 / 2
          else if p = 3 then Acoef s * Real.log 3 / (s : ℝ) ^ 2
            + (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 3 / 2) ^ 2 / 2
          else 0
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hA0 : 0 ≤ Acoef s := by unfold Acoef; positivity
  have hg0 : ∀ p, 0 ≤ g p := fun p => by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
    simp only [g]; split_ifs <;> positivity
  calc _ ≤ ∑ p ∈ R, g p := sum_le_sum fun p hp => prime_cost s hs p (hR p hp)
    _ ≤ ∑ p ∈ ({2, 3} : Finset ℕ), g p := by
        rw [← sum_filter_of_ne (p := fun p => p ∈ ({2, 3} : Finset ℕ)) (fun p _ h => by
          simp only [g] at h; split_ifs at h with h2 h3 <;> simp_all)]
        exact sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.1 hp).2)
          fun p _ _ => hg0 p
    _ = _ := by rw [sum_pair (by norm_num)]; simp [g]

/-! ### The per-character bound -/

theorem norm_logSum_char (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℕ) (hs : 31622 ≤ s) :
    ‖LLS.logSum χ (s ^ 2)‖
      ≤ Pc (Real.log q) s (Real.log ((s ^ 2 : ℕ) : ℝ))
        - 2 * Acoef s * (LLS.cesShift χ (s ^ 2)).re := by
  classical
  set X := s ^ 2 with hXdef
  set L := Real.log q
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
  have hψval : ∀ n : ℕ, n.Coprime q → ψ n = χ n := fun n hn => by
    have := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.2 hn)
    simpa using this
  set R := q.primeFactors.filter (fun p => ¬ p ∣ f) with hR
  have hRp : ∀ p ∈ R, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1
  -- numerical facts
  have hsR : (31622 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hX2 : 2 ≤ X := by nlinarith
  have hXR : ((X : ℕ) : ℝ) = (s : ℝ) ^ 2 := by rw [hXdef]; push_cast; ring
  have hsqX : √((X : ℕ) : ℝ) = s := by rw [hXR, Real.sqrt_sq hs0.le]
  have hl : 20.72 ≤ Real.log ((X : ℕ) : ℝ) := logX_ge hs
  have hl4 : 4 ≤ Real.log ((X : ℕ) : ℝ) := by linarith
  have hX9 : (10 : ℝ) ^ 8 ≤ (X : ℕ) := by rw [hXR]; nlinarith
  set A := Acoef s with hAdef
  have hden : 0 < (1 - 1 / (s : ℝ)) ^ 2 := by
    have : 1 / (s : ℝ) < 1 := by rw [div_lt_one hs0]; linarith
    nlinarith
  have hA0 : 0 ≤ A := by unfold A Acoef; positivity
  have hAZ : ∀ Z : ℝ, (s + 1) * Z = A * (Z * (1 - 1 / (s : ℝ)) ^ 2) := fun Z => by
    have : (s : ℝ) - 1 ≠ 0 := by linarith
    unfold A Acoef; field_simp
  -- step 1: compare with ψ
  have hdS : ‖LLS.logSum χ X - LLS.logSum ψ X‖ ≤ ∑ p ∈ R, llp X p := by
    have := norm_diff_le χ ψ hψval X (fun n => Real.log ((X : ℝ) / n)) (fun n hn => log_div_nonneg hn)
    simpa [LLS.logSum, llp, hR] using this
  have hdC : ‖LLS.cesShift χ X - LLS.cesShift ψ X‖ ≤ ∑ p ∈ R, lcp X p := by
    have := norm_diff_le χ ψ hψval X (fun n => 1 / (n : ℝ) * (1 - (n : ℝ) / X))
      (fun n hn => ces_weight_nonneg hn)
    rw [cesShift_eq_succ, cesShift_eq_succ]
    simpa [lcp, hR] using this
  have hreC : -(LLS.cesShift ψ X).re ≤ -(LLS.cesShift χ X).re + ∑ p ∈ R, lcp X p := by
    have := (Complex.abs_re_le_norm (LLS.cesShift χ X - LLS.cesShift ψ X)).trans hdC
    rw [Complex.sub_re] at this
    have := le_abs_self ((LLS.cesShift χ X).re - (LLS.cesShift ψ X).re)
    linarith
  -- step 2: the primitive character
  have hP := norm_logSum_le hGRH hψprim hψ1 X hX1 hl4
  rw [hsqX] at hP
  have hZ := (LLS.Sharp.AssemblyAux.cesShift_two_sided hGRH hψprim hψ1 X hX2).1
  rw [hsqX] at hZ
  have hG := (LLS.Sharp.AssemblyAux.gamma_shift_bounds ψ X hX1).2
  have hEU := EUpar_le (parity ψ) hX9
  have hZ' : LLS.Z2 ψ * (1 - 1 / (s : ℝ)) ^ 2
      ≤ (1 - 1 / (s : ℝ) ^ 2) * Real.log f + (-2 * (LLS.cesShift ψ X).re) + 2 * (-0.86) := by
    rw [hXR] at hZ; linarith
  have hZA : (s + 1) * LLS.Z2 ψ
      ≤ A * ((1 - 1 / (s : ℝ) ^ 2) * Real.log f) + A * (-2 * (LLS.cesShift ψ X).re)
        + A * (2 * (-0.86)) := by
    rw [hAZ, ← mul_add, ← mul_add]; exact mul_le_mul_of_nonneg_left hZ' hA0
  -- step 3: `|V'|`
  have hM := maxV_le hGRH hψprim hψ1 100 (by norm_num) 1.5 (gamma100 _)
  have hP2 := P2sum100_le hGRH
  have hlf0 : 0 ≤ Real.log f := Real.log_natCast_nonneg f
  have hs100 : √((100 : ℕ) : ℝ) = 10 := by
    rw [show ((100 : ℕ) : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs100] at hM
  have hV : ‖((1 / 2 * Real.log f : ℝ) : ℂ) + LLS.D ψ⁻¹ 1‖ ≤ 0.627 * Real.log f + 5.93 := by
    have hmax := le_max_right ‖((1 / 2 * Real.log f : ℝ) : ℂ) + LLS.D ψ 1‖
      ‖((1 / 2 * Real.log f : ℝ) : ℂ) + LLS.D ψ⁻¹ 1‖
    have h79 : (1 - 1 / ((100 : ℕ) : ℝ) - 2 / 10) = 0.79 := by norm_num
    have h99 : (1 - 1 / ((100 : ℕ) : ℝ)) = 0.99 := by norm_num
    rw [h79, h99] at hM
    have := mul_le_mul_of_nonneg_right hmax (show (0 : ℝ) ≤ 0.79 by norm_num)
    linarith
  -- step 4: the conductor
  have hlfq := LLS.log_add_sum_log_le hfq hq0
  rw [← hR] at hlfq
  have hRlog : 0 ≤ ∑ p ∈ R, Real.log p := sum_nonneg fun p hp =>
    Real.log_nonneg (by exact_mod_cast (hRp p hp).one_lt.le)
  have hlfL : Real.log f ≤ L := by linarith
  have hmax : max (Real.log f - 3) (Real.log ((X : ℕ) : ℝ) + 2) ≤ max (L - 3) (Real.log ((X : ℕ) : ℝ) + 2) :=
    max_le_max (by linarith) le_rfl
  have hbad := bad_cost s hs R hRp
  rw [← hXdef] at hbad
  -- assembly
  have hnorm : ‖LLS.logSum χ X‖ ≤ ‖LLS.logSum ψ X‖ + ∑ p ∈ R, llp X p := by
    have := norm_sub_norm_le (LLS.logSum χ X) (LLS.logSum ψ X); linarith
  have hsumR : ∑ p ∈ R, (llp X p + 2 * A * lcp X p - A * (1 - 1 / (s : ℝ) ^ 2) * Real.log p)
      = ∑ p ∈ R, llp X p + 2 * A * ∑ p ∈ R, lcp X p
        - A * (1 - 1 / (s : ℝ) ^ 2) * ∑ p ∈ R, Real.log p := by
    rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [hsumR] at hbad
  have hc1 : 0 ≤ 1 - 1 / (s : ℝ) ^ 2 := by
    have : 1 / (s : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith)
    linarith
  have hk1 : A * ((1 - 1 / (s : ℝ) ^ 2) * Real.log f)
      ≤ A * ((1 - 1 / (s : ℝ) ^ 2) * (L - ∑ p ∈ R, Real.log p)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hc1) hA0
  have hk2 : A * (-2 * (LLS.cesShift ψ X).re) ≤ A * (-2 * (LLS.cesShift χ X).re
      + 2 * ∑ p ∈ R, lcp X p) := mul_le_mul_of_nonneg_left (by linarith) hA0
  have hk3 : ‖((1 / 2 * Real.log f : ℝ) : ℂ) + LLS.D ψ⁻¹ 1‖ * Real.log ((X : ℕ) : ℝ)
      ≤ (0.627 * L + 5.93) * Real.log ((X : ℕ) : ℝ) :=
    mul_le_mul (hV.trans (by linarith)) le_rfl (by linarith) (by linarith)
  have hk4 : 1 / 2 * Real.log ((X : ℕ) : ℝ) * max (Real.log f - 3) (Real.log ((X : ℕ) : ℝ) + 2)
      ≤ 1 / 2 * Real.log ((X : ℕ) : ℝ) * max (L - 3) (Real.log ((X : ℕ) : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hmax (by linarith)
  unfold Pc
  rw [← hAdef]
  linear_combination hnorm + hP + hZA + hk1 + hk2 + hk3 + hk4 + hbad

end LLS.Thm14
