import LLS.Bach2.KeyP
import LLS.Numerics.Budget

/-!
# Budgets for Bach's constant `2`

`LLS.keyP` with the prime-power losses bounded prime by prime (`LLS.prime_cost`) gives, under
GRH, for a non-trivial character `χ` mod `q` equal to `1` on every `n ≤ x` prime to `q`:

  `base2 x Pc − κ(x) log q − C ≤ 0`

for any `C` bounding the total cost of the primes dividing `q`. Two choices of `C`:

* `costQ x q = Σ_{p ∣ q, p ≤ x} W_p(x)` (one modulus at a time; `budgetQ_nonpos`);
* `Σ_{p < P₀} max(0, W_p − β log p) + β log q` with `β = (log x)²/(2 log P₀) + 2K/(P₀ − 1)`
  (uniform in `q`; `budgetU_nonpos`), which is `LLS.Phi` for `P₀ = 17`.
-/

namespace LLS

open Real Finset ArithmeticFunction

/-- The main terms of the budget, with `Pc` a lower bound for the Cesàro sum. -/
noncomputable def base2 (x Pc : ℝ) : ℝ :=
  x - 3 / 20 * √x - 3 * Real.log x - 3 + 2 * Kc x * Pc - 2 * Kc x * Eshift x
    + 1 / 2 * Real.log Real.pi * Real.log x - Etil x

/-- The Cesàro sum `Σ_{n ≤ x} Λ(n) (1/n)(1 − n/x)`. -/
noncomputable def cesSum (x : ℕ) : ℝ :=
  ∑ n ∈ range (x + 1), (Λ n : ℝ) * (1 / (n : ℝ) * (1 - (n : ℝ) / x))

/-- **The general budget inequality.** -/
theorem budget_nonpos (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (Pc : ℝ) (hPc : Pc ≤ cesSum x) (C : ℝ)
    (hC : ∀ R ⊆ q.primeFactors,
      ∑ p ∈ q.primeFactors, ((llp x p + 2 * Kc x * lcp x p)
        + (if p ∈ R then llp x p + 2 * Kc x * lcp x p - kap x * Real.log p else 0)) ≤ C) :
    base2 x Pc - kap x * Real.log q - C ≤ 0 := by
  classical
  obtain ⟨lf, Z, hlf, hZ0, R, hRq, hlog, h1, h2⟩ := keyP hGRH χ hχ x hx hval Pc hPc
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  set s := √(x : ℝ)
  set l := Real.log x
  set den := 1 + 1 / (x : ℝ) - 2 / s
  have hden : 3 / 4 ≤ den := den_pos hxR
  have hs8 : 8 ≤ s := sqrt_ge_eight hxR
  have hl4 : 4 ≤ l := log_ge_four hxR
  set K := Kc x
  have hKdef : K * den = s + 1 + l / 2 := by
    show Kc x * den = _
    unfold Kc
    exact div_mul_cancel₀ _ (ne_of_gt (by linarith))
  have hK0 : 0 < K := Kc_pos hxR
  set SC := ∑ p ∈ q.primeFactors, lcp x p
  set SCR := ∑ p ∈ R, lcp x p
  set SL := ∑ p ∈ q.primeFactors, llp x p
  set SLR := ∑ p ∈ R, llp x p
  set SRlog := ∑ p ∈ R, Real.log p
  have hN : (s + 1 + l / 2) * Z ≤ K * (lf * (1 - 1 / x) - 2 * (Pc - SC - SCR) + 2 * Eshift x) := by
    rw [← hKdef]
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    nlinarith
  have hS : (x : ℝ) - 3 / 20 * s - 3 * l - 3 - SL - SLR
      ≤ K * (lf * (1 - 1 / x) - 2 * (Pc - SC - SCR) + 2 * Eshift x) + lf / 2 * l
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
  have hcost : SL + 2 * K * SC + (SLR + 2 * K * SCR - kap x * SRlog) ≤ C := by
    have hsplit : SL + 2 * K * SC + (SLR + 2 * K * SCR - kap x * SRlog)
        = ∑ p ∈ q.primeFactors, ((llp x p + 2 * K * lcp x p)
          + (if p ∈ R then llp x p + 2 * K * lcp x p - kap x * Real.log p else 0)) := by
      rw [sum_add_distrib, ← sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hRq]
      simp only [SL, SC, SLR, SCR, SRlog, sum_add_distrib, sum_sub_distrib, mul_sum]
    rw [hsplit]
    exact hC R hRq
  unfold base2
  change (x : ℝ) - 3 / 20 * s - 3 * l - 3 + 2 * K * Pc - 2 * K * Eshift x
    + 1 / 2 * Real.log Real.pi * l - Etil x - kap x * Real.log q - C ≤ 0
  have hexp : K * (lf * (1 - 1 / x) - 2 * (Pc - SC - SCR) + 2 * Eshift x)
      = K * (lf * (1 - 1 / x)) - 2 * K * Pc + 2 * K * SC + 2 * K * SCR
        + 2 * K * Eshift x := by ring
  have hkq : kap x * (Real.log q - SRlog) = kap x * Real.log q - kap x * SRlog := by ring
  nlinarith

/-! ### One modulus at a time -/

/-- The cost of the primes `p ≤ x` dividing `q`. -/
noncomputable def costQ (x q : ℕ) : ℝ := ∑ p ∈ q.primeFactors.filter (· ≤ x), Wp x p

lemma cost_le_costQ (x : ℕ) (hx : 64 ≤ x) (q : ℕ) (R : Finset ℕ) [DecidablePred (· ∈ R)] :
    ∑ p ∈ q.primeFactors, ((llp x p + 2 * Kc x * lcp x p)
        + (if p ∈ R then llp x p + 2 * Kc x * lcp x p - kap x * Real.log p else 0))
      ≤ costQ x q := by
  classical
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hkap0 : 0 ≤ kap x := by
    have h1x : 0 ≤ 1 - 1 / (x : ℝ) := by
      have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have := Kc_pos hxR
    have := log_ge_four hxR
    unfold kap; positivity
  unfold costQ
  rw [sum_filter]
  refine sum_le_sum fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  by_cases hpx : p ≤ x
  · rw [if_pos hpx]
    exact prime_cost x hx p hpp (p ∈ R)
  · rw [if_neg hpx]
    have hlt : x < p := lt_of_not_ge hpx
    rw [llp_eq_zero hpp hlt, lcp_eq_zero hpp hlt]
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    split_ifs
    · nlinarith
    · simp

/-- **Budget, one modulus at a time.** -/
theorem budgetQ_nonpos (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (Pc : ℝ) (hPc : Pc ≤ cesSum x) :
    base2 x Pc - kap x * Real.log q - costQ x q ≤ 0 := by
  classical
  exact budget_nonpos hGRH χ hχ x hx hval Pc hPc _ fun R _ => cost_le_costQ x hx q R

/-! ### Uniform in `q` -/

/-- `β(x, P₀) = (log x)²/(2 log P₀) + 2K/(P₀ − 1)`. -/
noncomputable def betP (x : ℝ) (P0 : ℕ) : ℝ := Real.log x ^ 2 / (2 * Real.log P0) + 2 * Kc x / (P0 - 1)

/-- The primes below `P₀`. -/
def smallPN (P0 : ℕ) : Finset ℕ := (range P0).filter Nat.Prime

lemma betP_nonneg {x : ℝ} (hx : 64 ≤ x) {P0 : ℕ} (hP0 : 2 ≤ P0) : 0 ≤ betP x P0 := by
  have := Kc_pos hx
  have : 0 < Real.log P0 := Real.log_pos (by exact_mod_cast hP0)
  have : (0 : ℝ) < (P0 : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P0 := by exact_mod_cast hP0
    linarith
  unfold betP; positivity

/-- A prime `p ≥ P₀` dividing `q` costs at most `β log p`. -/
lemma large_prime_costP (x : ℕ) (hx : 64 ≤ x) (P0 : ℕ) (hP0 : 2 ≤ P0)
    (hβκ : betP x P0 ≤ kap x) (p : ℕ) (hp : p.Prime)
    (hpP : P0 ≤ p) (inR : Prop) [Decidable inR] :
    (llp x p + 2 * Kc x * lcp x p)
        + (if inR then llp x p + 2 * Kc x * lcp x p - kap x * Real.log p else 0)
      ≤ betP x P0 * Real.log p := by
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hK := Kc_pos hxR
  have hl4 := log_ge_four hxR
  have hP0R : (2 : ℝ) ≤ P0 := by exact_mod_cast hP0
  have hlP : 0 < Real.log P0 := Real.log_pos (by linarith)
  have hlpP : Real.log P0 ≤ Real.log p := Real.log_le_log (by linarith) (by exact_mod_cast hpP)
  have hb0 := betP_nonneg hxR hP0
  rcases lt_or_ge x p with hpx | hpx
  · rw [llp_eq_zero hp hpx, lcp_eq_zero hp hpx]
    have : 0 ≤ Real.log p := by linarith
    split_ifs
    · have : 0 ≤ kap x := le_trans hb0 hβκ
      nlinarith
    · simp; positivity
  · have hlpx : Real.log p ≤ Real.log x := Real.log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast hpx)
    have h1 := llp_le x p hp (by omega)
    have h2 := lcp_le x p hp (by omega)
    have hp1 : (P0 : ℝ) - 1 ≤ (p : ℝ) - 1 := by
      have : (P0 : ℝ) ≤ p := by exact_mod_cast hpP
      linarith
    have hP1 : 0 < (P0 : ℝ) - 1 := by linarith
    have hlp0 : 0 ≤ Real.log p := by linarith
    have hsq : (Real.log x - Real.log p / 2) ^ 2 / 2
        ≤ Real.log x ^ 2 / (2 * Real.log P0) * Real.log p := by
      have e1 : (Real.log x - Real.log p / 2) ^ 2 ≤ Real.log x ^ 2 := by nlinarith
      have e2 : Real.log x ^ 2 / 2 ≤ Real.log x ^ 2 / (2 * Real.log P0) * Real.log p := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (Real.log x)]
      linarith
    have hlc : 2 * Kc x * (Real.log p / ((p : ℝ) - 1)) ≤ 2 * Kc x / (P0 - 1) * Real.log p := by
      have : Real.log p / ((p : ℝ) - 1) ≤ Real.log p / ((P0 : ℝ) - 1) :=
        div_le_div_of_nonneg_left hlp0 hP1 hp1
      have h' := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 2 * Kc x)
      calc 2 * Kc x * (Real.log p / ((p : ℝ) - 1)) ≤ 2 * Kc x * (Real.log p / ((P0 : ℝ) - 1)) := h'
        _ = 2 * Kc x / (P0 - 1) * Real.log p := by ring
    have hA : llp x p + 2 * Kc x * lcp x p ≤ betP x P0 * Real.log p := by
      unfold betP
      have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * Kc x)
      nlinarith
    split_ifs
    · have : betP x P0 * Real.log p ≤ kap x * Real.log p := mul_le_mul_of_nonneg_right hβκ hlp0
      linarith
    · linarith

/-- The uniform cost bound. -/
noncomputable def costU (x : ℕ) (P0 : ℕ) (L : ℝ) : ℝ :=
  ∑ p ∈ smallPN P0, max 0 (Wp x p - betP x P0 * Real.log p) + betP x P0 * L

lemma cost_le_costU (x : ℕ) (hx : 64 ≤ x) (P0 : ℕ) (hP0 : 2 ≤ P0) (hβκ : betP x P0 ≤ kap x)
    (q : ℕ) (hq0 : q ≠ 0) (R : Finset ℕ) [DecidablePred (· ∈ R)] :
    ∑ p ∈ q.primeFactors, ((llp x p + 2 * Kc x * lcp x p)
        + (if p ∈ R then llp x p + 2 * Kc x * lcp x p - kap x * Real.log p else 0))
      ≤ costU x P0 (Real.log q) := by
  classical
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  set c : ℕ → ℝ := fun p => (llp x p + 2 * Kc x * lcp x p)
    + (if p ∈ R then llp x p + 2 * Kc x * lcp x p - kap x * Real.log p else 0)
  have hβ0 := betP_nonneg hxR hP0
  have hlogsum : ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
    have hpos : ∀ p ∈ q.primeFactors, (0 : ℝ) < p := fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
    apply Real.log_le_log (prod_pos hpos)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.prod_primeFactors_dvd q)
    have h' : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    simpa using h'
  have hle : ∀ p ∈ q.primeFactors, c p - betP x P0 * Real.log p
      ≤ if p ∈ smallPN P0 then max 0 (Wp x p - betP x P0 * Real.log p) else 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    split_ifs with hs
    · have := prime_cost x hx p hpp (p ∈ R)
      have := le_max_right 0 (Wp x p - betP x P0 * Real.log p)
      simp only [c]; linarith
    · have hP : P0 ≤ p := by
        by_contra h
        exact hs (mem_filter.2 ⟨mem_range.2 (lt_of_not_ge h), hpp⟩)
      have := large_prime_costP x hx P0 hP0 hβκ p hpp hP (p ∈ R)
      simp only [c]; linarith
  show ∑ p ∈ q.primeFactors, c p ≤ _
  unfold costU
  calc ∑ p ∈ q.primeFactors, c p
      = ∑ p ∈ q.primeFactors, (c p - betP x P0 * Real.log p)
        + betP x P0 * ∑ p ∈ q.primeFactors, Real.log p := by
        rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ p ∈ q.primeFactors,
          (if p ∈ smallPN P0 then max 0 (Wp x p - betP x P0 * Real.log p) else 0)
        + betP x P0 * Real.log q :=
        add_le_add (sum_le_sum hle) (mul_le_mul_of_nonneg_left hlogsum hβ0)
    _ ≤ ∑ p ∈ smallPN P0, max 0 (Wp x p - betP x P0 * Real.log p) + betP x P0 * Real.log q := by
        gcongr
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => le_max_left _ _
        intro p hp; exact (mem_filter.1 hp).2

/-- **Budget, uniform in `q`.** -/
theorem budgetU_nonpos (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (Pc : ℝ) (hPc : Pc ≤ cesSum x)
    (P0 : ℕ) (hP0 : 2 ≤ P0) (hβκ : betP x P0 ≤ kap x) :
    base2 x Pc - kap x * Real.log q - costU x P0 (Real.log q) ≤ 0 := by
  classical
  exact budget_nonpos hGRH χ hχ x hx hval Pc hPc _ fun R _ =>
    cost_le_costU x hx P0 hP0 hβκ q (NeZero.ne q) R

end LLS
