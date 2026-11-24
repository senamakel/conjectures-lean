import LLS.Key

/-!
# From the key inequality to a single numerical budget `Φ(x, log q) ≤ 0`

Bounds for the prime-power losses (LLS Lemma 3.1, sharpened):
`llp x p ≤ (log x − (log p)/2)²/2` and `lcp x p ≤ log p/(p − 1)`, both `0` for `p > x`.

Writing `K = (√x + 1 + ½ log x)/(1 + 1/x − 2/√x)`, `κ = K(1 − 1/x) + ½ log x` and
`β = (log x)²/(2 log 17) + 2K/16`, a prime `p ∣ q` with `p ≥ 17` costs at most `β log p`, and the
primes below `17` are listed explicitly. The key inequality then gives `Φ(x, log q) ≤ 0` for the
explicit function `Φ` below (when `β ≤ κ`); the numerical files show `Φ > 0`.
-/

namespace LLS

open Real Finset ArithmeticFunction

/-! ### Prime-power losses -/

lemma ppF_subset (x p : ℕ) (hp : p.Prime) :
    ppF x p ⊆ (range (Nat.log p x)).image (fun k => p ^ (k + 1)) := by
  intro n hn
  simp only [ppF, mem_filter, mem_range] at hn
  obtain ⟨hnx, hpp, hmin⟩ := hn
  obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
  have hrp : r = p := by rw [← hmin, Nat.Prime.pow_minFac hr hk.ne']
  subst hrp
  refine mem_image.2 ⟨k - 1, mem_range.2 ?_, by congr 1; omega⟩
  have := Nat.le_log_of_pow_le hr.one_lt (Nat.lt_succ_iff.1 hnx)
  omega

lemma ppF_eq_empty {x p : ℕ} (hp : p.Prime) (hpx : x < p) : ppF x p = ∅ := by
  ext n
  simp only [ppF, mem_filter, mem_range, Finset.notMem_empty, iff_false, not_and]
  intro hnx hpp hmin
  have hn0 : n ≠ 0 := by rintro rfl; exact not_isPrimePow_zero hpp
  have := Nat.minFac_le (Nat.pos_of_ne_zero hn0)
  omega

lemma sum_pow_loss (a l : ℝ) (K : ℕ) :
    ∑ k ∈ range K, a * (l - ((k : ℝ) + 1) * a)
      = (l - a / 2) ^ 2 / 2 - (l - ((K : ℝ) + 1 / 2) * a) ^ 2 / 2 := by
  induction K with
  | zero => simp; ring
  | succ K ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_geom_inv (p : ℝ) (hp : 1 < p) (K : ℕ) :
    ∑ k ∈ range K, (1 / p) ^ (k + 1) = (1 - (1 / p) ^ K) / (p - 1) := by
  have hp0 : p - 1 ≠ 0 := by linarith
  have hp1 : p ≠ 0 := by linarith
  have hr : 1 / p * p = 1 := by field_simp
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, div_add' _ _ _ hp0, div_left_inj' hp0, pow_succ]
    linear_combination ((1 / p) ^ K) * hr

lemma image_sum_eq {x p : ℕ} (hp : p.Prime) (g : ℕ → ℝ) :
    ∑ n ∈ (range (Nat.log p x)).image (fun k => p ^ (k + 1)), g n
      = ∑ k ∈ range (Nat.log p x), g (p ^ (k + 1)) := by
  refine sum_image fun a _ b _ h => ?_
  have := Nat.pow_right_injective hp.two_le h
  omega

lemma pow_le_of_lt_log {x p k : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hk : k < Nat.log p x) :
    p ^ (k + 1) ≤ x :=
  (Nat.pow_le_pow_right hp.pos hk).trans (Nat.pow_log_le_self p (by omega))

theorem llp_le (x p : ℕ) (hp : p.Prime) (hx : 1 ≤ x) :
    llp x p ≤ (Real.log x - Real.log p / 2) ^ 2 / 2 := by
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hval : ∀ k < Nat.log p x, (Λ (p ^ (k + 1)) : ℝ) * Real.log ((x : ℝ) / ↑(p ^ (k + 1)))
      = Real.log p * (Real.log x - ((k : ℝ) + 1) * Real.log p) := by
    intro k _
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, Real.log_div hx0.ne'
      (by exact_mod_cast (pow_pos hp.pos _).ne'), Nat.cast_pow, Real.log_pow]
    push_cast; ring
  calc llp x p ≤ ∑ n ∈ (range (Nat.log p x)).image (fun k => p ^ (k + 1)),
        (Λ n : ℝ) * Real.log ((x : ℝ) / n) := by
        refine sum_le_sum_of_subset_of_nonneg (ppF_subset x p hp) fun n hn _ => ?_
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hn
        exact mul_nonneg vonMangoldt_nonneg (log_div_nonneg
          (pow_le_of_lt_log hp hx (mem_range.1 hk)))
    _ = ∑ k ∈ range (Nat.log p x), Real.log p * (Real.log x - ((k : ℝ) + 1) * Real.log p) := by
        rw [image_sum_eq hp]
        exact sum_congr rfl fun k hk => hval k (mem_range.1 hk)
    _ ≤ (Real.log x - Real.log p / 2) ^ 2 / 2 := by
        rw [sum_pow_loss]
        nlinarith [sq_nonneg (Real.log x - ((Nat.log p x : ℝ) + 1 / 2) * Real.log p)]

theorem lcp_le (x p : ℕ) (hp : p.Prime) (hx : 1 ≤ x) :
    lcp x p ≤ Real.log p / ((p : ℝ) - 1) := by
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  calc lcp x p ≤ ∑ n ∈ (range (Nat.log p x)).image (fun k => p ^ (k + 1)),
        (Λ n : ℝ) * (1 / (n : ℝ) * (1 - (n : ℝ) / x)) := by
        refine sum_le_sum_of_subset_of_nonneg (ppF_subset x p hp) fun n hn _ => ?_
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hn
        exact mul_nonneg vonMangoldt_nonneg (ces_weight_nonneg
          (pow_le_of_lt_log hp hx (mem_range.1 hk)))
    _ = ∑ k ∈ range (Nat.log p x),
          (Λ (p ^ (k + 1)) : ℝ) * (1 / ((p ^ (k + 1) : ℕ) : ℝ) * (1 - ((p ^ (k + 1) : ℕ) : ℝ) / x)) :=
        image_sum_eq hp _
    _ ≤ ∑ k ∈ range (Nat.log p x), Real.log p * (1 / (p : ℝ)) ^ (k + 1) := by
        refine sum_le_sum fun k hk => ?_
        rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
        have hpk : (0 : ℝ) < ((p ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos _
        have h1 : 1 - ((p ^ (k + 1) : ℕ) : ℝ) / x ≤ 1 := by
          have : 0 ≤ ((p ^ (k + 1) : ℕ) : ℝ) / x := by positivity
          linarith
        have h2 : 0 ≤ 1 / ((p ^ (k + 1) : ℕ) : ℝ) := by positivity
        have e : (1 / (p : ℝ)) ^ (k + 1) = 1 / ((p ^ (k + 1) : ℕ) : ℝ) := by
          push_cast; rw [one_div_pow]
        rw [e]
        have := mul_le_mul_of_nonneg_left h1 h2
        nlinarith
    _ = Real.log p * ((1 - (1 / (p : ℝ)) ^ (Nat.log p x)) / ((p : ℝ) - 1)) := by
        rw [← mul_sum, sum_geom_inv _ hp1]
    _ ≤ Real.log p / ((p : ℝ) - 1) := by
        have h0 : 0 ≤ (1 / (p : ℝ)) ^ (Nat.log p x) := by positivity
        have hd : 0 < (p : ℝ) - 1 := by linarith
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hd]
        nlinarith

theorem llp_eq_zero {x p : ℕ} (hp : p.Prime) (hpx : x < p) : llp x p = 0 := by
  simp [llp, ppF_eq_empty hp hpx]

theorem lcp_eq_zero {x p : ℕ} (hp : p.Prime) (hpx : x < p) : lcp x p = 0 := by
  simp [lcp, ppF_eq_empty hp hpx]

theorem llp_nonneg (x p : ℕ) : 0 ≤ llp x p :=
  sum_nonneg fun n hn => by
    simp only [ppF, mem_filter, mem_range] at hn
    exact mul_nonneg vonMangoldt_nonneg (log_div_nonneg (Nat.lt_succ_iff.1 hn.1))

theorem lcp_nonneg (x p : ℕ) : 0 ≤ lcp x p :=
  sum_nonneg fun n hn => by
    simp only [ppF, mem_filter, mem_range] at hn
    exact mul_nonneg vonMangoldt_nonneg (ces_weight_nonneg (Nat.lt_succ_iff.1 hn.1))

/-! ### The budget -/

/-- `K(x) = (√x + 1 + ½ log x)/(1 + 1/x − 2/√x)`. -/
noncomputable def Kc (x : ℝ) : ℝ := (√x + 1 + Real.log x / 2) / (1 + 1 / x - 2 / √x)

/-- `κ(x) = K(x)(1 − 1/x) + ½ log x`, the coefficient of `log f`. -/
noncomputable def kap (x : ℝ) : ℝ := Kc x * (1 - 1 / x) + Real.log x / 2

/-- `β(x)`: the cost per unit of `log p` of a prime `p ≥ 17` dividing `q`. -/
noncomputable def bet (x : ℝ) : ℝ := Real.log x ^ 2 / (2 * Real.log 17) + 2 * Kc x / 16

/-- Bound for `llp + 2K lcp` at a prime `p`. -/
noncomputable def Ap (x p : ℝ) : ℝ :=
  (Real.log x - Real.log p / 2) ^ 2 / 2 + 2 * Kc x * (Real.log p / (p - 1))

/-- Bound for the total cost of a prime `p ∣ q`, whether or not `p` divides the conductor. -/
noncomputable def Wp (x p : ℝ) : ℝ := Ap x p + max 0 (Ap x p - kap x * Real.log p)

/-- The primes below `17`. -/
def smallP : Finset ℕ := {2, 3, 5, 7, 11, 13}

/-- The budget: the key inequality forces `Φ(x, log q) ≤ 0`. -/
noncomputable def Phi (x L : ℝ) : ℝ :=
  x - 3 / 20 * √x - 3 * Real.log x - 3 + 2 * Kc x * (Real.log x - 2) - kap x * L
    - 2 * Kc x * Eshift x + 1 / 2 * Real.log Real.pi * Real.log x - Etil x - bet x * L
    - ∑ p ∈ smallP, max 0 (Wp x p - bet x * Real.log p)

lemma sqrt_ge_eight {x : ℝ} (hx : 64 ≤ x) : 8 ≤ √x := by
  rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hx

lemma den_pos {x : ℝ} (hx : 64 ≤ x) : 3 / 4 ≤ 1 + 1 / x - 2 / √x := by
  have h8 := sqrt_ge_eight hx
  have h1 : 0 ≤ 1 / x := by positivity
  have h2 : 2 / √x ≤ 1 / 4 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma log_ge_four {x : ℝ} (hx : 64 ≤ x) : 4 ≤ Real.log x := by
  have h := Real.log_le_log (by norm_num) hx
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

lemma Kc_pos {x : ℝ} (hx : 64 ≤ x) : 0 < Kc x := by
  have := den_pos hx
  have := log_ge_four hx
  have := sqrt_ge_eight hx
  unfold Kc; apply div_pos <;> linarith

lemma bet_nonneg {x : ℝ} (hx : 64 ≤ x) : 0 ≤ bet x := by
  have := Kc_pos hx
  have : 0 < Real.log 17 := Real.log_pos (by norm_num)
  unfold bet; positivity

/-- The cost of one prime `p ∣ q` (`p` in `R` or not). -/
lemma prime_cost (x : ℕ) (hx : 64 ≤ x) (p : ℕ) (hp : p.Prime) (inR : Prop) [Decidable inR] :
    (llp x p + 2 * Kc x * lcp x p)
        + (if inR then llp x p + 2 * Kc x * lcp x p - kap x * Real.log p else 0)
      ≤ Wp x p := by
  have hK := Kc_pos (by exact_mod_cast hx : (64 : ℝ) ≤ x)
  have hA : llp x p + 2 * Kc x * lcp x p ≤ Ap x p := by
    unfold Ap
    have h1 := llp_le x p hp (by omega)
    have h2 := lcp_le x p hp (by omega)
    nlinarith
  unfold Wp
  split_ifs
  · have := le_max_right 0 (Ap x p - kap x * Real.log p)
    linarith
  · have := le_max_left 0 (Ap x p - kap x * Real.log p)
    linarith

/-- A prime `p ≥ 17` dividing `q` costs at most `β log p`. -/
lemma large_prime_cost (x : ℕ) (hx : 64 ≤ x) (hβκ : bet x ≤ kap x) (p : ℕ) (hp : p.Prime)
    (hp17 : 17 ≤ p) (inR : Prop) [Decidable inR] :
    (llp x p + 2 * Kc x * lcp x p)
        + (if inR then llp x p + 2 * Kc x * lcp x p - kap x * Real.log p else 0)
      ≤ bet x * Real.log p := by
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  have hK := Kc_pos hxR
  have hl4 := log_ge_four hxR
  have hl17 : 0 < Real.log 17 := Real.log_pos (by norm_num)
  have hlp17 : Real.log 17 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp17)
  rcases lt_or_ge x p with hpx | hpx
  · rw [llp_eq_zero hp hpx, lcp_eq_zero hp hpx]
    have := bet_nonneg hxR
    have : 0 ≤ Real.log p := by linarith
    split_ifs
    · have : 0 ≤ kap x := le_trans (bet_nonneg hxR) hβκ
      nlinarith
    · simp; positivity
  · have hlpx : Real.log p ≤ Real.log x := Real.log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast hpx)
    have h1 := llp_le x p hp (by omega)
    have h2 := lcp_le x p hp (by omega)
    have hp1 : (16 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (17 : ℝ) ≤ p := by exact_mod_cast hp17
      linarith
    have hlp0 : 0 ≤ Real.log p := by linarith
    -- `(log x − log p/2)² ≤ (log x)²` and `(log x)²/2 ≤ (log x)²/(2 log 17) · log p`
    have hsq : (Real.log x - Real.log p / 2) ^ 2 / 2 ≤ Real.log x ^ 2 / (2 * Real.log 17) * Real.log p := by
      have e1 : (Real.log x - Real.log p / 2) ^ 2 ≤ Real.log x ^ 2 := by nlinarith
      have e2 : Real.log x ^ 2 / 2 ≤ Real.log x ^ 2 / (2 * Real.log 17) * Real.log p := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (Real.log x)]
      linarith
    have hlc : 2 * Kc x * (Real.log p / ((p : ℝ) - 1)) ≤ 2 * Kc x / 16 * Real.log p := by
      have : Real.log p / ((p : ℝ) - 1) ≤ Real.log p / 16 :=
        div_le_div_of_nonneg_left hlp0 (by norm_num) hp1
      have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 2 * Kc x)
      linarith
    have hA : llp x p + 2 * Kc x * lcp x p ≤ bet x * Real.log p := by
      unfold bet
      have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * Kc x)
      nlinarith
    split_ifs
    · have : bet x * Real.log p ≤ kap x * Real.log p := mul_le_mul_of_nonneg_right hβκ hlp0
      linarith
    · linarith

/-- **The budget inequality.** Under GRH, if `χ ≠ 1` mod `q` is `1` on all `n ≤ x` prime to `q`,
`x ≥ 64` and `β(x) ≤ κ(x)`, then `Φ(x, log q) ≤ 0`. -/
theorem Phi_nonpos (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℕ) (hx : 64 ≤ x)
    (hval : ∀ n ≤ x, n.Coprime q → χ n = 1) (hβκ : bet x ≤ kap x) :
    Phi x (Real.log q) ≤ 0 := by
  classical
  obtain ⟨lf, Z, hlf, hZ0, R, hRq, hlog, h1, h2⟩ := key hGRH χ hχ x hx hval
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
  have hq0 : q ≠ 0 := NeZero.ne q
  set SC := ∑ p ∈ q.primeFactors, lcp x p
  set SCR := ∑ p ∈ R, lcp x p
  set SL := ∑ p ∈ q.primeFactors, llp x p
  set SLR := ∑ p ∈ R, llp x p
  set SRlog := ∑ p ∈ R, Real.log p
  -- eliminate `Z`
  have hN : (s + 1 + l / 2) * Z ≤ K * (lf * (1 - 1 / x) - 2 * (l - 2 - SC - SCR) + 2 * Eshift x) := by
    rw [← hKdef]
    have := mul_le_mul_of_nonneg_left h1 hK0.le
    nlinarith
  have hS : (x : ℝ) - 3 / 20 * s - 3 * l - 3 - SL - SLR
      ≤ K * (lf * (1 - 1 / x) - 2 * (l - 2 - SC - SCR) + 2 * Eshift x) + lf / 2 * l
        - 1 / 2 * Real.log Real.pi * l + Etil x := by
    have : (√(x : ℝ) + 1) * Z + (lf + Z) / 2 * l = (s + 1 + l / 2) * Z + lf / 2 * l := by ring
    linarith
  -- `log f ≤ log q − Σ_R log p`, with coefficient `κ ≥ 0`
  have hkap0 : 0 ≤ kap x := by
    have h1x : 0 ≤ 1 - 1 / (x : ℝ) := by
      have : 1 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    unfold kap; positivity
  have hlf' : K * (lf * (1 - 1 / x)) + lf / 2 * l ≤ kap x * (Real.log q - SRlog) := by
    have : K * (lf * (1 - 1 / x)) + lf / 2 * l = kap x * lf := by simp only [kap, K, l]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hkap0
  -- the per-prime costs
  have hcost : SL + 2 * K * SC + (SLR + 2 * K * SCR - kap x * SRlog)
      ≤ ∑ p ∈ smallP, max 0 (Wp x p - bet x * Real.log p) + bet x * Real.log q := by
    have hsplit : SL + 2 * K * SC + (SLR + 2 * K * SCR - kap x * SRlog)
        = ∑ p ∈ q.primeFactors, ((llp x p + 2 * K * lcp x p)
          + (if p ∈ R then llp x p + 2 * K * lcp x p - kap x * Real.log p else 0)) := by
      rw [sum_add_distrib, ← sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hRq]
      simp only [SL, SC, SLR, SCR, SRlog, sum_add_distrib, sum_sub_distrib, mul_sum]
    rw [hsplit]
    set c : ℕ → ℝ := fun p => (llp x p + 2 * K * lcp x p)
      + (if p ∈ R then llp x p + 2 * K * lcp x p - kap x * Real.log p else 0)
    have hβ0 := bet_nonneg hxR
    have hlogsum : ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
      have hpos : ∀ p ∈ q.primeFactors, (0 : ℝ) < p := fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
      apply Real.log_le_log (prod_pos hpos)
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.prod_primeFactors_dvd q)
      have h' : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by exact_mod_cast this
      simpa using h'
    have hle : ∀ p ∈ q.primeFactors, c p - bet x * Real.log p
        ≤ if p ∈ smallP then max 0 (Wp x p - bet x * Real.log p) else 0 := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      split_ifs with hs
      · have := prime_cost x hx p hpp (p ∈ R)
        have := le_max_right 0 (Wp x p - bet x * Real.log p)
        simp only [c, K]; linarith
      · have h17 : 17 ≤ p := by
          by_contra h
          apply hs
          have h2 := hpp.two_le
          interval_cases p <;> simp_all (config := { decide := true })
        have := large_prime_cost x hx hβκ p hpp h17 (p ∈ R)
        simp only [c, K]; linarith
    calc ∑ p ∈ q.primeFactors, c p
        = ∑ p ∈ q.primeFactors, (c p - bet x * Real.log p)
          + bet x * ∑ p ∈ q.primeFactors, Real.log p := by
          rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ p ∈ q.primeFactors, (if p ∈ smallP then max 0 (Wp x p - bet x * Real.log p) else 0)
          + bet x * Real.log q :=
          add_le_add (sum_le_sum hle) (mul_le_mul_of_nonneg_left hlogsum hβ0)
      _ ≤ ∑ p ∈ smallP, max 0 (Wp x p - bet x * Real.log p) + bet x * Real.log q := by
          gcongr
          rw [← sum_filter]
          refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => le_max_left _ _
          intro p hp; exact (mem_filter.1 hp).2
  -- assemble
  unfold Phi
  change (x : ℝ) - 3 / 20 * s - 3 * l - 3 + 2 * K * (l - 2) - kap x * Real.log q
    - 2 * K * Eshift x + 1 / 2 * Real.log Real.pi * l - Etil x - bet x * Real.log q
    - ∑ p ∈ smallP, max 0 (Wp x p - bet x * Real.log p) ≤ 0
  have hexp : K * (lf * (1 - 1 / x) - 2 * (l - 2 - SC - SCR) + 2 * Eshift x)
      = K * (lf * (1 - 1 / x)) - 2 * K * (l - 2) + 2 * K * SC + 2 * K * SCR
        + 2 * K * Eshift x := by ring
  have hkq : kap x * (Real.log q - SRlog) = kap x * Real.log q - kap x * SRlog := by ring
  nlinarith

end LLS
