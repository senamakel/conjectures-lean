import Implications.PrimeGaps.Granville.Statement

/-!
# Granville's prime-gap conjecture refutes three other open prime-gap conjectures

Granville (*Harald Cramér and the distribution of prime numbers*, Scand. Actuar. J. 1995,
12–28) conjectured, from Maier's theorem on primes in short intervals, that
`limsup g_n / (log p_n)^2 ≥ 2 e^{-γ} ≈ 1.1229`, and remarked that this contradicts the
prediction `limsup = 1` from Cramér's random model. formal-conjectures states the conjecture as
`CramerConjecture.cramer_conjecture.variants.granville` (for every `c < 2 e^{-γ}`, infinitely
many `n` have `c ≤ g_n / (log p_n)^2`), and records in its docstrings that it contradicts
`limsup_eq_one`, `strict_bound` and Shanks's `G(x) ~ (log x)^2`. We prove the three
contradictions. The only arithmetic input is `1 < 2 e^{-γ}`, from Mathlib's `γ < 2/3` and
`0.6931471803 < log 2`.

* `not_limsupEqOne_of_granville`: Granville ⇒ ¬ `limsup_eq_one`, at `c = (1 + 2 e^{-γ}) / 2`.
* `not_strictBound_of_granville`: Granville ⇒ ¬ `strict_bound`, at `c = 1`.
* `not_shanks_of_granville`: Granville ⇒ ¬ Shanks. A gap `g_n ≥ c (log p_n)^2` with `c > 1`
  gives `G(p_n + 1) ≥ g_n`, while `log (p_n + 1) ≤ log p_n + 1`.
* `not_granville_of_firoozbakht`: Firoozbakht's conjecture, together with formal-conjectures'
  `firoozbakht_conjecture_consequence` (`g_n < (log p_n)^2 - log p_n` for `n > 3`, a cited
  hypothesis here), implies the strict bound and so refutes Granville.

Both sides of every edge are open conjectures; none of them is proved or disproved here.
-/

open Filter

set_option linter.dupNamespace false

namespace Implications.PrimeGaps

/-! ## The arithmetic input: `1 < 2 e^{-γ}` -/

/-- `1 < 2 e^{-γ}`, because `γ < 2/3 < log 2`. -/
theorem one_lt_two_mul_exp_neg_eulerMascheroni :
    1 < 2 * Real.exp (-Real.eulerMascheroniConstant) := by
  have hγ : Real.eulerMascheroniConstant < Real.log 2 := by
    have h1 := Real.eulerMascheroniConstant_lt_two_thirds
    have h2 := Real.log_two_gt_d9
    norm_num at h2
    linarith
  have hexp : Real.exp Real.eulerMascheroniConstant < 2 := by
    simpa [Real.exp_log two_pos] using Real.exp_lt_exp.2 hγ
  rw [Real.exp_neg, ← div_eq_mul_inv, one_lt_div (Real.exp_pos _)]
  exact hexp

/-! ## Helper facts about primes and `sup_primeGap` -/

/-- `0 < log p_n`, since `p_n ≥ 2`. -/
lemma log_nth_prime_pos (n : ℕ) : 0 < Real.log (Nat.nth Nat.Prime n : ℝ) :=
  Real.log_pos (by exact_mod_cast (_root_.Nat.prime_nth_prime n).one_lt)

/-- `c ≤ cramerRatio n` means `c (log p_n)^2 ≤ g_n`. -/
lemma le_cramerRatio_iff (c : ℝ) (n : ℕ) :
    c ≤ CramerConjecture.cramerRatio n ↔
      c * Real.log (Nat.nth Nat.Prime n : ℝ) ^ 2 ≤ primeGap n := by
  rw [CramerConjecture.cramerRatio, le_div_iff₀ (by have := log_nth_prime_pos n; positivity)]

/-- The gap `g_n` starts below `p_n + 1`, so it is at most `G(p_n + 1)`. -/
lemma primeGap_le_sup_primeGap (n : ℕ) :
    primeGap n ≤ sup_primeGap ((Nat.nth Nat.Prime n + 1 : ℕ) : ℝ) := by
  unfold sup_primeGap
  rw [Nat.ceil_natCast]
  apply Finset.le_sup
  rw [Finset.mem_range]
  have hc : Nat.primeCounting' (Nat.nth Nat.Prime n + 1) = n + 1 := by
    rw [Nat.primeCounting', Nat.count_succ, if_pos (_root_.Nat.prime_nth_prime n)]
    rw [← Nat.primeCounting', Nat.primeCounting'_nth_eq]
  omega

/-- `log (p + 1) ≤ log p + 1` for `p ≥ 1`. -/
lemma log_add_one_le {p : ℝ} (hp : 1 ≤ p) : Real.log (p + 1) ≤ Real.log p + 1 := by
  have he : p + 1 ≤ p * Real.exp 1 := by
    have := Real.exp_one_gt_d9
    nlinarith
  calc Real.log (p + 1) ≤ Real.log (p * Real.exp 1) :=
        Real.log_le_log (by linarith) he
    _ = Real.log p + 1 := by
        rw [Real.log_mul (by linarith) (Real.exp_pos 1).ne', Real.log_exp]

/-! ## Headline theorems -/

/-- **Granville's conjecture implies that Cramér's `limsup = 1` prediction is false.** -/
theorem not_limsupEqOne_of_granville (hG : CramerConjecture.Granville) :
    ¬ CramerConjecture.LimsupEqOne := by
  intro h
  have h1 := one_lt_two_mul_exp_neg_eulerMascheroni
  set A := 2 * Real.exp (-Real.eulerMascheroniConstant)
  set c := (1 + A) / 2 with hc
  have hcA : c < A := by rw [hc]; linarith
  have hε : 0 < (c - 1) / 2 := by rw [hc]; linarith
  obtain ⟨n, hn1, hn2⟩ := ((hG c hcA).and_eventually (h.1 _ hε)).exists
  linarith

/-- **Granville's conjecture implies that the strict numerical Cramér bound
`g_n < (log p_n)^2` (for all `n ≥ 4`) is false.** -/
theorem not_strictBound_of_granville (hG : CramerConjecture.Granville) :
    ¬ CramerConjecture.StrictBound := by
  intro h
  obtain ⟨n, hn1, hn2⟩ :=
    ((hG 1 one_lt_two_mul_exp_neg_eulerMascheroni).and_eventually
      (eventually_ge_atTop 4)).exists
  exact absurd (h n hn2) (not_lt.2 hn1)

/-- **Granville's conjecture implies that Shanks's conjecture `G(x) ~ (log x)^2` is false.** -/
theorem not_shanks_of_granville (hG : CramerConjecture.Granville) :
    ¬ MaximalPrimeGap.ShanksConjecture := by
  intro hS
  have h1 := one_lt_two_mul_exp_neg_eulerMascheroni
  set A := 2 * Real.exp (-Real.eulerMascheroniConstant)
  set c := (1 + A) / 2 with hc
  have hcA : c < A := by rw [hc]; linarith
  set ε := (c - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef, hc]; linarith
  -- Shanks, in the form `|G(x) - (log x)^2| ≤ ε (log x)^2` eventually, at `x = p_n + 1`
  have hx : Tendsto (fun n : ℕ => ((Nat.nth Nat.Prime n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp <| tendsto_atTop_mono (fun n ↦ Nat.le_succ _)
      (_root_.Nat.nth_strictMono _root_.Nat.infinite_setOfPred_prime).tendsto_atTop
  have hb := hx.eventually (hS.isLittleO.bound hε)
  -- `log p_n` is eventually large
  set K := max 1 (3 * (1 + ε) / ε)
  have hL := (Real.tendsto_log_atTop.comp tendsto_nth_prime_real).eventually_ge_atTop K
  obtain ⟨n, hgap, hbn, hLn⟩ := ((hG c hcA).and_eventually (hb.and hL)).exists
  simp only [Function.comp_apply, Pi.sub_apply, Real.norm_eq_abs] at hbn hLn
  rw [le_cramerRatio_iff] at hgap
  set p : ℝ := (Nat.nth Nat.Prime n : ℝ) with hp
  set L := Real.log p with hLdef
  have hp1 : 1 ≤ p := by
    rw [hp]; exact_mod_cast (_root_.Nat.prime_nth_prime n).one_lt.le
  have hK1 : 1 ≤ L := le_trans (le_max_left _ _) hLn
  have hK2 : 3 * (1 + ε) / ε ≤ L := le_trans (le_max_right _ _) hLn
  have hK2' : 3 * (1 + ε) ≤ ε * L := by
    rwa [div_le_iff₀ hε, mul_comm] at hK2
  push_cast at hbn
  rw [← hp] at hbn
  set l := Real.log (p + 1) with hldef
  have hl0 : 0 ≤ l := Real.log_nonneg (by linarith)
  have hlL : l ≤ L + 1 := log_add_one_le hp1
  have hl2 : l ^ 2 ≤ (L + 1) ^ 2 := pow_le_pow_left₀ hl0 hlL 2
  rw [abs_of_nonneg (sq_nonneg l)] at hbn
  -- the chain `c L² ≤ g_n ≤ G(p_n + 1) ≤ (1 + ε) l² ≤ (1 + ε) (L + 1)² < c L²`
  have hGle : (primeGap n : ℝ) ≤ (sup_primeGap (p + 1) : ℝ) := by
    have := primeGap_le_sup_primeGap n
    have h' : (((Nat.nth Nat.Prime n + 1 : ℕ) : ℝ)) = p + 1 := by rw [hp]; push_cast; rfl
    rw [h'] at this
    exact_mod_cast this
  have hsup : (sup_primeGap (p + 1) : ℝ) ≤ (1 + ε) * l ^ 2 := by
    have := le_abs_self ((sup_primeGap (p + 1) : ℝ) - l ^ 2)
    nlinarith
  have hfinal : (1 + ε) * (L + 1) ^ 2 < c * L ^ 2 := by
    have hc' : c = 1 + 2 * ε := by rw [hεdef]; ring
    rw [hc']
    nlinarith
  nlinarith

/-- **Firoozbakht's conjecture, with its cited consequence `g_n < (log p_n)^2 - log p_n`
(formal-conjectures `firoozbakht_conjecture_consequence`), implies the strict numerical Cramér
bound.** -/
theorem strictBound_of_firoozbakht (hF : Firoozbakht.FiroozbakhtConjecture)
    (hK : Firoozbakht.FiroozbakhtConsequence) : CramerConjecture.StrictBound := by
  have hPrime : (fun n : ℕ => Prime n) = Nat.Prime :=
    funext fun n ↦ propext _root_.Nat.prime_iff.symm
  intro n hn
  have h := hK n (by omega) hF
  simp only [hPrime] at h
  have hlog := log_nth_prime_pos n
  have hlt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    _root_.Nat.nth_strictMono _root_.Nat.infinite_setOfPred_prime (by omega)
  rw [CramerConjecture.cramerRatio, div_lt_one (by positivity), primeGap,
    Nat.cast_sub hlt.le]
  linarith

/-- **Firoozbakht's conjecture, with its cited consequence, implies Granville's conjecture is
false.** -/
theorem not_granville_of_firoozbakht (hF : Firoozbakht.FiroozbakhtConjecture)
    (hK : Firoozbakht.FiroozbakhtConsequence) : ¬ CramerConjecture.Granville :=
  fun hG ↦ not_strictBound_of_granville hG (strictBound_of_firoozbakht hF hK)

end Implications.PrimeGaps
