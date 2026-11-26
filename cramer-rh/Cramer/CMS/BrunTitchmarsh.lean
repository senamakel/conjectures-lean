import Cramer.Vendor.LS.LargeSieveMVProof
import Cramer.Vendor.LS.Montgomery
import Cramer.Vendor.LS.SumMuSqPhi

/-!
# A Brun–Titchmarsh inequality from the weighted large sieve

For naturals `M₀`, `N` with `R = √(2N/3) ≤ M₀`, the number `Z` of primes in `(M₀, M₀ + N]`
satisfies `Z · W(R) ≤ N`, where
`W(R) = Σ_{r ≤ R, r squarefree} (1 + r/R)⁻¹ / φ(r)` (`card_primes_mul_W_le`), and
`W(R) ≥ log(R − 1) + 1/2 − log 2` (`W_ge`), so `Z ≲ 2N/log N`.

This is Montgomery–Vaughan's route to their Brun–Titchmarsh theorem (*The large sieve*,
Mathematika 20 (1973), Theorem 2): Montgomery's inequality for each squarefree `r ≤ R`
(`Cramer.Vendor.TG.montgomery_ineq`), the weighted large sieve over the Farey points `b/r`
with `δ = 1/(rR)` (`Cramer.Vendor.TG.Prelim.LS.large_sieve_weighted`), and the lower bound
`Σ_{n ≤ R} (1 + n/R)⁻¹/n ≤ W(R)` from `Σ_{n ≤ t} 1/n ≤ Σ_{r ≤ t sq-free} 1/φ(r)`
(`Cramer.Vendor.TG.Prelim.sum_inv_le_sum_inv_totient`). Both large-sieve inputs are vendored
from calr3/ternary-goldbach (Apache-2.0), as are `frac_sep'` and `le_dist_round_of_forall'`
below (copied from `TernaryGoldbach/MinorArcs/TypeII.lean`, `frac_sep` and
`le_dist_round_of_forall`, specialised to `q = 1`, `A = 0`, `u = 0`).
-/

namespace Cramer.CMS

open Finset Real
open TernaryGoldbach (e)

/-- (From calr3/ternary-goldbach, `TypeII.lean`, `le_dist_round_of_forall`.) -/
theorem le_dist_round_of_forall' {t ν : ℝ} (h : ∀ n : ℤ, ν ≤ |t - n|) : ν ≤ |t - round t| :=
  h (round t)

/-- Separation of Farey fractions (from calr3/ternary-goldbach, `TypeII.lean`, `frac_sep`, with
`q = 1`, `A = 0`, `u = 0`): for `b < r`, `b' < r'`, `(b, r) = (b', r') = 1` and
`(r, b) ≠ (r', b')`, `‖b/r − b'/r'‖ ≥ 1/(r r')`. -/
theorem frac_sep' {r r' b b' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') (hb : b < r) (hb' : b' < r')
    (hbr : Nat.Coprime r b) (hb'r : Nat.Coprime r' b') (hne : ¬ (r = r' ∧ b = b')) :
    1 / ((r : ℝ) * r') ≤ |((b : ℝ) / r - b' / r') - round ((b : ℝ) / r - b' / r')| := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr'0 : (0 : ℝ) < r' := by exact_mod_cast hr'
  set M : ℤ := (b * r' - b' * r : ℤ)
  have hM : ((b : ℝ) / r - b' / r') = M / (r * r') := by
    simp only [M]; push_cast; field_simp
  have hdiv : ¬ ((r * r' : ℕ) : ℤ) ∣ M := by
    intro hdiv
    apply hne
    have hbr' : IsCoprime (r : ℤ) b := Nat.isCoprime_iff_coprime.2 hbr
    have hb'r' : IsCoprime (r' : ℤ) b' := Nat.isCoprime_iff_coprime.2 hb'r
    have h1 : (r : ℤ) ∣ r' := by
      have : (r : ℤ) ∣ M := dvd_trans (⟨(r' : ℤ), by push_cast; ring⟩ : (r : ℤ) ∣ ((r * r' : ℕ) : ℤ)) hdiv
      have h2 : (r : ℤ) ∣ b * r' := by
        have e : ((b : ℤ) * r') = M + r * b' := by simp only [M]; ring
        rw [e]; exact dvd_add this (dvd_mul_right _ _)
      exact hbr'.dvd_of_dvd_mul_left h2
    have h1' : (r' : ℤ) ∣ r := by
      have : (r' : ℤ) ∣ M := dvd_trans (⟨(r : ℤ), by push_cast; ring⟩ : (r' : ℤ) ∣ ((r * r' : ℕ) : ℤ)) hdiv
      have h2 : (r' : ℤ) ∣ b' * r := by
        have e : ((b' : ℤ) * r) = r' * b - M := by simp only [M]; ring
        rw [e]; exact dvd_sub (dvd_mul_right _ _) this
      exact hb'r'.dvd_of_dvd_mul_left h2
    have hrr : r = r' := by
      have := Int.dvd_antisymm (by positivity) (by positivity) h1 h1'
      exact_mod_cast this
    subst hrr
    have h4 : (r : ℤ) ∣ (b : ℤ) - b' := by
      have e : M = r * ((b : ℤ) - b') := by simp only [M]; ring
      rw [e] at hdiv
      have : ((r * r : ℕ) : ℤ) = r * (r : ℤ) := by push_cast; ring
      rw [this] at hdiv
      exact Int.dvd_of_mul_dvd_mul_left (by positivity) hdiv
    have hbb : b = b' := by
      obtain ⟨c, hc⟩ := h4
      have : c = 0 := by
        by_contra hc0
        have : (r : ℤ) ≤ |(b : ℤ) - b'| := by
          rw [hc, abs_mul]
          nlinarith [abs_nonneg (r : ℤ), Int.one_le_abs hc0,
            abs_of_pos (show (0:ℤ) < r by positivity)]
        have : |(b : ℤ) - b'| < r := by rw [abs_lt]; constructor <;> omega
        omega
      rw [this, mul_zero] at hc; omega
    exact ⟨rfl, hbb⟩
  apply le_dist_round_of_forall'
  intro n
  have hne' : M - n * (r * r' : ℕ) ≠ 0 := by
    intro h; exact hdiv ⟨n, by linarith⟩
  have hqrr : (0 : ℝ) < r * r' := by positivity
  have e : ((b : ℝ) / r - b' / r') - n = ((M - n * (r * r' : ℕ) : ℤ) : ℝ) / (r * r') := by
    rw [hM]; push_cast; field_simp
  rw [e, abs_div, abs_of_pos hqrr]
  refine div_le_div_of_nonneg_right ?_ hqrr.le
  rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne'

/-- `W(R) = Σ_{r ≤ R, r squarefree} (1 + r/R)⁻¹ / φ(r)`. -/
noncomputable def W (R : ℝ) : ℝ :=
  ∑ r ∈ (Icc 1 ⌊R⌋₊).filter Squarefree, (1 + r / R)⁻¹ / (Nat.totient r : ℝ)

/-- The Farey index set: `(r, b)` with `r ≤ Q` squarefree, `b < r`, `(r, b) = 1`. -/
def fareySet (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 Q).filter Squarefree).sigma (fun r => (range r).filter r.Coprime) |>.map
    ⟨fun p => (p.1, p.2), fun p q h => by
      obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl⟩

lemma mem_fareySet {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ fareySet Q ↔ (1 ≤ p.1 ∧ p.1 ≤ Q) ∧ Squarefree p.1 ∧ p.2 < p.1 ∧ Nat.Coprime p.1 p.2 := by
  obtain ⟨r, b⟩ := p
  simp only [fareySet, mem_map, mem_sigma, mem_filter, mem_Icc, mem_range, Sigma.exists]
  constructor
  · rintro ⟨r', b', ⟨⟨h1, h2⟩, h3, h4⟩, he⟩
    have he' : (r', b') = (r, b) := he
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨r, b, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩

lemma sum_fareySet {Q : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ fareySet Q, f p.1 p.2 =
      ∑ r ∈ (Icc 1 Q).filter Squarefree, ∑ b ∈ (range r).filter r.Coprime, f r b := by
  rw [fareySet, sum_map, sum_sigma]
  rfl

/-- **The large-sieve count**: if `R = √(2N/3) ≤ M₀`, the number `Z` of primes in
`(M₀, M₀ + N]` satisfies `Z · W(R) ≤ N`. -/
theorem card_primes_mul_W_le {M₀ N : ℕ} (hN : 1 ≤ N) (hR : Real.sqrt (2 * N / 3) ≤ M₀) :
    (#((Ioc M₀ (M₀ + N)).filter Nat.Prime) : ℝ) * W (Real.sqrt (2 * N / 3)) ≤ N := by
  set R := Real.sqrt (2 * N / 3) with hRdef
  set P := (Ioc M₀ (M₀ + N)).filter Nat.Prime
  set Z : ℝ := (#P : ℝ)
  set Q := ⌊R⌋₊
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR0 : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hR2 : R ^ 2 = 2 * N / 3 := Real.sq_sqrt (by positivity)
  have hQR : (Q : ℝ) ≤ R := Nat.floor_le hR0.le
  set a : ℕ → ℂ := fun n => if n.Prime then 1 else 0
  set S : ℝ → ℂ := fun α => ∑ n ∈ Ioc M₀ (M₀ + N), a n * e (α * n)
  have hSP : ∀ α, S α = ∑ n ∈ P, (1 : ℂ) * e (α * n) := by
    intro α
    simp only [S, a, P, sum_filter, ite_mul, zero_mul]
  have hnormA : ∑ n ∈ Ioc M₀ (M₀ + N), ‖a n‖ ^ 2 = Z := by
    simp only [a, Z, P, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  have hS0 : S 0 = Z := by
    rw [hSP]; simp [Z, TernaryGoldbach.e_zero]
  -- the weighted large sieve over the Farey points
  set s := fareySet Q
  set α : ℕ × ℕ → ℝ := fun p => (p.2 : ℝ) / p.1
  set δ : ℕ × ℕ → ℝ := fun p => 1 / ((p.1 : ℝ) * R)
  have hδ : ∀ p ∈ s, 0 < δ p := by
    intro p hp
    have := (mem_fareySet.1 hp).1.1
    have : (0 : ℝ) < p.1 := by exact_mod_cast this
    simp only [δ]; positivity
  have hsep : ∀ p ∈ s, ∀ p' ∈ s, p ≠ p' → δ p ≤ |(α p - α p') - round (α p - α p')| := by
    intro p hp p' hp' hne
    obtain ⟨⟨h1, h2⟩, -, h3, h4⟩ := mem_fareySet.1 hp
    obtain ⟨⟨h1', h2'⟩, -, h3', h4'⟩ := mem_fareySet.1 hp'
    have hne' : ¬ (p.1 = p'.1 ∧ p.2 = p'.2) := fun h => hne (Prod.ext h.1 h.2)
    have key := frac_sep' h1 h1' h3 h3' h4 h4' hne'
    refine le_trans ?_ key
    have hr0 : (0 : ℝ) < p.1 := by exact_mod_cast h1
    have hr'R : (p'.1 : ℝ) ≤ R := le_trans (by exact_mod_cast h2') hQR
    have hr'0 : (0 : ℝ) < p'.1 := by exact_mod_cast h1'
    simp only [δ]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hr'R hr0.le)
  have hLS := Cramer.Vendor.TG.Prelim.LS.large_sieve_weighted s α δ hδ hsep M₀ N a
  rw [hnormA] at hLS
  -- Montgomery's inequality for each squarefree `r ≤ Q`
  have hMont : ∀ r ∈ (Icc 1 Q).filter Squarefree,
      Z ^ 2 / Nat.totient r ≤ ∑ b ∈ (range r).filter r.Coprime, ‖S (b / r)‖ ^ 2 := by
    intro r hr
    obtain ⟨hr1, hsq⟩ := mem_filter.1 hr
    obtain ⟨hr1, hrQ⟩ := mem_Icc.1 hr1
    have hcop : ∀ n ∈ P, Nat.Coprime n r := by
      intro n hn
      obtain ⟨hn1, hnp⟩ := mem_filter.1 hn
      have hnM : M₀ < n := (mem_Ioc.1 hn1).1
      have hrn : r < n := by
        have : (r : ℝ) < n := by
          calc (r : ℝ) ≤ Q := by exact_mod_cast hrQ
            _ ≤ R := hQR
            _ ≤ M₀ := hR
            _ < n := by exact_mod_cast hnM
        exact_mod_cast this
      exact (Nat.Prime.coprime_iff_not_dvd hnp).2
        (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
    have hM := Cramer.Vendor.TG.montgomery_ineq hsq P (fun _ => 1) hcop 0
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.2 (by omega)
    rw [div_le_iff₀ hφ]
    have h0 : ‖∑ n ∈ P, (1 : ℂ) * e (0 * n)‖ = Z := by
      have := hS0; rw [hSP] at this; rw [this]; simp [Z]
    rw [h0] at hM
    calc Z ^ 2 ≤ Nat.totient r * ∑ b ∈ (range r).filter r.Coprime,
          ‖∑ n ∈ P, (1 : ℂ) * e ((0 + b / r) * n)‖ ^ 2 := hM
      _ = (∑ b ∈ (range r).filter r.Coprime, ‖S (b / r)‖ ^ 2) * Nat.totient r := by
          rw [mul_comm]; congr 1
          refine sum_congr rfl fun b _ => ?_
          rw [hSP, zero_add]
  -- combine
  have hweight : ∀ r ∈ (Icc 1 Q).filter Squarefree,
      ((N : ℝ) + 3 / 2 * (1 / ((r : ℝ) * R))⁻¹)⁻¹ = (1 + r / R)⁻¹ / N := by
    intro r hr
    have hr1 := (mem_Icc.1 (mem_filter.1 hr).1).1
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    rw [one_div, inv_inv]
    have : (N : ℝ) + 3 / 2 * (r * R) = N * (1 + r / R) := by
      have : (N : ℝ) = 3 / 2 * R ^ 2 := by rw [hR2]; ring
      rw [this]; field_simp
    rw [this, mul_inv, div_eq_mul_inv, mul_comm, div_eq_mul_inv]
  have hLS' : ∑ r ∈ (Icc 1 Q).filter Squarefree, (1 + r / R)⁻¹ / N *
      ∑ b ∈ (range r).filter r.Coprime, ‖S (b / r)‖ ^ 2 ≤ Z := by
    have := hLS
    rw [show (∑ p ∈ s, ((N : ℝ) + 3 / 2 * (δ p)⁻¹)⁻¹ *
        ‖∑ n ∈ Ioc M₀ (M₀ + N), a n * e (α p * n)‖ ^ 2) =
        ∑ r ∈ (Icc 1 Q).filter Squarefree, ∑ b ∈ (range r).filter r.Coprime,
          ((N : ℝ) + 3 / 2 * (1 / ((r : ℝ) * R))⁻¹)⁻¹ * ‖S (b / r)‖ ^ 2 from
        sum_fareySet (fun r b => ((N : ℝ) + 3 / 2 * (1 / ((r : ℝ) * R))⁻¹)⁻¹ *
          ‖S (b / r)‖ ^ 2)] at this
    refine le_trans (le_of_eq ?_) this
    refine sum_congr rfl fun r hr => ?_
    rw [mul_sum, hweight r hr]
  have hZ0 : 0 ≤ Z := Nat.cast_nonneg _
  have hW0 : 0 ≤ W R := by
    unfold W
    refine sum_nonneg fun r hr => ?_
    have := (mem_Icc.1 (mem_filter.1 hr).1).1
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    positivity
  have hkey : Z ^ 2 * W R / N ≤ Z := by
    refine le_trans ?_ hLS'
    rw [W, mul_sum, sum_div]
    refine sum_le_sum fun r hr => ?_
    have hφ : (0 : ℝ) < Nat.totient r := by
      exact_mod_cast Nat.totient_pos.2 (by have := (mem_Icc.1 (mem_filter.1 hr).1).1; omega)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hw : 0 ≤ (1 + r / R)⁻¹ / N := by positivity
    calc Z ^ 2 * ((1 + r / R)⁻¹ / Nat.totient r) / N = (1 + r / R)⁻¹ / N * (Z ^ 2 / Nat.totient r) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hMont r hr) hw
  rcases eq_or_lt_of_le hZ0 with h | h
  · rw [← h, zero_mul]; exact hN0.le
  · rw [div_le_iff₀ hN0] at hkey
    nlinarith

/-- Abel summation against an antitone nonnegative weight: `Σ_{n ≤ Q} w(n)/n ≤ W`-type sums. -/
lemma sum_antitone_le {Q : ℕ} (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hw : ∀ m n, m ≤ n → w n ≤ w m)
    (f g : ℕ → ℝ) (hfg : ∀ t ≤ Q, ∑ n ∈ Icc 1 t, f n ≤ ∑ n ∈ Icc 1 t, g n) :
    ∑ n ∈ Icc 1 Q, w n * f n ≤ ∑ n ∈ Icc 1 Q, w n * g n := by
  -- Abel: Σ_{n ≤ Q} w(n) h(n) = w(Q) H(Q) + Σ_{t < Q} (w t − w (t+1)) H(t), H(t) = Σ_{n ≤ t} h n
  have abel : ∀ (h : ℕ → ℝ) (T : ℕ), ∑ n ∈ Icc 1 T, w n * h n =
      w T * ∑ n ∈ Icc 1 T, h n + ∑ t ∈ range T, (w t - w (t + 1)) * ∑ n ∈ Icc 1 t, h n := by
    intro h T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [sum_Icc_succ_top (by omega), ih, sum_range_succ, sum_Icc_succ_top (by omega)]
      ring
  rw [abel f, abel g]
  have h1 : w Q * ∑ n ∈ Icc 1 Q, f n ≤ w Q * ∑ n ∈ Icc 1 Q, g n :=
    mul_le_mul_of_nonneg_left (hfg Q le_rfl) (hw0 Q)
  have h2 : ∑ t ∈ range Q, (w t - w (t + 1)) * ∑ n ∈ Icc 1 t, f n ≤
      ∑ t ∈ range Q, (w t - w (t + 1)) * ∑ n ∈ Icc 1 t, g n := by
    refine sum_le_sum fun t ht => ?_
    exact mul_le_mul_of_nonneg_left (hfg t (mem_range.1 ht).le)
      (sub_nonneg.2 (hw t (t + 1) (by omega)))
  linarith

/-- `Σ_{n ≤ R} (1 + n/R)⁻¹/n ≤ W(R)`. -/
lemma sum_harm_le_W {R : ℝ} (hR : 0 < R) :
    ∑ n ∈ Icc 1 ⌊R⌋₊, (1 + n / R)⁻¹ * (1 / (n : ℝ)) ≤ W R := by
  set w : ℕ → ℝ := fun n => (1 + n / R)⁻¹
  have hw0 : ∀ n, 0 ≤ w n := fun n => by simp only [w]; positivity
  have hw : ∀ m n, m ≤ n → w n ≤ w m := by
    intro m n hmn
    simp only [w]
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact inv_anti₀ (by positivity) (by gcongr)
  set g : ℕ → ℝ := fun n => if Squarefree n then 1 / (Nat.totient n : ℝ) else 0
  have hfg : ∀ t ≤ ⌊R⌋₊, ∑ n ∈ Icc 1 t, 1 / (n : ℝ) ≤ ∑ n ∈ Icc 1 t, g n := by
    intro t _
    have := Cramer.Vendor.TG.Prelim.sum_inv_le_sum_inv_totient t
    simp only [g]
    rw [← sum_filter]
    simpa using this
  have := sum_antitone_le w hw0 hw (fun n => 1 / (n : ℝ)) g hfg
  refine this.trans (le_of_eq ?_)
  unfold W
  rw [sum_filter]
  refine sum_congr rfl fun n _ => ?_
  simp only [w, g]
  split_ifs <;> simp [div_eq_mul_inv]

/-- `Σ_{n=1}^{T} 1/(R+n) ≤ log((R+T)/R)`. -/
lemma sum_inv_add_le {R : ℝ} (hR : 0 < R) (T : ℕ) :
    ∑ n ∈ Icc 1 T, 1 / (R + n) ≤ Real.log (R + T) - Real.log R := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h0 : (0 : ℝ) < R + T := by positivity
    have h1 : (0 : ℝ) < R + (T + 1) := by positivity
    have hl : 1 / (R + ((T + 1 : ℕ) : ℝ)) ≤ Real.log (R + ((T + 1 : ℕ) : ℝ)) - Real.log (R + T) := by
      push_cast
      rw [← Real.log_div h1.ne' h0.ne']
      have := Real.one_sub_inv_le_log_of_pos (show 0 < (R + (T + 1)) / (R + T) by positivity)
      have e : 1 - ((R + (T + 1)) / (R + T))⁻¹ = 1 / (R + (T + 1)) := by
        field_simp; ring
      linarith
    linarith

/-- `W(R) ≥ log(R − 1) + 1/2 − log 2` for `R ≥ 2`. -/
theorem W_ge {R : ℝ} (hR : 2 ≤ R) : Real.log (R - 1) + 1 / 2 - Real.log 2 ≤ W R := by
  have hR0 : 0 < R := by linarith
  set Q := ⌊R⌋₊
  have hQ1 : 1 ≤ Q := Nat.le_floor (by norm_num; linarith)
  have hQR : (Q : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRQ : R - 1 < Q := by have := Nat.lt_floor_add_one R; linarith
  refine le_trans ?_ (sum_harm_le_W hR0)
  have hsplit : ∑ n ∈ Icc 1 Q, (1 + n / R)⁻¹ * (1 / (n : ℝ)) =
      ∑ n ∈ Icc 1 Q, 1 / (n : ℝ) - ∑ n ∈ Icc 1 Q, 1 / (R + n) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
    field_simp
    ring
  rw [hsplit]
  have hH : Real.log Q + 1 / 2 ≤ ∑ n ∈ Icc 1 Q, 1 / (n : ℝ) := by
    have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' Q
    have h2 := Real.one_half_lt_eulerMascheroniConstant
    rw [Real.eulerMascheroniSeq'] at h1
    have : (harmonic Q : ℝ) = ∑ n ∈ Icc 1 Q, 1 / (n : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp
    have hQ0 : Q ≠ 0 := by omega
    simp only [hQ0, ite_false] at h1
    linarith
  have hL := sum_inv_add_le hR0 Q
  have hlog : Real.log (R + Q) - Real.log R ≤ Real.log 2 := by
    rw [← Real.log_div (by positivity) hR0.ne']
    exact Real.log_le_log (by positivity) (by rw [div_le_iff₀ hR0]; linarith)
  have hlogQ : Real.log (R - 1) ≤ Real.log Q :=
    Real.log_le_log (by linarith) hRQ.le
  linarith

end Cramer.CMS
