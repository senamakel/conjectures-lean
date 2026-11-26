import Implications.PrimeGaps.Erdos382
import Implications.PrimeGaps.Andrica
import Implications.PrimeGaps.FiroozbakhtChain

/-!
# Firoozbakht ⇒ Oppermann, and so ⇒ Andrica, Legendre and Brocard

Firoozbakht's conjecture (`Firoozbakht.FiroozbakhtConjecture`, copied verbatim from
formal-conjectures in `Implications.PrimeGaps.Erdos382`) implies Oppermann's conjecture
(`Oppermann.OppermannConjecture`, copied verbatim in `Implications.PrimeGaps.Andrica`). With
`Implications.PrimeGaps.Andrica` this gives Andrica's, Legendre's and Brocard's conjectures as well.

The argument (the implication is attributed to Ferreira–Mariano; we did not use their paper):

1. **Explicit gap bound** (`gap_lt_sqrt_of_firoozbakht`). Write `a = p_k`, `b = p_{k+1}`,
   `L = log a`, `t = L / (k + 1)`. Firoozbakht at `k` gives `b < a · exp t`, and Chebyshev's
   `a log 2 ≤ (k + 1) L` (Mathlib's `Chebyshev.psi_ge_of_seven_le`, via `nth_mul_log_two_le`) gives
   `a t ≤ L² / log 2`. Since `log s / √s` decreases for `s ≥ e²` (Mathlib's
   `Real.log_div_sqrt_antitoneOn`), at `s = √a ≥ 256` we get `L² ≤ (log 2)² √a`. With
   `exp t ≤ 1 + t + t²` this yields `b - a < (log 2) √a + (log 2)² < √a` whenever `a ≥ 2^16`.
2. **Finite range** (`Firoozbakht.exists_prime_sq_lt_small`, no hypothesis). A kernel-checked chain
   of 535 primes from `127` to `65731` gives, for every `127 ≤ m < 65731`, a prime `q > m` with
   `(q - m)² < m`.
3. Together: every `m ≥ 127` has a prime `q > m` with `(q - m)² < m`
   (`exists_prime_sq_lt_of_firoozbakht`). Applied to `m = x(x-1)` and `m = x²` this gives
   Oppermann's two primes for `x ≥ 12`; `2 ≤ x ≤ 11` is checked by hand.
-/

open Real

namespace Implications.PrimeGaps

/-- `(log a)² ≤ (log 2)² √a` for `a ≥ 2^16`. -/
lemma log_sq_le_of_ge {a : ℝ} (ha : 65536 ≤ a) :
    Real.log a ^ 2 ≤ Real.log 2 ^ 2 * Real.sqrt a := by
  have ha0 : 0 ≤ a := by linarith
  set s := Real.sqrt a with hs
  have hss : s ^ 2 = a := Real.sq_sqrt ha0
  have hs256 : (256 : ℝ) ≤ s := by
    have : Real.sqrt 65536 = 256 := by
      rw [show (65536 : ℝ) = 256 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this, hs]; exact Real.sqrt_le_sqrt ha
  have he2 : Real.exp 2 ≤ 256 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h2]; nlinarith [Real.exp_pos 1]
  have hanti := Real.log_div_sqrt_antitoneOn (Set.mem_Ici.2 he2)
    (Set.mem_Ici.2 (he2.trans hs256)) hs256
  simp only at hanti
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have hsq256 : Real.sqrt 256 = 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h256, hsq256] at hanti
  have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have h1 : Real.log s ≤ Real.log 2 / 2 * Real.sqrt s := by
    rw [div_le_iff₀ hsqs] at hanti; linarith
  have hla : Real.log a = 2 * Real.log s := by
    rw [← hss, Real.log_pow]; norm_num
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hsqs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt (by linarith)
  rw [hla]
  have h2 : 2 * Real.log s ≤ Real.log 2 * Real.sqrt s := by linarith
  calc (2 * Real.log s) ^ 2 ≤ (Real.log 2 * Real.sqrt s) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
    _ = Real.log 2 ^ 2 * s := by rw [mul_pow, hsqs2]

/-- **Explicit gap bound from Firoozbakht's conjecture**: `p_{k+1} - p_k < √p_k` once
`p_k ≥ 2^16`. -/
theorem gap_lt_sqrt_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) {k : ℕ}
    (hk : 65536 ≤ Nat.nth Nat.Prime k) :
    (Nat.nth Nat.Prime (k + 1) : ℝ) - Nat.nth Nat.Prime k < Real.sqrt (Nat.nth Nat.Prime k) := by
  have hPrime : (fun n : ℕ => Prime n) = Nat.Prime :=
    funext fun n ↦ propext _root_.Nat.prime_iff.symm
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' := Real.log_two_lt_d9
  set a : ℝ := (Nat.nth Nat.Prime k : ℝ) with ha
  set b : ℝ := (Nat.nth Nat.Prime (k + 1) : ℝ) with hb
  have ha16 : (65536 : ℝ) ≤ a := by rw [ha]; exact_mod_cast hk
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by
    have := (_root_.Nat.prime_nth_prime (k + 1)).pos
    rw [hb]; exact_mod_cast this
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  -- Firoozbakht at `k`, in logarithms (as in `cramer_of_firoozbakht`)
  have hF := h k
  simp only [Firoozbakht.firoozbakhtSeq, hPrime] at hF
  rw [← ha, ← hb] at hF
  have hF' := Real.log_lt_log (Real.rpow_pos_of_pos hb0 _) hF
  rw [Real.log_rpow hb0, Real.log_rpow ha0] at hF'
  push_cast at hF'
  set L := Real.log a with hL
  set t : ℝ := L / (k + 1 : ℝ) with ht
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hlogb : Real.log b < L + t := by
    have e1 : Real.log b = (k + 1 + 1) * (1 / ((k : ℝ) + 1 + 1) * Real.log b) := by
      field_simp
    have e2 : L + t = (k + 1 + 1) * (1 / ((k : ℝ) + 1) * L) := by
      rw [ht]; field_simp
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hF' (by positivity)
  have hbexp : b < a * Real.exp t := by
    have := Real.exp_lt_exp.2 hlogb
    rwa [Real.exp_log hb0, Real.exp_add, hL, Real.exp_log ha0] at this
  have ht0 : 0 ≤ t := by positivity
  -- Chebyshev: `a log 2 ≤ (k + 1) L`
  have hcheb := nth_mul_log_two_le (k := k) (by omega)
  rw [← ha, ← hL] at hcheb
  have htk : t * (k + 1) = L := by rw [ht]; field_simp
  have hat : a * t * Real.log 2 ≤ L ^ 2 := by
    have h1 : (k + 1 : ℝ) * (a * t * Real.log 2) ≤ (k + 1) * L ^ 2 := by
      have : (k + 1 : ℝ) * (a * t * Real.log 2) = (a * Real.log 2) * (t * (k + 1)) := by ring
      rw [this, htk]
      have := mul_le_mul_of_nonneg_right hcheb hla.le
      nlinarith
    exact le_of_mul_le_mul_left h1 hk1
  -- `L² ≤ (log 2)² s` with `s = √a`
  set s := Real.sqrt a with hs
  have hss : s ^ 2 = a := Real.sq_sqrt ha0.le
  have hs256 : (256 : ℝ) ≤ s := by
    have : Real.sqrt 65536 = 256 := by
      rw [show (65536 : ℝ) = 256 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this, hs]; exact Real.sqrt_le_sqrt ha16
  have hL2 : L ^ 2 ≤ Real.log 2 ^ 2 * s := log_sq_le_of_ge ha16
  have hat' : a * t ≤ Real.log 2 * s := by
    have : a * t * Real.log 2 ≤ (Real.log 2 * s) * Real.log 2 := by nlinarith
    exact le_of_mul_le_mul_right this hlog2
  have hts : t * s ≤ Real.log 2 := by
    rw [← hss] at hat'
    have : s * (t * s) ≤ s * Real.log 2 := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  have ht1 : t ≤ 1 := by nlinarith
  have hexp : Real.exp t ≤ 1 + t + t ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := t) (by rw [abs_of_nonneg ht0]; exact ht1)
    have := (le_abs_self _).trans this
    linarith
  have hgap : b - a < Real.log 2 * s + Real.log 2 ^ 2 := by
    have h1 : b - a < a * t + a * t * t := by nlinarith [Real.exp_pos t]
    have h2 : a * t * t ≤ Real.log 2 * s * t := mul_le_mul_of_nonneg_right hat' ht0
    have h3 : Real.log 2 * s * t ≤ Real.log 2 ^ 2 := by
      have := mul_le_mul_of_nonneg_left hts hlog2.le
      nlinarith
    linarith
  have : Real.log 2 * s + Real.log 2 ^ 2 < s := by nlinarith
  linarith

/-- The explicit gap bound, squared out in `ℕ`: `(p_{k+1} - p_k)² < p_k` once `p_k ≥ 2^16`. -/
theorem gap_sq_lt_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) {k : ℕ}
    (hk : 65536 ≤ Nat.nth Nat.Prime k) :
    (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) ^ 2 < Nat.nth Nat.Prime k := by
  have hg := gap_lt_sqrt_of_firoozbakht h hk
  have hlt := nth_lt_nth_succ k
  have ha0 : (0 : ℝ) ≤ Nat.nth Nat.Prime k := by positivity
  have hd : ((Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k : ℕ) : ℝ) =
      (Nat.nth Nat.Prime (k + 1) : ℝ) - Nat.nth Nat.Prime k := Nat.cast_sub hlt.le
  have hd0 : (0 : ℝ) ≤ (Nat.nth Nat.Prime (k + 1) : ℝ) - Nat.nth Nat.Prime k := by
    rw [← hd]; positivity
  have h2 := pow_lt_pow_left₀ hg hd0 (two_ne_zero)
  rw [Real.sq_sqrt ha0, ← hd] at h2
  exact_mod_cast h2

/-- **Under Firoozbakht's conjecture, every `m ≥ 127` has a prime `q > m` with `(q - m)² < m`.** -/
theorem exists_prime_sq_lt_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) {m : ℕ}
    (hm : 127 ≤ m) : ∃ q : ℕ, q.Prime ∧ m < q ∧ (q - m) ^ 2 < m := by
  rcases lt_or_ge m 65731 with hlt | hge
  · exact Firoozbakht.exists_prime_sq_lt_small hm hlt
  obtain ⟨k, hk1, hk2⟩ := exists_nth_le_lt (m := m) (by omega)
  have hk16 : 65536 ≤ Nat.nth Nat.Prime k := by
    by_contra hc
    push Not at hc
    have : Nat.nth Nat.Prime (k + 1) ≤ 65731 :=
      nth_succ_le_of_prime (by norm_num) (by omega)
    omega
  refine ⟨Nat.nth Nat.Prime (k + 1), _root_.Nat.prime_nth_prime _, hk2, ?_⟩
  have hg := gap_sq_lt_of_firoozbakht h hk16
  calc (Nat.nth Nat.Prime (k + 1) - m) ^ 2
      ≤ (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
    _ < Nat.nth Nat.Prime k := hg
    _ ≤ m := hk1

/-- If `(q - m)² < m < x²` then `q < m + x`. -/
lemma lt_add_of_sq_lt {q m x : ℕ} (hmq : m < q) (h : (q - m) ^ 2 < m) (hm : m ≤ x * x) :
    q < m + x := by
  by_contra hc
  push Not at hc
  have h1 : x ≤ q - m := by omega
  have h2 : x * x ≤ (q - m) ^ 2 := by rw [sq]; exact Nat.mul_le_mul h1 h1
  omega

/-! ## Headline theorems -/

/-- **Firoozbakht's conjecture implies Oppermann's conjecture.** -/
theorem oppermann_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) :
    Oppermann.OppermannConjecture := by
  intro x hx
  rcases lt_or_ge x 12 with hsmall | hbig
  · have w : ∀ a b p : ℕ, a < p → p < b → p.Prime → ∃ q ∈ Finset.Ioo a b, q.Prime :=
      fun a b p h1 h2 hp => ⟨p, Finset.mem_Ioo.2 ⟨h1, h2⟩, hp⟩
    interval_cases x
    · exact ⟨w _ _ 3 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 5 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 7 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 11 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 13 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 17 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 23 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 29 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 31 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 37 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 43 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 53 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 59 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 67 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 73 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 83 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 97 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 101 (by norm_num) (by norm_num) (by norm_num)⟩
    · exact ⟨w _ _ 113 (by norm_num) (by norm_num) (by norm_num),
        w _ _ 127 (by norm_num) (by norm_num) (by norm_num)⟩
  · have hxx : 144 ≤ x * x := Nat.mul_le_mul hbig hbig
    have e1 : x * (x - 1) + x = x * x := by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      rw [Nat.add_sub_cancel]; ring
    have e2 : x ^ 2 = x * x := sq x
    have e3 : x * (x + 1) = x * x + x := by ring
    constructor
    · obtain ⟨q, hq, h1, h2⟩ := exists_prime_sq_lt_of_firoozbakht h (m := x * (x - 1)) (by omega)
      have := lt_add_of_sq_lt h1 h2 (by omega)
      exact ⟨q, Finset.mem_Ioo.2 ⟨h1, by omega⟩, hq⟩
    · obtain ⟨q, hq, h1, h2⟩ := exists_prime_sq_lt_of_firoozbakht h (m := x ^ 2) (by omega)
      have := lt_add_of_sq_lt h1 h2 (by omega)
      exact ⟨q, Finset.mem_Ioo.2 ⟨h1, by omega⟩, hq⟩

/-- **Firoozbakht's conjecture implies Andrica's conjecture** (through Oppermann's). -/
theorem andrica_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) :
    Andrica.AndricaConjecture :=
  andrica_of_oppermann (oppermann_of_firoozbakht h)

/-- **Firoozbakht's conjecture implies Legendre's conjecture** (through Andrica's). -/
theorem legendre_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) :
    LegendreConjecture.LegendreConjecture :=
  legendre_of_andrica (andrica_of_firoozbakht h)

/-- **Firoozbakht's conjecture implies Brocard's conjecture** (through Oppermann's). -/
theorem brocard_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) :
    Brocard.BrocardConjecture :=
  brocard_of_oppermann (oppermann_of_firoozbakht h)

end Implications.PrimeGaps
