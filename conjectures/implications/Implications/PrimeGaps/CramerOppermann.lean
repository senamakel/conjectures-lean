import Implications.PrimeGaps.FiroozbakhtOppermann

/-!
# The strict Cramér bound ⇒ Oppermann, Andrica, Legendre and Brocard

`CramerConjecture.StrictBound` (formal-conjectures `cramer_conjecture.variants.strict_bound`:
`p_{n+1} - p_n < (log p_n)²` for `n ≥ 4`, copied verbatim in `Implications.PrimeGaps.Erdos382`)
implies the full Oppermann conjecture (`Oppermann.OppermannConjecture`, copied verbatim in
`Implications.PrimeGaps.Andrica`), and through the merged implications Andrica's, Legendre's and
Brocard's conjectures.

1. **Large primes.** For `p_k ≥ 2^16`, `(log p_k)² ≤ (log 2)² √p_k < √p_k`
   (`log_sq_le_of_ge`, from `Implications.PrimeGaps.FiroozbakhtOppermann`), so the strict bound
   gives `(p_{k+1} - p_k)² < p_k`.
2. **Small range.** The merged kernel-`decide` chain `Firoozbakht.exists_prime_sq_lt_small`
   (no hypothesis) gives, for `127 ≤ m < 65731`, a prime `q > m` with `(q - m)² < m`.
3. So every `m ≥ 127` has a prime `q > m` with `(q - m)² < m`; applied to `m = x(x-1)` and
   `m = x²` this is Oppermann for `x ≥ 12`, and `2 ≤ x ≤ 11` is checked by hand.

The inequality `(q - m)² < m` is exactly what Oppermann needs: a prime in `(m, m + x)` with
`m ≤ x²`. The threshold `2^16` is not optimal (`(log p)² < √p` already for `p ≥ 5504`), but the
merged chain reaches `65731`, so nothing is lost.
-/

namespace Implications.PrimeGaps

/-- Any supply of primes `q > m` with `(q - m)² < m` for all `m ≥ 127` gives Oppermann's
conjecture. (The final step of `oppermann_of_firoozbakht`, with the hypothesis abstracted.) -/
theorem oppermann_of_exists_prime_sq_lt
    (H : ∀ m : ℕ, 127 ≤ m → ∃ q : ℕ, q.Prime ∧ m < q ∧ (q - m) ^ 2 < m) :
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
  · obtain ⟨A, hA⟩ : ∃ A, A = x * x := ⟨_, rfl⟩
    have hxA : 12 * x ≤ A := hA ▸ Nat.mul_le_mul_right x hbig
    have e1 : x * (x - 1) + x = A := by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      rw [hA, Nat.add_sub_cancel]; ring
    have e2 : x ^ 2 = A := by rw [hA, sq]
    have e3 : x * (x + 1) = A + x := by rw [hA]; ring
    rw [e2, e3]
    generalize hB : x * (x - 1) = B at e1 ⊢
    constructor
    · obtain ⟨q, hq, h1, h2⟩ := H B (by omega)
      have := lt_add_of_sq_lt (x := x) h1 h2 (by rw [← hA]; omega)
      exact ⟨q, Finset.mem_Ioo.2 ⟨h1, by omega⟩, hq⟩
    · obtain ⟨q, hq, h1, h2⟩ := H A (by omega)
      have := lt_add_of_sq_lt (x := x) h1 h2 (by rw [← hA])
      exact ⟨q, Finset.mem_Ioo.2 ⟨h1, by omega⟩, hq⟩

/-- **The strict Cramér bound gives `(p_{k+1} - p_k)² < p_k` once `p_k ≥ 2^16`.** -/
theorem gap_sq_lt_of_strictBound (h : CramerConjecture.StrictBound) {k : ℕ}
    (hk : 65536 ≤ Nat.nth Nat.Prime k) :
    (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) ^ 2 < Nat.nth Nat.Prime k := by
  have hinf := _root_.Nat.infinite_setOfPred_prime
  have hk4 : 4 ≤ k := by
    by_contra hc
    push Not at hc
    have : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime 3 := (_root_.Nat.nth_le_nth hinf).2 (by omega)
    have h3 : Nat.nth Nat.Prime 3 < 65536 := by
      have := Nat.nth_count (p := Nat.Prime) (n := 7) (by norm_num)
      have hc : Nat.count Nat.Prime 7 = 3 := by decide
      rw [hc] at this; omega
    omega
  have hr := h k hk4
  set a : ℝ := (Nat.nth Nat.Prime k : ℝ) with ha
  have ha16 : (65536 : ℝ) ≤ a := by rw [ha]; exact_mod_cast hk
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  rw [CramerConjecture.cramerRatio, div_lt_one (by positivity)] at hr
  have hL := log_sq_le_of_ge ha16
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hs : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hss : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have hs1 : (256 : ℝ) ≤ Real.sqrt a := by
    have : Real.sqrt 65536 = 256 := by
      rw [show (65536 : ℝ) = 256 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this]; exact Real.sqrt_le_sqrt ha16
  have hg : (primeGap k : ℝ) < Real.sqrt a := by
    have hl1 : Real.log 2 ^ 2 < 1 := by nlinarith
    have : Real.log 2 ^ 2 * Real.sqrt a < Real.sqrt a := by nlinarith
    rw [← ha] at hr; linarith
  have hlt := nth_lt_nth_succ k
  have hd : ((Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k : ℕ) : ℝ) = primeGap k := rfl
  have h2 := pow_lt_pow_left₀ hg (by positivity) (two_ne_zero)
  rw [hss, ← hd, ha] at h2
  exact_mod_cast h2

/-- Under the strict Cramér bound, every `m ≥ 127` has a prime `q > m` with `(q - m)² < m`. -/
theorem exists_prime_sq_lt_of_strictBound (h : CramerConjecture.StrictBound) {m : ℕ}
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
  have hg := gap_sq_lt_of_strictBound h hk16
  calc (Nat.nth Nat.Prime (k + 1) - m) ^ 2
      ≤ (Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
    _ < Nat.nth Nat.Prime k := hg
    _ ≤ m := hk1

/-! ## Headline theorems -/

/-- **The strict Cramér bound implies Oppermann's conjecture.** -/
theorem oppermann_of_strictBound (h : CramerConjecture.StrictBound) :
    Oppermann.OppermannConjecture :=
  oppermann_of_exists_prime_sq_lt fun _ hm ↦ exists_prime_sq_lt_of_strictBound h hm

/-- **The strict Cramér bound implies Andrica's conjecture** (through Oppermann's). -/
theorem andrica_of_strictBound (h : CramerConjecture.StrictBound) :
    Andrica.AndricaConjecture :=
  andrica_of_oppermann (oppermann_of_strictBound h)

/-- **The strict Cramér bound implies Legendre's conjecture** (through Andrica's). -/
theorem legendre_of_strictBound (h : CramerConjecture.StrictBound) :
    LegendreConjecture.LegendreConjecture :=
  legendre_of_andrica (andrica_of_strictBound h)

/-- **The strict Cramér bound implies Brocard's conjecture** (through Oppermann's). -/
theorem brocard_of_strictBound (h : CramerConjecture.StrictBound) :
    Brocard.BrocardConjecture :=
  brocard_of_oppermann (oppermann_of_strictBound h)

end Implications.PrimeGaps
