import Goldbach.Compute.Sieve

/-!
# Soundness of the binary Goldbach checker

`goldbachChunk_sound`: if `goldbachChunk P A k n = true`, every even `m` with
`A ≤ m < A + 2 k n` is a sum of two primes.
-/

namespace Goldbach.Check

/-! ### Base primes -/

theorem oddsUpTo_mem {r x : ℕ} : x ∈ oddsUpTo r ↔ ∃ i < r, 2 * i + 3 = x := by
  simp [oddsUpTo]

theorem mem_basePrimes {len r x : ℕ} :
    x ∈ basePrimes len r ↔
      ∃ i < len, (sieve 3 len (oddsUpTo r))[i]! = 1 ∧ 3 + 2 * i = x := by
  simp only [basePrimes, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    split_ifs at h with h1
    · exact ⟨i, hi, by simpa using h1, by simpa using h⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, by simp [h1, h2]⟩

theorem oddsUpTo_odd {r : ℕ} : ∀ p ∈ oddsUpTo r, Odd p := by
  intro p hp
  obtain ⟨i, -, rfl⟩ := oddsUpTo_mem.mp hp
  exact ⟨i + 1, by ring⟩

theorem oddsUpTo_three_le {r : ℕ} : ∀ p ∈ oddsUpTo r, 3 ≤ p := by
  intro p hp
  obtain ⟨i, -, rfl⟩ := oddsUpTo_mem.mp hp
  omega

theorem basePrimes_odd {len r : ℕ} : ∀ p ∈ basePrimes len r, Odd p := by
  intro p hp
  obtain ⟨i, -, -, rfl⟩ := mem_basePrimes.mp hp
  exact ⟨i + 1, by ring⟩

theorem basePrimes_three_le {len r : ℕ} : ∀ p ∈ basePrimes len r, 3 ≤ p := by
  intro p hp
  obtain ⟨i, -, -, rfl⟩ := mem_basePrimes.mp hp
  omega

/-- Every odd prime below `3 + 2 len` is a base prime. -/
theorem mem_basePrimes_of_prime {len r q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hlt : q < 3 + 2 * len) : q ∈ basePrimes len r := by
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases Nat.eq_or_lt_of_le this with h | h
    · rw [← h] at hodd; exact absurd hodd (by decide)
    · omega
  obtain ⟨b, hb⟩ := hodd
  refine mem_basePrimes.mpr ⟨b - 1, by omega, ?_, by omega⟩
  rw [sieve_eq_one_iff 3 len _ (by decide) oddsUpTo_odd _ (by omega)]
  have e : 3 + 2 * (b - 1) = q := by omega
  rw [e]
  exact unmarked_of_prime oddsUpTo_three_le hq

/-- Base primes are prime, when `3 + 2 len < (2 r + 3)²`. -/
theorem prime_of_mem_basePrimes {len r x : ℕ} (hr : 3 + 2 * len < (2 * r + 3) * (2 * r + 3))
    (hx : x ∈ basePrimes len r) : x.Prime := by
  obtain ⟨i, hi, h1, rfl⟩ := mem_basePrimes.mp hx
  rw [sieve_eq_one_iff 3 len _ (by decide) oddsUpTo_odd _ hi] at h1
  refine prime_of_unmarked (B := 2 * r + 2) ?_ ⟨i + 1, by ring⟩ (by omega) (by
    have : (2 * r + 2 + 1) = 2 * r + 3 := by ring
    rw [this]; omega) h1
  intro q hq hqo hqB
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases Nat.eq_or_lt_of_le this with h | h
    · rw [← h] at hqo; exact absurd hqo (by decide)
    · omega
  obtain ⟨b, hb⟩ := hqo
  exact oddsUpTo_mem.mpr ⟨b - 1, by omega, by omega⟩

/-! ### Segments -/

theorem allEven_spec {f : ℕ → Bool} : ∀ {k m : ℕ}, allEven f m k = true →
    ∀ j < k, f (m + 2 * j) = true
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, m, h, j, hj => by
    simp only [allEven, Bool.and_eq_true] at h
    rcases j with _ | j
    · simpa using h.1
    · have := allEven_spec h.2 j (by omega)
      rwa [show m + 2 + 2 * j = m + 2 * (j + 1) by ring] at this

/-- A sum of two primes. -/
def SumTwo (m : ℕ) : Prop := ∃ p q, p.Prime ∧ q.Prime ∧ p + q = m

theorem segLo_odd {P A : ℕ} (hP : Odd P) (hA : Even A) : Odd (segLo P A) := by
  unfold segLo
  split_ifs with h
  · obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hP
    exact ⟨a - b - 1, by omega⟩
  · decide

theorem three_le_segLo (P A : ℕ) : 3 ≤ segLo P A := by
  unfold segLo; split_ifs with h <;> omega

theorem segLo_le (P A : ℕ) (hA : 6 ≤ A) : segLo P A ≤ A := by
  unfold segLo; split_ifs with h <;> omega

theorem goldbachSeg_sound {ps qs : List ℕ} {P A k B : ℕ}
    (hps : ∀ p ∈ ps, Odd p) (hcomp : ∀ q, q.Prime → Odd q → q ≤ B → q ∈ ps)
    (hqs : ∀ p ∈ qs, p.Prime ∧ Odd p) (hP : Odd P) (hA : Even A) (hA6 : 6 ≤ A)
    (hB : A + 2 * k ≤ B * B) (h : goldbachSeg ps qs P A k = true) :
    ∀ m, Even m → A ≤ m → m < A + 2 * k → SumTwo m := by
  intro m hm hAm hmk
  unfold goldbachSeg at h
  set lo := segLo P A with hlo
  set len := (A + 2 * k - lo) / 2
  have hloodd : Odd lo := segLo_odd hP hA
  have hlo3 : 3 ≤ lo := three_le_segLo P A
  obtain ⟨a, ha⟩ := hA
  obtain ⟨c, hc⟩ := hm
  have hj := allEven_spec h ((m - A) / 2) (by omega)
  rw [show A + 2 * ((m - A) / 2) = m by omega] at hj
  simp only [hasRep, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hj
  obtain ⟨p, hpq, ⟨⟨h1, h2⟩, h3⟩⟩ := hj
  obtain ⟨hpp, hpo⟩ := hqs p hpq
  have hx : lo + 2 * ((m - p - lo) / 2) = m - p := by
    obtain ⟨d, hd⟩ := hpo; obtain ⟨e, he⟩ := hloodd; omega
  rw [sieve_eq_one_iff lo len ps hloodd hps _ h2, hx] at h3
  have hxodd : Odd (m - p) := by
    obtain ⟨d, hd⟩ := hpo; exact ⟨c - d - 1, by omega⟩
  have hxp : (m - p).Prime :=
    prime_of_unmarked hcomp hxodd (by omega)
      (lt_of_lt_of_le (show m - p < B * B by omega)
        (Nat.mul_le_mul (Nat.le_succ B) (Nat.le_succ B))) h3
  exact ⟨p, m - p, hpp, hxp, by omega⟩

theorem goldbachFrom_sound {ps qs : List ℕ} {P k B : ℕ}
    (hps : ∀ p ∈ ps, Odd p) (hcomp : ∀ q, q.Prime → Odd q → q ≤ B → q ∈ ps)
    (hqs : ∀ p ∈ qs, p.Prime ∧ Odd p) (hP : Odd P) :
    ∀ n A, Even A → 6 ≤ A → A + 2 * k * n ≤ B * B → goldbachFrom ps qs P k A n = true →
      ∀ m, Even m → A ≤ m → m < A + 2 * k * n → SumTwo m
  | 0, A, _, _, _, _, m, _, h1, h2 => by omega
  | n + 1, A, hA, hA6, hB, h, m, hm, h1, h2 => by
    simp only [goldbachFrom, Bool.and_eq_true] at h
    by_cases hlt : m < A + 2 * k
    · exact goldbachSeg_sound hps hcomp hqs hP hA hA6 (by nlinarith) h.1 m hm h1 hlt
    · have hA' : Even (A + 2 * k) := hA.add (even_two_mul k)
      exact goldbachFrom_sound hps hcomp hqs hP n (A + 2 * k) hA' (by omega)
        (by rw [Nat.mul_succ] at hB; omega) h.2 m hm (by omega)
        (by rw [Nat.mul_succ] at h2; omega)

theorem goldbachChunk_sound {P A k n : ℕ} (h : goldbachChunk P A k n = true) :
    ∀ m, Even m → A ≤ m → m < A + 2 * k * n → SumTwo m := by
  unfold goldbachChunk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hA, hP⟩, hA6⟩, hHB⟩, hr⟩, hrun⟩ := h
  set B := sqrtUp (A + 2 * k * n)
  set len := max B P / 2 + 1
  set r := sqrtUp (3 + 2 * len) / 2 + 1
  refine goldbachFrom_sound (B := B) basePrimes_odd ?_ ?_ (Nat.odd_iff.mpr hP) n A
    (Nat.even_iff.mpr hA) hA6 hHB hrun
  · intro q hq hqo hqB
    exact mem_basePrimes_of_prime hq hqo (by omega)
  · intro p hp
    rw [List.mem_filter] at hp
    exact ⟨prime_of_mem_basePrimes hr hp.1, basePrimes_odd p hp.1⟩

end Goldbach.Check
