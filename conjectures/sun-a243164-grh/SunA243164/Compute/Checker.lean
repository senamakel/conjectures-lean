import Erdos985.Compute.Checker
import SunA243164.Assembly

/-!
# A counting checker for the finite range, with a soundness proof

The finite range needs the index `n = π(P)` of each prime `P`, so the checker walks through
`[lo, lo + k)` carrying the number `c` of primes below the current point. Primality is decided
exactly (`isPrimeB`): a base-2 Fermat test discards most composites cheaply and `Nat.minFac`
settles the rest. For each prime `P` of index `n > 6` it looks for a small prime `q < n` with
`(q n)^((P-1)/r) ≢ 1 (mod P)` for every prime `r ∣ P - 1`, which makes `q n` a primitive root
(`orderOf_eq_of_pow_and_pow_div_prime`).

`countFrom_sound` is the soundness theorem: if `countFrom lo k c = some c'` and `c` is the number
of primes below `lo`, then `c'` is the number of primes below `lo + k` and every prime in
`[lo, lo + k)` of index `> 6` is a `GoodPrime`. The arithmetic (`powMod`, `smallPrimes`) is
erdos-985's.
-/

namespace SunA243164.Compute

open Erdos985.Compute

/-- A small prime `q < n` such that `g = q n` passes Lucas' test modulo `m`:
`g^(m-1) ≡ 1` and `g^((m-1)/r) ≢ 1` for every prime `r ∣ m - 1`. This proves at once that `m`
is prime (`lucas_primality`) and that `q n` is a primitive root modulo `m`. -/
def lucasB (m n : ℕ) : Bool :=
  let fs := (m - 1).primeFactorsList.dedup
  smallPrimes.any fun q =>
    decide (q < n) && powMod (q * n) (m - 1) m == 1 &&
      fs.all fun r => powMod (q * n) ((m - 1) / r) m != 1

theorem lucasB_sound {m n : ℕ} (h : lucasB m n = true) (hm : 2 ≤ m) :
    m.Prime ∧ ∃ q, q.Prime ∧ q < n ∧ orderOf ((q * n : ℕ) : ZMod m) = m - 1 := by
  simp only [lucasB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨q, hq, ⟨hqn, hferm⟩, hfs⟩ := h
  have hferm' : ((q * n : ℕ) : ZMod m) ^ (m - 1) = 1 := (zmod_pow_eq_one_iff hm _ _).mpr hferm
  have hdiv : ∀ r : ℕ, r.Prime → r ∣ m - 1 → ((q * n : ℕ) : ZMod m) ^ ((m - 1) / r) ≠ 1 := by
    intro r hr hrd
    rw [ne_eq, zmod_pow_eq_one_iff hm]
    apply hfs r
    rw [List.mem_dedup, Nat.mem_primeFactorsList (by omega)]
    exact ⟨hr, hrd⟩
  have hprime : m.Prime := lucas_primality m _ hferm' hdiv
  exact ⟨hprime, q, prime_of_mem_smallPrimes hq, hqn,
    orderOf_eq_of_pow_and_pow_div_prime hferm' hdiv⟩

/-- One step of the walk: `some (c', ok)` gives the new count and whether the step is fine. -/
def step (m c : ℕ) : Option ℕ :=
  if m < 2 then some c
  else if m % 2 = 0 then (if m = 2 then some (c + 1) else some c)
  else if powMod 2 (m - 1) m != 1 then some c
  else if decide (6 < c + 1) && lucasB m (c + 1) then some (c + 1)
  else if m.minFac = m then (if c + 1 ≤ 6 then some (c + 1) else none)
  else some c

/-- Walk through `[lo, lo + k)` carrying the prime count `c`; `none` on a failure. -/
def countFrom : ℕ → ℕ → ℕ → Option ℕ
  | _, 0, c => some c
  | lo, k + 1, c =>
    match step lo c with
    | some c' => countFrom (lo + 1) k c'
    | none => none

lemma primeCounting_of_prime {P : ℕ} (hP : P.Prime) :
    Nat.primeCounting P = Nat.count Nat.Prime P + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]; simp [hP]

lemma fermat_two {m : ℕ} (hp : m.Prime) (h2 : m ≠ 2) : powMod 2 (m - 1) m = 1 := by
  have hm3 : 3 ≤ m := by have := hp.two_le; omega
  have : Fact m.Prime := ⟨hp⟩
  rw [← zmod_pow_eq_one_iff (by omega)]
  apply ZMod.pow_card_sub_one_eq_one
  intro h0
  have h0' : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h0
  rw [ZMod.natCast_eq_zero_iff] at h0'
  have := Nat.le_of_dvd (by norm_num) h0'
  omega

theorem step_sound {m c c' : ℕ} (h : step m c = some c') (hc : c = Nat.count Nat.Prime m) :
    (c' = if m.Prime then c + 1 else c) ∧
      (m.Prime → 6 < c + 1 →
        ∃ q, q.Prime ∧ q < c + 1 ∧ orderOf ((q * (c + 1) : ℕ) : ZMod m) = m - 1) := by
  unfold step at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> simp only [Option.some.injEq] at h
  · have : ¬ m.Prime := fun hp => by have := hp.two_le; omega
    simp [this, ← h]
  · subst h3
    have hc0 : c = 0 := by rw [hc]; decide
    refine ⟨by simp [Nat.prime_two, ← h], fun _ h6 => by omega⟩
  · have : ¬ m.Prime := fun hp => by
      rcases hp.eq_two_or_odd with h' | h' <;> omega
    simp [this, ← h]
  · have : ¬ m.Prime := fun hp => by simp [fermat_two hp (by omega)] at h4
    simp [this, ← h]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h5
    obtain ⟨hp, hq⟩ := lucasB_sound h5.2 (by omega)
    exact ⟨by simp [hp, ← h], fun _ _ => hq⟩
  · have hp : m.Prime := Nat.prime_def_minFac.mpr ⟨by omega, h6⟩
    exact ⟨by simp [hp, ← h], fun _ h' => by omega⟩
  · have hp : ¬ m.Prime := fun hp => h6 (Nat.prime_def_minFac.mp hp).2
    simp [hp, ← h]

theorem countFrom_sound : ∀ (k lo c c' : ℕ), countFrom lo k c = some c' →
    c = Nat.count Nat.Prime lo →
    c' = Nat.count Nat.Prime (lo + k) ∧
      ∀ P, lo ≤ P → P < lo + k → P.Prime → 6 < Nat.primeCounting P → GoodPrime P
  | 0, lo, c, c', h, hc => by
    simp only [countFrom, Option.some.injEq] at h
    exact ⟨by rw [← h, hc]; rfl, fun P h1 h2 => by omega⟩
  | k + 1, lo, c, c', h, hc => by
    simp only [countFrom] at h
    rcases hs : step lo c with _ | c₁
    · rw [hs] at h; exact absurd h (by simp)
    rw [hs] at h
    obtain ⟨hc₁, hgood⟩ := step_sound hs hc
    have hc1 : c₁ = Nat.count Nat.Prime (lo + 1) := by
      rw [Nat.count_succ, ← hc, hc₁]; split_ifs <;> simp
    obtain ⟨ih1, ih2⟩ := countFrom_sound k (lo + 1) c₁ c' h hc1
    refine ⟨by rw [ih1]; ring_nf, fun P h1 h2 hP h6 => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · have hπ : Nat.primeCounting lo = c + 1 := by rw [primeCounting_of_prime hP, hc]
      obtain ⟨q, hq, hqn, hord⟩ := hgood hP (by omega)
      exact ⟨q, hq, hπ ▸ hqn, hπ ▸ hord⟩
    · exact ih2 P h1 (by omega) hP h6

end SunA243164.Compute
