import Mathlib

/-!
# A computable checker for prime primitive roots, with a soundness proof
-/

namespace Erdos985.Compute

/-- `powModAux m b e acc = acc * b ^ e % m`, by binary exponentiation. -/
def powModAux (m : ℕ) (b e acc : ℕ) : ℕ :=
  if e = 0 then acc % m
  else powModAux m (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)
termination_by e
decreasing_by omega

/-- Modular exponentiation `b ^ e % m`. -/
def powMod (b e m : ℕ) : ℕ := powModAux m (b % m) e 1

theorem powModAux_eq (m b e acc : ℕ) : powModAux m b e acc = acc * b ^ e % m := by
  induction e using Nat.strong_induction_on generalizing b acc with
  | _ e ih =>
    rw [powModAux]
    split_ifs with h0 h1
    · simp [h0]
    · rw [ih (e / 2) (by omega), ← ZMod.natCast_eq_natCast_iff']
      push_cast [ZMod.natCast_mod]
      conv_rhs => rw [← Nat.div_add_mod e 2, h1]
      ring
    · rw [ih (e / 2) (by omega), ← ZMod.natCast_eq_natCast_iff']
      push_cast [ZMod.natCast_mod]
      have h2 : e % 2 = 0 := by omega
      conv_rhs => rw [← Nat.div_add_mod e 2, h2]
      ring

theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := by
  rw [powMod, powModAux_eq, one_mul, ← Nat.pow_mod]

/-- Small primes used as candidate primitive roots. -/
def smallPrimes : List ℕ := (List.range 2000).filter (fun q => Nat.Prime q)

theorem prime_of_mem_smallPrimes {q : ℕ} (h : q ∈ smallPrimes) : q.Prime := by
  simp only [smallPrimes, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

/-- Is there a small prime `q < n` with `q ^ ((n - 1) / r) ≢ 1 (mod n)` for every prime
`r ∣ n - 1`?  For prime `n` this certifies that `q` is a primitive root (the condition
`q ^ (n - 1) ≡ 1` is Fermat's little theorem, so it is not rechecked). -/
def hasPrimRoot (n : ℕ) : Bool :=
  let fs := (n - 1).primeFactorsList.dedup
  smallPrimes.any fun q =>
    decide (q < n) && fs.all fun r => powMod q ((n - 1) / r) n != 1

/-- Per-`n` check: `n` is even, or `< 3`, or fails the base-2 Fermat test, or has a
small prime primitive root, or is visibly composite.  Soundness (`okN_sound`) only
concerns prime `n`, so the cheap disjuncts that are false for odd primes may
short-circuit composite `n`. -/
def okN (n : ℕ) : Bool :=
  decide (n < 3) || n % 2 == 0 || powMod 2 (n - 1) n != 1 || hasPrimRoot n || n.minFac != n

/-- `checkFrom lo k` checks `okN n` for all `n ∈ [lo, lo + k)`. -/
def checkFrom : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, k + 1 => okN lo && checkFrom (lo + 1) k

/-- Check all `n < N`. -/
def checkAll (N : ℕ) : Bool := checkFrom 0 N

theorem checkFrom_sound : ∀ (k lo : ℕ), checkFrom lo k = true →
    ∀ n, lo ≤ n → n < lo + k → okN n = true
  | 0, lo, _, n, h1, h2 => by omega
  | k + 1, lo, h, n, h1, h2 => by
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact checkFrom_sound k (lo + 1) h.2 n h1 (by omega)

theorem zmod_pow_eq_one_iff {n : ℕ} (hn : 2 ≤ n) (q e : ℕ) :
    (q : ZMod n) ^ e = 1 ↔ powMod q e n = 1 := by
  rw [powMod_eq, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, Nat.ModEq,
    Nat.one_mod_eq_one.mpr (by omega)]

theorem okN_sound {n : ℕ} (hok : okN n = true) (hp : n.Prime) (h2 : n ≠ 2) :
    ∃ q, q.Prime ∧ q < n ∧ orderOf (q : ZMod n) = n - 1 := by
  have hn3 : 3 ≤ n := by have := hp.two_le; omega
  have hodd : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
  have : Fact n.Prime := ⟨hp⟩
  have hn2 : 2 ≤ n := by omega
  simp only [okN, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  have fermat : ∀ q, 0 < q → q < n → powMod q (n - 1) n = 1 := by
    intro q hq0 hqn
    rw [← zmod_pow_eq_one_iff hn2]
    apply ZMod.pow_card_sub_one_eq_one
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd hq0 h0
    omega
  rcases hok with (((h | h) | h) | h) | h
  · omega
  · omega
  · exact absurd (fermat 2 (by norm_num) (by omega)) h
  · simp only [hasPrimRoot, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨q, hq, hqn, hfs⟩ := h
    have hqp := prime_of_mem_smallPrimes hq
    refine ⟨q, hqp, hqn, ?_⟩
    apply orderOf_eq_of_pow_and_pow_div_prime
    · exact (zmod_pow_eq_one_iff hn2 _ _).mpr (fermat q hqp.pos hqn)
    · intro r hr hrd
      rw [ne_eq, zmod_pow_eq_one_iff hn2]
      apply hfs r
      rw [List.mem_dedup, Nat.mem_primeFactorsList (by omega)]
      exact ⟨hr, hrd⟩
  · exact absurd ((Nat.prime_def_minFac.mp hp).2) h

theorem checkAll_sound {N : ℕ} (h : checkAll N = true) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : p < N) : ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 :=
  okN_sound (checkFrom_sound N 0 h p (Nat.zero_le _) (by omega)) hp hp2

theorem checkFrom_add : ∀ (a lo b : ℕ),
    checkFrom lo (a + b) = (checkFrom lo a && checkFrom (lo + a) b)
  | 0, lo, b => by simp [checkFrom]
  | a + 1, lo, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega, checkFrom, checkFrom, checkFrom_add a (lo + 1) b,
      Bool.and_assoc, show lo + 1 + a = lo + (a + 1) by omega]

end Erdos985.Compute
