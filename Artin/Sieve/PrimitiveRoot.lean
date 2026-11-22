import Artin.Interfaces

/-!
# The primitive-root criterion and the inclusion–exclusion identity

Unconditional, elementary input to the sieve half (`docs/BLUEPRINT.md`, part B).

* `Artin.orderOf_eq_sub_one_iff`: for a prime `p ∤ a`, `a` is a primitive root mod `p` iff
  `a^((p-1)/q) ≠ 1` for every prime `q ∣ p - 1`.
* `Artin.sum_moebius_kummerCount`: for any finite set `Q` of primes,
  `Σ_{k ∣ ∏ Q} μ(k) · kummerCount a k x` counts the primes `p < x`, `p ∤ a`, for which no
  `q ∈ Q` has `q ∣ p - 1` and `a^((p-1)/q) = 1`.
* `Artin.primRootCount_eq_sum_moebius`: when `Q` contains every prime `< x`, that sum is
  exactly `primRootCount a x`, the number of primes `p < x` with `a` a primitive root mod `p`.
* `Artin.primRootCount_le_sum_moebius`, `Artin.sum_moebius_sub_le_primRootCount`: the truncated
  version, sifting only by the primes `q ≤ ξ`.
-/

namespace Artin

open ArtinPrimitiveRootsConjecture Finset
open scoped ArithmeticFunction.Moebius

/-- The number of primes `p < x` for which `a` is a primitive root mod `p`, that is the number of
elements of `S a` below `x`. Primes dividing `a` are never counted, since then `a = 0` in
`ZMod p` and `orderOf 0 = 0 ≠ p - 1`. -/
noncomputable def primRootCount (a : ℤ) (x : ℕ) : ℕ :=
  ((range x).filter fun p : ℕ => p.Prime ∧ orderOf (a : ZMod p) = p - 1).card

/-- The number of primes `p < x`, `p ∤ a`, such that no `q ∈ Q` has `q ∣ p - 1` and
`a^((p-1)/q) = 1` in `ZMod p`: the primes surviving the sieve by the set `Q`. -/
noncomputable def siftedCount (a : ℤ) (Q : Finset ℕ) (x : ℕ) : ℕ :=
  ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
    ∀ q ∈ Q, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)).card

lemma intCast_zmod_ne_zero {p : ℕ} {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : (a : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma pow_sub_one_eq_one {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    (a : ZMod p) ^ (p - 1) = 1 := by
  have := Fact.mk hp
  exact ZMod.pow_card_sub_one_eq_one (intCast_zmod_ne_zero ha)

/-- **Primitive-root criterion.** For a prime `p ∤ a`, `a` has order `p - 1` mod `p` iff
`a^((p-1)/q) ≠ 1` for every prime `q ∣ p - 1`. -/
theorem orderOf_eq_sub_one_iff {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    orderOf (a : ZMod p) = p - 1 ↔
      ∀ q : ℕ, q.Prime → q ∣ p - 1 → (a : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
  constructor
  · intro h q hq hqd heq
    have hdvd := orderOf_dvd_of_pow_eq_one heq
    rw [h] at hdvd
    have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have h1 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hpos hqd) hq.pos) hdvd
    have h2 := Nat.div_lt_self hpos hq.one_lt
    omega
  · intro h
    exact orderOf_eq_of_pow_and_pow_div_prime (pow_sub_one_eq_one hp ha) h

lemma orderOf_dvd_sub_one {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    orderOf (a : ZMod p) ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one (pow_sub_one_eq_one hp ha)

lemma orderOf_pos' {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    0 < orderOf (a : ZMod p) := by
  rcases Nat.eq_zero_or_pos (orderOf (a : ZMod p)) with h | h
  · have := orderOf_dvd_sub_one hp ha
    rw [h, zero_dvd_iff] at this
    have := hp.one_lt
    omega
  · exact h

/-- For a prime `p ∤ a`, the Kummer condition `k ∣ p - 1 ∧ a^((p-1)/k) = 1` says exactly that
`k` divides the index `(p - 1) / orderOf a` of `⟨a⟩` in `(ZMod p)ˣ`. -/
theorem kummer_cond_iff {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (k : ℕ) :
    (k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1) ↔
      k ∣ (p - 1) / orderOf (a : ZMod p) := by
  set d := orderOf (a : ZMod p) with hd
  have hdpos : 0 < d := orderOf_pos' hp ha
  obtain ⟨m, hm⟩ := orderOf_dvd_sub_one hp ha
  rw [← hd] at hm
  have hm' : (p - 1) / d = m := by rw [hm, Nat.mul_div_cancel_left _ hdpos]
  rw [hm', hm]
  constructor
  · rintro ⟨⟨j, hj⟩, hpow⟩
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        have h1 := hp.one_lt
        have : d * m ≠ 0 := by omega
        simp at hj; exact absurd hj (by simpa using this)
      · exact h
    rw [hj, Nat.mul_div_cancel_left _ hk0] at hpow
    obtain ⟨i, hi⟩ := orderOf_dvd_of_pow_eq_one hpow
    rw [← hd] at hi
    refine ⟨i, ?_⟩
    have : d * m = d * (k * i) := by rw [hj, hi]; ring
    exact Nat.eq_of_mul_eq_mul_left hdpos this
  · intro hk
    refine ⟨Dvd.dvd.mul_left hk d, ?_⟩
    rw [Nat.mul_div_assoc d hk, pow_mul, hd, pow_orderOf_eq_one, one_pow]

/-- `Σ_{d ∣ n} μ(d) = [n = 1]`. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

/-- **Inclusion–exclusion.** For a finite set `Q` of primes, the Möbius-weighted sum of Kummer
counts over the divisors of `∏ Q` is the number of primes `p < x`, `p ∤ a`, that no `q ∈ Q`
sifts out. -/
theorem sum_moebius_kummerCount (a : ℤ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (x : ℕ) :
    ∑ k ∈ (∏ q ∈ Q, q).divisors, (μ k : ℤ) * kummerCount a k x = siftedCount a Q x := by
  classical
  set P := ∏ q ∈ Q, q with hPdef
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hQ q hq).ne_zero
  set A := (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a with hA
  set m : ℕ → ℕ := fun p => (p - 1) / orderOf (a : ZMod p) with hm
  -- each Kummer count as a sum over `A`
  have hK : ∀ k, (kummerCount a k x : ℤ) = ∑ p ∈ A, if k ∣ m p then (1 : ℤ) else 0 := by
    intro k
    rw [kummerCount, Finset.card_filter, hA, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.Prime ∧ ¬ (p : ℤ) ∣ a
    · have := kummer_cond_iff h.1 h.2 k
      simp only [h, not_false_eq_true, true_and, ite_true]
      by_cases h' : k ∣ m p
      · simp [h', this.mpr h']
      · have h3 : ¬ (k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1) := fun h'' => h' (this.mp h'')
        simp only [h', h3, ite_false]
    · have h2 : ¬ (p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1) :=
        fun h'' => h ⟨h''.1, h''.2.1⟩
      simp only [h, h2, ite_false]
  -- the inner Möbius sum
  have hinner : ∀ p, (∑ k ∈ P.divisors, (μ k : ℤ) * if k ∣ m p then (1 : ℤ) else 0) =
      if Nat.gcd P (m p) = 1 then 1 else 0 := by
    intro p
    rw [← sum_moebius_divisors]
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have : Nat.gcd P (m p) ≠ 0 := Nat.gcd_ne_zero_left hP
    tauto
  have hcop : ∀ p ∈ A, (Nat.gcd P (m p) = 1 ↔
      ∀ q ∈ Q, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)) := by
    intro p hpA
    rw [hA, Finset.mem_filter] at hpA
    rw [← Nat.Coprime, hPdef, Nat.coprime_prod_left_iff]
    refine forall₂_congr fun q hq => ?_
    rw [Nat.Prime.coprime_iff_not_dvd (hQ q hq), kummer_cond_iff hpA.2.1 hpA.2.2]
  calc ∑ k ∈ P.divisors, (μ k : ℤ) * kummerCount a k x
      = ∑ k ∈ P.divisors, ∑ p ∈ A, (μ k : ℤ) * if k ∣ m p then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hK, Finset.mul_sum]
    _ = ∑ p ∈ A, ∑ k ∈ P.divisors, (μ k : ℤ) * if k ∣ m p then (1 : ℤ) else 0 :=
        Finset.sum_comm
    _ = ∑ p ∈ A, if Nat.gcd P (m p) = 1 then (1 : ℤ) else 0 :=
        Finset.sum_congr rfl fun p _ => hinner p
    _ = ((A.filter fun p => Nat.gcd P (m p) = 1).card : ℤ) := by
        rw [Finset.card_filter]; push_cast; rfl
    _ = siftedCount a Q x := by
        rw [siftedCount]
        congr 2
        rw [hA, Finset.filter_filter]
        refine Finset.filter_congr fun p hp => ?_
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h2, (hcop p (by simp [hA, hp, h1, h2])).mp h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2⟩, (hcop p (by simp [hA, hp, h1, h2])).mpr h3⟩

/-- A prime `p` counted by `primRootCount` does not divide `a`. -/
lemma not_dvd_of_orderOf_eq {p : ℕ} (hp : p.Prime) {a : ℤ}
    (h : orderOf (a : ZMod p) = p - 1) : ¬ (p : ℤ) ∣ a := by
  intro hdvd
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
  rw [hdvd, orderOf_eq_zero_iff'.mpr] at h
  · have := hp.one_lt; omega
  · intro n hn h0
    have := Fact.mk hp
    rw [zero_pow hn.ne'] at h0
    exact zero_ne_one h0

/-- If `a` is a primitive root mod `p`, no prime `q` sifts `p` out. -/
lemma not_kummer_of_orderOf_eq {p : ℕ} (hp : p.Prime) {a : ℤ}
    (h : orderOf (a : ZMod p) = p - 1) (q : ℕ) (hq : q.Prime) :
    ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1) := fun hc =>
  (orderOf_eq_sub_one_iff hp (not_dvd_of_orderOf_eq hp h)).mp h q hq hc.1 hc.2

/-- **Inclusion–exclusion, exact form.** If `Q` is a finite set of primes containing every prime
below `x`, the number of primes `p < x` with `a` a primitive root mod `p` is
`Σ_{k ∣ ∏ Q} μ(k) · kummerCount a k x`. -/
theorem primRootCount_eq_sum_moebius (a : ℤ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (x : ℕ)
    (hQx : ∀ q : ℕ, q.Prime → q < x → q ∈ Q) :
    (primRootCount a x : ℤ) =
      ∑ k ∈ (∏ q ∈ Q, q).divisors, (μ k : ℤ) * kummerCount a k x := by
  rw [sum_moebius_kummerCount a Q hQ x, primRootCount, siftedCount]
  congr 2
  refine Finset.filter_congr fun p hp => ?_
  rw [Finset.mem_range] at hp
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, not_dvd_of_orderOf_eq h1 h2, fun q hq => not_kummer_of_orderOf_eq h1 h2 q (hQ q hq)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, (orderOf_eq_sub_one_iff h1 h2).mpr fun q hq hqd heq => h3 q ?_ ⟨hqd, heq⟩⟩
    refine hQx q hq ?_
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt h1.one_lt) hqd
    omega

/-- **Truncated sieve, upper bound.** Sifting only by the primes `q ≤ ξ`,
`N(x) ≤ Σ_{k ∣ ∏_{q ≤ ξ} q} μ(k) · kummerCount a k x`. -/
theorem primRootCount_le_sum_moebius (a : ℤ) (ξ x : ℕ) :
    (primRootCount a x : ℤ) ≤
      ∑ k ∈ (∏ q ∈ Nat.primesLE ξ, q).divisors, (μ k : ℤ) * kummerCount a k x := by
  rw [sum_moebius_kummerCount a _ (fun q hq => (Nat.mem_primesLE.mp hq).2) x]
  exact_mod_cast Finset.card_le_card fun p hp => by
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, not_dvd_of_orderOf_eq hp.2.1 hp.2.2, fun q hq =>
      not_kummer_of_orderOf_eq hp.2.1 hp.2.2 q (Nat.mem_primesLE.mp hq).2⟩

/-- **Truncated sieve, lower bound.** Sifting only by the primes `q ≤ ξ` overcounts by at most
the primes `p < x` sifted out by some prime `ξ < q < x`:
`N(x) ≥ Σ_{k ∣ ∏_{q ≤ ξ} q} μ(k) · kummerCount a k x − Σ_{ξ < q < x} kummerCount a q x`. -/
theorem sum_moebius_sub_le_primRootCount (a : ℤ) (ξ x : ℕ) :
    ∑ k ∈ (∏ q ∈ Nat.primesLE ξ, q).divisors, (μ k : ℤ) * kummerCount a k x -
        ∑ q ∈ (range x).filter (fun q => q.Prime ∧ ξ < q), (kummerCount a q x : ℤ) ≤
      primRootCount a x := by
  classical
  rw [sub_le_iff_le_add, sum_moebius_kummerCount a _ (fun q hq => (Nat.mem_primesLE.mp hq).2) x]
  have key : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∀ q ∈ Nat.primesLE ξ, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)) ⊆
      ((range x).filter fun p : ℕ => p.Prime ∧ orderOf (a : ZMod p) = p - 1) ∪
        ((range x).filter (fun q => q.Prime ∧ ξ < q)).biUnion fun q =>
          (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ q ∣ p - 1 ∧
            (a : ZMod p) ^ ((p - 1) / q) = 1 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hp, hpa, hsift⟩ := hp
    by_cases hord : orderOf (a : ZMod p) = p - 1
    · exact Finset.mem_union_left _ (by simp [hpx, hp, hord])
    · refine Finset.mem_union_right _ ?_
      have := mt (orderOf_eq_sub_one_iff hp hpa).mpr hord
      push Not at this
      obtain ⟨q, hq, hqd, heq⟩ := this
      have hqp := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hqd
      have hξq : ξ < q := by
        by_contra hle
        exact hsift q (Nat.mem_primesLE.mpr ⟨by omega, hq⟩) ⟨hqd, heq⟩
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
      exact ⟨q, ⟨by omega, hq, hξq⟩, hpx, hp, hpa, hqd, heq⟩
  have := (Finset.card_le_card key).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  rw [siftedCount, primRootCount]
  simp only [kummerCount]
  exact_mod_cast this

end Artin
