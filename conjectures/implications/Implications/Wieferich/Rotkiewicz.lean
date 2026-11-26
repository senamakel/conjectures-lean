import Mathlib

/-!
# Squarefree Mersenne numbers and non-Wieferich primes (Rotkiewicz 1965)

Source of the statements: google-deepmind/formal-conjectures, commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`.

* `IsWieferichPrimeBase`, its `Decidable` instance and `IsWieferichPrime` are copied word for
  word from `FormalConjecturesForMathlib/NumberTheory/WieferichPrime.lean`.
* `sq_dvd_mersenne_iff_isWieferichPrime` and
  `rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne` are copied word for word from
  `FormalConjectures/Wikipedia/Mersenne.lean` (namespace `Mersenne`), where both are `sorry`.

The definitions live in the namespace `Implications.Wieferich` so that the copies do not clash
with copies of the same definitions in other modules of this package.

Deduction (Rotkiewicz, *Mat. Vesnik* 2 (17) (1965), 78–80): if `p` is a Wieferich prime and
`p ∣ 2 ^ n - 1`, then `p ^ 2 ∣ 2 ^ n - 1` (`sq_dvd_two_pow_sub_one_of_isWieferichPrime`). So a
squarefree `2 ^ n - 1` has only non-Wieferich prime factors; if these were finitely many, every
squarefree `2 ^ n - 1` would divide their product, and only finitely many `n` would remain.
-/

namespace Implications.Wieferich

/-! ### Copied verbatim from `FormalConjecturesForMathlib/NumberTheory/WieferichPrime.lean` -/

/--
**Wieferich prime to base `a`**
A prime $p$ is a Wieferich prime to base $a$ if $p^2 \mid a^{p-1} - 1$, i.e. if
$a^{p-1} \equiv 1 \pmod{p^2}$.

The subtraction is truncated, so, as with `Nat.ProbablePrime`, every prime is a Wieferich prime to
base $0$. For `a ≠ 0` the definition agrees with the congruence, see
`isWieferichPrimeBase_iff_pow_modEq`.
-/
@[mk_iff]
structure IsWieferichPrimeBase (a p : ℕ) : Prop where
  prime : p.Prime
  sq_dvd_pow_sub_one : p ^ 2 ∣ a ^ (p - 1) - 1

instance (a p : ℕ) : Decidable (IsWieferichPrimeBase a p) :=
  decidable_of_iff _ (isWieferichPrimeBase_iff a p).symm

/--
**Wieferich prime**
A Wieferich prime is a prime $p$ with $2^{p-1} \equiv 1 \pmod{p^2}$, i.e. a Wieferich prime to
base $2$.
-/
abbrev IsWieferichPrime (p : ℕ) : Prop := IsWieferichPrimeBase 2 p

/-! ### Auxiliary lemmas -/

/-- `p ^ k ∣ 2 ^ n - 1` in `ℕ` iff `2 ^ n = 1` in `ZMod (p ^ k)`. -/
lemma dvd_two_pow_sub_one_iff (m n : ℕ) : m ∣ 2 ^ n - 1 ↔ (2 : ZMod m) ^ n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff_dvd, Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero]
  push_cast
  rfl

/-- For an odd prime `p` (here: any prime not dividing `2`), the multiplicative order of `2`
in `ZMod p` divides `p - 1`. -/
lemma two_pow_sub_one_eq_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    (2 : ZMod p) ^ (p - 1) = 1 := by
  haveI := Fact.mk hp
  apply ZMod.pow_card_sub_one_eq_one
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff_dvd] at this
  exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

/-- For `n > 0`, a number dividing `2 ^ n - 1` is not `2`. -/
lemma ne_two_of_dvd {p n : ℕ} (hn : 0 < n) (hdvd : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    (Nat.even_pow.2 ⟨even_two, hn.ne'⟩) odd_one
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

/-- **Lifting for Wieferich primes.** If `p` is a Wieferich prime and `p ∣ 2 ^ n - 1`, then
`p ^ 2 ∣ 2 ^ n - 1`. In `ZMod (p ^ 2)`, `(2 ^ n) ^ p = 1` because `2 ^ n ≡ 1 [MOD p]`, and
`2 ^ (p - 1) = 1` by the Wieferich condition; the order of `2` divides `p - 1`, so it is prime
to `p` and divides `n`. -/
theorem sq_dvd_two_pow_sub_one_of_isWieferichPrime {p n : ℕ} (hW : IsWieferichPrime p)
    (hdvd : p ∣ 2 ^ n - 1) : p ^ 2 ∣ 2 ^ n - 1 := by
  have hp := hW.prime
  rw [dvd_two_pow_sub_one_iff]
  have hW' : (2 : ZMod (p ^ 2)) ^ (p - 1) = 1 :=
    (dvd_two_pow_sub_one_iff _ _).1 hW.sq_dvd_pow_sub_one
  -- `(2 ^ n) ^ p = 1` in `ZMod (p ^ 2)`.
  have hnp : (2 : ZMod (p ^ 2)) ^ (n * p) = 1 := by
    have h1 : ((p : ℤ)) ∣ (2 : ℤ) ^ n - 1 := by
      have := Int.natCast_dvd_natCast.2 hdvd
      rwa [Nat.cast_sub Nat.one_le_two_pow] at this
      |> fun h => by simpa using h
    have h2 := dvd_sub_pow_of_dvd_sub (R := ℤ) (p := p) (a := 2 ^ n) (b := 1) h1 1
    simp only [pow_one, one_pow] at h2
    have h3 : (((p ^ 2 : ℕ) : ℤ)) ∣ (2 : ℤ) ^ (n * p) - 1 := by
      rw [pow_mul]; push_cast; exact h2
    have h4 : ((2 ^ (n * p) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (n * p) - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; rfl
    rw [← h4, Int.natCast_dvd_natCast] at h3
    exact (dvd_two_pow_sub_one_iff _ _).1 h3
  have ho1 : orderOf (2 : ZMod (p ^ 2)) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hW'
  have ho2 : orderOf (2 : ZMod (p ^ 2)) ∣ n * p := orderOf_dvd_of_pow_eq_one hnp
  have hcop : Nat.Coprime (orderOf (2 : ZMod (p ^ 2))) p := by
    have : Nat.Coprime (p - 1) p := by
      have h := hp.one_lt
      rw [Nat.coprime_comm, Nat.Coprime, ← Nat.gcd_sub_self_right (by omega : 1 ≤ p)]
      · simp
    exact Nat.Coprime.coprime_dvd_left ho1 this
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right ho2)

/-! ### Target statements (copied verbatim from `FormalConjectures/Wikipedia/Mersenne.lean`) -/

/--
For primes $q$ and $p$ with $p \mid M_q$, the square $p^2$ divides $M_q = 2^q - 1$ precisely when
`IsWieferichPrime p` holds. The unsolved-problems source states the forward direction from
$p^2 \mid M_q$ to `IsWieferichPrime p`; the converse under $p \mid M_q$ is added here.
-/
theorem sq_dvd_mersenne_iff_isWieferichPrime
    {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hdvd : p ∣ mersenne q) :
    p ^ 2 ∣ mersenne q ↔ IsWieferichPrime p := by
  unfold mersenne at hdvd ⊢
  constructor
  · intro hsq
    have h2 : p ≠ 2 := ne_two_of_dvd hq.pos hdvd
    -- the order of `2` mod `p` is `q`, so `q ∣ p - 1`
    have hqp : q ∣ p - 1 := by
      have hpq : (2 : ZMod p) ^ q = 1 := (dvd_two_pow_sub_one_iff _ _).1 hdvd
      have hord : orderOf (2 : ZMod p) = q := by
        rcases (Nat.dvd_prime hq).1 (orderOf_dvd_of_pow_eq_one hpq) with h | h
        · exfalso
          rw [orderOf_eq_one_iff] at h
          have : p ∣ 2 ^ 1 - 1 := (dvd_two_pow_sub_one_iff _ _).2 (by rw [pow_one, h])
          exact hp.one_lt.ne' (Nat.dvd_one.1 (by simpa using this))
        · exact h
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one (two_pow_sub_one_eq_one hp h2)
    refine ⟨hp, ?_⟩
    rw [dvd_two_pow_sub_one_iff] at hsq ⊢
    obtain ⟨k, hk⟩ := hqp
    rw [hk, pow_mul, hsq, one_pow]
  · intro hW
    exact sq_dvd_two_pow_sub_one_of_isWieferichPrime hW hdvd

/--
Rotkiewicz's theorem (1965): if infinitely many values $M_n = 2^n - 1$ are squarefree, then
infinitely many primes fail `IsWieferichPrime`. Allowing $n$ to range over all natural numbers
rather than only primes gives the stronger form of this implication.
-/
theorem rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne :
    {n : ℕ | Squarefree (mersenne n)}.Infinite →
      {p : ℕ | p.Prime ∧ ¬ IsWieferichPrime p}.Infinite := by
  intro hinf hfin
  set S := {p : ℕ | p.Prime ∧ ¬ IsWieferichPrime p}
  set P := ∏ p ∈ hfin.toFinset, p
  apply hinf
  apply (Set.finite_Iic P).subset
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  -- every prime factor of the squarefree `mersenne n` is non-Wieferich
  have hsub : (mersenne n).primeFactors ⊆ hfin.toFinset := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Set.Finite.mem_toFinset]
    refine ⟨hp.1, fun hW => ?_⟩
    have hsq := sq_dvd_two_pow_sub_one_of_isWieferichPrime hW hp.2.1
    rw [sq] at hsq
    exact hp.1.one_lt.ne' (Nat.isUnit_iff.1 (hn p hsq))
  have hdvd : mersenne n ∣ P := by
    rw [← Nat.prod_primeFactors_of_squarefree hn]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hP : 0 < P := Finset.prod_pos fun p hp =>
    ((Set.Finite.mem_toFinset _).1 hp).1.pos
  have hle := Nat.le_of_dvd hP hdvd
  have : n < 2 ^ n := Nat.lt_two_pow_self
  unfold mersenne at hle
  omega

end Implications.Wieferich
