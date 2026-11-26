import LLS.Numerics.Budget
import Ankeny.Character

/-!
# Shared facts for LLS Theorem 1.1

* `LLS.Thm11.llp_eq_zero_of_le`, `lcp_eq_zero_of_le`: the prime-power losses at a prime `p ≥ x`
  vanish (for `p = x` the only prime power is `p` itself, with weight `0`).
* `LLS.Thm11.exists_char_of_primes_mem`: if every prime `ℓ ≤ x` prime to `q` lies in a proper
  subgroup `H`, some character `χ ≠ 1` is `1` on every `n ≤ x` prime to `q`.
-/

namespace LLS.Thm11

open Finset ArithmeticFunction

lemma ppF_self {p : ℕ} (hp : p.Prime) : ppF p p = {p} := by
  ext n
  simp only [ppF, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hn, hpp, hmin⟩
    obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    have hrp : r = p := by rw [← hmin, Nat.Prime.pow_minFac hr hk.ne']
    subst hrp
    have hle : r ^ k ≤ r := Nat.lt_succ_iff.1 hn
    have hk1 : k = 1 := by
      by_contra h
      have : r ^ 2 ≤ r ^ k := Nat.pow_le_pow_right hr.pos (by omega)
      have : r < r ^ 2 := by nlinarith [hr.two_le]
      omega
    simp [hk1]
  · rintro rfl
    exact ⟨Nat.lt_succ_self _, hp.isPrimePow, hp.minFac_eq⟩

theorem llp_eq_zero_of_le {x p : ℕ} (hp : p.Prime) (hxp : x ≤ p) : llp x p = 0 := by
  rcases lt_or_eq_of_le hxp with h | rfl
  · exact llp_eq_zero hp h
  · simp [llp, ppF_self hp]

theorem lcp_eq_zero_of_le {x p : ℕ} (hp : p.Prime) (hxp : x ≤ p) : lcp x p = 0 := by
  rcases lt_or_eq_of_le hxp with h | rfl
  · exact lcp_eq_zero hp h
  · have : (x : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    simp [lcp, ppF_self hp, this]

lemma unitOfCoprime_mul {q a b : ℕ} (ha : a.Coprime q) (hb : b.Coprime q) :
    ZMod.unitOfCoprime (a * b) (Nat.Coprime.mul_left ha hb)
      = ZMod.unitOfCoprime a ha * ZMod.unitOfCoprime b hb := by
  ext; simp [ZMod.coe_unitOfCoprime]

/-- Every `n ≤ x` prime to `q` lies in `H` once every prime `ℓ ≤ x` prime to `q` does. -/
lemma unitOfCoprime_mem {q : ℕ} (H : Subgroup (ZMod q)ˣ) (x : ℕ)
    (hprime : ∀ ℓ ≤ x, ℓ.Prime → ∀ hc : ℓ.Coprime q, ZMod.unitOfCoprime ℓ hc ∈ H) :
    ∀ n ≤ x, ∀ hc : n.Coprime q, ZMod.unitOfCoprime n hc ∈ H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnx hc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · have hq : q = 1 := by simpa using hc
        subst hq
        have : ZMod.unitOfCoprime 0 hc = 1 := Subsingleton.elim _ _
        rw [this]; exact H.one_mem
      · have : ZMod.unitOfCoprime 1 hc = 1 := by ext; simp [ZMod.coe_unitOfCoprime]
        rw [this]; exact H.one_mem
    · set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpn : p ∣ n := Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := hpn
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; omega
        · exact h
      have hmn : m < n := by
        rw [hm]; have := hp.two_le; nlinarith
      have hpc : p.Coprime q := Nat.Coprime.coprime_dvd_left ⟨m, hm⟩ hc
      have hmc : m.Coprime q := Nat.Coprime.coprime_dvd_left ⟨p, by rw [hm, mul_comm]⟩ hc
      have hpx : p ≤ x := le_trans (Nat.minFac_le (by omega)) hnx
      have e : ZMod.unitOfCoprime n hc = ZMod.unitOfCoprime p hpc * ZMod.unitOfCoprime m hmc := by
        rw [← unitOfCoprime_mul]; ext; simp [ZMod.coe_unitOfCoprime, ← hm]
      rw [e]
      exact H.mul_mem (hprime p hpx hp hpc) (ih m hmn (by omega) hmc)

/-- A non-trivial character equal to `1` on every `n ≤ x` prime to `q`, when every prime
`ℓ ≤ x` prime to `q` lies in the proper subgroup `H`. -/
theorem exists_char_of_primes_mem {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (x : ℕ) (hprime : ∀ ℓ ≤ x, ℓ.Prime → ∀ hc : ℓ.Coprime q, ZMod.unitOfCoprime ℓ hc ∈ H) :
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧ ∀ n ≤ x, n.Coprime q → χ n = 1 := by
  obtain ⟨χ, hχ, hχH⟩ := Ankeny.exists_dirichletCharacter_trivial_on H hH
  refine ⟨χ, hχ, fun n hn hc => ?_⟩
  have := hχH _ (unitOfCoprime_mem H x hprime n hn hc)
  simpa [ZMod.coe_unitOfCoprime] using this

end LLS.Thm11
