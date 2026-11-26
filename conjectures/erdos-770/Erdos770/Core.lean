import Erdos770.Basic
import Ankeny.Statement

/-!
# The bad prime and the two bounds on it

Suppose `gcd(2ⁿ - 1, …, Mⁿ - 1) ≠ 1` with `M ≥ P n`. Then:

* `exists_bad_prime`: some prime `r > M`, `r ≤ 2ⁿ - 1`, divides `iⁿ - 1` for all `2 ≤ i ≤ M`;
* `lt_of_bach`: Bach's bound, applied to the proper subgroup `H = {x : xⁿ = 1}` of `(ZMod r)ˣ`
  (it contains `1, …, M`), gives `M < c log² r`;
* `choose_le_of_bad`: if `K ≤ M` and `K^j < r`, the products of `j` distinct primes `≤ K` are
  distinct residues in `H`, and `|H| ≤ n`, so `(π K).choose j ≤ n`.
-/

open Finset

namespace Erdos770

theorem exists_bad_prime {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (hg : gcdUpTo n M ≠ 1) :
    ∃ r, r.Prime ∧ M < r ∧ r ≤ 2 ^ n - 1 ∧ ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1 := by
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hg
  have hdvd := dvd_gcdUpTo_iff.1 hrd
  refine ⟨r, hr, ?_, ?_, hdvd⟩
  · by_contra hle
    push Not at hle
    have h1 := hdvd r hr.two_le hle
    have h2 : r ∣ r ^ n := dvd_pow_self r (by omega)
    have h3 := Nat.dvd_sub h2 h1
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hr.pos)] at h3
    exact hr.one_lt.ne' (Nat.dvd_one.1 h3)
  · have h1 := hdvd 2 le_rfl hM
    have : 0 < 2 ^ n - 1 := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    exact Nat.le_of_dvd this h1

/-- Bach's bound forces `M < c log² r`. -/
theorem lt_of_bach {c : ℝ} (hB : Ankeny.BachSubgroupBound c) {n M r : ℕ} (hn : 1 ≤ n)
    (hr : r.Prime) (hMr : M < r) (hPM : P n ≤ M)
    (hdvd : ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1) :
    (M : ℝ) < c * Real.log r ^ 2 := by
  have := Fact.mk hr
  have : NeZero r := ⟨hr.ne_zero⟩
  let H : Subgroup (ZMod r)ˣ := (powMonoidHom n : (ZMod r)ˣ →* (ZMod r)ˣ).ker
  have hmem : ∀ x : (ZMod r)ˣ, x ∈ H ↔ x ^ n = 1 := fun x => by
    simp [H, MonoidHom.mem_ker]
  have hH : H ≠ ⊤ := by
    intro htop
    have hall : ∀ x : (ZMod r)ˣ, x ^ n = 1 := fun x => (hmem x).1 (htop ▸ Subgroup.mem_top x)
    have hexp : Monoid.exponent (ZMod r)ˣ ∣ n := Monoid.exponent_dvd_of_forall_pow_eq_one hall
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units] at hexp
    have := le_P hn hr hexp
    omega
  obtain ⟨a, haH, hav⟩ := hB r H hH
  refine lt_of_lt_of_le ?_ hav
  by_contra hle
  push Not at hle
  have hle' : (a : ZMod r).val ≤ M := by exact_mod_cast hle
  have hv0 : (a : ZMod r).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero]
    exact a.ne_zero
  apply haH
  rw [hmem]
  ext
  push_cast
  rw [← ZMod.natCast_zmod_val (a : ZMod r)]
  rcases Nat.lt_or_ge (a : ZMod r).val 2 with h | h
  · have : (a : ZMod r).val = 1 := by omega
    rw [this]
    simp
  · exact (dvd_pow_sub_one_iff (by omega)).1 (hdvd _ h hle')

/-- The counting bound: `(π K).choose j ≤ n` when `K ≤ M` and `K ^ j < r`. -/
theorem choose_le_of_bad {n M r : ℕ} (hn : 1 ≤ n) (hr : r.Prime)
    (hdvd : ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1) (K j : ℕ) (hKM : K ≤ M) (hKj : K ^ j < r) :
    (Nat.primeCounting K).choose j ≤ n := by
  classical
  have := Fact.mk hr
  rw [← Nat.primesLE_card_eq_primeCounting, ← Finset.card_powersetCard]
  set A := (Nat.primesLE K).powersetCard j
  let f : Finset ℕ → ZMod r := fun T => ((∏ p ∈ T, p : ℕ) : ZMod r)
  have hprime : ∀ T ∈ A, ∀ p ∈ T, p.Prime ∧ p ≤ K := fun T hT p hp => by
    rw [Finset.mem_powersetCard] at hT
    exact (Nat.mem_primesLE.1 (hT.1 hp)).symm
  have hlt : ∀ T ∈ A, ∏ p ∈ T, p < r := fun T hT => by
    have hc := (Finset.mem_powersetCard.1 hT).2
    calc ∏ p ∈ T, p ≤ K ^ T.card := Finset.prod_le_pow_card T id K fun p hp => (hprime T hT p hp).2
      _ = K ^ j := by rw [hc]
      _ < r := hKj
  have hmaps : ∀ T ∈ A, f T ∈ (Polynomial.nthRoots n (1 : ZMod r)).toFinset := fun T hT => by
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
    simp only [f, Nat.cast_prod]
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro p hp
    obtain ⟨hpp, hpK⟩ := hprime T hT p hp
    exact (dvd_pow_sub_one_iff hpp.one_lt.le).1 (hdvd p hpp.two_le (hpK.trans hKM))
  have hinj : Set.InjOn f A := fun T hT T' hT' hTT' => by
    have h1 := (ZMod.natCast_eq_natCast_iff' _ _ r).1 hTT'
    rw [Nat.mod_eq_of_lt (hlt T hT), Nat.mod_eq_of_lt (hlt T' hT')] at h1
    have := congrArg Nat.primeFactors h1
    rwa [Nat.primeFactors_prod fun p hp => (hprime T hT p hp).1,
      Nat.primeFactors_prod fun p hp => (hprime T' hT' p hp).1] at this
  calc A.card ≤ (Polynomial.nthRoots n (1 : ZMod r)).toFinset.card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ Multiset.card (Polynomial.nthRoots n (1 : ZMod r)) := Multiset.toFinset_card_le _
    _ ≤ n := Polynomial.card_nthRoots n 1

end Erdos770
