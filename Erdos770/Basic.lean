import Erdos770.Statement

/-!
# Elementary facts about `h` and `P`

* `P_mem`, `le_P`: for `n ≥ 1` the set `{m | m.Prime ∧ m - 1 ∣ n}` contains `2` and is bounded
  by `n + 1`, so `P n` is its largest element.
* `P_le_h`: `P n ≤ h n` (Fermat: `P n ∣ iⁿ - 1` for `2 ≤ i < P n`).
* `h_le_of_gcd`: `h n ≤ M` as soon as `gcd(2ⁿ - 1, …, Mⁿ - 1) = 1` and `M > 2`.
-/

open Finset

namespace Erdos770

lemma two_mem_P_set (n : ℕ) : 2 ∈ {m : ℕ | m.Prime ∧ m - 1 ∣ n} :=
  ⟨Nat.prime_two, by simp⟩

lemma P_set_bddAbove {n : ℕ} (hn : 1 ≤ n) : BddAbove {m : ℕ | m.Prime ∧ m - 1 ∣ n} :=
  ⟨n + 1, fun m hm => by have := Nat.le_of_dvd hn hm.2; omega⟩

lemma P_mem {n : ℕ} (hn : 1 ≤ n) : (P n).Prime ∧ P n - 1 ∣ n :=
  Nat.sSup_mem ⟨2, two_mem_P_set n⟩ (P_set_bddAbove hn)

lemma le_P {n m : ℕ} (hn : 1 ≤ n) (hm : m.Prime) (hd : m - 1 ∣ n) : m ≤ P n :=
  le_csSup (P_set_bddAbove hn) ⟨hm, hd⟩

/-- `r ∣ aⁿ - 1` (natural subtraction) is `aⁿ = 1` in `ZMod r`, for `a ≥ 1`. -/
lemma dvd_pow_sub_one_iff {r a n : ℕ} (ha : 1 ≤ a) :
    r ∣ a ^ n - 1 ↔ (a : ZMod r) ^ n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ ha)]
  push_cast
  exact sub_eq_zero

/-- The gcd in the definition of `h`. -/
abbrev gcdUpTo (n M : ℕ) : ℕ := ((Finset.Icc 2 M).image fun i => (i ^ n - 1)).gcd id

lemma dvd_gcdUpTo_iff {d n M : ℕ} :
    d ∣ gcdUpTo n M ↔ ∀ i, 2 ≤ i → i ≤ M → d ∣ i ^ n - 1 := by
  constructor
  · intro hd i hi hiM
    exact hd.trans (Finset.gcd_dvd (Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨hi, hiM⟩)))
  · intro hd
    apply Finset.dvd_gcd
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
    rw [Finset.mem_Icc] at hi
    exact hd i hi.1 hi.2

/-- `P n ≤ h n`: every `i` with `2 ≤ i < P n` has `P n ∣ iⁿ - 1`. -/
theorem P_le_h {n : ℕ} (hn : 1 ≤ n) : (P n : ℕ∞) ≤ h n := by
  unfold h
  refine le_sInf ?_
  rintro m ⟨-, hg⟩
  induction m using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    simp only [ENat.toNat_natCast] at hg
    rw [Nat.cast_le]
    by_contra hlt
    push Not at hlt
    obtain ⟨hp, hd⟩ := P_mem hn
    generalize P n = p at hp hd hlt ⊢
    have := Fact.mk hp
    have hdiv : p ∣ gcdUpTo n m := by
      rw [dvd_gcdUpTo_iff]
      intro i hi him
      rw [dvd_pow_sub_one_iff (by omega)]
      have hi0 : (i : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      obtain ⟨t, ht⟩ := hd
      rw [ht, pow_mul, ZMod.pow_card_sub_one_eq_one hi0, one_pow]
    rw [gcdUpTo, hg] at hdiv
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdiv)

/-- If `gcd(2ⁿ - 1, …, Mⁿ - 1) = 1` with `M > 2`, then `h n ≤ M`. -/
theorem h_le_of_gcd {n M : ℕ} (hM : 2 < M) (hg : gcdUpTo n M = 1) : h n ≤ M :=
  sInf_le ⟨by exact_mod_cast hM, by simpa using hg⟩

end Erdos770
