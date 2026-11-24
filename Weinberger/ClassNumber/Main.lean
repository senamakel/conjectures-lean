import Weinberger.Large
import Weinberger.ClassNumber.Checker
import Weinberger.ClassNumber.Compute.Chunk00
import Weinberger.ClassNumber.Compute.Chunk01
import Weinberger.ClassNumber.Compute.Chunk02
import Weinberger.ClassNumber.Compute.Chunk03
import Weinberger.ClassNumber.Compute.Chunk04
import Weinberger.ClassNumber.Compute.Chunk05
import Weinberger.ClassNumber.Compute.Chunk06
import Weinberger.ClassNumber.Compute.Chunk07
import Weinberger.ClassNumber.Compute.Chunk08
import Weinberger.ClassNumber.Compute.Chunk09

/-!
# Class number one under GRH, given the two cited inputs

For squarefree `d = −n < 0` of class number one:

* `n < 10^8`: the checker `okB` (10 `native_decide` chunks) leaves only the nine values;
* `n ≥ 10^8`: `n ≡ 0 (mod 4)` is not squarefree, `n ≡ 1, 2` is ruled out by the prime `2`
  (`false_of_two`), and for `n ≡ 3` GRH gives an odd prime `p ∤ n` with `p² < n` and `−n` a
  square mod `p` (`exists_split_prime_of_GRH`, the same step as for idoneal numbers); then
  `p ∣ t² + t + (n+1)/4` for some `t`, and `4p < n` contradicts `false_of_split3`.
-/

namespace Weinberger.ClassNumber

open ClassNumberProblem Erdos985

theorem checkB_ok : checkFromB 0 (10 ^ 8) = true := by
  rw [show 10 ^ 8 = 10 * 10000000 by norm_num]
  apply checkFromB_chunks
  intro i hi
  interval_cases i
  · exact chunkB_ok_0
  · exact chunkB_ok_1
  · exact chunkB_ok_2
  · exact chunkB_ok_3
  · exact chunkB_ok_4
  · exact chunkB_ok_5
  · exact chunkB_ok_6
  · exact chunkB_ok_7
  · exact chunkB_ok_8
  · exact chunkB_ok_9

/-- A square root of `−n` mod an odd prime `p` gives `t` with `p ∣ t² + t + (n+1)/4`. -/
theorem exists_t_of_isSquare {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h4 : n % 4 = 3)
    (hsq : IsSquare (-(n : ZMod p))) : ∃ t, p ∣ t * t + t + (n + 1) / 4 := by
  have := Fact.mk hp
  obtain ⟨r, hr⟩ := hsq
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  set s := r.val
  obtain ⟨s', hs'odd, hs'⟩ : ∃ s' : ℕ, s' % 2 = 1 ∧ (s' : ZMod p) = r := by
    by_cases hs : s % 2 = 1
    · exact ⟨s, hs, ZMod.natCast_zmod_val r⟩
    · refine ⟨s + p, by omega, ?_⟩
      push_cast; rw [ZMod.natCast_self, add_zero]; exact ZMod.natCast_zmod_val r
  refine ⟨s' / 2, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  have h4c : 4 * ((n + 1) / 4) = n + 1 := by omega
  have h2t : 2 * (s' / 2) + 1 = s' := by omega
  have key : (((s' / 2) * (s' / 2) + s' / 2 + (n + 1) / 4 : ℕ) : ZMod p) * 4 = 0 := by
    have e : ((s' / 2) * (s' / 2) + s' / 2 + (n + 1) / 4) * 4 = s' * s' + n := by
      have : s' * s' = (2 * (s' / 2) + 1) * (2 * (s' / 2) + 1) := by rw [h2t]
      rw [this]; nlinarith [h4c]
    have e' : (((s' / 2) * (s' / 2) + s' / 2 + (n + 1) / 4 : ℕ) : ZMod p) * ((4 : ℕ) : ZMod p)
        = ((s' * s' + n : ℕ) : ZMod p) := by rw [← Nat.cast_mul, e]
    have h4' : ((4 : ℕ) : ZMod p) = 4 := by norm_num
    rw [h4'] at e'
    rw [e']
    push_cast; rw [hs', ← hr]; ring
  have h40 : (4 : ZMod p) ≠ 0 := by
    intro h
    have : ((4 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using this))
    exact hp2 this
  exact (mul_eq_zero.1 key).resolve_right h40

/-- **Class number one under GRH**, given the two cited inputs. -/
theorem starkHeegner_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (hPS : ClassNumberOneNorms) (hH : HeegnerClassNumberOne) : StarkHeegnerStatement := by
  ext d
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hsf, hneg, hcn⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = -(n : ℤ) := ⟨d.natAbs, by omega⟩
    have hn0 : n ≠ 0 := by omega
    suffices hmem : n ∈ heegnerNat by
      simp only [heegnerNat, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    by_cases hlt : n < 10 ^ 8
    · exact okB_sound hPS (checkFromB_sound _ 0 checkB_ok n (Nat.zero_le _) (by omega)) hn0 hsf hcn
    exfalso
    have hn : 10 ^ 8 ≤ n := not_lt.mp hlt
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h4 | h4 | h4 | h4
    · exact not_squarefree_of_four_dvd h4 hsf
    · exact false_of_two hPS (by omega) (Or.inl h4) hsf hcn
    · exact false_of_two hPS (by omega) (Or.inr h4) hsf hcn
    · obtain ⟨p, hp, hp2, -, hpp, hsq⟩ := exists_split_prime_of_GRH hGRH hn
      obtain ⟨t, ht⟩ := exists_t_of_isSquare hp hp2 h4 hsq
      have hpn : 4 * p < n := by nlinarith
      exact false_of_split3 hPS h4 hsf hcn hp hpn t ht
  · intro h
    have hmem : d ∈ ([-1, -2, -3, -7, -11, -19, -43, -67, -163] : List ℤ) := by
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    refine ⟨?_, ?_, hH d hmem⟩
    · rw [← Int.squarefree_natAbs]
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact squarefree_one
      all_goals exact (Nat.prime_iff.mp (by norm_num)).squarefree
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end Weinberger.ClassNumber
