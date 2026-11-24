import LLSCheck
import LLS.Bach2.Budget
import LLS.Numerics.Interval
import LLS.Analytic.Mertens

/-!
# Soundness of the checker, part 1: logarithms, primes, the Cesàro sum

The executable bounds of `LLSCheck` against their real counterparts: `logLo n m ≤ log n ≤
logHi n m`, `isPrimeB p ↔ p.Prime`, `lamLo n ≤ Λ(n)` and `cesLo x ≤ cesSum x`.
-/

namespace LLS.Check

open Real Finset ArithmeticFunction

lemma cast_lg2lo : ((lg2lo : ℚ) : ℝ) = 0.6931471803 := by norm_num [lg2lo]
lemma cast_lg2hi : ((lg2hi : ℚ) : ℝ) = 0.6931471808 := by norm_num [lg2hi]

theorem logLo_le (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : ((logLo n m : ℚ) : ℝ) ≤ Real.log n := by
  have hpow : 2 ^ Nat.log2 (n ^ m) ≤ n ^ m := by
    rw [Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 (by positivity)
  have := LLS.log_ge_of_pow n (Nat.log2 (n ^ m)) m (by omega) hpow
  have e : ((logLo n m : ℚ) : ℝ) = (Nat.log2 (n ^ m) : ℝ) / m * 0.6931471803 := by
    simp only [logLo]; push_cast; rw [cast_lg2lo]
  rw [e]; exact this

theorem le_logHi (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : Real.log n ≤ ((logHi n m : ℚ) : ℝ) := by
  have hpow : n ^ m ≤ 2 ^ (Nat.log2 (n ^ m) + 1) := by
    rw [Nat.log2_eq_log_two]; exact (Nat.lt_pow_succ_log_self (by norm_num) _).le
  have := LLS.log_le_of_pow n (Nat.log2 (n ^ m) + 1) m (by omega) (by omega) hpow
  have e : ((logHi n m : ℚ) : ℝ) = ((Nat.log2 (n ^ m) + 1 : ℕ) : ℝ) / m * 0.6931471808 := by
    simp only [logHi]; push_cast; rw [cast_lg2hi]
  rw [e]; exact this

lemma logLo_nonneg (n m : ℕ) : 0 ≤ logLo n m := by
  unfold logLo lg2lo; positivity

theorem isPrimeB_iff (p : ℕ) : isPrimeB p = true ↔ p.Prime := by
  rw [Nat.prime_def_lt']
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun d hd hdp hdvd => h d ⟨hd, by omega⟩ (Nat.mod_eq_zero_of_dvd hdvd)⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun d hd hmod => h d hd.1 (by omega) (Nat.dvd_of_mod_eq_zero hmod)⟩

lemma mem_primesL {p : ℕ} : p ∈ primesL ↔ p < NP ∧ p.Prime := by
  simp [primesL, isPrimeB_iff]

lemma primesL_nodup : primesL.Nodup := (List.nodup_range).filter _

lemma tab_eq : tab = primesL.map mkPE := rfl

lemma mem_tab {e : PE} (he : e ∈ tab) : ∃ p, p < NP ∧ p.Prime ∧ e = mkPE p := by
  rw [tab_eq, List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  exact ⟨p, (mem_primesL.1 hp).1, (mem_primesL.1 hp).2, rfl⟩

lemma mkPE_lo_le {p : ℕ} (hp : p.Prime) : (((mkPE p).lo : ℚ) : ℝ) ≤ Real.log p :=
  logLo_le p MP hp.one_lt.le (by norm_num [MP])

lemma le_mkPE_hi {p : ℕ} (hp : p.Prime) : Real.log p ≤ (((mkPE p).hi : ℚ) : ℝ) :=
  le_logHi p MP hp.one_lt.le (by norm_num [MP])

lemma isPowOf_sound (p : ℕ) : ∀ fuel n, isPowOf p fuel n = true → ∃ k, n = p ^ (k + 1)
  | 0, n, h => by simp [isPowOf] at h
  | fuel + 1, n, h => by
    simp only [isPowOf, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨hmod, -⟩, h⟩
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨k, hk⟩ := isPowOf_sound p fuel (n / p) h
      refine ⟨k + 1, ?_⟩
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      rw [← this, hk]; ring

theorem lamLo_le (n : ℕ) : ((lamLo n : ℚ) : ℝ) ≤ Λ n := by
  unfold lamLo
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    obtain ⟨p, -, hp, rfl⟩ := mem_tab hmem
    split_ifs with hpow
    · obtain ⟨k, rfl⟩ := isPowOf_sound _ _ _ hpow
      have hp' : (mkPE p).p = p := rfl
      rw [vonMangoldt_apply_pow (by omega), hp', vonMangoldt_apply_prime hp]
      exact mkPE_lo_le hp
    · simp
  · simp

lemma list_map_range_sum {β : Type*} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem cesLo_le (x : ℕ) : ((cesLo x : ℚ) : ℝ) ≤ cesSum x := by
  unfold cesLo cesSum
  rw [list_map_range_sum, Rat.cast_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hnx : n ≤ x := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have hw := LLS.ces_weight_nonneg (x := x) hnx
  push_cast
  exact mul_le_mul_of_nonneg_right (lamLo_le n) hw

theorem log_sub_two_le_cesSum (x : ℕ) (hx : 2 ≤ x) : Real.log x - 2 ≤ cesSum x := by
  have hPc := LLS.vonMangoldt_ces_ge x hx
  refine hPc.trans (le_of_eq ?_)
  unfold cesSum
  rw [sum_range_succ, div_self (by positivity : (x : ℝ) ≠ 0)]
  simp only [sub_self, mul_zero, add_zero]
  refine sum_congr rfl fun n _ => by ring

end LLS.Check
