import Robin.Compute.Log

/-!
# Soundness of the sieve and of the segment scans

A marked entry of `sieveSeg sp B h` is a multiple `j = q·t` of some `q ≥ 2` with `j ≥ q²`, so
`j` is not prime. Nothing else is needed: unmarked entries form a superset of the primes, and
every bound below is a sum of nonnegative terms over that superset.
-/

namespace Robin.Compute

open RobinCompute Real Finset

/-- No marked entry is a prime. -/
def SieveInv (arr : ByteArray) (base : ℕ) : Prop :=
  ∀ i, arr[i]! ≠ 0 → ¬ (base + i).Prime

lemma not_prime_of_dvd {q j : ℕ} (hq : 2 ≤ q) (hd : q ∣ j) (hj : q * q ≤ j) : ¬ j.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd q hd with h | h
  · omega
  · subst h; nlinarith

theorem markLoop_inv (q hi base : ℕ) (hq : 2 ≤ q) (j : ℕ) (arr : ByteArray)
    (hd : q ∣ j) (hjq : q * q ≤ j) (hb : base ≤ j) (hinv : SieveInv arr base) :
    SieveInv (markLoop arr j q hi base) base := by
  unfold markLoop
  split_ifs with hj h0
  · omega
  · apply markLoop_inv q hi base hq (j + q) _ (Nat.dvd_add hd dvd_rfl) (by omega) (by omega)
    intro i hi'
    by_cases hij : j - base = i
    · subst hij
      rw [show base + (j - base) = j by omega]
      exact not_prime_of_dvd hq hd hjq
    · rw [ByteArray.getElem!_set!_ne _ _ _ _ hij] at hi'
      exact hinv i hi'
  · exact hinv
termination_by hi - j

lemma dvd_max_mul (q a : ℕ) : q ∣ max (q * q) (a / q * q) := by
  rcases le_total (q * q) (a / q * q) with h | h
  · rw [max_eq_right h]; exact Dvd.intro_left _ rfl
  · rw [max_eq_left h]; exact Dvd.intro _ rfl

theorem sieveLoop_inv (sp : Array ℕ) (B hi : ℕ) (i : ℕ) (arr : ByteArray) (h : SieveInv arr B) :
    SieveInv (sieveLoop sp B hi i arr) B := by
  unfold sieveLoop
  by_cases hlt : i < sp.size
  · rw [if_pos hlt]
    dsimp only
    split_ifs with h1 h2
    · exact h
    · apply sieveLoop_inv sp B hi (i + 1)
      apply markLoop_inv _ hi B h2 _ _ (dvd_max_mul _ _) (le_max_left _ _) _ h
      apply le_trans _ (le_max_right _ _)
      have h3 := Nat.lt_div_mul_add (a := B + sp[i]! - 1) (b := sp[i]!) (by omega)
      omega
    · exact sieveLoop_inv sp B hi (i + 1) _ h
  · rw [if_neg hlt]; exact h
termination_by sp.size - i

lemma replicate_getElem! (h i : ℕ) : (ByteArray.mk (Array.replicate h (0 : UInt8)))[i]! = 0 := by
  have hs : (ByteArray.mk (Array.replicate h (0 : UInt8))).size = h := by
    show (Array.replicate h (0 : UInt8)).size = h; simp
  by_cases hi : i < h
  · rw [getElem!_pos (ByteArray.mk (Array.replicate h (0 : UInt8))) i (by rw [hs]; exact hi)]
    show (Array.replicate h (0 : UInt8))[i]'(by simpa using hi) = 0
    simp
  · rw [getElem!_neg (ByteArray.mk (Array.replicate h (0 : UInt8))) i (by rw [hs]; exact hi)]
    rfl

theorem sieveSeg_inv (sp : Array ℕ) (B h : ℕ) : SieveInv (sieveSeg sp B h) B := by
  unfold sieveSeg
  apply sieveLoop_inv
  intro i hi
  exact absurd (replicate_getElem! h i) hi

/-- The unmarked offsets below `n`. -/
def unmarked (arr : ByteArray) (n : ℕ) : Finset ℕ := (range n).filter (fun i => arr[i]! = 0)

lemma prime_mem_unmarked {arr : ByteArray} {B n i : ℕ} (hinv : SieveInv arr B) (hi : i < n)
    (hp : (B + i).Prime) : i ∈ unmarked arr n := by
  unfold unmarked
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨hi, ?_⟩
  by_contra h
  exact hinv i h hp

lemma unmarked_succ (arr : ByteArray) (n : ℕ) :
    unmarked arr (n + 1) = if arr[n]! = 0 then insert n (unmarked arr n) else unmarked arr n := by
  unfold unmarked
  rw [Finset.range_add_one, Finset.filter_insert]

lemma not_mem_unmarked_self (arr : ByteArray) (n : ℕ) : n ∉ unmarked arr n := by
  simp [unmarked]

theorem scanExact_eq (arr : ByteArray) (B : ℕ) :
    ∀ n, scanExact arr B n = (∑ i ∈ unmarked arr n, logUpS (B + i) 1,
      ∑ i ∈ unmarked arr n, logLoNatC (B + i))
  | 0 => by simp [scanExact, unmarked]
  | n + 1 => by
    rw [scanExact, unmarked_succ, scanExact_eq arr B n]
    by_cases h : arr[n]! = 0
    · simp [h, Finset.sum_insert (not_mem_unmarked_self arr n), add_comm]
    · simp [h]

theorem scanMomTR_eq (arr : ByteArray) (n i c s1 s2 : ℕ) (hin : i ≤ n) :
    scanMomTR arr i n c s1 s2 =
      (c + ((unmarked arr n).filter (i ≤ ·)).card,
       s1 + ∑ j ∈ (unmarked arr n).filter (i ≤ ·), j,
       s2 + ∑ j ∈ (unmarked arr n).filter (i ≤ ·), j * j) := by
  unfold scanMomTR
  split_ifs with hlt h
  · have hsplit : (unmarked arr n).filter (i ≤ ·) =
        insert i ((unmarked arr n).filter (i + 1 ≤ ·)) := by
      have h' : arr[i]! = 0 := by simpa using h
      ext j
      simp only [unmarked, Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
      constructor
      · rintro ⟨⟨hj, hj0⟩, hij⟩
        rcases eq_or_lt_of_le hij with e | e
        · left; exact e.symm
        · right; exact ⟨⟨hj, hj0⟩, e⟩
      · rintro (e | ⟨⟨hj, hj0⟩, hij⟩)
        · subst e; exact ⟨⟨hlt, h'⟩, le_rfl⟩
        · exact ⟨⟨hj, hj0⟩, by omega⟩
    have hnot : i ∉ (unmarked arr n).filter (i + 1 ≤ ·) := by simp
    rw [scanMomTR_eq arr n (i + 1) _ _ _ (by omega), hsplit,
      Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot, Finset.sum_insert hnot]
    simp only [Prod.mk.injEq]; omega
  · have hsplit : (unmarked arr n).filter (i ≤ ·) = (unmarked arr n).filter (i + 1 ≤ ·) := by
      have h' : arr[i]! ≠ 0 := by simpa using h
      ext j
      simp only [unmarked, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hj, hj0⟩, hij⟩
        refine ⟨⟨hj, hj0⟩, ?_⟩
        rcases eq_or_lt_of_le hij with e | e
        · subst e; exact absurd hj0 h'
        · exact e
      · rintro ⟨⟨hj, hj0⟩, hij⟩; exact ⟨⟨hj, hj0⟩, by omega⟩
    rw [scanMomTR_eq arr n (i + 1) _ _ _ (by omega), hsplit]
  · have : i = n := by omega
    subst this
    have : (unmarked arr i).filter (i ≤ ·) = ∅ := by
      ext j; simp [unmarked]; omega
    simp [this]
termination_by n - i

lemma filter_zero_le (s : Finset ℕ) : s.filter (0 ≤ ·) = s := by
  ext j; simp

theorem scanMom_eq (arr : ByteArray) (n : ℕ) :
    scanMomTR arr 0 n 0 0 0 = ((unmarked arr n).card, ∑ j ∈ unmarked arr n, j,
      ∑ j ∈ unmarked arr n, j * j) := by
  rw [scanMomTR_eq arr n 0 0 0 0 (Nat.zero_le _), filter_zero_le]
  simp

end Robin.Compute
