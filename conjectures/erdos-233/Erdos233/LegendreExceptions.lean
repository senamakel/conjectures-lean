import Erdos233.AlmostAll

/-!
# Exceptional square intervals and prime gaps

This file starts the quantitative Legendre consequence of the RH large-gap
bound. A prime-free square interval sits inside one consecutive-prime gap.
-/

namespace Erdos233

open Nat

/-- The integer points in the half-open square interval `[n^2, (n+1)^2)`. -/
def squareInterval (n : ℕ) : Finset ℕ := Finset.Ico (n ^ 2) ((n + 1) ^ 2)

/-- The Legendre failure predicate: no prime lies strictly between consecutive squares. -/
def legendreFailure (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (n ^ 2 < p ∧ p < (n + 1) ^ 2)

/-- Failed square intervals with left endpoint index in `[a, 2a)`. -/
noncomputable def legendreBadBlock (a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico a (2 * a)).filter legendreFailure

/-- The index of the prime gap containing the square interval's left endpoint. -/
def squareGapIndex (n : ℕ) : ℕ := idx (n ^ 2) - 1

/-- The integer points in the half-open interval spanning a consecutive-prime gap. -/
noncomputable def primeGapInterval (k : ℕ) : Finset ℕ :=
  Finset.Ico (k.nth Nat.Prime) ((k + 1).nth Nat.Prime)

/-- Indices of prime gaps containing failed square intervals in one dyadic block. -/
noncomputable def legendreBadGapIndices (a : ℕ) : Finset ℕ := by
  classical
  exact (legendreBadBlock a).image squareGapIndex

/-- Long prime gaps with left endpoint in one dyadic prime block. -/
noncomputable def longGapBlock (x h : ℕ) : Finset ℕ := by
  classical
  exact (block x).filter (fun k => h ≤ primeGap k)

lemma squareInterval_card (n : ℕ) : (squareInterval n).card = 2 * n + 1 := by
  simp [squareInterval]
  have h : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  omega

lemma squareInterval_disjoint {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (squareInterval m) (squareInterval n) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [squareInterval, Finset.mem_Ico] at hx₁ hx₂
  rcases lt_or_gt_of_ne hmn with h | h
  · have hs : (m + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt h) 2
    omega
  · have hs : (n + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt h) 2
    omega

/-- A failed square interval is contained in the gap between its surrounding primes. -/
lemma legendreFailure_gap {n : ℕ} (hn : 2 ≤ n) (hbad : legendreFailure n) :
    let k := idx (n ^ 2) - 1
    (n + 1) ^ 2 ≤ (k + 1).nth Nat.Prime ∧
      k.nth Nat.Prime < n ^ 2 ∧ 2 * n + 1 ≤ primeGap k := by
  let k := idx (n ^ 2) - 1
  have hsq_gt : 2 < n ^ 2 := by nlinarith
  have hkpos : idx (n ^ 2) ≠ 0 := by
    intro hz
    have hle : n ^ 2 ≤ 2 := by
      simpa [idx] using (Nat.primeCounting'_eq_zero_iff.mp hz)
    omega
  have hsucc : k + 1 = idx (n ^ 2) := by
    dsimp [k]
    omega
  have hprev : k < idx (n ^ 2) := by omega
  have hpk : k.nth Nat.Prime < n ^ 2 := nth_lt_of_lt_idx hprev
  have hnextle : n ^ 2 ≤ (k + 1).nth Nat.Prime := by
    rw [hsucc]
    exact le_nth_of_idx_le le_rfl
  have hsq_not_prime : ¬ (n ^ 2).Prime := by
    rw [pow_two]
    exact Nat.not_prime_mul (by omega) (by omega)
  have hnextgt : n ^ 2 < (k + 1).nth Nat.Prime := by
    have hp := Nat.prime_nth_prime (k + 1)
    have hneq : (k + 1).nth Nat.Prime ≠ n ^ 2 := by
      intro heq
      apply hsq_not_prime
      simpa [heq] using hp
    omega
  have hupper : (n + 1) ^ 2 ≤ (k + 1).nth Nat.Prime := by
    by_contra h
    have hlt : (k + 1).nth Nat.Prime < (n + 1) ^ 2 := by omega
    exact hbad ((k + 1).nth Nat.Prime) (Nat.prime_nth_prime _) ⟨hnextgt, hlt⟩
  have hpow : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  refine ⟨hupper, hpk, ?_⟩
  have hsum : n ^ 2 + (2 * n + 1) ≤ (k + 1).nth Nat.Prime := by
    rw [← hpow]
    exact hupper
  have hsum' : n ^ 2 + (2 * n + 1) ≤ (idx (n ^ 2)).nth Nat.Prime := by
    simpa [hsucc] using hsum
  have hpk' : (idx (n ^ 2) - 1).nth Nat.Prime < n ^ 2 := by
    simpa [k] using hpk
  unfold primeGap
  rw [hsucc]
  change 2 * n + 1 ≤ (idx (n ^ 2)).nth Nat.Prime - (idx (n ^ 2) - 1).nth Nat.Prime
  omega

lemma squareInterval_subset_gap {n k : ℕ}
    (hleft : k.nth Nat.Prime ≤ n ^ 2)
    (hright : (n + 1) ^ 2 ≤ (k + 1).nth Nat.Prime) :
    squareInterval n ⊆ Finset.Ico (k.nth Nat.Prime) ((k + 1).nth Nat.Prime) := by
  intro x hx
  simp only [squareInterval, Finset.mem_Ico] at hx ⊢
  exact ⟨hleft.trans hx.1, lt_of_lt_of_le hx.2 hright⟩

lemma legendreFailure_squareInterval_subset_gap {n : ℕ} (hn : 2 ≤ n)
    (hbad : legendreFailure n) :
    squareInterval n ⊆ primeGapInterval (squareGapIndex n) := by
  obtain ⟨hnext, hprev, _⟩ := legendreFailure_gap hn hbad
  simpa [primeGapInterval, squareGapIndex] using
    squareInterval_subset_gap (Nat.le_of_lt hprev) hnext

lemma mem_block_of_nth_prime_bounds {k x : ℕ}
    (hlo : x ≤ k.nth Nat.Prime) (hhi : k.nth Nat.Prime < 2 * x) : k ∈ block x := by
  simp only [block, Finset.mem_Ico]
  constructor
  · by_contra h
    have hk : k < idx x := by omega
    have hp : k.nth Nat.Prime < x := nth_lt_of_lt_idx hk
    omega
  · by_contra h
    have hk : idx (2 * x) ≤ k := by omega
    have hp : 2 * x ≤ k.nth Nat.Prime := le_nth_of_idx_le hk
    omega

/-- The gap indices of failed square intervals in `[a,2a)` lie in three consecutive
prime-index blocks, and all these gaps have length at least `2a`. The hypothesis that `a`
is even makes the first prime scale exactly `a^2 / 2`. -/
theorem legendreBadGapIndices_subset_three_blocks (a : ℕ) (ha : 2 ≤ a)
    (haEven : 2 ∣ a) :
    legendreBadGapIndices a ⊆
      longGapBlock (a ^ 2 / 2) (2 * a) ∪
        longGapBlock (a ^ 2) (2 * a) ∪ longGapBlock (2 * a ^ 2) (2 * a) := by
  classical
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
  have hnmem := (Finset.mem_filter.mp hn).1
  have hnlo : a ≤ n := (Finset.mem_Ico.mp hnmem).1
  have hnhi : n < 2 * a := (Finset.mem_Ico.mp hnmem).2
  have hbad := (Finset.mem_filter.mp hn).2
  have hgap := legendreFailure_gap (le_trans ha hnlo) hbad
  have hpnext_le : (squareGapIndex n + 1).nth Nat.Prime ≤
      2 * (squareGapIndex n).nth Nat.Prime := nth_succ_le_two_mul _
  have hn2 : a ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hnlo 2
  have hnn : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
  have hnextLower : a ^ 2 ≤ (squareGapIndex n + 1).nth Nat.Prime :=
    hn2.trans (hnn.trans hgap.1)
  have hdiv : 2 ∣ a ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left haEven a
  have hfirst : 2 * (a ^ 2 / 2) = a ^ 2 := Nat.mul_div_cancel' hdiv
  have hfirstLower : a ^ 2 / 2 ≤ (squareGapIndex n).nth Nat.Prime := by
    have := hnextLower.trans hpnext_le
    rw [← hfirst] at this
    omega
  have hnlt : n ^ 2 < (2 * a) ^ 2 := Nat.pow_lt_pow_left hnhi (by decide)
  have hupperScale : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  have hlastUpper : (squareGapIndex n).nth Nat.Prime < 2 * (2 * a ^ 2) := by
    rw [hupperScale] at hnlt
    exact lt_trans hgap.2.1 hnlt
  have hlong : 2 * a ≤ primeGap (squareGapIndex n) := by omega
  by_cases hfirst : (squareGapIndex n).nth Nat.Prime < a ^ 2
  · have hmem := mem_block_of_nth_prime_bounds hfirstLower hfirst
    simp only [longGapBlock, Finset.mem_filter, hmem, true_and]
    exact Or.inl hlong
  · have hsecondLower : a ^ 2 ≤ (squareGapIndex n).nth Nat.Prime := le_of_not_gt hfirst
    by_cases hsecond : (squareGapIndex n).nth Nat.Prime < 2 * a ^ 2
    · have hmem := mem_block_of_nth_prime_bounds hsecondLower hsecond
      simp only [longGapBlock, Finset.mem_filter, hmem, true_and]
      exact Or.inr (Or.inl hlong)
    · have hthirdLower : 2 * a ^ 2 ≤ (squareGapIndex n).nth Nat.Prime := le_of_not_gt hsecond
      have hmem := mem_block_of_nth_prime_bounds hthirdLower hlastUpper
      simp only [longGapBlock, Finset.mem_filter, hmem, true_and]
      exact Or.inr (Or.inr hlong)

/-- The total square-interval length in one block is bounded by the total length of
the prime gaps which contain those intervals. -/
theorem legendreBadBlock_length_le_gapSum (a : ℕ) (ha : 2 ≤ a) :
    ((legendreBadBlock a).card : ℝ) * (2 * a : ℝ) ≤
      ∑ k ∈ legendreBadGapIndices a, (primeGap k : ℝ) := by
  classical
  let B := legendreBadBlock a
  let G := legendreBadGapIndices a
  let S := B.biUnion squareInterval
  let T := G.biUnion primeGapInterval
  have hdis : (B : Set ℕ).PairwiseDisjoint squareInterval := by
    intro m hm n hn hmn
    exact squareInterval_disjoint hmn
  have hlower : (B.card : ℝ) * (2 * a : ℝ) ≤ (S.card : ℝ) := by
    have hcard : S.card = ∑ n ∈ B, (squareInterval n).card := Finset.card_biUnion hdis
    have hterms : ∀ n ∈ B, (2 * a : ℝ) ≤ (squareInterval n).card := by
      intro n hn
      rw [squareInterval_card]
      have hmem := (Finset.mem_filter.mp hn).1
      have hnlo : a ≤ n := (Finset.mem_Ico.mp hmem).1
      exact_mod_cast (show 2 * a ≤ 2 * n + 1 by omega)
    calc
      (B.card : ℝ) * (2 * a : ℝ) = ∑ n ∈ B, (2 * a : ℝ) := by simp
      _ ≤ ∑ n ∈ B, ((squareInterval n).card : ℝ) := Finset.sum_le_sum fun n hn => hterms n hn
      _ = (S.card : ℝ) := by exact_mod_cast hcard.symm
  have hsubset : S ⊆ T := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨n, hn, hx⟩
    have hnmem := (Finset.mem_filter.mp hn).1
    have hnlo : a ≤ n := (Finset.mem_Ico.mp hnmem).1
    have hbad := (Finset.mem_filter.mp hn).2
    have hinc : squareInterval n ⊆ primeGapInterval (squareGapIndex n) :=
      legendreFailure_squareInterval_subset_gap (le_trans ha hnlo) hbad
    have hk : squareGapIndex n ∈ G := by
      exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨squareGapIndex n, hk, hinc hx⟩
  have hupper : (S.card : ℝ) ≤ ∑ k ∈ G, (primeGap k : ℝ) := by
    have hcardT : T.card ≤ ∑ k ∈ G, (primeGapInterval k).card := Finset.card_biUnion_le
    calc
      (S.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
      _ ≤ ∑ k ∈ G, (primeGap k : ℝ) := by
        calc
          (T.card : ℝ) ≤ (∑ k ∈ G, (primeGapInterval k).card : ℕ) := by exact_mod_cast hcardT
          _ = ∑ k ∈ G, (primeGap k : ℝ) := by simp [primeGapInterval, primeGap]
  exact hlower.trans hupper

end Erdos233
