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
  have hdivEq : 2 * (a ^ 2 / 2) = a ^ 2 := Nat.mul_div_cancel' hdiv
  have hfirstLower : a ^ 2 / 2 ≤ (squareGapIndex n).nth Nat.Prime := by
    have := hnextLower.trans hpnext_le
    rw [← hdivEq] at this
    omega
  have hnlt : n ^ 2 < (2 * a) ^ 2 := Nat.pow_lt_pow_left hnhi (by decide)
  have hupperScale : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
  have hscale : 4 * a ^ 2 = 2 * (2 * a ^ 2) := by ring
  have hlastUpper : (squareGapIndex n).nth Nat.Prime < 2 * (2 * a ^ 2) := by
    rw [hupperScale] at hnlt
    calc
      (squareGapIndex n).nth Nat.Prime < 4 * a ^ 2 := lt_trans hgap.2.1 hnlt
      _ = 2 * (2 * a ^ 2) := hscale
  have hlong : 2 * a ≤ primeGap (squareGapIndex n) := by
    have h := hgap.2.2
    dsimp [squareGapIndex] at h ⊢
    omega
  by_cases hfirst : (squareGapIndex n).nth Nat.Prime < a ^ 2
  · have hfirst' : (squareGapIndex n).nth Nat.Prime < 2 * (a ^ 2 / 2) := by
      calc
        (squareGapIndex n).nth Nat.Prime < a ^ 2 := hfirst
        _ = 2 * (a ^ 2 / 2) := hdivEq.symm
    have hmem := mem_block_of_nth_prime_bounds hfirstLower hfirst'
    have hlongmem : squareGapIndex n ∈ longGapBlock (a ^ 2 / 2) (2 * a) := by
      simp [longGapBlock, hmem, hlong]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hlongmem)))
  · have hsecondLower : a ^ 2 ≤ (squareGapIndex n).nth Nat.Prime := le_of_not_gt hfirst
    by_cases hsecond : (squareGapIndex n).nth Nat.Prime < 2 * a ^ 2
    · have hmem := mem_block_of_nth_prime_bounds hsecondLower hsecond
      have hlongmem : squareGapIndex n ∈ longGapBlock (a ^ 2) (2 * a) := by
        simp [longGapBlock, hmem, hlong]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hlongmem)))
    · have hthirdLower : 2 * a ^ 2 ≤ (squareGapIndex n).nth Nat.Prime := le_of_not_gt hsecond
      have hmem := mem_block_of_nth_prime_bounds hthirdLower hlastUpper
      have hlongmem : squareGapIndex n ∈ longGapBlock (2 * a ^ 2) (2 * a) := by
        simp [longGapBlock, hmem, hlong]
      exact Finset.mem_union.mpr (Or.inr hlongmem)

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

open Filter

/-- Under RH there are eventually at most a constant times `log a ^ 2`
Legendre failures with index in `[a, 2a)` at even scales. -/
theorem eventually_legendreBadBlock_le_log_sq_of_RH (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ a : ℕ in atTop,
      2 ∣ a → ((legendreBadBlock a).card : ℝ) ≤ K * Real.log (a : ℝ) ^ 2 := by
  obtain ⟨C, X₀, hC, hgap⟩ := large_gaps_of_RH hRH
  let A : ℝ := 256 * 36 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmallReal := (Real.isLittleO_pow_log_id_atTop (n := 2)).def
    (show 0 < 2 / A by positivity)
  have hsmall : ∀ᶠ a : ℕ in atTop, A * Real.log (a : ℝ) ^ 2 ≤ 2 * (a : ℝ) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmallReal] with a ha
    have hh : Real.log (a : ℝ) ^ 2 ≤ (2 / A) * (a : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (a : ℝ))),
        abs_of_nonneg (show (0 : ℝ) ≤ (a : ℝ) from Nat.cast_nonneg a)] using ha
    calc
      _ ≤ A * ((2 / A) * (a : ℝ)) := mul_le_mul_of_nonneg_left hh hA.le
      _ = _ := by field_simp
  refine ⟨27 * C / 2, by positivity, ?_⟩
  filter_upwards [hsmall, Filter.eventually_ge_atTop (2 : ℕ),
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop X₀)] with
    a haSmall ha hXa
  intro hEven
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have haPos : (0 : ℝ) < a := by linarith
  have haLog : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by linarith)
  have haSq : a * 2 ≤ a ^ 2 := by nlinarith [Nat.mul_sub_left_distrib a a 2]
  have haHalf : a ≤ a ^ 2 / 2 := (Nat.le_div_iff_mul_le (by decide)).mpr haSq
  have hblock (x : ℕ) (hax : a ≤ x) (hxUpper : x ≤ 2 * a ^ 2) :
      ∑ k ∈ longGapBlock x (2 * a), (primeGap k : ℝ) ≤
        9 * C * a * Real.log (a : ℝ) ^ 2 := by
    have haxR : (a : ℝ) ≤ x := by exact_mod_cast hax
    have hxUpperR : (x : ℝ) ≤ 2 * (a : ℝ) ^ 2 := by exact_mod_cast hxUpper
    have hxPos : (0 : ℝ) < x := haPos.trans_le haxR
    have hxLog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by linarith)
    have haPow4 : (16 : ℝ) ≤ (a : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) haR 4
      norm_num at hh ⊢
      exact hh
    have hscale : 5 * (x : ℝ) ≤ (a : ℝ) ^ 6 := by
      calc
        _ ≤ 10 * (a : ℝ) ^ 2 := by linarith
        _ ≤ (a : ℝ) ^ 4 * (a : ℝ) ^ 2 := by gcongr; linarith
        _ = _ := by ring
    have hlogUpper : Real.log (5 * (x : ℝ)) ≤ 6 * Real.log (a : ℝ) := by
      simpa [Real.log_pow] using Real.log_le_log (by positivity : 0 < 5 * (x : ℝ)) hscale
    have hxLog5 : 0 ≤ Real.log (5 * (x : ℝ)) := Real.log_nonneg (by linarith)
    have hthr : 256 * (Real.log (5 * (x : ℝ)) ^ 2 / Real.log 2) ≤ 2 * (a : ℝ) := by
      calc
        _ ≤ 256 * ((6 * Real.log (a : ℝ)) ^ 2 / Real.log 2) := by gcongr
        _ = A * Real.log (a : ℝ) ^ 2 := by dsimp [A]; ring
        _ ≤ _ := haSmall
    have hh := hgap x (hXa.trans haxR) (2 * (a : ℝ)) hthr (by linarith)
    have hFilter : ((block x).filter (fun k => 2 * (a : ℝ) ≤ (primeGap k : ℝ))) =
        longGapBlock x (2 * a) := by
      classical
      ext k
      simp only [longGapBlock, Finset.mem_filter]
      exact_mod_cast Iff.rfl
    rw [hFilter] at hh
    have hlog : Real.log (x : ℝ) ≤ 3 * Real.log (a : ℝ) := by
      have hpow : (x : ℝ) ≤ (a : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr haR) (sq_nonneg (a : ℝ))]
      simpa [Real.log_pow] using Real.log_le_log hxPos hpow
    calc
      _ ≤ C * (x : ℝ) * Real.log (x : ℝ) ^ 2 / (2 * (a : ℝ)) := hh
      _ ≤ C * (2 * (a : ℝ) ^ 2) * (3 * Real.log (a : ℝ)) ^ 2 / (2 * (a : ℝ)) := by
        gcongr
      _ = _ := by field_simp; ring
  classical
  have hunion (s t : Finset ℕ) : (∑ k ∈ s ∪ t, (primeGap k : ℝ)) ≤
      (∑ k ∈ s, (primeGap k : ℝ)) + ∑ k ∈ t, (primeGap k : ℝ) := by
    have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := fun k => (primeGap k : ℝ))
    have hnonneg : 0 ≤ ∑ k ∈ s ∩ t, (primeGap k : ℝ) := by positivity
    linarith
  have hlen := legendreBadBlock_length_le_gapSum a ha
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (legendreBadGapIndices_subset_three_blocks a ha hEven)
      (f := fun k => (primeGap k : ℝ)) (by intros; positivity)
  let B := longGapBlock (a ^ 2 / 2) (2 * a)
  let D := longGapBlock (a ^ 2) (2 * a)
  let E := longGapBlock (2 * a ^ 2) (2 * a)
  have hsum := hunion (B ∪ D) E
  have hsum' := hunion B D
  have hB : (∑ k ∈ B, (primeGap k : ℝ)) ≤ 9 * C * a * Real.log (a : ℝ) ^ 2 :=
    hblock _ haHalf (by have := Nat.div_le_self (a ^ 2) 2; omega)
  have hD : (∑ k ∈ D, (primeGap k : ℝ)) ≤ 9 * C * a * Real.log (a : ℝ) ^ 2 :=
    hblock _ (by omega) (by omega)
  have hE : (∑ k ∈ E, (primeGap k : ℝ)) ≤ 9 * C * a * Real.log (a : ℝ) ^ 2 :=
    hblock _ (by omega) le_rfl
  change (∑ k ∈ legendreBadGapIndices a, (primeGap k : ℝ)) ≤
    ∑ k ∈ B ∪ D ∪ E, (primeGap k : ℝ) at hsub
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 2 * (a : ℝ) by positivity)).mp
  calc
    _ ≤ 27 * C * a * Real.log (a : ℝ) ^ 2 := by linarith
    _ = _ := by ring

#print axioms legendreBadGapIndices_subset_three_blocks
#print axioms legendreBadBlock_length_le_gapSum
#print axioms eventually_legendreBadBlock_le_log_sq_of_RH

end Erdos233
