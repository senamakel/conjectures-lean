import LLS.Bach2.Core
import BachSharpCheck

/-!
# Soundness of the checker with a general constant

`BachSharp.Check.checkChunkC_sound`: `checkChunkC cn cd m w lo hi = true` implies `GoodC (cn/cd) q`
for every `lo ≤ q < hi`. The proof is lls-grh's `LLS.Check.checkChunk_sound`
(`LLS/Bach2/Sound.lean`) with the constant `2` replaced by `cn/cd`; every interval lemma is
reused from there. `bach_of_goodC` is `LLS.bach_of_good2` with the same replacement.
-/

namespace BachSharp

open Erdos985 (DirichletLNonvanishingRightOfHalf)
open LLS

/-- What the checker certifies for a modulus `q` and a constant `c` (lls-grh's `LLS.Good2`
with `2` replaced by `c`). -/
def GoodC (c : ℝ) (q : ℕ) : Prop :=
  ∃ x : ℕ, (x : ℝ) ≤ c * Real.log q ^ 2 ∧
    (Subgroup.closure (Ankeny.Checker.smallUnits q x) = ⊤ ∨
     (64 ≤ x ∧ ∃ Pc : ℝ, Pc ≤ cesSum x ∧
       (0 < base2 x Pc - kap x * Real.log q - costQ x q ∨
        (betP x 53 ≤ kap x ∧ 0 < base2 x Pc - kap x * Real.log q - costU x 53 (Real.log q)))))

/-- **From a certified modulus to the subgroup bound** (`LLS.bach_of_good2` with `c`). -/
theorem bach_of_goodC (hGRH : DirichletLNonvanishingRightOfHalf) {c : ℝ} (q : ℕ) [NeZero q]
    (hq : GoodC c q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ c * Real.log q ^ 2 := by
  obtain ⟨x, hxq, hgen | ⟨hx64, Pc, hPc, hpos⟩⟩ := hq
  · by_contra hcon
    push Not at hcon
    apply hH
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro u hu
    by_contra huH
    have h1 := hcon u huH
    have h2 : ((u : ZMod q).val : ℝ) ≤ x := by exact_mod_cast hu
    linarith
  · by_contra hcon
    push Not at hcon
    obtain ⟨χ, hχ, hχH⟩ := Ankeny.exists_dirichletCharacter_trivial_on H hH
    have hval : ∀ n ≤ x, n.Coprime q → χ n = 1 := by
      intro n hn hcop
      set u := ZMod.unitOfCoprime n hcop
      have hu : u ∈ H := by
        by_contra hu
        have h1 := hcon u hu
        have e : (u : ZMod q).val = n % q := by simp [u, ZMod.val_natCast]
        have : ((n % q : ℕ) : ℝ) ≤ x := by exact_mod_cast (Nat.mod_le n q).trans hn
        rw [e] at h1
        linarith
      simpa [u] using hχH u hu
    rcases hpos with hQ | ⟨hβκ, hU⟩
    · have := budgetQ_nonpos hGRH χ hχ x hx64 hval Pc hPc
      linarith
    · have := budgetU_nonpos hGRH χ hχ x hx64 hval Pc hPc 53 (by norm_num) hβκ
      linarith

end BachSharp

namespace BachSharp.Check

open Real Finset LLS LLS.Check

lemma mkBDC_ok (cn cd m a b : ℕ) : BDOK m a b (mkBDC cn cd m a b) where
  La := rfl
  Lb := rfl
  l1 := rfl
  l2 := rfl
  Pc := rfl
  s2 := by simp only [mkBDC]; positivity

/-- **Soundness of one block.** -/
theorem blockOKC_sound (cn cd m a b : ℕ) (hcd : 0 < cd) (hm : 1 ≤ m) (ha : 3 ≤ a)
    (h : blockOKC cn cd m a b = true) :
    ∀ q, a ≤ q → q < b → GoodC ((cn : ℝ) / cd) q := by
  intro q hqa hqb
  have hq3 : 3 ≤ q := le_trans ha hqa
  haveI : NeZero q := ⟨by omega⟩
  have hd := mkBDC_ok cn cd m a b
  unfold blockOKC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  generalize mkBDC cn cd m a b = d at h hd
  obtain ⟨⟨hLa0, hxLa⟩, hrest⟩ := h
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hLq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hLa : ((d.La : ℚ) : ℝ) ≤ Real.log q := by
    rw [hd.La]
    exact (logLo_le a m (by omega) hm).trans
      (Real.log_le_log (by exact_mod_cast (show 0 < a by omega)) (by exact_mod_cast hqa))
  have hLa0' : (0 : ℝ) ≤ ((d.La : ℚ) : ℝ) := by exact_mod_cast hLa0
  have hxq : (d.x : ℝ) ≤ (cn : ℝ) / cd * Real.log q ^ 2 := by
    have : (((d.x : ℚ)) : ℝ) ≤ (((cn : ℚ) * d.La * d.La / (cd : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hxLa
    push_cast at this
    have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
    have hc0 : (0 : ℝ) ≤ (cn : ℝ) / cd := by positivity
    have hsq : ((d.La : ℚ) : ℝ) * ((d.La : ℚ) : ℝ) ≤ Real.log q ^ 2 := by nlinarith
    calc (d.x : ℝ) ≤ (cn : ℝ) * ((d.La : ℚ) : ℝ) * ((d.La : ℚ) : ℝ) / cd := this
      _ = (cn : ℝ) / cd * (((d.La : ℚ) : ℝ) * ((d.La : ℚ) : ℝ)) := by ring
      _ ≤ (cn : ℝ) / cd * Real.log q ^ 2 := mul_le_mul_of_nonneg_left hsq hc0
  have hLbq : Real.log q ≤ ((d.Lb : ℚ) : ℝ) := by
    rw [hd.Lb]
    exact (Real.log_le_log (by positivity) (by exact_mod_cast hqb.le)).trans
      (le_logHi b m (by omega) hm)
  have hab : q < a + (b - a) := by omega
  split_ifs at hrest with hx64
  · have := allQ_sound _ _ _ hrest q hqa hab
    exact ⟨d.x, hxq, Or.inl (Ankeny.Checker.closure_eq_top_of_checkGen q d.x this)⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hrest
  obtain ⟨hside, hrest⟩ := hrest
  obtain ⟨hS, h64, hPc0, hPc, hLb0⟩ := side_of_sideOK hd hside
  obtain ⟨hK1, hK2, hk1, hk2, -, hK10, hk10⟩ := hS.core
  have hB : ((Bq d : ℚ) : ℝ) ≤ base2 d.x d.Pc - kap d.x * Real.log q := by
    unfold Bq
    push_cast
    rw [cast_baseLo, cast_k2]
    have := hS.base hPc0
    have := kap_log_le hS (by omega) hLbq
    linarith
  rcases hrest with hU | ⟨⟨hNP, hW⟩, hBn, hall⟩
  · -- uniform budget
    unfold unifOK at hU
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hU
    obtain ⟨⟨⟨hlP, hbk⟩, hpe⟩, hpos⟩ := hU
    have hlP' : (0 : ℝ) < ((logLo P0 MP : ℚ) : ℝ) := by exact_mod_cast hlP
    have hlo53 : ((logLo P0 MP : ℚ) : ℝ) ≤ Real.log (53 : ℕ) :=
      logLo_le 53 MP (by norm_num) (by norm_num [MP])
    have hhi53 : Real.log (53 : ℕ) ≤ ((logHi P0 MP : ℚ) : ℝ) :=
      le_logHi 53 MP (by norm_num) (by norm_num [MP])
    obtain ⟨hbl0, hblb, hbbh⟩ := hS.bet 53 (by norm_num) hlo53 hhi53 hlP'
    have e53 : ((P0 : ℚ) : ℝ) = ((53 : ℕ) : ℝ) := by norm_num [P0]
    have hbl : ((betLo (d.x : ℚ) d.s1 d.s2 d.l1 (logHi P0 MP) (P0 : ℚ) : ℚ) : ℝ)
        = betLoR d.x d.s1 d.s2 d.l1 (logHi P0 MP) (53 : ℕ) := by rw [cast_betLo, e53]
    have hbh : ((betHi (d.x : ℚ) d.s1 d.s2 d.l2 (logLo P0 MP) (P0 : ℚ) : ℚ) : ℝ)
        = betHiR d.x d.s1 d.s2 d.l2 (logLo P0 MP) (53 : ℕ) := by rw [cast_betHi, e53]
    have hbk' : betP d.x 53 ≤ kap d.x := by
      have : ((betHi (d.x : ℚ) d.s1 d.s2 d.l2 (logLo P0 MP) (P0 : ℚ) : ℚ) : ℝ)
          ≤ ((k1 (d.x : ℚ) d.s1 d.s2 d.l1 : ℚ) : ℝ) := by exact_mod_cast hbk
      rw [hbh, cast_k1] at this
      linarith
    refine ⟨d.x, hxq, Or.inr ⟨h64, d.Pc, hPc, Or.inr ⟨hbk', ?_⟩⟩⟩
    -- the small primes
    have hsum : ∑ p ∈ smallPN 53, max 0 (Wp d.x p - betP d.x 53 * Real.log p)
        ≤ ((((primesL.filter (· < P0)).map fun p =>
            pos (wOf d (mkPE p) - betLo (d.x : ℚ) d.s1 d.s2 d.l1 (logHi P0 MP) (P0 : ℚ)
              * (mkPE p).lo)).sum : ℚ) : ℝ) := by
      rw [cast_list_sum_map, list_sum_primes, smallPN_eq]
      refine Finset.sum_le_sum fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨hpNP, hp, hp53⟩ := hp
      have hpe' := hpe p (mem_primesL_filter hp hpNP hp53)
      have hWp := Wp_le_wOf (m := m) (a := a) (b := b) hS p hp hpe'
      rw [cast_pos]
      push_cast
      rw [hbl]
      refine max_le_max le_rfl ?_
      have hlo := mkPE_lo_le hp
      have hlo0 : (0 : ℝ) ≤ (((mkPE p).lo : ℚ) : ℝ) := by exact_mod_cast logLo_nonneg p MP
      have : betLoR d.x d.s1 d.s2 d.l1 (logHi P0 MP) (53 : ℕ) * (((mkPE p).lo : ℚ) : ℝ)
          ≤ betP d.x 53 * Real.log p := mul_le_mul hblb hlo hlo0 (le_trans hbl0 hblb)
      linarith
    have hbq : betP d.x 53 * Real.log q
        ≤ betHiR d.x d.s1 d.s2 d.l2 (logLo P0 MP) (53 : ℕ) * ((d.Lb : ℚ) : ℝ) :=
      mul_le_mul hbbh hLbq hLq0 (le_trans (le_trans hbl0 hblb) hbbh)
    have hpos' : (0 : ℝ) < ((Bq d - betHi (d.x : ℚ) d.s1 d.s2 d.l2 (logLo P0 MP) (P0 : ℚ) * d.Lb
        - ((primesL.filter (· < P0)).map fun p =>
            pos (wOf d (mkPE p) - betLo (d.x : ℚ) d.s1 d.s2 d.l1 (logHi P0 MP) (P0 : ℚ)
              * (mkPE p).lo)).sum : ℚ) : ℝ) := by exact_mod_cast hpos
    simp only [Rat.cast_sub, Rat.cast_mul] at hpos'
    rw [hbh] at hpos'
    unfold costU
    linarith
  · -- one modulus at a time
    have := allQ_sound _ _ _ hall q hqa hab
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with hlt | hgen
    · refine ⟨d.x, hxq, Or.inr ⟨h64, d.Pc, hPc, Or.inl ?_⟩⟩
      have hBn' : (((Bq d * (SC : ℚ)).floor.toNat : ℕ) : ℝ) / (SC : ℝ) ≤ ((Bq d : ℚ) : ℝ) := by
        have := (Rat.cast_le (K := ℝ)).2 hBn
        push_cast at this
        exact this
      have hlt' : ((sumDiv q (wList d) 0 : ℕ) : ℝ) < (((Bq d * (SC : ℚ)).floor.toNat : ℕ) : ℝ) := by
        exact_mod_cast hlt
      have hSC : (0 : ℝ) < (SC : ℝ) := by norm_num [SC]
      -- the cost
      have hsd : sumDiv q (wList d) 0
          = ((primesL.filter fun p => decide (p ≤ d.x) && q % p == 0).map (Wn d)).sum := by
        rw [sumDiv_eq, zero_add, wList, List.filter_map, List.map_map, List.filter_filter]
        simp only [Function.comp_def, Bool.and_comm]
      have hcost : costQ d.x q ≤ ((sumDiv q (wList d) 0 : ℕ) : ℝ) / (SC : ℝ) := by
        rw [hsd, natCast_list_sum_map, list_sum_primes, costQ_eq d.x q hNP (by omega),
          Finset.sum_div]
        refine Finset.sum_le_sum fun p hp => ?_
        simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨hpNP, hp, hpx, -⟩ := hp
        have hw := List.all_eq_true.1 hW p
          (mem_primesL_filter hp hpNP (by simpa using hpx))
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        have hWp := Wp_le_wOf (m := m) (a := a) (b := b) hS p hp hw.1
        have : ((wOf d (mkPE p) : ℚ) : ℝ) ≤ (((Wn d p : ℚ) / (SC : ℚ) : ℚ) : ℝ) := by
          exact_mod_cast hw.2
        push_cast at this
        linarith
      have : ((sumDiv q (wList d) 0 : ℕ) : ℝ) / (SC : ℝ)
          < (((Bq d * (SC : ℚ)).floor.toNat : ℕ) : ℝ) / (SC : ℝ) :=
        div_lt_div_of_pos_right hlt' hSC
      linarith
    · exact ⟨d.x, hxq, Or.inl (Ankeny.Checker.closure_eq_top_of_checkGen q d.x hgen)⟩

/-- **Soundness of the block loop.** -/
theorem goC_sound (cn cd m w hi : ℕ) (hcd : 0 < cd) (hm : 1 ≤ m) :
    ∀ fuel a, 3 ≤ a → goC cn cd m w hi fuel a = true → ∀ q, a ≤ q → q < hi →
      GoodC ((cn : ℝ) / cd) q
  | 0, a, _, h, _, _, _ => by simp [goC] at h
  | fuel + 1, a, ha, h, q, hqa, hqh => by
    rw [goC] at h
    split_ifs at h with hha
    · omega
    simp only [Bool.and_eq_true] at h
    set b := min hi (a + max 1 (a >>> w))
    have hab : a < b := by
      have : 1 ≤ max 1 (a >>> w) := le_max_left _ _
      omega
    rcases lt_or_ge q b with hqb | hqb
    · exact blockOKC_sound cn cd m a b hcd hm ha h.1 q hqa hqb
    · exact goC_sound cn cd m w hi hcd hm fuel b (by omega) h.2 q hqb hqh

/-- **Soundness of a chunk.** -/
theorem checkChunkC_sound {cn cd m w lo hi : ℕ} (h : checkChunkC cn cd m w lo hi = true) :
    ∀ q, lo ≤ q → q < hi → GoodC ((cn : ℝ) / cd) q := by
  simp only [checkChunkC, Bool.and_eq_true, decide_eq_true_eq] at h
  exact goC_sound cn cd m w hi h.1.2 h.1.1.2 _ lo h.1.1.1 h.2

end BachSharp.Check
