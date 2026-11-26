import LLS.Bach2.SoundBounds
import Ankeny.Checker

/-!
# Soundness of the checker, part 3: blocks and chunks

`checkChunk m w lo hi = true` implies `Good2 q` for every `lo ≤ q < hi`: some `x ≤ 2 log² q`
either has the units of residue `≤ x` generating `(ZMod q)ˣ`, or makes one of the two GRH
budgets of `LLS/Bach2/Budget.lean` positive.
-/

namespace LLS

open Real Finset

/-- What the checker certifies for a modulus `q`. -/
def Good2 (q : ℕ) : Prop :=
  ∃ x : ℕ, (x : ℝ) ≤ 2 * Real.log q ^ 2 ∧
    (Subgroup.closure (Ankeny.Checker.smallUnits q x) = ⊤ ∨
     (64 ≤ x ∧ ∃ Pc : ℝ, Pc ≤ cesSum x ∧
       (0 < base2 x Pc - kap x * Real.log q - costQ x q ∨
        (betP x 53 ≤ kap x ∧ 0 < base2 x Pc - kap x * Real.log q - costU x 53 (Real.log q)))))

end LLS

namespace LLS.Check

open Real Finset LLS

lemma allQ_sound (f : ℕ → Bool) : ∀ n a, allQ f a n = true → ∀ q, a ≤ q → q < a + n → f q = true
  | 0, a, _, q, h1, h2 => by omega
  | n + 1, a, h, q, h1, h2 => by
    simp only [allQ, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact h.1
    · exact allQ_sound f n (a + 1) h.2 q h1' (by omega)

lemma sumDiv_eq (q : ℕ) (l : List (ℕ × ℕ)) (acc : ℕ) :
    sumDiv q l acc = acc + ((l.filter fun pw => q % pw.1 == 0).map Prod.snd).sum := by
  induction l generalizing acc with
  | nil => simp [sumDiv]
  | cons pw l ih =>
    rw [sumDiv, ih, List.filter_cons]
    by_cases h : q % pw.1 = 0
    · simp [h]; ring
    · simp [h]

/-- A list sum over the tabulated primes as a `Finset` sum. -/
lemma list_sum_primes (b : ℕ → Bool) (g : ℕ → ℝ) :
    ((primesL.filter b).map g).sum
      = ∑ p ∈ (Finset.range NP).filter (fun p => p.Prime ∧ b p = true), g p := by
  have h := List.sum_toFinset g (primesL_nodup.filter b)
  rw [← h]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  rw [List.mem_toFinset, List.mem_filter, mem_primesL, Finset.mem_filter, Finset.mem_range]
  exact and_assoc

lemma costQ_eq (x q : ℕ) (hx : x < NP) (hq : q ≠ 0) :
    costQ x q = ∑ p ∈ (Finset.range NP).filter
      (fun p => p.Prime ∧ (decide (p ≤ x) && q % p == 0) = true), Wp x p := by
  unfold costQ
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨hp, hdvd, -⟩, hpx⟩
    exact ⟨by omega, hp, hpx, Nat.mod_eq_zero_of_dvd hdvd⟩
  · rintro ⟨-, hp, hpx, hmod⟩
    exact ⟨⟨hp, Nat.dvd_of_mod_eq_zero hmod, hq⟩, hpx⟩

lemma smallPN_eq : smallPN 53 = (Finset.range NP).filter
    (fun p => p.Prime ∧ decide (p < P0) = true) := by
  ext p
  simp only [smallPN, Finset.mem_filter, Finset.mem_range]
  rw [decide_eq_true_iff]
  simp only [P0, NP]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2, h1⟩
  · rintro ⟨-, h2, h1⟩; exact ⟨h1, h2⟩

/-- The block data of `mkBD`, abstractly. -/
structure BDOK (m a b : ℕ) (d : BD) : Prop where
  La : d.La = logLo a m
  Lb : d.Lb = logHi b m
  l1 : d.l1 = logLo d.x MP
  l2 : d.l2 = logHi d.x MP
  Pc : d.Pc = if d.x < NP then cesLo d.x else d.l1 - 2
  s2 : 0 ≤ d.s2

lemma mkBD_ok (m a b : ℕ) : BDOK m a b (mkBD m a b) where
  La := rfl
  Lb := rfl
  l1 := rfl
  l2 := rfl
  Pc := rfl
  s2 := by simp only [mkBD]; positivity

/-- The real side conditions from `sideOK`. -/
lemma side_of_sideOK {m a b : ℕ} {d : BD} (hd : BDOK m a b d) (h : sideOK d = true) :
    Side d.x d.s1 d.s2 d.l1 d.l2 ∧ 64 ≤ d.x ∧ 0 ≤ (d.Pc : ℝ) ∧ (d.Pc : ℝ) ≤ cesSum d.x ∧
      0 ≤ (d.Lb : ℝ) := by
  simp only [sideOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h64, hs10⟩, hs1x⟩, hxs2⟩, hden⟩, hl10⟩, hPc0⟩, hLb0⟩, hEs⟩ := h
  have hx1 : 1 ≤ d.x := by omega
  have hl1 : ((d.l1 : ℚ) : ℝ) ≤ Real.log d.x := by rw [hd.l1]; exact logLo_le _ _ hx1 (by norm_num [MP])
  have hl2 : Real.log d.x ≤ ((d.l2 : ℚ) : ℝ) := by rw [hd.l2]; exact le_logHi _ _ hx1 (by norm_num [MP])
  have hs20 : (0 : ℝ) ≤ d.s2 := by exact_mod_cast hd.s2
  refine ⟨⟨?_, ?_, hl1, hl2, ?_, ?_, ?_, ?_, ?_⟩, h64, by exact_mod_cast hPc0, ?_, by exact_mod_cast hLb0⟩
  · apply Real.le_sqrt_of_sq_le
    have : ((d.s1 * d.s1 : ℚ) : ℝ) ≤ ((d.x : ℚ) : ℝ) := by exact_mod_cast hs1x
    push_cast at this; nlinarith
  · rw [Real.sqrt_le_left hs20]
    have : (((d.x : ℚ)) : ℝ) ≤ ((d.s2 * d.s2 : ℚ) : ℝ) := by exact_mod_cast hxs2
    push_cast at this; nlinarith
  · exact_mod_cast h64
  · exact_mod_cast hs10
  · have : ((0 : ℚ) : ℝ) < ((1 + 1 / (d.x : ℚ) - 2 / d.s1 : ℚ) : ℝ) := by exact_mod_cast hden
    push_cast at this; exact this
  · exact_mod_cast hl10
  · rw [← cast_Es]; exact_mod_cast hEs
  · rw [hd.Pc]
    split_ifs with hx
    · exact cesLo_le _
    · have := log_sub_two_le_cesSum d.x (by omega)
      push_cast
      linarith

/-- `κ log q ≤ k₂ Lb`. -/
lemma kap_log_le {x : ℕ} {s₁ s₂ l₁ l₂ Lb : ℝ} (hS : Side x s₁ s₂ l₁ l₂) {q : ℕ}
    (hq : 1 ≤ q) (hLb : Real.log q ≤ Lb) :
    kap x * Real.log q ≤ ik₂ x s₁ s₂ l₂ * Lb := by
  obtain ⟨-, -, hk1, hk2, -, -, hk10⟩ := hS.core
  have hL0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  exact mul_le_mul hk2 hLb hL0 (by linarith)

/-- The per-prime bound `W_p ≤ wOf`. -/
lemma Wp_le_wOf {m a b : ℕ} {d : BD} (hS : Side d.x d.s1 d.s2 d.l1 d.l2) (p : ℕ) (hp : p.Prime)
    (hok : peOK d (mkPE p) = true) : Wp d.x p ≤ ((wOf d (mkPE p) : ℚ) : ℝ) := by
  simp only [peOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  unfold wOf
  rw [cast_Wup]
  have hhi : ((((mkPE p).hi / 2 : ℚ)) : ℝ) ≤ (d.l1 : ℝ) := by exact_mod_cast hok.2
  push_cast at hhi
  have := hS.Wp_le p hp.two_le (mkPE_lo_le hp) (le_mkPE_hi hp) (by exact_mod_cast hok.1) hhi
  simpa [mkPE] using this

lemma cast_list_sum_map (l : List ℕ) (f : ℕ → ℚ) :
    (((l.map f).sum : ℚ) : ℝ) = (l.map fun p => ((f p : ℚ) : ℝ)).sum := by
  rw [Rat.cast_list_sum, List.map_map]; rfl

lemma natCast_list_sum_map (l : List ℕ) (f : ℕ → ℕ) :
    (((l.map f).sum : ℕ) : ℝ) = (l.map fun p => ((f p : ℕ) : ℝ)).sum := by
  rw [Nat.cast_list_sum, List.map_map]; rfl

lemma mem_primesL_filter {b : ℕ → Bool} {p : ℕ} (hp : p.Prime) (hNP : p < NP) (hb : b p = true) :
    p ∈ primesL.filter b :=
  List.mem_filter.2 ⟨mem_primesL.2 ⟨hNP, hp⟩, hb⟩

/-- **Soundness of one block.** -/
theorem blockOK_sound (m a b : ℕ) (hm : 1 ≤ m) (ha : 3 ≤ a) (h : blockOK m a b = true) :
    ∀ q, a ≤ q → q < b → Good2 q := by
  intro q hqa hqb
  have hq3 : 3 ≤ q := le_trans ha hqa
  haveI : NeZero q := ⟨by omega⟩
  have hd := mkBD_ok m a b
  unfold blockOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  generalize mkBD m a b = d at h hd
  obtain ⟨⟨hLa0, hxLa⟩, hrest⟩ := h
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hLq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hLa : ((d.La : ℚ) : ℝ) ≤ Real.log q := by
    rw [hd.La]
    exact (logLo_le a m (by omega) hm).trans
      (Real.log_le_log (by exact_mod_cast (show 0 < a by omega)) (by exact_mod_cast hqa))
  have hLa0' : (0 : ℝ) ≤ ((d.La : ℚ) : ℝ) := by exact_mod_cast hLa0
  have hxq : (d.x : ℝ) ≤ 2 * Real.log q ^ 2 := by
    have : (((d.x : ℚ)) : ℝ) ≤ ((2 * d.La * d.La : ℚ) : ℝ) := by exact_mod_cast hxLa
    push_cast at this
    nlinarith
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
theorem go_sound (m w hi : ℕ) (hm : 1 ≤ m) :
    ∀ fuel a, 3 ≤ a → go m w hi fuel a = true → ∀ q, a ≤ q → q < hi → Good2 q
  | 0, a, _, h, _, _, _ => by simp [go] at h
  | fuel + 1, a, ha, h, q, hqa, hqh => by
    rw [go] at h
    split_ifs at h with hha
    · omega
    simp only [Bool.and_eq_true] at h
    set b := min hi (a + max 1 (a >>> w))
    have hab : a < b := by
      have : 1 ≤ max 1 (a >>> w) := le_max_left _ _
      omega
    rcases lt_or_ge q b with hqb | hqb
    · exact blockOK_sound m a b hm ha h.1 q hqa hqb
    · exact go_sound m w hi hm fuel b (by omega) h.2 q hqb hqh

/-- **Soundness of a chunk.** -/
theorem checkChunk_sound {m w lo hi : ℕ} (h : checkChunk m w lo hi = true) :
    ∀ q, lo ≤ q → q < hi → Good2 q := by
  simp only [checkChunk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact go_sound m w hi h.1.2 _ lo h.1.1 h.2

end LLS.Check
