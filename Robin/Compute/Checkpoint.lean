import Robin.Compute.Step

/-!
# Checkpoints preserve the invariant

At a boundary `B` with data `ck = ckEps B` (exponent `ε = εn/εd`, cut-off `Q`, extras `E`),
the envelope gives, for every `n ≥ 1`,
`log(σ(n)/n) ≤ ε log n + (A εd − εn T + E)/(D εd)`;
`lineOK` at both ends of `[cov, hi]` then extends the coverage to `hi`.
-/

namespace Robin.Compute

open RobinCompute Real Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ### Prime-power extras -/

/-- `t_j = log(1 + 1/a_j) − ε log m`. -/
noncomputable def tj (ε : ℝ) (m j : ℕ) : ℝ := Real.log (1 + 1 / (aSeq m j : ℝ)) - ε * Real.log m

lemma tj_anti {ε : ℝ} {m : ℕ} (hm : 1 ≤ m) {i j : ℕ} (h : j ≤ i) : tj ε m i ≤ tj ε m j := by
  unfold tj
  have ha := aSeq_pos hm j
  have hmono : (aSeq m j : ℝ) ≤ aSeq m i := by exact_mod_cast aSeq_mono m h
  have : 1 / (aSeq m i : ℝ) ≤ 1 / (aSeq m j : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast ha) hmono
  have := Real.log_le_log (by positivity) (show 1 + 1 / (aSeq m i : ℝ) ≤ 1 + 1 / (aSeq m j : ℝ)
    by linarith)
  linarith

theorem extrasGo_spec (εn εd m : ℕ) (hm : 2 ≤ m) (hεd : 0 < εd) :
    ∀ fuel j acc E, extrasFor.go εd m (εn * logLoNatC m) (aSeq m j) (m ^ (j + 1)) fuel acc =
      some E → acc ≤ E ∧ ∀ K, ∑ i ∈ Ico j K, tj ((εn : ℝ) / εd) m i ≤
        ((E : ℝ) - acc) / (D * εd) := by
  have hD := D_pos
  have hεd' : (0 : ℝ) < εd := by exact_mod_cast hεd
  have hl : ((εn * logLoNatC m : ℕ) : ℝ) ≤ εn * (D * Real.log m) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (logLoNatC_le (by omega)) (by positivity)
  intro fuel
  induction fuel with
  | zero => intro j acc E h; simp [extrasFor.go] at h
  | succ fuel ih =>
    intro j acc E h
    unfold extrasFor.go at h
    dsimp only at h
    have hr : (εd : ℝ) * (D * Real.log (1 + 1 / (aSeq m j : ℝ))) ≤
        ((εd * logUpS (aSeq m j) 1 : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (le_logUp1 _ (aSeq_pos (by omega) j)) (by positivity)
    have htj : tj ((εn : ℝ) / εd) m j * (D * εd) ≤
        ((εd * logUpS (aSeq m j) 1 : ℕ) : ℝ) - ((εn * logLoNatC m : ℕ) : ℝ) := by
      unfold tj
      have : (εn : ℝ) / εd * Real.log m * (D * εd) = εn * (D * Real.log m) := by
        field_simp
      nlinarith
    split_ifs at h with hlr
    · have hnext : aSeq m j + m ^ (j + 1) * m = aSeq m (j + 1) := by
        rw [aSeq_succ]; ring
      rw [hnext, show m ^ (j + 1) * m = m ^ (j + 1 + 1) by ring] at h
      obtain ⟨h1, h2⟩ := ih (j + 1) _ E h
      refine ⟨by omega, fun K => ?_⟩
      rcases le_or_gt K j with hK | hK
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
        apply div_nonneg _ (by positivity)
        have : (acc : ℝ) ≤ E := by exact_mod_cast (show acc ≤ E by omega)
        linarith
      · rw [Finset.sum_eq_sum_Ico_succ_bot hK]
        have h3 := h2 K
        have hcast : ((acc + (εd * logUpS (aSeq m j) 1 - εn * logLoNatC m) : ℕ) : ℝ) =
            acc + (((εd * logUpS (aSeq m j) 1 : ℕ) : ℝ) - ((εn * logLoNatC m : ℕ) : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_sub hlr.le]
        rw [hcast] at h3
        have hpos : 0 < (D : ℝ) * εd := by positivity
        have htj' : tj ((εn : ℝ) / εd) m j ≤ ((((εd * logUpS (aSeq m j) 1 : ℕ) : ℝ) -
            ((εn * logLoNatC m : ℕ) : ℝ))) / (D * εd) := by
          rw [le_div_iff₀ hpos]; exact htj
        have : ((E : ℝ) - acc) / (D * εd) = (((εd * logUpS (aSeq m j) 1 : ℕ) : ℝ) -
            ((εn * logLoNatC m : ℕ) : ℝ)) / (D * εd) +
            ((E : ℝ) - (acc + (((εd * logUpS (aSeq m j) 1 : ℕ) : ℝ) -
              ((εn * logLoNatC m : ℕ) : ℝ)))) / (D * εd) := by
          field_simp; ring
        rw [this]
        linarith
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨le_rfl, fun K => ?_⟩
      simp only [sub_self, zero_div]
      apply Finset.sum_nonpos
      intro i hi
      have hij : j ≤ i := (Finset.mem_Ico.mp hi).1
      have := tj_anti (ε := (εn : ℝ) / εd) (m := m) (by omega) hij
      have hle : tj ((εn : ℝ) / εd) m j * (D * εd) ≤ 0 := by
        have : ((εd * logUpS (aSeq m j) 1 : ℕ) : ℝ) ≤ ((εn * logLoNatC m : ℕ) : ℝ) := by
          exact_mod_cast (not_lt.mp hlr)
        linarith
      have : tj ((εn : ℝ) / εd) m j ≤ 0 := by
        by_contra hc; push Not at hc
        have : 0 < tj ((εn : ℝ) / εd) m j * (D * εd) := by positivity
        linarith
      linarith

/-- The local bound at a prime `m < Q` with computed extras `E`. -/
theorem local_le_extras {εn εd m E : ℕ} (hm : 2 ≤ m) (hεd : 0 < εd)
    (h : extrasFor εn εd m = some E) (k : ℕ) (hk : 1 ≤ k) :
    Real.log (locT m k) - k * ((εn : ℝ) / εd * Real.log m) ≤
      tj ((εn : ℝ) / εd) m 0 + (E : ℝ) / (D * εd) := by
  unfold extrasFor at h
  have h' : extrasFor.go εd m (εn * logLoNatC m) (aSeq m 1) (m ^ (1 + 1)) 64 0 = some E := by
    have e1 : aSeq m 1 = m + m * m := by simp [aSeq, Finset.sum_range_succ]; ring
    rw [e1, show m ^ (1 + 1) = m * m by ring]; exact h
  obtain ⟨-, h2⟩ := extrasGo_spec εn εd m hm hεd 64 1 0 E h'
  have hsum : Real.log (locT m k) - k * ((εn : ℝ) / εd * Real.log m) =
      ∑ j ∈ range k, tj ((εn : ℝ) / εd) m j := by
    rw [log_locT_eq_sum (by omega)]
    unfold tj
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have := h2 k
  simp only [Nat.cast_zero, sub_zero] at this
  linarith

/-- The local bound at a prime `m ≥ Q`, where `1/Q² ≤ ε log Q`. -/
theorem local_le_noextras {ε : ℝ} {m Q : ℕ} (hQ : 2 ≤ Q) (hmQ : Q ≤ m)
    (hQε : 1 ≤ (Q : ℝ) ^ 2 * (ε * Real.log Q)) (k : ℕ) (hk : 1 ≤ k) :
    Real.log (locT m k) - k * (ε * Real.log m) ≤ tj ε m 0 := by
  have hm : 1 ≤ m := by omega
  have hsum : Real.log (locT m k) - k * (ε * Real.log m) = ∑ j ∈ range k, tj ε m j := by
    rw [log_locT_eq_sum hm]
    unfold tj
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have : ∑ j ∈ Ico (0 + 1) k, tj ε m j ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hj1 : 1 ≤ j := by simp at hj; omega
    refine (tj_anti hm hj1).trans ?_
    unfold tj
    have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hm' : (Q : ℝ) ≤ m := by exact_mod_cast hmQ
    have ha : ((m : ℝ)) ^ 2 ≤ aSeq m 1 := by exact_mod_cast sq_le_aSeq_one
    have h1 : Real.log (1 + 1 / (aSeq m 1 : ℝ)) ≤ 1 / (m : ℝ) ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (aSeq m 1 : ℝ) by positivity)
      have : 1 / (aSeq m 1 : ℝ) ≤ 1 / (m : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) ha
      linarith
    have hεpos : 0 ≤ ε * Real.log Q := by
      by_contra hc; push Not at hc; nlinarith [sq_nonneg (Q : ℝ)]
    have hlog : Real.log Q ≤ Real.log m := Real.log_le_log (by linarith) hm'
    have hε : 0 ≤ ε := by
      have hlQ : 0 < Real.log Q := Real.log_pos (by linarith)
      by_contra hc; push Not at hc; nlinarith
    have h2 : 1 / (m : ℝ) ^ 2 ≤ ε * Real.log m := by
      rw [div_le_iff₀ (by positivity)]
      have : (Q : ℝ) ^ 2 * (ε * Real.log Q) ≤ (m : ℝ) ^ 2 * (ε * Real.log m) := by
        apply mul_le_mul (pow_le_pow_left₀ (by linarith) hm' 2)
          (mul_le_mul_of_nonneg_left hlog hε) hεpos (by positivity)
      linarith
    linarith
  linarith

/-- The extras scan. -/
def Wset (arr : ByteArray) (n : ℕ) : Finset ℕ := (range n).filter (fun m => 2 ≤ m ∧ arr[m]! = 0)

theorem extrasScan_spec (arr : ByteArray) (εn εd : ℕ) :
    ∀ n E, extrasScan arr εn εd n = some E →
      (∀ m ∈ Wset arr n, ∃ e, extrasFor εn εd m = some e) ∧
      E = ∑ m ∈ Wset arr n, (extrasFor εn εd m).getD 0
  | 0, E, h => by simp [extrasScan] at h; subst h; simp [Wset]
  | n + 1, E, h => by
    unfold extrasScan at h
    rcases hr : extrasScan arr εn εd n with _ | r
    · rw [hr] at h; simp at h
    rw [hr] at h
    obtain ⟨hall, hE⟩ := extrasScan_spec arr εn εd n r hr
    have hW : Wset arr (n + 1) = if 2 ≤ n ∧ arr[n]! = 0 then insert n (Wset arr n)
        else Wset arr n := by
      unfold Wset; rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : n ∉ Wset arr n := by simp [Wset]
    dsimp only at h
    by_cases hc : 2 ≤ n ∧ arr[n]! = 0
    · have hc' : (2 ≤ n ∧ (arr[n]! == 0) = true) := ⟨hc.1, by simp [hc.2]⟩
      rw [if_pos hc'] at h
      rcases he : extrasFor εn εd n with _ | e
      · rw [he] at h; simp at h
      rw [he] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [hW, if_pos hc]
      refine ⟨?_, ?_⟩
      · intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact ⟨e, he⟩
        · exact hall m hm
      · rw [Finset.sum_insert hnot, he, ← h, hE]; simp; ring
    · have hc' : ¬ (2 ≤ n ∧ (arr[n]! == 0) = true) := by
        intro h'; exact hc ⟨h'.1, by simpa using h'.2⟩
      rw [if_neg hc'] at h
      simp only [Option.some.injEq] at h
      rw [hW, if_neg hc]
      exact ⟨hall, by rw [← h, hE]⟩

theorem extrasScanTR_eq (arr : ByteArray) (εn εd : ℕ) :
    ∀ n acc, extrasScanTR arr εn εd n acc = (extrasScan arr εn εd n).map (· + acc)
  | 0, acc => by simp [extrasScanTR, extrasScan]
  | n + 1, acc => by
    unfold extrasScanTR extrasScan
    split_ifs with hc
    · rcases he : extrasFor εn εd n with _ | e
      · rcases hr : extrasScan arr εn εd n <;> simp
      · rw [extrasScanTR_eq arr εn εd n]
        rcases hr : extrasScan arr εn εd n with _ | r
        · simp
        · simp; ring
    · rw [extrasScanTR_eq arr εn εd n]
      rcases hr : extrasScan arr εn εd n with _ | r <;> simp

/-! ### The checkpoint -/

lemma lineOK_spec {G : ℤ} (hG : (G : ℝ) ≤ D * Real.eulerMascheroniConstant)
    {εn εd : ℕ} (hεd : 0 < εd) {Cn : ℤ} {xn : ℕ} (h : lineOK G εn εd Cn xn = true) :
    1 < Real.log ((xn : ℝ) / XS) ∧
      (εn : ℝ) / εd * ((xn : ℝ) / XS) + (Cn : ℝ) / (D * εd) <
        Real.eulerMascheroniConstant + Real.log (Real.log ((xn : ℝ) / XS)) := by
  unfold lineOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hD := D_pos
  have hX := XS_pos
  have hεd' : (0 : ℝ) < εd := by exact_mod_cast hεd
  have hXS : 0 < XS := by unfold XS; positivity
  have hL := logLoQ_le hXS h1
  have hLL := logLogLo_le h1 h2.le
  have hlog : 1 < Real.log ((xn : ℝ) / XS) := by
    have : (D : ℝ) < logLoQ xn XS := by exact_mod_cast h2
    nlinarith
  refine ⟨hlog, ?_⟩
  have h3' : ((εn * xn * D : ℕ) : ℝ) + (Cn : ℝ) * XS < ((G : ℝ) + (logLogLo xn : ℝ)) *
      ((εd * XS : ℕ) : ℝ) := by exact_mod_cast h3
  push_cast at h3'
  have hpos : 0 < (D : ℝ) * εd * XS := by positivity
  have key : (εn : ℝ) / εd * ((xn : ℝ) / XS) + (Cn : ℝ) / (D * εd) <
      ((G : ℝ) + (logLogLo xn : ℝ)) / D := by
    have e1 : (εn : ℝ) / εd * ((xn : ℝ) / XS) + (Cn : ℝ) / (D * εd) =
        ((εn : ℝ) * xn * D + Cn * XS) / (D * εd * XS) := by field_simp
    have e2 : ((G : ℝ) + (logLogLo xn : ℝ)) / D =
        ((G : ℝ) + (logLogLo xn : ℝ)) * (εd * XS) / (D * εd * XS) := by field_simp
    rw [e1, e2]
    exact div_lt_div_of_pos_right h3' hpos
  have : ((G : ℝ) + (logLogLo xn : ℝ)) / D ≤
      Real.eulerMascheroniConstant + Real.log (Real.log ((xn : ℝ) / XS)) := by
    rw [div_le_iff₀ hD]; nlinarith
  linarith

lemma ckEps_spec {B : ℕ} {ck : CK} (h : ckEps B = some ck) :
    3 ≤ B ∧ 0 < ck.εd ∧
      ck.εn * ck.εd ≠ 0 ∧
      (ck.εn : ℝ) / ck.εd * Real.log ((B - 1 : ℕ) : ℝ) ≤ Real.log (1 + 1 / ((B - 1 : ℕ) : ℝ)) ∧
      Real.log (1 + 1 / (B : ℝ)) ≤ (ck.εn : ℝ) / ck.εd * Real.log B ∧
      2 ≤ ck.Q ∧ ck.Q ≤ B ∧
      1 ≤ (ck.Q : ℝ) ^ 2 * ((ck.εn : ℝ) / ck.εd * Real.log ck.Q) ∧
      extras ck.εn ck.εd ck.Q = some ck.E := by
  unfold ckEps at h
  dsimp only at h
  split_ifs at h with h1 h2
  rcases hE : extras (logLoS (B - 1) 1) (logUpNat (B - 1))
      (chooseQ (logLoS (B - 1) 1) (logUpNat (B - 1)) (logLoNat B)) with _ | E
  · rw [hE] at h; simp at h
  rw [hE] at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hB, hlb, he1, hc2⟩ := h1
  obtain ⟨hQ2, hQB, hQc⟩ := h2
  dsimp only
  set e1 := logLoS (B - 1) 1
  set lb := logUpNat (B - 1)
  set Q := chooseQ e1 lb (logLoNat B)
  have hD := D_pos
  have hlb' : (0 : ℝ) < lb := by exact_mod_cast hlb
  have he1' : (0 : ℝ) < e1 := by exact_mod_cast he1
  refine ⟨hB, hlb, by positivity, ?_, ?_, hQ2, hQB, ?_, hE⟩
  · -- ε log(B-1) ≤ e1/D ≤ log(1 + 1/(B-1))
    have hup := le_logUpNat (m := B - 1) (by omega)
    have hlo := logLo1_le (B - 1) (by omega)
    have : (e1 : ℝ) / lb * Real.log ((B - 1 : ℕ) : ℝ) ≤ e1 / D := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hlb' hD]
      nlinarith
    have : (e1 : ℝ) / D ≤ Real.log (1 + 1 / ((B - 1 : ℕ) : ℝ)) := by
      rw [div_le_iff₀ hD]; linarith
    linarith
  · have hup := le_logUp1 B (by omega)
    have hlo := logLoNat_le (m := B) (by omega)
    have hc2' : ((logUpS B 1 : ℕ) : ℝ) * lb ≤ (e1 : ℝ) * logLoNat B := by exact_mod_cast hc2
    rw [div_mul_eq_mul_div, le_div_iff₀ hlb']
    have : Real.log (1 + 1 / (B : ℝ)) * lb * D ≤ (logUpS B 1 : ℝ) * lb := by nlinarith
    have : (e1 : ℝ) * logLoNat B ≤ e1 * (D * Real.log B) := by nlinarith
    nlinarith
  · have hlo := logLoNat_le (m := Q) (by omega)
    have hQc' : (D : ℝ) * lb ≤ (Q : ℝ) * Q * e1 * logLoNat Q := by exact_mod_cast hQc
    have hQ0 : (0 : ℝ) ≤ (Q : ℝ) * Q * e1 := by positivity
    have : (D : ℝ) * lb ≤ (Q : ℝ) * Q * e1 * (D * Real.log Q) := by nlinarith
    rw [show (Q : ℝ) ^ 2 * ((e1 : ℝ) / lb * Real.log Q) = (Q * Q * e1 * (D * Real.log Q)) / (D * lb)
      by field_simp]
    rw [le_div_iff₀ (by positivity)]; linarith

theorem envelope_of_ck {x0 : ℕ} {s : St} (hv : Valid x0 s) {ck : CK} (h : ckEps s.B = some ck)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((σ 1 n : ℝ) / n) ≤
      (ck.εn : ℝ) / ck.εd * Real.log n + (cnOf s ck : ℝ) / (D * ck.εd) := by
  obtain ⟨hB3, hεd, -, hc1, hc2, hQ2, hQB, hQε, hE⟩ := ckEps_spec h
  obtain ⟨-, U, hU, hP, hA, hT, -⟩ := hv
  set ε : ℝ := (ck.εn : ℝ) / ck.εd
  set arrQ := sieveSeg ((List.range (Nat.sqrt ck.Q + 2)).toArray) 0 ck.Q
  have hinvQ := sieveSeg_inv ((List.range (Nat.sqrt ck.Q + 2)).toArray) 0 ck.Q
  have hE' : extrasScan arrQ ck.εn ck.εd ck.Q = some ck.E := by
    have h0 : extrasScanTR arrQ ck.εn ck.εd ck.Q 0 = some ck.E := hE
    rw [extrasScanTR_eq] at h0
    clear_value arrQ
    rcases h' : extrasScan arrQ ck.εn ck.εd ck.Q with _ | r
    · rw [h'] at h0; exact absurd h0 (by simp)
    · rw [h'] at h0
      simp only [Option.map_some, Option.some.injEq, add_zero] at h0
      rw [h0]
  obtain ⟨hall, hEsum⟩ := extrasScan_spec arrQ ck.εn ck.εd ck.Q ck.E hE'
  set W := Wset arrQ ck.Q
  set ex : ℕ → ℕ := fun m => (extrasFor ck.εn ck.εd m).getD 0
  have hD := D_pos
  have hεd' : (0 : ℝ) < ck.εd := by exact_mod_cast hεd
  have hε0 : 0 ≤ ε := by positivity
  set b : ℕ → ℝ := fun m => tj ε m 0 + (if m ∈ W then (ex m : ℝ) / (D * ck.εd) else 0)
  have htj0 : ∀ m ∈ U, 0 ≤ tj ε m 0 := by
    intro m hm
    obtain ⟨hm2, hmB⟩ := hU m hm
    unfold tj; rw [aSeq_zero]
    have hm' : (1 : ℝ) < m := by exact_mod_cast hm2
    have hmB' : (m : ℝ) ≤ ((s.B - 1 : ℕ) : ℝ) := by exact_mod_cast (show m ≤ s.B - 1 by omega)
    have := le_log_one_add_inv_of_le hm' hmB' hc1
    linarith
  have hexnn : ∀ m, 0 ≤ (if m ∈ W then (ex m : ℝ) / (D * ck.εd) else 0) := by
    intro m; split_ifs <;> positivity
  have henv := log_sigma_div_le_env hn ε U b ?hout ?hin ?hnn
  case hout =>
    intro p hp hpU
    have hpB : s.B ≤ p := by
      by_contra hc; exact hpU (hP p hp (by omega))
    have hB1 : (1 : ℝ) < s.B := by exact_mod_cast (show 1 < s.B by omega)
    have hpB' : (s.B : ℝ) ≤ p := by exact_mod_cast hpB
    exact local_le_zero_of hp.one_lt.le (log_one_add_inv_le_of_le hB1 hpB' hc2)
  case hin =>
    intro p hpU hp k hk
    by_cases hW : p ∈ W
    · obtain ⟨e, he⟩ := hall p hW
      have := local_le_extras hp.two_le hεd he k hk
      simp only [b, if_pos hW, ex, he, Option.getD_some]
      exact this
    · have hpQ : ck.Q ≤ p := by
        by_contra hc
        apply hW
        simp only [W, Wset, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, hp.two_le, ?_⟩
        by_contra h0
        exact hinvQ p h0 (by simpa using hp)
      have := local_le_noextras hQ2 hpQ hQε k hk
      simp only [b, if_neg hW, add_zero]
      exact this
  case hnn =>
    intro m hm
    exact add_nonneg (htj0 m hm) (hexnn m)
  refine henv.trans (add_le_add le_rfl ?_)
  -- Σ_U b ≤ Cn / (D εd)
  have hsplit : ∑ m ∈ U, b m = (∑ m ∈ U, Real.log (1 + 1 / (m : ℝ))) - ε * ∑ m ∈ U, Real.log m +
      ∑ m ∈ U, (if m ∈ W then (ex m : ℝ) / (D * ck.εd) else 0) := by
    simp only [b, tj, aSeq_zero]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hW : ∑ m ∈ U, (if m ∈ W then (ex m : ℝ) / (D * ck.εd) else 0) ≤ (ck.E : ℝ) / (D * ck.εd) := by
    rw [Finset.sum_ite_mem]
    refine (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun m _ _ => by positivity)).trans (le_of_eq ?_)
    rw [← Finset.sum_div, hEsum]; push_cast; rfl
  have hcn : (cnOf s ck : ℝ) / (D * ck.εd) =
      (s.A : ℝ) / D - ε * ((s.T : ℝ) / D) + (ck.E : ℝ) / (D * ck.εd) := by
    unfold cnOf; push_cast
    simp only [ε]; field_simp
  rw [hsplit, hcn]
  have h1 : ∑ m ∈ U, Real.log (1 + 1 / (m : ℝ)) ≤ (s.A : ℝ) / D := by
    rw [le_div_iff₀ hD]; linarith
  have h2 : (s.T : ℝ) / D ≤ ∑ m ∈ U, Real.log m := by
    rw [div_le_iff₀ hD]; linarith
  have h3 : ε * ((s.T : ℝ) / D) ≤ ε * ∑ m ∈ U, Real.log m := mul_le_mul_of_nonneg_left h2 hε0
  linarith

theorem checkpoint_valid {x0 : ℕ} {s : St} (hv : Valid x0 s) :
    Valid x0 (checkpoint Gc s) := by
  have hG : ((Gc : ℤ) : ℝ) ≤ D * Real.eulerMascheroniConstant := gammaLoOf_le (by norm_num)
  unfold checkpoint
  rcases hck : ckEps s.B with _ | ck
  · exact hv
  dsimp only
  unfold applyCk
  dsimp only
  have hεd := (ckEps_spec hck).2.1
  split_ifs with hlo hhi
  · obtain ⟨hB2, U, hU, hP, hA, hT, hC⟩ := hv
    refine ⟨hB2, U, hU, hP, hA, hT, ?_⟩
    intro n hn hx0 hxhi
    by_cases hold : Real.log n < (s.cov : ℝ) / XS
    · exact hC n hn hx0 hold
    push Not at hold
    obtain ⟨hl1, hl⟩ := lineOK_spec hG hεd hlo
    obtain ⟨-, hh⟩ := lineOK_spec hG hεd hhi.1
    have hne : (s.cov : ℝ) / XS ≠ 0 := fun h0 => by rw [h0, Real.log_zero] at hl1; linarith
    have hlo0 : 0 < (s.cov : ℝ) / XS := lt_of_le_of_ne (by positivity) (Ne.symm hne)
    have hlo1 : 1 < (s.cov : ℝ) / XS := by
      by_contra hc; push Not at hc
      have := Real.log_nonpos hlo0.le hc; linarith
    have hline := line_of_ends hlo0 hl1 hold hxhi.le hl hh
    have hlogn : 1 < Real.log n := lt_of_lt_of_le hlo1 hold
    exact robin_of_env hn (envelope_of_ck ⟨hB2, U, hU, hP, hA, hT, hC⟩ hck hn) hline hlogn
  · exact hv
  · exact hv

end Robin.Compute
