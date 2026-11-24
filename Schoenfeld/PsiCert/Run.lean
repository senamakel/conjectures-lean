import Schoenfeld.PsiCert.Pp
import Schoenfeld.PsiCert.Log

/-!
# Soundness of the PsiCert run

`Inv st`: `st.plo ≤ D ψ(a) ≤ st.phi`, `st.llo ≤ D log a ≤ st.lhi` and
`|ψ(x) − x| ≤ (4/5)√x` for every real `x ∈ (10⁶, a]`, where `a = st.a`.
`blockStep`, `blkLoop`, `segStep` and `runSegs` preserve it (`runSegs_sound`).

Over a block `(a, b]`, `ψ(b) − ψ(a) = Σ Λ(n)` with `Λ(n) = log n` at the primes (unmarked
entries of the sieve, `sieveSeg_spec`), `Λ(n) = (log n)/k` at `n = p^k`, `k ≥ 2` (the entries
of `ppMark`), and `Λ(n) = 0` otherwise; `log a ≤ log n ≤ log b` bounds each term. For
`x ∈ [a, b]`, `ψ(x) − x ≤ ψ(b) − a` and `x − ψ(x) ≤ b − ψ(a)` by monotonicity, and the guards
bound both by `(4/5)√a ≤ (4/5)√x`.
-/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute Real Chebyshev ArithmeticFunction

/-- The two arrays of a segment describe the numbers `base + i`, `i < w`. -/
structure SegOK (arr pw : ByteArray) (base w : ℕ) : Prop where
  prime_iff : ∀ i < w, 2 ≤ base + i → (arr[i]! = 0 ↔ (base + i).Prime)
  pw_sound : PwSound pw base
  pw_complete : ∀ i < w, ∀ p k, p.Prime → 2 ≤ k → base + i = p ^ k → pw[i]! ≠ 0

lemma psi_nat_succ (m : ℕ) : ψ ((m + 1 : ℕ) : ℝ) = ψ (m : ℝ) + Λ (m + 1) := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le m)]

lemma toNat_eq_zero {v : UInt8} : v.toNat = 0 ↔ v = 0 := by
  constructor
  · intro h; exact UInt8.toNat_inj.mp (by simpa using h)
  · rintro rfl; rfl

/-- `Λ` at the numbers of a segment. -/
lemma vonMangoldt_seg {arr pw : ByteArray} {base w : ℕ} (h : SegOK arr pw base w) {i : ℕ}
    (hi : i < w) (h2 : 2 ≤ base + i) :
    (arr[i]! = 0 → Λ (base + i) = Real.log (base + i : ℕ)) ∧
    (arr[i]! ≠ 0 → pw[i]! ≠ 0 → Λ (base + i) * pw[i]!.toNat = Real.log (base + i : ℕ)) ∧
    (arr[i]! ≠ 0 → pw[i]! = 0 → Λ (base + i) = 0) := by
  refine ⟨fun h0 => vonMangoldt_apply_prime ((h.prime_iff i hi h2).mp h0), ?_, ?_⟩
  · intro _ hpw
    obtain ⟨p, hp, hk, he⟩ := h.pw_sound i hpw
    rw [he, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    push_cast
    rw [Real.log_pow]; ring
  · intro h0 hpw
    rw [vonMangoldt_eq_zero_iff]
    rintro ⟨p, k, hp, hk, he⟩
    rw [← Nat.prime_iff] at hp
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have : k = 1 := by omega
      subst this
      rw [pow_one] at he
      exact h0 ((h.prime_iff i hi h2).mpr (he ▸ hp))
    · exact h.pw_complete i hi p k hp hk2 he.symm hpw

lemma div_le_real (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

lemma le_cdiv_real (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := le_cdiv a b hb

theorem scanBlk_sound {arr pw : ByteArray} {base w : ℕ} (hseg : SegOK arr pw base w)
    (llo lhi : ℕ) : ∀ (c t m plo phi : ℕ), base + t = m + 1 → t + c ≤ w → 1 ≤ m →
      (∀ n : ℕ, m < n → n ≤ m + c → (llo : ℝ) ≤ D * Real.log n ∧ D * Real.log n ≤ lhi) →
      (plo : ℝ) ≤ D * ψ (m : ℝ) → D * ψ (m : ℝ) ≤ phi →
      ((scanBlk arr pw llo lhi t c plo phi).1 : ℝ) ≤ D * ψ ((m + c : ℕ) : ℝ) ∧
        D * ψ ((m + c : ℕ) : ℝ) ≤ (scanBlk arr pw llo lhi t c plo phi).2 := by
  intro c
  induction c with
  | zero => intro t m plo phi _ _ _ _ h1 h2; simpa [scanBlk] using ⟨h1, h2⟩
  | succ c ih =>
    intro t m plo phi ht htc hm hlog h1 h2
    have hn := hlog (m + 1) (by omega) (by omega)
    have hD := D_pos
    obtain ⟨hpr, hpp, hz⟩ := vonMangoldt_seg hseg (i := t) (by omega) (by omega)
    rw [ht] at hpr hpp hz
    have hps := psi_nat_succ m
    have hlog' : ∀ n : ℕ, m + 1 < n → n ≤ m + 1 + c →
        (llo : ℝ) ≤ D * Real.log n ∧ D * Real.log n ≤ lhi :=
      fun n h1 h2 => hlog n (by omega) (by omega)
    rw [show m + (c + 1) = m + 1 + c by omega]
    simp only [scanBlk]
    by_cases ha : arr[t]! = 0
    · rw [if_pos (by simpa using ha)]
      apply ih (t + 1) (m + 1) _ _ (by omega) (by omega) (by omega) hlog'
      · have := hn.1; rw [hps, hpr ha, mul_add]; push_cast at this ⊢; linarith
      · have := hn.2; rw [hps, hpr ha, mul_add]; push_cast at this ⊢; linarith
    · rw [if_neg (by simpa using ha)]
      by_cases hk : pw[t]! = 0
      · rw [if_pos (by simp [toNat_eq_zero.mpr hk])]
        apply ih (t + 1) (m + 1) _ _ (by omega) (by omega) (by omega) hlog'
        · rw [hps, hz ha hk]; simpa using h1
        · rw [hps, hz ha hk]; simpa using h2
      · have hk0 : pw[t]!.toNat ≠ 0 := fun h => hk (toNat_eq_zero.mp h)
        rw [if_neg (by simpa using hk0)]
        have hkpos : (0 : ℝ) < pw[t]!.toNat := by exact_mod_cast Nat.pos_of_ne_zero hk0
        have hL := hpp ha hk
        have hΛ : Λ (m + 1) = Real.log ((m + 1 : ℕ) : ℝ) / pw[t]!.toNat := by
          rw [← hL]; field_simp
        apply ih (t + 1) (m + 1) _ _ (by omega) (by omega) (by omega) hlog'
        · rw [hps, hΛ]; push_cast
          have e1 := div_le_real llo (pw[t]!.toNat)
          have e2 : (llo : ℝ) / pw[t]!.toNat ≤ D * Real.log ((m + 1 : ℕ) : ℝ) / pw[t]!.toNat :=
            div_le_div_of_nonneg_right hn.1 hkpos.le
          have e3 : D * (ψ (m : ℝ) + Real.log ((m + 1 : ℕ) : ℝ) / pw[t]!.toNat) =
              D * ψ (m : ℝ) + D * Real.log ((m + 1 : ℕ) : ℝ) / pw[t]!.toNat := by ring
          push_cast at e2 e3
          rw [e3]; linarith
        · rw [hps, hΛ]; push_cast
          have e1 := le_cdiv_real lhi (pw[t]!.toNat) (Nat.pos_of_ne_zero hk0)
          have e2 : D * Real.log ((m + 1 : ℕ) : ℝ) / pw[t]!.toNat ≤ (lhi : ℝ) / pw[t]!.toNat :=
            div_le_div_of_nonneg_right hn.2 hkpos.le
          have e3 : D * (ψ (m : ℝ) + Real.log ((m + 1 : ℕ) : ℝ) / pw[t]!.toNat) =
              D * ψ (m : ℝ) + D * Real.log ((m + 1 : ℕ) : ℝ) / pw[t]!.toNat := by ring
          push_cast at e2 e3
          rw [e3]; linarith

/-- The invariant of the run. -/
def Inv (st : PS) : Prop :=
  1 ≤ st.a ∧ (st.plo : ℝ) ≤ D * ψ (st.a : ℝ) ∧ D * ψ (st.a : ℝ) ≤ st.phi ∧
    (st.llo : ℝ) ≤ D * Real.log st.a ∧ D * Real.log st.a ≤ st.lhi ∧
    ∀ x : ℝ, (A0 : ℝ) < x → x ≤ st.a → |ψ x - x| ≤ 4 / 5 * √x

lemma guard_le {a v : ℕ} (h : v ≤ a * D ∨ 25 * ((v - a * D) * (v - a * D)) ≤ 16 * a * (D * D)) :
    (v : ℝ) / D - a ≤ 4 / 5 * √(a : ℝ) := by
  have hD := D_pos
  have hs : 0 ≤ 4 / 5 * √(a : ℝ) := by positivity
  rcases h with h | h
  · have : (v : ℝ) ≤ a * D := by exact_mod_cast h
    have : (v : ℝ) / D ≤ a := by rw [div_le_iff₀ hD]; exact this
    linarith
  · by_cases hv : v ≤ a * D
    · have : (v : ℝ) ≤ a * D := by exact_mod_cast hv
      have : (v : ℝ) / D ≤ a := by rw [div_le_iff₀ hD]; exact this
      linarith
    · push Not at hv
      have hc : ((v - a * D : ℕ) : ℝ) = v - a * D := by
        rw [Nat.cast_sub hv.le]; push_cast; ring
      have h' : (25 : ℝ) * (((v : ℝ) - a * D) * ((v : ℝ) - a * D)) ≤ 16 * a * (D * D) := by
        have := (Nat.cast_le (α := ℝ)).mpr h
        push_cast at this
        rw [hc] at this
        exact this
      have hy0 : 0 ≤ (v : ℝ) / D - a := by
        have : (a : ℝ) * D < v := by exact_mod_cast hv
        rw [sub_nonneg, le_div_iff₀ hD]; linarith
      rw [← pow_le_pow_iff_left₀ hy0 hs two_ne_zero]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have e : ((v : ℝ) / D - a) ^ 2 = ((v : ℝ) - a * D) * ((v : ℝ) - a * D) / (D * D) := by
        field_simp
      rw [e, div_le_iff₀ (by positivity)]
      nlinarith

lemma guard_le' {a b p : ℕ} (h : b * D ≤ p ∨ 25 * ((b * D - p) * (b * D - p)) ≤ 16 * a * (D * D)) :
    (b : ℝ) - p / D ≤ 4 / 5 * √(a : ℝ) := by
  have hD := D_pos
  have hs : 0 ≤ 4 / 5 * √(a : ℝ) := by positivity
  by_cases hv : b * D ≤ p
  · have : (b : ℝ) * D ≤ p := by exact_mod_cast hv
    have : (b : ℝ) ≤ p / D := by rw [le_div_iff₀ hD]; exact this
    linarith
  · rcases h with h | h
    · exact absurd h hv
    push Not at hv
    have hc : ((b * D - p : ℕ) : ℝ) = b * D - p := by
      rw [Nat.cast_sub hv.le]; push_cast; ring
    have h' : (25 : ℝ) * (((b : ℝ) * D - p) * ((b : ℝ) * D - p)) ≤ 16 * a * (D * D) := by
      have := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at this
      rw [hc] at this
      exact this
    have hy0 : 0 ≤ (b : ℝ) - p / D := by
      have : (p : ℝ) < b * D := by exact_mod_cast hv
      rw [sub_nonneg, div_le_iff₀ hD]; linarith
    rw [← pow_le_pow_iff_left₀ hy0 hs two_ne_zero]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have e : ((b : ℝ) - p / D) ^ 2 = ((b : ℝ) * D - p) * ((b : ℝ) * D - p) / (D * D) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith

lemma log_add_split {a B : ℕ} (ha : 1 ≤ a) :
    Real.log ((a + B : ℕ) : ℝ) = Real.log a + Real.log (1 + (B : ℝ) / a) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [← Real.log_mul ha'.ne' (by positivity)]
  congr 1
  push_cast
  field_simp

theorem blockStep_sound {arr pw : ByteArray} {base w B : ℕ} (hseg : SegOK arr pw base w)
    (hB : 0 < B) {st st' : PS} (hinv : Inv st) (hbase : base ≤ st.a + 1)
    (hend : st.a + B + 1 ≤ base + w) (h : blockStep arr pw base B st = some st') :
    Inv st' ∧ st'.a = st.a + B := by
  obtain ⟨ha1, hplo, hphi, hllo, hlhi, hcov⟩ := hinv
  unfold blockStep at h
  dsimp only at h
  split_ifs at h with hg
  injection h with h
  subst h
  have hD := D_pos
  have ha' : (1 : ℝ) ≤ st.a := by exact_mod_cast ha1
  have hlS := logLoS_le st.a B (by omega) hB
  have huS := le_logUpS st.a B (by omega) hB
  have hsplit := log_add_split (B := B) ha1
  -- logs of the numbers of the block
  have hlog : ∀ n : ℕ, st.a < n → n ≤ st.a + B →
      ((st.llo : ℕ) : ℝ) ≤ D * Real.log n ∧ D * Real.log n ≤ ((st.lhi + logUpS st.a B : ℕ) : ℝ) := by
    intro n h1 h2
    have hn1 : (st.a : ℝ) ≤ n := by exact_mod_cast h1.le
    have hn2 : (n : ℝ) ≤ (st.a + B : ℕ) := by exact_mod_cast h2
    have l1 : Real.log st.a ≤ Real.log n := Real.log_le_log (by linarith) hn1
    have l2 : Real.log n ≤ Real.log ((st.a + B : ℕ) : ℝ) := Real.log_le_log (by linarith) hn2
    push_cast
    constructor <;> nlinarith
  have hsc := scanBlk_sound hseg st.llo (st.lhi + logUpS st.a B) B (st.a + 1 - base) st.a st.plo
    st.phi (by omega) (by omega) ha1 hlog hplo hphi
  set r := scanBlk arr pw st.llo (st.lhi + logUpS st.a B) (st.a + 1 - base) B st.plo st.phi
  refine ⟨⟨show 1 ≤ st.a + B by omega, hsc.1, hsc.2, ?_, ?_, ?_⟩, rfl⟩
  · simp only; rw [hsplit]; push_cast; nlinarith
  · simp only; rw [hsplit]; push_cast; nlinarith
  · intro x hx1 hx2
    simp only at hx2
    rcases le_or_gt x st.a with hxa | hxa
    · exact hcov x hx1 hxa
    rcases Bool.or_eq_true _ _ ▸ hg with hb | hg
    · simp only [decide_eq_true_eq] at hb
      have : ((st.a + B : ℕ) : ℝ) ≤ A0 := by exact_mod_cast hb
      push_cast at this hx2; linarith
    simp only [guardOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hg
    obtain ⟨g1, g2⟩ := hg
    have G1 := guard_le g1
    have G2 := guard_le' g2
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hsq : √(st.a : ℝ) ≤ √x := Real.sqrt_le_sqrt hxa.le
    have m1 : ψ x ≤ ψ ((st.a + B : ℕ) : ℝ) := psi_mono (by exact_mod_cast hx2)
    have m2 : ψ (st.a : ℝ) ≤ ψ x := psi_mono hxa.le
    have p1 : ψ ((st.a + B : ℕ) : ℝ) ≤ (r.2 : ℝ) / D := by
      rw [le_div_iff₀ hD]; linarith [hsc.2]
    have p2 : (st.plo : ℝ) / D ≤ ψ (st.a : ℝ) := by
      rw [div_le_iff₀ hD]; linarith
    push_cast at hx2 G2
    rw [abs_le]
    constructor <;> nlinarith

theorem blkLoop_sound {arr pw : ByteArray} {base w B : ℕ} (hseg : SegOK arr pw base w)
    (hB : 0 < B) : ∀ (n : ℕ) (st st' : PS), Inv st → base ≤ st.a + 1 →
      st.a + n * B + 1 ≤ base + w → blkLoop arr pw base B n st = some st' →
      Inv st' ∧ st'.a = st.a + n * B := by
  intro n
  induction n with
  | zero => intro st st' h _ _ e; simp [blkLoop] at e; subst e; simpa using h
  | succ n ih =>
    intro st st' h hb he e
    simp only [blkLoop, Option.bind_eq_some_iff] at e
    obtain ⟨s1, e1, e2⟩ := e
    obtain ⟨h1, ha1⟩ := blockStep_sound hseg hB h hb (by nlinarith) e1
    obtain ⟨h2, ha2⟩ := ih s1 st' h1 (by omega) (by rw [ha1]; nlinarith) e2
    exact ⟨h2, by rw [ha2, ha1]; ring⟩

theorem segStep_sound {st st' : PS} (hinv : Inv st) (h : segStep basePrimes st = some st') :
    Inv st' ∧ st'.a = st.a + segLen st.a := by
  unfold segStep at h
  dsimp only at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨h1, hB⟩, hmod⟩, hcov⟩, h40⟩ := hc
  set L := st.a with hL
  set w := segLen L
  set B := blkLen L
  have hseg : SegOK (sieveSeg basePrimes (L + 1) w) (ppMark basePrimes (L + 1) w) (L + 1) w :=
    ⟨fun i hi h2 => sieveSeg_spec _ _ _ basePrimes_sorted (basePrimes_covers (by omega)) i hi h2,
     ppMark_sound _ _ _ basePrimes_prime,
     fun i hi p k hp hk he => ppMark_complete _ _ _ basePrimes_sorted
       (basePrimes_covers (by omega)) (by omega) i hi p k hp hk he⟩
  have hdiv : w / B * B = w := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
  obtain ⟨hi, ha⟩ := blkLoop_sound hseg hB (w / B) st st' hinv (by omega) (by rw [hdiv]; omega) h
  exact ⟨hi, by rw [ha, hdiv]⟩

theorem runSegs_sound : ∀ (n : ℕ) (st st' : PS), Inv st →
    runSegs basePrimes n st = some st' → Inv st' := by
  intro n
  induction n with
  | zero => intro st st' h e; simp [runSegs] at e; subst e; exact h
  | succ n ih =>
    intro st st' h e
    simp only [runSegs, Option.bind_eq_some_iff] at e
    obtain ⟨s1, e1, e2⟩ := e
    exact ih s1 st' (segStep_sound h e1).1 e2

lemma inv_init : Inv init := by
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [init, Chebyshev.psi]
  intro x hx1 hx2
  have : (A0 : ℝ) = 1000000 := by norm_num [A0]
  linarith

end Schoenfeld.PsiCert
