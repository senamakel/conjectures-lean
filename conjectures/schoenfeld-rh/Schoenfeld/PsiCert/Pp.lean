import Schoenfeld.PsiCert.Sieve

/-!
# Proper prime powers and the base primes

* `ppMark_sound`: a nonzero entry `k` of `ppMark sp base h` at index `i` has `base + i = p^k`
  with `p` prime and `k ≥ 2` (when every entry of `sp` is prime).
* `ppMark_complete`: every proper prime power `p^k` of `[base, base + h)` gets a nonzero entry
  (when `sp` is sorted and covers `base + h ≤ 2^40`).
* `basePrimes`: exactly the primes `≤ 131072`, sorted, so it covers every `hi ≤ 131073²`.
-/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

lemma getElem!_set!_eq (arr : ByteArray) (k i : ℕ) (v : UInt8) :
    (arr.set! k v)[i]! = if k = i ∧ k < arr.size then v else arr[i]! := by
  by_cases hki : k = i
  · subst hki
    by_cases hk : k < arr.size
    · rw [if_pos ⟨rfl, hk⟩, ByteArray.getElem!_set!_self _ _ _ hk]
    · rw [if_neg (by tauto), getElem!_neg (arr.set! k v) k (by simpa using hk),
        getElem!_neg arr k hk]
  · rw [if_neg (by tauto), ByteArray.getElem!_set!_ne _ _ _ _ hki]

/-- A nonzero entry is the exponent of a proper prime power. -/
def PwSound (pw : ByteArray) (base : ℕ) : Prop :=
  ∀ i, pw[i]! ≠ 0 → ∃ p, p.Prime ∧ 2 ≤ pw[i]!.toNat ∧ base + i = p ^ pw[i]!.toNat

lemma ofNat_toNat {k : ℕ} (hk : k < 256) : (UInt8.ofNat k).toNat = k := by
  simp only [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt hk

theorem ppLoop_sound (q hi base : ℕ) (hq : q.Prime) :
    ∀ fuel pk k (pw : ByteArray), pk = q ^ k → 2 ≤ k → k + fuel ≤ 255 → PwSound pw base →
      PwSound (ppLoop q hi base fuel pk k pw) base := by
  intro fuel
  induction fuel with
  | zero => intro pk k pw _ _ _ h; simpa [ppLoop] using h
  | succ fuel ih =>
    intro pk k pw hpk hk hkf h
    simp only [ppLoop]
    by_cases hlt : pk < hi
    · rw [if_pos hlt]
      apply ih (pk * q) (k + 1) _ (by rw [hpk, pow_succ]) (by omega) (by omega)
      by_cases hb : base ≤ pk
      · rw [if_pos hb]
        intro i hi
        rw [getElem!_set!_eq] at hi ⊢
        split_ifs at hi ⊢ with he
        · refine ⟨q, hq, ?_, ?_⟩ <;> rw [ofNat_toNat (by omega)]
          · exact hk
          · rw [← hpk]; omega
        · exact h i hi
      · rw [if_neg hb]; exact h
    · rw [if_neg hlt]; exact h

theorem ppLoop_mono (q hi base : ℕ) :
    ∀ fuel pk k (pw : ByteArray) (i : ℕ), 2 ≤ k → k + fuel ≤ 255 → pw[i]! ≠ 0 →
      (ppLoop q hi base fuel pk k pw)[i]! ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro pk k pw i _ _ h; simpa [ppLoop] using h
  | succ fuel ih =>
    intro pk k pw i hk hkf h
    simp only [ppLoop]
    by_cases hlt : pk < hi
    · rw [if_pos hlt]
      apply ih _ (k + 1) _ i (by omega) (by omega)
      by_cases hb : base ≤ pk
      · rw [if_pos hb]
        apply set_ne_zero _ h
        intro h0
        have := congrArg UInt8.toNat h0
        rw [ofNat_toNat (by omega)] at this
        simp at this; omega
      · rw [if_neg hb]; exact h
    · rw [if_neg hlt]; exact h

theorem ppLoop_marks (q hi base : ℕ) (hq : 2 ≤ q) :
    ∀ fuel pk k (pw : ByteArray), pk = q ^ k → 2 ≤ k → k + fuel ≤ 255 →
      ∀ j, k ≤ j → j < k + fuel → base ≤ q ^ j → q ^ j < hi → q ^ j - base < pw.size →
        (ppLoop q hi base fuel pk k pw)[q ^ j - base]! ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro pk k pw _ _ _ j h1 h2; omega
  | succ fuel ih =>
    intro pk k pw hpk hk hkf j hj1 hj2 hb hh hs
    simp only [ppLoop]
    have hmono : q ^ k ≤ q ^ j := Nat.pow_le_pow_right (by omega) hj1
    by_cases hlt : pk < hi
    · rw [if_pos hlt]
      rcases eq_or_lt_of_le hj1 with e | e
      · subst e
        apply ppLoop_mono _ _ _ _ _ _ _ _ (by omega) (by omega)
        rw [if_pos (by omega), getElem!_set!_eq, if_pos ⟨by rw [hpk], by rw [hpk]; exact hs⟩]
        intro h0
        have := congrArg UInt8.toNat h0
        rw [ofNat_toNat (by omega)] at this
        simp at this; omega
      · apply ih (pk * q) (k + 1) _ (by rw [hpk, pow_succ]) (by omega) (by omega) j (by omega)
          (by omega) hb hh
        split_ifs <;> simp [hs]
    · rw [if_neg hlt]; omega

theorem size_ppLoop (q hi base : ℕ) : ∀ fuel pk k (pw : ByteArray),
    (ppLoop q hi base fuel pk k pw).size = pw.size := by
  intro fuel
  induction fuel with
  | zero => intro pk k pw; rfl
  | succ fuel ih =>
    intro pk k pw
    simp only [ppLoop]
    split_ifs <;> simp [ih]

theorem ppSieve_sound (sp : Array ℕ) (base hi i : ℕ) (pw : ByteArray)
    (hp : ∀ j < sp.size, (sp[j]!).Prime) (h : PwSound pw base) :
    PwSound (ppSieve sp base hi i pw) base := by
  unfold ppSieve
  by_cases hlt : i < sp.size
  · rw [if_pos hlt]
    dsimp only
    split_ifs with h1 h2
    · exact h
    · exact ppSieve_sound sp base hi (i + 1) _ hp
        (ppLoop_sound _ _ _ (hp i hlt) 40 _ 2 _ (by ring) le_rfl (by norm_num) h)
    · exact ppSieve_sound sp base hi (i + 1) _ hp h
  · rw [if_neg hlt]; exact h
termination_by sp.size - i

theorem ppSieve_mono (sp : Array ℕ) (base hi i : ℕ) (pw : ByteArray) (idx : ℕ)
    (h : pw[idx]! ≠ 0) : (ppSieve sp base hi i pw)[idx]! ≠ 0 := by
  unfold ppSieve
  by_cases hlt : i < sp.size
  · rw [if_pos hlt]
    dsimp only
    split_ifs with h1 h2
    · exact h
    · exact ppSieve_mono sp base hi (i + 1) _ idx
        (ppLoop_mono _ _ _ 40 _ 2 _ idx le_rfl (by norm_num) h)
    · exact ppSieve_mono sp base hi (i + 1) _ idx h
  · rw [if_neg hlt]; exact h
termination_by sp.size - i

theorem size_ppSieve (sp : Array ℕ) (base hi i : ℕ) (pw : ByteArray) :
    (ppSieve sp base hi i pw).size = pw.size := by
  unfold ppSieve
  by_cases hlt : i < sp.size
  · rw [if_pos hlt]
    dsimp only
    split_ifs with h1 h2
    · rfl
    · rw [size_ppSieve, size_ppLoop]
    · rw [size_ppSieve]
  · rw [if_neg hlt]
termination_by sp.size - i

lemma pow_lt_40 {p k hi : ℕ} (hp : 2 ≤ p) (h : p ^ k < hi) (hhi : hi ≤ 2 ^ 40) : k < 40 := by
  by_contra hk
  push Not at hk
  have : 2 ^ 40 ≤ p ^ k :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hk) (Nat.pow_le_pow_left hp k)
  omega

theorem ppSieve_marks (sp : Array ℕ) (base hi i : ℕ) (pw : ByteArray) (hs : Sorted sp)
    (hhi : hi ≤ 2 ^ 40) (i0 : ℕ) (hi0 : i ≤ i0) (hi0' : i0 < sp.size) (h2 : 2 ≤ sp[i0]!)
    (hqq : sp[i0]! * sp[i0]! < hi) (k : ℕ) (hk : 2 ≤ k) (hb : base ≤ sp[i0]! ^ k)
    (hh : sp[i0]! ^ k < hi) (hsz : sp[i0]! ^ k - base < pw.size) :
    (ppSieve sp base hi i pw)[sp[i0]! ^ k - base]! ≠ 0 := by
  unfold ppSieve
  have hlt : i < sp.size := by omega
  rw [if_pos hlt]
  dsimp only
  split_ifs with h1 h2'
  · have := hs i i0 hi0 hi0'
    have : sp[i]! * sp[i]! ≤ sp[i0]! * sp[i0]! := Nat.mul_le_mul this this
    omega
  · rcases eq_or_lt_of_le hi0 with e | e
    · subst e
      apply ppSieve_mono
      have := pow_lt_40 h2 hh hhi
      exact ppLoop_marks _ _ _ h2 40 _ 2 _ (by ring) le_rfl (by norm_num) k hk (by omega) hb hh
        hsz
    · exact ppSieve_marks sp base hi (i + 1) _ hs hhi i0 e hi0' h2 hqq k hk hb hh
        (by rw [size_ppLoop]; exact hsz)
  · rcases eq_or_lt_of_le hi0 with e | e
    · subst e; omega
    · exact ppSieve_marks sp base hi (i + 1) _ hs hhi i0 e hi0' h2 hqq k hk hb hh hsz
termination_by sp.size - i

lemma size_ppMark (sp : Array ℕ) (base h : ℕ) : (ppMark sp base h).size = h := by
  unfold ppMark; rw [size_ppSieve, size_replicate]

theorem ppMark_sound (sp : Array ℕ) (base h : ℕ) (hp : ∀ j < sp.size, (sp[j]!).Prime) :
    PwSound (ppMark sp base h) base := by
  unfold ppMark
  apply ppSieve_sound _ _ _ _ _ hp
  intro i hi
  exact absurd (replicate_getElem! h i) hi

theorem ppMark_complete (sp : Array ℕ) (base h : ℕ) (hs : Sorted sp) (hc : Covers sp (base + h))
    (hhi : base + h ≤ 2 ^ 40) (i : ℕ) (hi : i < h) (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k)
    (he : base + i = p ^ k) : (ppMark sp base h)[i]! ≠ 0 := by
  have hpp : p * p ≤ p ^ k := by
    calc p * p = p ^ 2 := by ring
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  obtain ⟨i0, hi0, hq0⟩ := hc p hp (by omega)
  have := ppSieve_marks sp base (base + h) 0 (ByteArray.mk (Array.replicate h 0)) hs hhi i0
    (Nat.zero_le _) hi0 (by rw [hq0]; exact hp.two_le) (by rw [hq0]; omega) k hk
    (by rw [hq0]; omega) (by rw [hq0]; omega) (by rw [hq0, size_replicate]; omega)
  rw [hq0, show p ^ k - base = i by omega] at this
  exact this

/-! ### Base primes -/

lemma toArray_getElem! (l : List ℕ) (i : ℕ) (hi : i < l.length) : l.toArray[i]! = l[i] := by
  rw [getElem!_pos l.toArray i (by simpa using hi)]
  simp

lemma range_getElem! {n i : ℕ} (hi : i < n) : (List.range n).toArray[i]! = i := by
  rw [toArray_getElem! _ _ (by simpa using hi)]
  simp

lemma baseArr_spec (i : ℕ) (hi : i ≤ baseMax) (h2 : 2 ≤ i) : baseArr[i]! = 0 ↔ i.Prime := by
  have hs : Sorted (List.range 364).toArray := by
    intro a b hab hb
    simp at hb
    rw [range_getElem! (by omega), range_getElem! hb]; exact hab
  have hc : Covers (List.range 364).toArray (0 + (baseMax + 1)) := by
    intro q _ hq
    have : q < 364 := by
      unfold baseMax at hq
      by_contra h; push Not at h; nlinarith
    exact ⟨q, by simpa using this, range_getElem! this⟩
  have := sieveSeg_spec _ 0 (baseMax + 1) hs hc i (by omega) (by omega)
  simpa [baseArr] using this

/-- The list behind `basePrimes`. -/
def baseList : List ℕ := (List.range (baseMax + 1)).filter (fun i => 2 ≤ i && baseArr[i]! == 0)

lemma basePrimes_eq : basePrimes = baseList.toArray := rfl

lemma mem_baseList (q : ℕ) : q ∈ baseList ↔ q.Prime ∧ q ≤ baseMax := by
  unfold baseList
  rw [List.mem_filter, List.mem_range]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(baseArr_spec q (by omega) h2).mp h3, by omega⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by omega, hp.two_le, (baseArr_spec q hq hp.two_le).mpr hp⟩

lemma basePrimes_prime : ∀ j < basePrimes.size, (basePrimes[j]!).Prime := by
  intro j hj
  rw [basePrimes_eq] at hj ⊢
  simp only [List.size_toArray] at hj
  rw [toArray_getElem! _ _ hj]
  exact ((mem_baseList _).mp (List.getElem_mem hj)).1

lemma basePrimes_sorted : Sorted basePrimes := by
  intro a b hab hb
  rw [basePrimes_eq] at hb ⊢
  simp only [List.size_toArray] at hb
  rw [toArray_getElem! _ _ (by omega), toArray_getElem! _ _ hb]
  rcases eq_or_lt_of_le hab with e | e
  · subst e; rfl
  · have hpw : baseList.Pairwise (· < ·) := (List.pairwise_lt_range).filter _
    exact (List.pairwise_iff_getElem.mp hpw a b (by omega) hb e).le

lemma basePrimes_covers {hi : ℕ} (hhi : hi ≤ (baseMax + 1) * (baseMax + 1)) :
    Covers basePrimes hi := by
  intro q hq hqq
  have : q ≤ baseMax := by
    by_contra h; push Not at h
    have : (baseMax + 1) * (baseMax + 1) ≤ q * q := Nat.mul_le_mul h h
    omega
  obtain ⟨j, hj, hjq⟩ := List.mem_iff_getElem.mp ((mem_baseList q).mpr ⟨hq, this⟩)
  refine ⟨j, by rw [basePrimes_eq]; simpa using hj, ?_⟩
  rw [basePrimes_eq, toArray_getElem! _ _ hj, hjq]

end Schoenfeld.PsiCert
