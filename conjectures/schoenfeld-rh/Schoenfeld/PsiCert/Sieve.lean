import Mathlib
import SchoenfeldCompute.Psi

/-!
# The segmented sieve is exact

`sieveSeg sp B h` leaves index `i` unmarked exactly when `B + i` is prime (for `B + i ≥ 2`),
provided `sp` is sorted and contains every prime `q` with `q² < B + h`.

* Soundness (a marked entry is composite): copied from robin-rh (`Robin/Compute/Sieve.lean`
  at `343518c`, same authors): `markLoop_inv`, `sieveLoop_inv`, `replicate_getElem!`.
* Completeness (a composite entry is marked): `markLoop_marks`, `sieveLoop_marks`; the smallest
  prime factor `q` of a composite `m` has `q² ≤ m`, so `q` is a sieving prime and `m` is one of
  the multiples `q·t ≥ q²` it marks.
-/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute


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


/-! ### Completeness -/

lemma ne_zero_lt_size {arr : ByteArray} {i : ℕ} (h : arr[i]! ≠ 0) : i < arr.size := by
  by_contra hc
  rw [getElem!_neg arr i hc] at h
  exact h rfl

lemma set_ne_zero {arr : ByteArray} {i k : ℕ} {v : UInt8} (hv : v ≠ 0) (h : arr[i]! ≠ 0) :
    (arr.set! k v)[i]! ≠ 0 := by
  by_cases hki : k = i
  · subst hki; rw [ByteArray.getElem!_set!_self _ _ _ (ne_zero_lt_size h)]; exact hv
  · rw [ByteArray.getElem!_set!_ne _ _ _ _ hki]; exact h

theorem size_markLoop (arr : ByteArray) (j q hi base : ℕ) :
    (markLoop arr j q hi base).size = arr.size := by
  unfold markLoop
  split_ifs with hj h0
  · rfl
  · rw [size_markLoop]; simp
  · rfl
termination_by hi - j

theorem markLoop_mono (arr : ByteArray) (j q hi base i : ℕ) (h : arr[i]! ≠ 0) :
    (markLoop arr j q hi base)[i]! ≠ 0 := by
  unfold markLoop
  split_ifs with hj h0
  · exact h
  · exact markLoop_mono _ (j + q) q hi base i (set_ne_zero (by decide) h)
  · exact h
termination_by hi - j

theorem markLoop_marks (arr : ByteArray) (j q hi base : ℕ) (hq : 0 < q) (hb : base ≤ j)
    (hsz : hi ≤ base + arr.size) (m : ℕ) (hjm : j ≤ m) (hmh : m < hi) (hd : q ∣ m - j) :
    (markLoop arr j q hi base)[m - base]! ≠ 0 := by
  unfold markLoop
  split_ifs with hj h0
  · omega
  · by_cases hmj : m = j
    · subst hmj
      apply markLoop_mono
      rw [ByteArray.getElem!_set!_self _ _ _ (by omega)]
      decide
    · have hqm : q ≤ m - j := Nat.le_of_dvd (by omega) hd
      apply markLoop_marks _ (j + q) q hi base hq (by omega) (by simp; omega) m (by omega) hmh
      have : m - (j + q) = (m - j) - q := by omega
      rw [this]
      exact Nat.dvd_sub hd dvd_rfl
  · omega
termination_by hi - j

theorem size_sieveLoop (sp : Array ℕ) (B hi i : ℕ) (arr : ByteArray) :
    (sieveLoop sp B hi i arr).size = arr.size := by
  unfold sieveLoop
  by_cases hlt : i < sp.size
  · rw [if_pos hlt]
    dsimp only
    split_ifs with h1 h2
    · rfl
    · rw [size_sieveLoop, size_markLoop]
    · rw [size_sieveLoop]
  · rw [if_neg hlt]
termination_by sp.size - i

theorem sieveLoop_mono (sp : Array ℕ) (B hi i : ℕ) (arr : ByteArray) (idx : ℕ)
    (h : arr[idx]! ≠ 0) : (sieveLoop sp B hi i arr)[idx]! ≠ 0 := by
  unfold sieveLoop
  by_cases hlt : i < sp.size
  · rw [if_pos hlt]
    dsimp only
    split_ifs with h1 h2
    · exact h
    · exact sieveLoop_mono sp B hi (i + 1) _ idx (markLoop_mono _ _ _ _ _ _ h)
    · exact sieveLoop_mono sp B hi (i + 1) _ idx h
  · rw [if_neg hlt]; exact h
termination_by sp.size - i

/-- `sp` is sorted. -/
def Sorted (sp : Array ℕ) : Prop := ∀ a b, a ≤ b → b < sp.size → sp[a]! ≤ sp[b]!

lemma first_mult_le {q B m : ℕ} (hq : 0 < q) (hd : q ∣ m) (hm : B ≤ m) :
    (B + q - 1) / q * q ≤ m := by
  obtain ⟨t, rfl⟩ := hd
  have : (B + q - 1) / q < t + 1 := by
    rw [Nat.div_lt_iff_lt_mul hq, add_mul, one_mul, mul_comm t q]
    omega
  calc (B + q - 1) / q * q ≤ t * q := Nat.mul_le_mul_right _ (by omega)
    _ = q * t := by ring

lemma le_first_mult {q B : ℕ} (hq : 0 < q) : B ≤ (B + q - 1) / q * q := by
  have h := Nat.lt_div_mul_add (a := B + q - 1) (b := q) hq
  omega

theorem sieveLoop_marks (sp : Array ℕ) (B hi i : ℕ) (arr : ByteArray) (hs : Sorted sp)
    (hsz : hi ≤ B + arr.size) (i0 : ℕ) (hi0 : i ≤ i0) (hi0' : i0 < sp.size) (h2 : 2 ≤ sp[i0]!)
    (hqq : sp[i0]! * sp[i0]! < hi) (m : ℕ) (hBm : B ≤ m) (hmh : m < hi) (hd : sp[i0]! ∣ m)
    (hqm : sp[i0]! * sp[i0]! ≤ m) : (sieveLoop sp B hi i arr)[m - B]! ≠ 0 := by
  unfold sieveLoop
  have hlt : i < sp.size := by omega
  rw [if_pos hlt]
  dsimp only
  split_ifs with h1 h2'
  · have := hs i i0 hi0 hi0'
    have : sp[i]! * sp[i]! ≤ sp[i0]! * sp[i0]! := Nat.mul_le_mul this this
    omega
  · rcases eq_or_lt_of_le hi0 with e | e
    · subst e
      apply sieveLoop_mono
      set q := sp[i]!
      have hq0 : 0 < q := by omega
      apply markLoop_marks _ _ q hi B hq0 (le_trans (le_first_mult hq0) (le_max_right _ _))
        hsz m (max_le hqm (first_mult_le hq0 hd hBm)) hmh
      apply Nat.dvd_sub hd
      rcases le_total (q * q) ((B + q - 1) / q * q) with h | h
      · rw [max_eq_right h]; exact Dvd.intro_left _ rfl
      · rw [max_eq_left h]; exact Dvd.intro _ rfl
    · exact sieveLoop_marks sp B hi (i + 1) _ hs (by rw [size_markLoop]; exact hsz) i0 e hi0'
        h2 hqq m hBm hmh hd hqm
  · rcases eq_or_lt_of_le hi0 with e | e
    · subst e; omega
    · exact sieveLoop_marks sp B hi (i + 1) _ hs hsz i0 e hi0' h2 hqq m hBm hmh hd hqm
termination_by sp.size - i

/-- `sp` contains every prime `q` with `q² < hi`. -/
def Covers (sp : Array ℕ) (hi : ℕ) : Prop :=
  ∀ q, q.Prime → q * q < hi → ∃ i < sp.size, sp[i]! = q

lemma size_replicate (h : ℕ) : (ByteArray.mk (Array.replicate h (0 : UInt8))).size = h := by
  show (Array.replicate h (0 : UInt8)).size = h; simp

lemma size_sieveSeg (sp : Array ℕ) (B h : ℕ) : (sieveSeg sp B h).size = h := by
  unfold sieveSeg; rw [size_sieveLoop, size_replicate]

/-- **The segmented sieve is exact.** -/
theorem sieveSeg_spec (sp : Array ℕ) (B h : ℕ) (hs : Sorted sp) (hc : Covers sp (B + h))
    (i : ℕ) (hi : i < h) (h2 : 2 ≤ B + i) : (sieveSeg sp B h)[i]! = 0 ↔ (B + i).Prime := by
  constructor
  · intro h0
    by_contra hnp
    set m := B + i
    have hm1 : m ≠ 1 := by omega
    have hq := Nat.minFac_prime hm1
    have hsq : m.minFac * m.minFac ≤ m := by
      have := Nat.minFac_sq_le_self (by omega : 0 < m) hnp
      nlinarith [this]
    obtain ⟨i0, hi0, hq0⟩ := hc m.minFac hq (by omega)
    have := sieveLoop_marks sp B (B + h) 0 (ByteArray.mk (Array.replicate h 0)) hs
      (by rw [size_replicate]) i0 (Nat.zero_le _) hi0 (by rw [hq0]; exact hq.two_le)
      (by rw [hq0]; omega) m (by omega) (by omega) (by rw [hq0]; exact Nat.minFac_dvd m)
      (by rw [hq0]; exact hsq)
    unfold sieveSeg at h0
    rw [show m - B = i by omega] at this
    exact this h0
  · intro hp
    by_contra h0
    exact sieveSeg_inv sp B h i h0 hp

end Schoenfeld.PsiCert
