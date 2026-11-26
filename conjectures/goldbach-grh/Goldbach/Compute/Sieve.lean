import Mathlib
import GoldbachCheck

/-!
# Soundness of the odd-only segmented sieve

`sieve_spec`: byte `i < len` of `sieve lo len ps` is `0` exactly when some `p ∈ ps` divides
`x = lo + 2 i` with `3 p ≤ x` (for odd `lo` and a list `ps` of odd numbers `≥ 3`).

`prime_of_unmarked`: an unmarked odd `x ≥ 3` with `x ≤ B²` is prime when `ps` contains every
odd prime `≤ B`. `unmarked_of_prime`: an odd prime is never marked.
-/

namespace Goldbach.Check

/-! ### `markFrom` -/

theorem size_markFrom (p len : ℕ) (a : ByteArray) (j : ℕ) :
    (markFrom p len a j).size = a.size := by
  induction a, j using markFrom.induct p len with
  | case1 a j h ih => rw [markFrom, ite_eq_left h, ih, ByteArray.size_set!]
  | case2 a j h => rw [markFrom, ite_eq_right h]

theorem getElem!_markFrom (p len : ℕ) (a : ByteArray) (j : ℕ) (hp : 0 < p)
    (ha : a.size = len) (i : ℕ) :
    (markFrom p len a j)[i]! = if j ≤ i ∧ i < len ∧ p ∣ i - j then 0 else a[i]! := by
  induction a, j using markFrom.induct p len with
  | case1 a j h ih =>
    rw [markFrom, ite_eq_left h, ih (by rw [ByteArray.size_set!, ha]),
      ByteArray.getElem!_set! _ _ _ _ (by omega)]
    by_cases hij : j = i
    · subst hij
      have : ¬ (j + p ≤ j) := by omega
      simp [this, h.1]
    · rw [ite_eq_right hij]
      by_cases hle : j + p ≤ i
      · have e : i - j = (i - (j + p)) + p := by omega
        have hj : j ≤ i := by omega
        have hiff : p ∣ i - j ↔ p ∣ i - (j + p) := by rw [e, Nat.dvd_add_self_right]
        simp only [hle, hj, true_and, hiff]
      · have hnd : ¬ (j ≤ i ∧ i < len ∧ p ∣ i - j) := by
          rintro ⟨h1, -, h3⟩
          have hpos : 0 < i - j := by omega
          have := Nat.le_of_dvd hpos h3
          omega
        simp [hle, hnd]
  | case2 a j h =>
    rw [markFrom, ite_eq_right h]
    have hnd : ¬ (j ≤ i ∧ i < len ∧ p ∣ i - j) := by
      rintro ⟨h1, h2, -⟩
      exact h ⟨by omega, hp⟩
    simp [hnd]

/-! ### `firstIdx` -/

/-- The odd multiple of `p` that `firstIdx` points at. -/
def firstMul (lo p : ℕ) : ℕ :=
  let k := (max lo (3 * p) + p - 1) / p
  p * (if k % 2 = 0 then k + 1 else k)

theorem firstMul_spec {lo p : ℕ} (hp : Odd p) (hlo : Odd lo) :
    Odd (firstMul lo p) ∧ p ∣ firstMul lo p ∧ max lo (3 * p) ≤ firstMul lo p ∧
      lo + 2 * firstIdx lo p = firstMul lo p ∧
      ∀ m, Odd m → max lo (3 * p) ≤ p * m → firstMul lo p ≤ p * m := by
  have hp0 : 0 < p := hp.pos
  set s := max lo (3 * p) with hs
  set k₀ := (s + p - 1) / p with hk₀
  set k := (if k₀ % 2 = 0 then k₀ + 1 else k₀) with hk
  have hfm : firstMul lo p = p * k := rfl
  have hkodd : Odd k := by
    rw [hk]; split_ifs with h
    · exact Nat.odd_iff.mpr (by omega)
    · exact Nat.odd_iff.mpr (by omega)
  have hkk₀ : k₀ ≤ k := by rw [hk]; split_ifs <;> omega
  have hsk₀ : s ≤ p * k₀ := by
    have := Nat.div_add_mod (s + p - 1) p
    have := Nat.mod_lt (s + p - 1) hp0
    rw [← hk₀] at *
    omega
  have hsk : s ≤ p * k := le_trans hsk₀ (Nat.mul_le_mul_left p hkk₀)
  have hodd : Odd (p * k) := hp.mul hkodd
  have hlos : lo ≤ s := le_max_left _ _
  refine ⟨hfm ▸ hodd, hfm ▸ dvd_mul_right p k, hfm ▸ hsk, ?_, ?_⟩
  · show lo + 2 * ((p * (if ((max lo (3 * p)) + p - 1) / p % 2 = 0 then
      (max lo (3 * p) + p - 1) / p + 1 else (max lo (3 * p) + p - 1) / p) - lo) / 2) = p * k
    rw [← hs, ← hk₀, ← hk]
    obtain ⟨a, ha⟩ := hodd
    obtain ⟨b, hb⟩ := hlo
    omega
  · intro m hm hsm
    rw [hfm]
    apply Nat.mul_le_mul_left
    have hk₀m : k₀ ≤ m := by
      rw [hk₀]
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hp0]
      have : p * m = m * p := Nat.mul_comm _ _
      rw [Nat.succ_mul]
      omega
    rw [hk]
    split_ifs with h
    · have : m % 2 = 1 := Nat.odd_iff.mp hm
      rcases Nat.eq_or_lt_of_le hk₀m with h' | h'
      · rw [← h'] at this; omega
      · omega
    · exact hk₀m

/-! ### One marking pass -/

/-- The predicate that the sieve computes: some `p ∈ ps` divides `x` and `3 p ≤ x`. -/
def Marked (ps : List ℕ) (x : ℕ) : Prop := ∃ p ∈ ps, p ∣ x ∧ 3 * p ≤ x

instance (ps : List ℕ) : DecidablePred (Marked ps) := fun x => by
  unfold Marked; infer_instance

theorem marked_pass_iff {lo p i : ℕ} (hp : Odd p) (hlo : Odd lo) :
    (firstIdx lo p ≤ i ∧ p ∣ i - firstIdx lo p) ↔ (p ∣ lo + 2 * i ∧ 3 * p ≤ lo + 2 * i) := by
  obtain ⟨hfo, hfd, hfs, hfe, hfmin⟩ := firstMul_spec hp hlo
  set f := firstIdx lo p
  set M := firstMul lo p
  have hcop : Nat.Coprime p 2 := Nat.Coprime.symm ((Nat.coprime_two_left).mpr hp)
  constructor
  · rintro ⟨hfi, hd⟩
    have e : lo + 2 * i = M + 2 * (i - f) := by omega
    refine ⟨?_, ?_⟩
    · rw [e]; exact dvd_add hfd (Dvd.dvd.mul_left hd 2)
    · have : 3 * p ≤ M := le_trans (le_max_right _ _) hfs
      omega
  · rintro ⟨hd, h3⟩
    obtain ⟨m, hm⟩ := hd
    have hxodd : Odd (lo + 2 * i) := by
      obtain ⟨b, hb⟩ := hlo; exact ⟨b + i, by omega⟩
    have hmodd : Odd m := by
      rw [hm] at hxodd; exact (Nat.odd_mul.mp hxodd).2
    have hle : M ≤ p * m := hfmin m hmodd (by rw [← hm]; exact max_le (by omega) h3)
    have hfi : f ≤ i := by omega
    refine ⟨hfi, ?_⟩
    have h2 : p ∣ 2 * (i - f) := by
      have e : 2 * (i - f) = p * m - M := by omega
      rw [e]; exact Nat.dvd_sub (dvd_mul_right p m) hfd
    exact hcop.dvd_of_dvd_mul_left h2

/-! ### The sieve -/

theorem size_foldl_mark (lo len : ℕ) (ps : List ℕ) (a : ByteArray) :
    (ps.foldl (fun a p => markFrom p len a (firstIdx lo p)) a).size = a.size := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih => rw [List.foldl_cons, ih, size_markFrom]

theorem getElem!_foldl_mark (lo len : ℕ) (ps : List ℕ) (hlo : Odd lo)
    (hps : ∀ p ∈ ps, Odd p) (a : ByteArray) (ha : a.size = len) (i : ℕ) (hi : i < len) :
    (ps.foldl (fun a p => markFrom p len a (firstIdx lo p)) a)[i]! =
      if Marked ps (lo + 2 * i) then 0 else a[i]! := by
  induction ps generalizing a with
  | nil => simp [Marked]
  | cons p ps ih =>
    rw [List.foldl_cons, ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _
      (by rw [size_markFrom, ha])]
    have hpo := hps p List.mem_cons_self
    rw [getElem!_markFrom p len a _ hpo.pos ha]
    have hpass := marked_pass_iff (i := i) hpo hlo
    by_cases h1 : Marked ps (lo + 2 * i)
    · have : Marked (p :: ps) (lo + 2 * i) := by
        obtain ⟨q, hq, h⟩ := h1; exact ⟨q, List.mem_cons_of_mem _ hq, h⟩
      simp [h1, this]
    · by_cases h2 : p ∣ lo + 2 * i ∧ 3 * p ≤ lo + 2 * i
      · have : Marked (p :: ps) (lo + 2 * i) := ⟨p, List.mem_cons_self, h2⟩
        have h2' := hpass.mpr h2
        simp [h1, this, h2'.1, h2'.2, hi]
      · have : ¬ Marked (p :: ps) (lo + 2 * i) := by
          rintro ⟨q, hq, h⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact h2 h
          · exact h1 ⟨q, hq, h⟩
        have h2' : ¬ (firstIdx lo p ≤ i ∧ i < len ∧ p ∣ i - firstIdx lo p) := by
          rintro ⟨a1, -, a3⟩; exact h2 (hpass.mp ⟨a1, a3⟩)
        simp only [h1, this, ite_false]
        rw [ite_eq_right h2']

theorem size_mk_replicate (len : ℕ) : (⟨Array.replicate len 1⟩ : ByteArray).size = len := by
  show (Array.replicate len (1 : UInt8)).size = len
  simp

theorem getElem!_replicate_one (len i : ℕ) (hi : i < len) :
    (⟨Array.replicate len 1⟩ : ByteArray)[i]! = 1 := by
  have hi' : i < (⟨Array.replicate len 1⟩ : ByteArray).size := by
    show i < (Array.replicate len (1 : UInt8)).size
    simpa using hi
  rw [getElem!_pos (⟨Array.replicate len 1⟩ : ByteArray) i hi']
  show (Array.replicate len (1 : UInt8))[i]'(by simpa using hi) = 1
  simp

theorem sieve_spec (lo len : ℕ) (ps : List ℕ) (hlo : Odd lo) (hps : ∀ p ∈ ps, Odd p)
    (i : ℕ) (hi : i < len) :
    (sieve lo len ps)[i]! = if Marked ps (lo + 2 * i) then 0 else 1 := by
  rw [sieve, getElem!_foldl_mark lo len ps hlo hps _ (size_mk_replicate len) i hi,
    getElem!_replicate_one len i hi]

theorem sieve_eq_one_iff (lo len : ℕ) (ps : List ℕ) (hlo : Odd lo) (hps : ∀ p ∈ ps, Odd p)
    (i : ℕ) (hi : i < len) :
    (sieve lo len ps)[i]! = 1 ↔ ¬ Marked ps (lo + 2 * i) := by
  rw [sieve_spec lo len ps hlo hps i hi]
  split_ifs with h <;> simp [h]

theorem size_sieve (lo len : ℕ) (ps : List ℕ) : (sieve lo len ps).size = len := by
  rw [sieve, size_foldl_mark, size_mk_replicate]

/-! ### What an unmarked entry means -/

theorem prime_of_unmarked {ps : List ℕ} {B x : ℕ}
    (hcomp : ∀ q, q.Prime → Odd q → q ≤ B → q ∈ ps)
    (hx : Odd x) (h3 : 3 ≤ x) (hxB : x < (B + 1) * (B + 1)) (hu : ¬ Marked ps x) : x.Prime := by
  by_contra hnp
  have hx1 : x ≠ 1 := by omega
  set q := x.minFac
  have hq : q.Prime := Nat.minFac_prime hx1
  have hqx : q ∣ x := Nat.minFac_dvd x
  have hsq : q ^ 2 ≤ x := Nat.minFac_sq_le_self (by omega) hnp
  have hqodd : Odd q := Odd.of_dvd_nat hx hqx
  have hqB : q ≤ B := by
    by_contra h
    have : (B + 1) * (B + 1) ≤ q * q := Nat.mul_self_le_mul_self (by omega)
    rw [sq] at hsq; omega
  apply hu
  refine ⟨q, hcomp q hq hqodd hqB, hqx, ?_⟩
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases Nat.eq_or_lt_of_le this with h | h
    · rw [← h] at hqodd; exact absurd hqodd (by decide)
    · omega
  calc 3 * q ≤ q * q := Nat.mul_le_mul_right q hq3
    _ = q ^ 2 := (sq q).symm
    _ ≤ x := hsq

theorem unmarked_of_prime {ps : List ℕ} (hps : ∀ p ∈ ps, 3 ≤ p) {x : ℕ} (hx : x.Prime) :
    ¬ Marked ps x := by
  rintro ⟨p, hp, hd, h3⟩
  rcases (Nat.dvd_prime hx).mp hd with h | h
  · have := hps p hp; omega
  · subst h; have := hx.pos; omega

end Goldbach.Check
