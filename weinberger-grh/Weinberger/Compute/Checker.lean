import Weinberger.Elementary

/-!
# A computable checker for non-idoneal numbers, with a soundness proof

`okN n` holds when `n = 0`, when `n` is one of Euler's 65 numbers, or when the search finds
`u ≥ 3` and `1 ≤ a ≤ (u − 1)/2` with `u ∣ n + a²` and `u² < n + a²`. By
`Weinberger.not_isIdoneal_of_witness` the last case makes `n` non-idoneal. `checkFrom lo k`
checks `okN` on `[lo, lo + k)`. Separately, `repB n` searches every representation
`n = ab + bc + ca`, and `repB_of_rep` shows that it finds one if one exists; this is used to
check that the 65 numbers are idoneal.
-/

namespace Weinberger.Compute

open Idoneal

/-- Is there `a ∈ [1, k]` with `u ∣ n + a²` and `u² < n + a²`? -/
def anyA (n u : ℕ) : ℕ → Bool
  | 0 => false
  | a + 1 => ((n + (a + 1) * (a + 1)) % u == 0 && decide (u * u < n + (a + 1) * (a + 1)))
      || anyA n u a

/-- Try `u, u + 1, …, u + fuel − 1`, each with `a ∈ [1, (u − 1)/2]`. -/
def anyU (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | u, f + 1 => anyA n u ((u - 1) / 2) || anyU n (u + 1) f

/-- Search window for `u`: `u ∈ [3, 3 + 400)`. Below `10^8` the largest `u` needed is 113. -/
def hasRep (n : ℕ) : Bool := anyU n 3 400

/-- Per-`n` check. -/
def okN (n : ℕ) : Bool := n == 0 || hasRep n || decide (n ∈ knownIdonealNumbers)

/-- `checkFrom lo k` checks `okN n` for all `n ∈ [lo, lo + k)`. -/
def checkFrom : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, k + 1 => okN lo && checkFrom (lo + 1) k

theorem anyA_sound {n u : ℕ} : ∀ k, anyA n u k = true →
    ∃ a, 1 ≤ a ∧ a ≤ k ∧ u ∣ n + a * a ∧ u * u < n + a * a
  | 0, h => by simp [anyA] at h
  | k + 1, h => by
    simp only [anyA, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨k + 1, by omega, le_rfl, Nat.dvd_of_mod_eq_zero h1, h2⟩
    · obtain ⟨a, h1, h2, h3, h4⟩ := anyA_sound k h
      exact ⟨a, h1, by omega, h3, h4⟩

theorem anyU_sound {n : ℕ} : ∀ f u, anyU n u f = true →
    ∃ u', u ≤ u' ∧ anyA n u' ((u' - 1) / 2) = true
  | 0, u, h => by simp [anyU] at h
  | f + 1, u, h => by
    simp only [anyU, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨u, le_rfl, h⟩
    · obtain ⟨u', h1, h2⟩ := anyU_sound f (u + 1) h
      exact ⟨u', by omega, h2⟩

theorem hasRep_sound {n : ℕ} (h : hasRep n = true) : ¬ IsIdoneal n := by
  obtain ⟨u, hu, hA⟩ := anyU_sound 400 3 h
  obtain ⟨a, ha1, ha2, hdvd, hlt⟩ := anyA_sound _ hA
  exact not_isIdoneal_of_witness (by omega) (by omega) hdvd hlt

theorem okN_sound {n : ℕ} (h : okN n = true) (hn : IsIdoneal n) : n ∈ knownIdonealNumbers := by
  simp only [okN, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact absurd hn.1 (by omega)
  · exact absurd hn (hasRep_sound h)
  · exact h

theorem checkFrom_sound : ∀ (k lo : ℕ), checkFrom lo k = true →
    ∀ n, lo ≤ n → n < lo + k → okN n = true
  | 0, lo, _, n, h1, h2 => by omega
  | k + 1, lo, h, n, h1, h2 => by
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact checkFrom_sound k (lo + 1) h.2 n h1 (by omega)

theorem checkFrom_add : ∀ (a lo b : ℕ),
    checkFrom lo (a + b) = (checkFrom lo a && checkFrom (lo + a) b)
  | 0, lo, b => by simp [checkFrom]
  | a + 1, lo, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega, checkFrom, checkFrom, checkFrom_add a (lo + 1) b,
      Bool.and_assoc, show lo + 1 + a = lo + (a + 1) by omega]

theorem checkFrom_chunks (c : ℕ) :
    ∀ j, (∀ i < j, checkFrom (i * c) c = true) → checkFrom 0 (j * c) = true
  | 0, _ => by simp [checkFrom]
  | j + 1, h => by
    rw [Nat.succ_mul, checkFrom_add, checkFrom_chunks c j (fun i hi => h i (by omega)),
      Nat.zero_add, h j (by omega), Bool.and_self]

/-! ### The 65 numbers are idoneal -/

/-- Search every representation `n = ab + c(a + b)` with `0 < a < b < c`: for `a ≤ n` and
`b ≤ n / a` (forced by `ab < n`) the value of `c` is fixed by exact division. -/
def repB (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun a => (List.range (n / a + 1)).any fun b =>
    decide (0 < a) && decide (a < b) && decide (a * b < n) && (n - a * b) % (a + b) == 0 &&
      decide (b < (n - a * b) / (a + b))

theorem repB_of_rep {n a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h : n = a * b + b * c + a * c) : repB n = true := by
  have hsum : n - a * b = c * (a + b) := by
    have : n = a * b + c * (a + b) := by rw [h]; ring
    omega
  have hpos : 0 < a + b := by omega
  have hc : (n - a * b) / (a + b) = c := by rw [hsum]; exact Nat.mul_div_cancel _ hpos
  have habn : a * b < n := by
    have : 0 < b * c := Nat.mul_pos (by omega) (by omega)
    omega
  have han : a ≤ n := le_trans (Nat.le_mul_of_pos_right a (by omega)) habn.le
  have hbn : b ≤ n / a := (Nat.le_div_iff_mul_le ha).2 (by nlinarith)
  simp only [repB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  refine ⟨a, by omega, b, by omega, ⟨⟨⟨⟨ha, hab⟩, habn⟩, ?_⟩, by rw [hc]; exact hbc⟩⟩
  rw [hsum]; exact Nat.mul_mod_left _ _

theorem isIdoneal_of_repB {n : ℕ} (hn : 0 < n) (h : repB n = false) : IsIdoneal n := by
  refine ⟨hn, ?_⟩
  rintro ⟨a, b, c, ha, hab, hbc, he⟩
  rw [repB_of_rep ha hab hbc he] at h
  exact Bool.noConfusion h

end Weinberger.Compute
