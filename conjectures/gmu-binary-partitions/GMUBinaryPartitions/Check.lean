import GMUBinaryPartitions.Series

/-!
# A checker for `b m n`, proved sound

`bList m N L` is the list of the first `L + 1` coefficients of `truncatedSeries m N`, computed
by multiplying `1` by `∑_j X^{2^i j}` (`m` times for each `i < N`). One multiplication by
`∑_j X^{d j}` is the transform `r(n) = l(n) + r(n − d)`, which `stepAux` carries out in blocks of
`d` entries. `bList_sound` proves that entry `n ≤ L` is `b m n` when `L < 2^N`. The lists hold
natural numbers so that the kernel's GMP arithmetic does the additions.
-/

namespace GMU

open PowerSeries

/-- Entry `n` of a list, `0` past its end. -/
def get0 : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: l, n + 1 => get0 l n

/-- Add `a` entrywise to the front of `l`; the result has the length of `l`. -/
def addPre : List ℕ → List ℕ → List ℕ
  | [], l => l
  | _ :: _, [] => []
  | x :: a, y :: l => (x + y) :: addPre a l

/-- `r(n) = l(n) + r(n − d)`, a block of `d` entries at a time (`f` is fuel). -/
def stepAux (d : ℕ) : ℕ → List ℕ → List ℕ
  | 0, l => l
  | _ + 1, [] => []
  | f + 1, x :: l =>
    (x :: l).take d ++ stepAux d f (addPre ((x :: l).take d) ((x :: l).drop d))

/-- `k` multiplications by `∑_j X^{d j}`. -/
def iterPow (d F : ℕ) : ℕ → List ℕ → List ℕ
  | 0, l => l
  | k + 1, l => iterPow d F k (stepAux d F l)

/-- Multiply by `∏_{i<N} (∑_j X^{2^i j})^m`. -/
def coeffList (m F : ℕ) (l : List ℕ) : ℕ → List ℕ
  | 0 => l
  | N + 1 => iterPow (2 ^ N) F m (coeffList m F l N)

/-- The first `L + 1` coefficients of `truncatedSeries m N`. -/
def bList (m N L : ℕ) : List ℕ := coeffList m (L + 1) (1 :: List.replicate L 0) N

/-! ### List lemmas -/

theorem get0_take (l : List ℕ) (d n : ℕ) (h : n < d) : get0 (l.take d) n = get0 l n := by
  induction l generalizing d n with
  | nil => simp [get0]
  | cons x l ih =>
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    cases n with
    | zero => simp [get0]
    | succ n => simp only [List.take_succ_cons, get0]; exact ih d n (by omega)

theorem get0_drop (l : List ℕ) (d j : ℕ) : get0 (l.drop d) j = get0 l (d + j) := by
  induction l generalizing d with
  | nil => simp [get0]
  | cons x l ih =>
    cases d with
    | zero => simp
    | succ d => simp only [List.drop_succ_cons, get0, ih]; congr 1; omega

theorem get0_append_left (a c : List ℕ) (n : ℕ) (h : n < a.length) :
    get0 (a ++ c) n = get0 a n := by
  induction a generalizing n with
  | nil => simp at h
  | cons x a ih =>
    cases n with
    | zero => simp [get0]
    | succ n => simp only [List.cons_append, get0]; exact ih n (by simp at h; omega)

theorem get0_append_right (a c : List ℕ) (n : ℕ) (h : a.length ≤ n) :
    get0 (a ++ c) n = get0 c (n - a.length) := by
  induction a generalizing n with
  | nil => simp
  | cons x a ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.cons_append, get0, List.length_cons]
      rw [ih n (by simp at h; omega)]; congr 1

theorem length_addPre (a l : List ℕ) : (addPre a l).length = l.length := by
  induction a generalizing l with
  | nil => simp [addPre]
  | cons x a ih => cases l <;> simp [addPre, ih]

theorem get0_addPre (a l : List ℕ) (j : ℕ) (h : j < l.length) :
    get0 (addPre a l) j = get0 a j + get0 l j := by
  induction a generalizing l j with
  | nil => simp [addPre, get0]
  | cons x a ih =>
    cases l with
    | nil => simp at h
    | cons y l =>
      cases j with
      | zero => simp [addPre, get0]
      | succ j => simp only [addPre, get0]; exact ih l j (by simp at h; omega)

theorem get0_of_length_le (a : List ℕ) (j : ℕ) (h : a.length ≤ j) : get0 a j = 0 := by
  induction a generalizing j with
  | nil => simp [get0]
  | cons x a ih =>
    cases j with
    | zero => simp at h
    | succ j => simp only [get0]; exact ih j (by simp at h; omega)

theorem length_stepAux (d : ℕ) (hd : 0 < d) (f : ℕ) (l : List ℕ) :
    (stepAux d f l).length = l.length := by
  induction f generalizing l with
  | zero => rfl
  | succ f ih =>
    cases l with
    | nil => simp [stepAux]
    | cons x l =>
      simp only [stepAux, List.length_append, ih, length_addPre, List.length_take,
        List.length_drop]
      omega

/-- `stepAux` computes `r(n) = l(n) + r(n − d)`: any `c` satisfying this recursion on the
indices of `l` is what it returns. -/
theorem get0_stepAux (d : ℕ) (hd : 0 < d) (f : ℕ) (l : List ℕ) (hf : l.length ≤ f)
    (c : ℕ → ℕ) (hc : ∀ n < l.length, c n = get0 l n + if d ≤ n then c (n - d) else 0) :
    ∀ n < l.length, get0 (stepAux d f l) n = c n := by
  induction f generalizing l c with
  | zero => intro n hn; omega
  | succ f ih =>
    intro n hn
    cases l with
    | nil => simp at hn
    | cons x l =>
      set L := x :: l with hL
      have hlen : (L.take d).length = min d L.length := List.length_take
      simp only [stepAux]
      rw [← hL]
      by_cases hnd : n < d
      · rw [get0_append_left _ _ _ (by rw [hlen]; omega), get0_take _ _ _ hnd, hc n hn,
          if_neg (by omega), add_zero]
      · have hdl : d ≤ L.length := by omega
        rw [get0_append_right _ _ _ (by rw [hlen]; omega), hlen, min_eq_left hdl]
        have hl' : (addPre (L.take d) (L.drop d)).length = L.length - d := by
          rw [length_addPre, List.length_drop]
        refine ih (addPre (L.take d) (L.drop d)) (by rw [hl']; simp [hL] at hf ⊢; omega)
          (fun j => c (d + j)) ?_ (n - d) (by rw [hl']; omega) |>.trans (by congr 1; omega)
        intro j hj
        rw [hl'] at hj
        rw [get0_addPre _ _ _ (by rw [List.length_drop]; omega), get0_drop,
          hc (d + j) (by omega), if_pos (by omega), show d + j - d = j by omega]
        by_cases hjd : j < d
        · rw [get0_take _ _ _ hjd, if_neg (by omega), add_zero, hc j (by omega),
            if_neg (by omega), add_zero, add_comm]
        · rw [get0_of_length_le _ _ (by rw [hlen]; omega), zero_add, if_pos (by omega),
            show d + (j - d) = j by omega]

/-! ### Soundness against the series -/

/-- A list `l` lists the first `l.length` coefficients of `A`. -/
def Represents (l : List ℕ) (A : PowerSeries ℤ) : Prop :=
  ∀ n < l.length, ((get0 l n : ℕ) : ℤ) = coeff n A

theorem coeff_mul_geomPow2 (A : PowerSeries ℤ) (i n : ℕ) :
    coeff n (A * geomPow2 i) =
      coeff n A + if 2 ^ i ≤ n then coeff (n - 2 ^ i) (A * geomPow2 i) else 0 := by
  conv_lhs => rw [geomPow2_eq i]
  rw [mul_add, mul_one, map_add, mul_left_comm, coeff_X_pow_mul']

theorem coeff_mul_geomPow2_nonneg (A : PowerSeries ℤ) (i : ℕ) (hA : ∀ n, 0 ≤ coeff n A) :
    ∀ n, 0 ≤ coeff n (A * geomPow2 i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [coeff_mul_geomPow2]
    split_ifs with h
    · exact add_nonneg (hA n) (ih _ (by have := Nat.pow_pos (n := i) (by norm_num : 0 < 2); omega))
    · simpa using hA n

theorem represents_stepAux (i F : ℕ) (l : List ℕ) (hF : l.length ≤ F) (A : PowerSeries ℤ)
    (hA : ∀ n, 0 ≤ coeff n A) (hl : Represents l A) :
    Represents (stepAux (2 ^ i) F l) (A * geomPow2 i) ∧
      (stepAux (2 ^ i) F l).length = l.length := by
  have hd : 0 < 2 ^ i := Nat.pow_pos (by norm_num)
  have hlen := length_stepAux _ hd F l
  refine ⟨?_, hlen⟩
  intro n hn
  rw [hlen] at hn
  have hnn := coeff_mul_geomPow2_nonneg A i hA
  rw [get0_stepAux _ hd F l hF (fun n => (coeff n (A * geomPow2 i)).toNat) ?_ n hn]
  · exact Int.toNat_of_nonneg (hnn n)
  · intro n hn
    have h1 := coeff_mul_geomPow2 A i n
    rw [← hl n hn] at h1
    apply Int.ofNat.inj
    push_cast
    rw [Int.toNat_of_nonneg (hnn n), h1]
    split_ifs
    · push_cast; rw [Int.toNat_of_nonneg (hnn _)]
    · simp

theorem represents_iterPow (i F : ℕ) (k : ℕ) (l : List ℕ) (hF : l.length ≤ F)
    (A : PowerSeries ℤ) (hA : ∀ n, 0 ≤ coeff n A) (hl : Represents l A) :
    Represents (iterPow (2 ^ i) F k l) (A * geomPow2 i ^ k) ∧
      (iterPow (2 ^ i) F k l).length = l.length ∧ ∀ n, 0 ≤ coeff n (A * geomPow2 i ^ k) := by
  induction k generalizing l A with
  | zero => simpa [iterPow] using ⟨hl, hA⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := represents_stepAux i F l hF A hA hl
    obtain ⟨h3, h4, h5⟩ := ih (stepAux (2 ^ i) F l) (by rw [h2]; exact hF) (A * geomPow2 i)
      (coeff_mul_geomPow2_nonneg A i hA) h1
    refine ⟨?_, by simp only [iterPow]; rw [h4, h2], ?_⟩
    · simp only [iterPow]; rwa [pow_succ', ← mul_assoc]
    · rwa [pow_succ', ← mul_assoc]

theorem represents_coeffList (m F : ℕ) (l : List ℕ) (hF : l.length ≤ F) (A : PowerSeries ℤ)
    (hA : ∀ n, 0 ≤ coeff n A) (hl : Represents l A) (N : ℕ) :
    Represents (coeffList m F l N) (A * truncatedSeries m N) ∧
      (coeffList m F l N).length = l.length ∧ ∀ n, 0 ≤ coeff n (A * truncatedSeries m N) := by
  induction N with
  | zero => simpa [coeffList, truncatedSeries] using ⟨hl, hA⟩
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨h4, h5, h6⟩ := represents_iterPow N F m (coeffList m F l N) (by rw [h2]; exact hF)
      _ h3 h1
    have e : A * truncatedSeries m (N + 1) = A * truncatedSeries m N * geomPow2 N ^ m := by
      rw [truncatedSeries, Finset.prod_range_succ, ← truncatedSeries, mul_assoc]
    rw [e]
    exact ⟨h4, by simp only [coeffList]; rw [h5, h2], h6⟩

theorem represents_one (L : ℕ) : Represents (1 :: List.replicate L 0) 1 := by
  intro n hn
  rw [coeff_one]
  cases n with
  | zero => simp [get0]
  | succ n =>
    simp only [get0, Nat.succ_ne_zero, if_false]
    have : ∀ (L n : ℕ), get0 (List.replicate L 0) n = 0 := by
      intro L; induction L with
      | zero => intro n; simp [get0]
      | succ L ih => intro n; cases n <;> simp [List.replicate_succ, get0, ih]
    simp [this]

/-- **Soundness of the checker.** Entry `n ≤ L` of `bList m N L` is `b m n` when `L < 2^N`. -/
theorem bList_sound (m N L n : ℕ) (hL : L < 2 ^ N) (hn : n ≤ L) :
    ((get0 (bList m N L) n : ℕ) : ℤ) = b m n := by
  obtain ⟨h1, -, -⟩ := represents_coeffList m (L + 1) (1 :: List.replicate L 0) (by simp) 1
    (fun n => by rw [coeff_one]; split_ifs <;> norm_num) (represents_one L) N
  rw [one_mul] at h1
  rw [bList, h1 n (by simp; omega), coeff_truncatedSeries m n N (by omega)]

end GMU
