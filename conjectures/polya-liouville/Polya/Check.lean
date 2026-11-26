import Polya.Identities

/-!
# A checker for `M(x)` and `L(x)`, proved sound

The trusted computation is a check of tables, not the computation that fills them.

* `blockSum f x n` evaluates `∑_{k=n}^{x} f ⌊x/k⌋` in `O(√x)` steps, grouping the `k` on which
  `⌊x/k⌋` is constant (`blockSum_eq`).
* A candidate for `M` is any function `f : ℕ → ℤ`, read here from two arrays (`tableFn`): `f y`
  for `y ≤ T`, and `f ⌊X/a⌋` for `⌊X/a⌋ > T`.
* `tablesOK X T f` checks the identity `∑_{k=1}^{y} f ⌊y/k⌋ = 1` at every `y` of the set
  `V = {1 ≤ y ≤ T} ∪ {⌊X/a⌋ : a ≥ 1}`. `V` is closed under `y ↦ ⌊y/k⌋`, and the identity
  determines `M` (`sum_mertens_div`), so a passing check forces `f = M` on `V` (`tables_sound`),
  whatever arrays are supplied.
* `L(X) = ∑_{d ≤ √X} M(⌊X/d²⌋)` (`liouvilleSum_eq_sum_mertens`) and every `⌊X/d²⌋` lies in `V`.

The arrays are filled by `buildSmall` and `buildBig`, the usual `O(X^{3/4})` recursion. Nothing
about them is proved and nothing needs to be: the check is run on whatever they return.
-/

namespace Polya.Check

open Finset

/-! ## Block sums -/

theorem le_div_div {x n : ℕ} (h : n ≤ x) : n ≤ x / (x / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hq : 0 < x / n := Nat.div_pos h hn
  rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm]
  exact Nat.mul_div_le x n

/-- `blockSum f x n = ∑_{k=n}^{x} f ⌊x/k⌋`, summed over the blocks `[n, ⌊x/⌊x/n⌋⌋]` on which
`⌊x/k⌋` is constant. -/
def blockSum (f : ℕ → ℤ) (x n : ℕ) : ℤ :=
  if h : x < n then 0 else
    ((x / (x / n) + 1 - n : ℕ) : ℤ) * f (x / n) + blockSum f x (x / (x / n) + 1)
termination_by x + 1 - n
decreasing_by
  have := le_div_div (Nat.le_of_not_lt h)
  omega

theorem Icc_eq_Ico (a b : ℕ) : Icc a b = Ico a (b + 1) := by
  ext k; simp only [mem_Icc, mem_Ico]; omega

/-- On `[n, ⌊x/⌊x/n⌋⌋]` the quotient `⌊x/k⌋` is constant. -/
theorem div_eq_of_mem_block {x n k : ℕ} (hnx : n ≤ x) (hnk : n ≤ k) (hk : k ≤ x / (x / n)) :
    x / k = x / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.div_zero] at hk
    rw [Nat.le_zero.1 hk]
  have hk0 : 0 < k := lt_of_lt_of_le hn hnk
  have hq : 0 < x / n := Nat.div_pos hnx hn
  apply le_antisymm
  · exact Nat.div_le_div_left hnk hn
  · rw [Nat.le_div_iff_mul_le hk0, Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hq).1 hk

theorem blockSum_eq (f : ℕ → ℤ) (x n : ℕ) :
    blockSum f x n = ∑ k ∈ Icc n x, f (x / k) := by
  rw [blockSum]
  split_ifs with h
  · rw [Icc_eq_empty (by omega), sum_empty]
  · have hnx : n ≤ x := Nat.le_of_not_lt h
    have h1 := le_div_div hnx
    have h2 : x / (x / n) ≤ x := Nat.div_le_self _ _
    rw [blockSum_eq f x (x / (x / n) + 1), Icc_eq_Ico, Icc_eq_Ico,
      ← sum_Ico_consecutive _ (show n ≤ x / (x / n) + 1 by omega) (show x / (x / n) + 1 ≤ x + 1 by omega)]
    congr 1
    rw [sum_congr rfl (g := fun _ => f (x / n)), sum_const, Nat.card_Ico, nsmul_eq_mul]
    intro k hk
    rw [mem_Ico] at hk
    rw [div_eq_of_mem_block hnx hk.1 (by omega)]
termination_by x + 1 - n
decreasing_by
  omega

/-! ## Loops -/

/-- `allBelow p n` is `true` when `p k` holds for every `k < n` (a tail-recursive loop). -/
def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => if p n then allBelow p n else false

theorem allBelow_iff (p : ℕ → Bool) (n : ℕ) : allBelow p n = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow]
    split_ifs with h
    · rw [ih]
      constructor
      · intro H k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact H k hk
        · exact h
      · intro H k hk
        exact H k (Nat.lt_succ_of_lt hk)
    · simp only [Bool.false_eq_true, false_iff, not_forall]
      exact ⟨n, Nat.lt_succ_self n, h⟩

/-- `sqSum f X D = ∑_{d=1}^{D} f ⌊X/d²⌋`. -/
def sqSum (f : ℕ → ℤ) (X : ℕ) : ℕ → ℤ
  | 0 => 0
  | d + 1 => f (X / ((d + 1) * (d + 1))) + sqSum f X d

theorem sqSum_eq (f : ℕ → ℤ) (X D : ℕ) :
    sqSum f X D = ∑ d ∈ Icc 1 D, f (X / (d * d)) := by
  induction D with
  | zero => simp [sqSum]
  | succ D ih =>
    rw [sqSum, ih, sum_Icc_succ_top (by omega), add_comm]

/-! ## The table check and its soundness -/

/-- The candidate for `M` read from the tables: `small[q]` for `q ≤ T`, `big[⌊X/q⌋]` above. -/
def tableFn (X T : ℕ) (small big : Array ℤ) (q : ℕ) : ℤ :=
  if q ≤ T then small.getD q 0 else big.getD (X / q) 0

/-- `∑_{k=1}^{y} f ⌊y/k⌋ = 1`. -/
def identityOK (f : ℕ → ℤ) (y : ℕ) : Bool :=
  blockSum f y 1 == 1

/-- The identity at every `y ≤ T` and at every `⌊X/a⌋` with `1 ≤ a ≤ ⌊X/(T+1)⌋`. -/
def tablesOK (X T : ℕ) (f : ℕ → ℤ) : Bool :=
  allBelow (fun y => y == 0 || identityOK f y) (T + 1) &&
    allBelow (fun a => a == 0 || identityOK f (X / a)) (X / (T + 1) + 1)

/-- The set `V` on which the tables are checked. -/
def InV (X T y : ℕ) : Prop :=
  1 ≤ y ∧ (y ≤ T ∨ ∃ a, X / a = y)

theorem identity_of_tablesOK {X T : ℕ} {f : ℕ → ℤ} (h : tablesOK X T f = true) {y : ℕ}
    (hy : InV X T y) : ∑ k ∈ Icc 1 y, f (y / k) = 1 := by
  rw [← blockSum_eq]
  simp only [tablesOK, Bool.and_eq_true, allBelow_iff] at h
  have key : identityOK f y = true := by
    rcases Nat.lt_or_ge T y with hT | hT
    · obtain ⟨a, rfl⟩ := hy.2.resolve_left (by omega)
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hy
        exact absurd hy.1 (by omega)
      have haA : a < X / (T + 1) + 1 := by
        have : a ≤ X / (T + 1) := by
          rw [Nat.le_div_iff_mul_le (Nat.succ_pos T), Nat.mul_comm]
          have h3 := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero ha)).1 (show T + 1 ≤ X / a by omega)
          exact h3
        omega
      have := h.2 a haA
      simpa [ha] using this
    · have := h.1 y (by omega)
      have hy0 : y ≠ 0 := by have := hy.1; omega
      simpa [hy0] using this
  simpa [identityOK] using key

/-- A passing check forces the tables to agree with `M` on `V`. -/
theorem tables_sound {X T : ℕ} {f : ℕ → ℤ} (h : tablesOK X T f = true) :
    ∀ y, InV X T y → f y = mertens y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hy
  have hy1 : 1 ≤ y := hy.1
  have hf := identity_of_tablesOK h hy
  have hM := sum_mertens_div hy1
  rw [Icc_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)] at hf hM
  have hrest : ∑ k ∈ Ico (1 + 1) (y + 1), f (y / k) = ∑ k ∈ Ico (1 + 1) (y + 1), mertens (y / k) := by
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Ico] at hk
    apply ih
    · exact Nat.div_lt_self (by omega) (by omega)
    · refine ⟨Nat.div_pos (by omega) (by omega), ?_⟩
      rcases hy.2 with hT | ⟨a, rfl⟩
      · exact Or.inl (le_trans (Nat.div_le_self _ _) hT)
      · exact Or.inr ⟨a * k, (Nat.div_div_eq_div_mul X a k).symm⟩
  rw [hrest, Nat.div_one] at hf
  rw [Nat.div_one] at hM
  omega

/-! ## The two checks -/

/-- `M(X) = target`, read off checked tables. -/
def mertensCheck (X T : ℕ) (small big : Array ℤ) (target : ℤ) : Bool :=
  tablesOK X T (tableFn X T small big) && tableFn X T small big X == target

theorem mertensCheck_sound {X T : ℕ} {small big : Array ℤ} {target : ℤ}
    (h : mertensCheck X T small big target = true) (hX : 1 ≤ X) : mertens X = target := by
  simp only [mertensCheck, Bool.and_eq_true, beq_iff_eq] at h
  rw [← tables_sound h.1 X ⟨hX, Or.inr ⟨1, Nat.div_one X⟩⟩]
  exact h.2

/-- `L(X) = target`, as `∑_{d ≤ √X} M(⌊X/d²⌋)` read off checked tables. -/
def liouvilleCheck (X T : ℕ) (small big : Array ℤ) (target : ℤ) : Bool :=
  tablesOK X T (tableFn X T small big) && sqSum (tableFn X T small big) X (Nat.sqrt X) == target

theorem liouvilleCheck_sound {X T : ℕ} {small big : Array ℤ} {target : ℤ}
    (h : liouvilleCheck X T small big target = true) : liouvilleSum X = target := by
  simp only [liouvilleCheck, Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.2, sqSum_eq, liouvilleSum_eq_sum_mertens]
  refine sum_congr rfl fun d hd => ?_
  rw [mem_Icc] at hd
  refine (tables_sound h.1 _ ⟨Nat.div_pos (Nat.le_sqrt.1 hd.2) (Nat.mul_pos hd.1 hd.1),
    Or.inr ⟨d * d, rfl⟩⟩).symm

/-! ## Filling the tables (untrusted)

The usual recursion `M(y) = 1 − ∑_{k=2}^{y} M(⌊y/k⌋)`, first for `y ≤ T` in increasing order, then
for `y = ⌊X/a⌋` with `a` decreasing. No property of these functions is used: the check above runs
on whatever they return. -/

def buildSmall (T : ℕ) : Array ℤ := Id.run do
  let mut s : Array ℤ := Array.replicate (T + 1) 0
  for y in [1:T + 1] do
    let v := 1 - blockSum (fun q => s.getD q 0) y 2
    s := s.set! y v
  return s

def buildBig (X T : ℕ) (small : Array ℤ) : Array ℤ := Id.run do
  let A := X / (T + 1)
  let mut b : Array ℤ := Array.replicate (A + 1) 0
  for i in [0:A] do
    let a := A - i
    let v := 1 - blockSum (tableFn X T small b) (X / a) 2
    b := b.set! a v
  return b

/-- Fill the tables with `T = ⌊√X⌋` and check `M(X) = target`. -/
def runMertens (X : ℕ) (target : ℤ) : Bool :=
  let T := Nat.sqrt X
  let s := buildSmall T
  mertensCheck X T s (buildBig X T s) target

/-- Fill the tables with `T = ⌊√X⌋` and check `L(X) = target`. -/
def runLiouville (X : ℕ) (target : ℤ) : Bool :=
  let T := Nat.sqrt X
  let s := buildSmall T
  liouvilleCheck X T s (buildBig X T s) target

theorem runMertens_sound {X : ℕ} {target : ℤ} (h : runMertens X target = true) (hX : 1 ≤ X) :
    mertens X = target :=
  mertensCheck_sound h hX

theorem runLiouville_sound {X : ℕ} {target : ℤ} (h : runLiouville X target = true) :
    liouvilleSum X = target :=
  liouvilleCheck_sound h

end Polya.Check
