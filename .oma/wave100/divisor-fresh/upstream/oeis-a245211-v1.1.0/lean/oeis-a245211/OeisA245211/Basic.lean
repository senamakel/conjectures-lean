/-
Copyright (c) 2026 Mar Allen P. Sugui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mar Allen P. Sugui
-/

/-!
# OEIS A245211: Divisor-Count Moments of Proper Divisors and Basic Equivalences

Defines the arithmetic functions underlying sequence A245211 in the On-Line Encyclopedia of
Integer Sequences (Jaroslav Krizek, 2014):
- `tau n` (OEIS A000005): the number of positive divisors $\tau(n)$ of $n$.
- `sigma n` (OEIS A000203): the sum of positive divisors $\sigma(n)$ of $n$.
- `nTau n` (OEIS A038040): the product $n \cdot \tau(n)$.
- `fullMoment n` (OEIS A060640): the full divisor-count moment $S(n) = \sum_{d \mid n} d \cdot \tau(d)$.
- `a n` (OEIS A245211): the proper-divisor moment $a(n) = \sum_{d \mid n,\, d < n} d \cdot \tau(d)$.
- `cantileverDiff n` (OEIS A245212): the cantilever moment difference $n \cdot \tau(n) - a(n)$.

Proves equivalence between the summation primitives `sumUpTo` / `sumDiv` and explicit duplicate-free
divisor lists `divisors n` and `properDivisors n`, proves the OEIS identities
`fullMoment n = a n + n * tau n` and `cantileverDiff n = n * tau n - a n`, characterizes the
fixed-point predicate `IsFixedPoint n` ($a(n) = n \iff S(n) = n(\tau(n) + 1)$), and establishes
explicit refutation checks for $n = 0, 1, 2, 3, 4, 6, 9, 15, 25, 33, 71, 72$ alongside the
certified fixed point $a(21) = 21$.
-/

namespace OeisA245211

section SummationPrimitives

/-- Linear range sum `f (a + 1) + f (a + 2) + ... + f (a + len)` used to
    prove the additivity of the balanced binary-tree range sum. -/
def sumRangeLinear (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => sumRangeLinear f a len + f (a + len + 1)

theorem sumRangeLinear_split (f : Nat → Nat) (a len1 : Nat) :
    ∀ len2, sumRangeLinear f a (len1 + len2) =
      sumRangeLinear f a len1 + sumRangeLinear f (a + len1) len2
  | 0 => by simp [sumRangeLinear]
  | len2 + 1 => by
    have h : len1 + (len2 + 1) = (len1 + len2) + 1 := by omega
    rw [h, sumRangeLinear, sumRangeLinear, sumRangeLinear_split f a len1 len2]
    have hidx : a + (len1 + len2) + 1 = a + len1 + len2 + 1 := by omega
    rw [hidx]
    omega

/-- Balanced binary-tree range sum `f (a + 1) + ... + f (a + len)` with fuel `fuel`.
    Keep WHNF recursion depth $O(\log k)$ so kernel `decide` evaluates larger inputs
    without increasing `maxRecDepth`. -/
def sumRangeBin (f : Nat → Nat) : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | _, a, 1 => f (a + 1)
  | 0, a, len + 2 => sumRangeLinear f a (len + 2)
  | fuel + 1, a, len + 2 =>
    let half := (len + 2) / 2
    sumRangeBin f fuel a half + sumRangeBin f fuel (a + half) ((len + 2) - half)

theorem sumRangeBin_eq_sumRangeLinear (f : Nat → Nat) :
    ∀ fuel a len, sumRangeBin f fuel a len = sumRangeLinear f a len
  | 0, a, 0 => rfl
  | 0, a, 1 => by simp [sumRangeBin, sumRangeLinear]
  | 0, a, len + 2 => rfl
  | fuel + 1, a, 0 => rfl
  | fuel + 1, a, 1 => by simp [sumRangeBin, sumRangeLinear]
  | fuel + 1, a, len + 2 => by
    change sumRangeBin f fuel a ((len + 2) / 2) +
      sumRangeBin f fuel (a + (len + 2) / 2) ((len + 2) - (len + 2) / 2) =
      sumRangeLinear f a (len + 2)
    rw [sumRangeBin_eq_sumRangeLinear f fuel a ((len + 2) / 2)]
    rw [sumRangeBin_eq_sumRangeLinear f fuel (a + (len + 2) / 2) ((len + 2) - (len + 2) / 2)]
    have hsplit := sumRangeLinear_split f a ((len + 2) / 2) ((len + 2) - (len + 2) / 2)
    have hadd : (len + 2) / 2 + ((len + 2) - (len + 2) / 2) = len + 2 := by omega
    rw [hadd] at hsplit
    exact hsplit.symm

/-- Sum of `f 1 + f 2 + ... + f k` over `1 ≤ i ≤ k`. -/
def sumUpTo (f : Nat → Nat) (k : Nat) : Nat :=
  sumRangeBin f 16 0 k

theorem sumUpTo_eq_sumRangeLinear (f : Nat → Nat) (k : Nat) :
    sumUpTo f k = sumRangeLinear f 0 k :=
  sumRangeBin_eq_sumRangeLinear f 16 0 k

@[simp]
theorem sumUpTo_zero (f : Nat → Nat) : sumUpTo f 0 = 0 := rfl

@[simp]
theorem sumUpTo_succ (f : Nat → Nat) (k : Nat) :
    sumUpTo f (k + 1) = sumUpTo f k + f (k + 1) := by
  rw [sumUpTo_eq_sumRangeLinear, sumUpTo_eq_sumRangeLinear, sumRangeLinear]
  simp

/-- Decidable positive divisor test: `0 < d` and `d ∣ n`. -/
def dividesB (d n : Nat) : Bool :=
  0 < d && n % d == 0

theorem dividesB_eq_true (d n : Nat) :
    dividesB d n = true ↔ 0 < d ∧ d ∣ n := by
  unfold dividesB
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero]

theorem dividesB_eq_false (d n : Nat) :
    dividesB d n = false ↔ ¬ (0 < d ∧ d ∣ n) := by
  rw [← Bool.not_eq_true, dividesB_eq_true]

theorem dividesB_self {n : Nat} (hn : 0 < n) : dividesB n n = true := by
  rw [dividesB_eq_true]
  exact ⟨hn, Nat.dvd_refl n⟩

theorem dividesB_one (n : Nat) : dividesB 1 n = true := by
  rw [dividesB_eq_true]
  exact ⟨by decide, Nat.one_dvd n⟩

theorem dividesB_eq_false_of_gt {d n : Nat} (hn : 0 < n) (hgt : n < d) :
    dividesB d n = false := by
  rw [dividesB_eq_false]
  rintro ⟨_, hdvd⟩
  have hle := Nat.le_of_dvd hn hdvd
  omega

/-- Weighted sum over positive divisors `d` of `n` in `1 ≤ d ≤ k`. -/
def sumDivUpTo (n : Nat) (w : Nat → Nat) (k : Nat) : Nat :=
  sumUpTo (fun d => if dividesB d n then w d else 0) k

/-- Weighted sum over all positive divisors `d ∣ n` (`1 ≤ d ≤ n`). -/
def sumDiv (n : Nat) (w : Nat → Nat) : Nat :=
  sumDivUpTo n w n

/-- Weighted sum over all proper positive divisors `d ∣ n` (`1 ≤ d < n`). -/
def sumProperDiv (n : Nat) (w : Nat → Nat) : Nat :=
  sumDivUpTo n w (n - 1)

theorem sumDiv_eq_sumProperDiv_add {n : Nat} (hn : 0 < n) (w : Nat → Nat) :
    sumDiv n w = sumProperDiv n w + w n := by
  unfold sumDiv sumProperDiv sumDivUpTo
  cases n with
  | zero => omega
  | succ m =>
    simp [dividesB_self (Nat.succ_pos m)]

end SummationPrimitives

section ArithmeticFunctions

/-- Number of positive divisors $\tau(n)$ (OEIS A000005). -/
def tau (n : Nat) : Nat :=
  sumDiv n (fun _ => 1)

/-- Sum of positive divisors $\sigma(n)$ (OEIS A000203). -/
def sigma (n : Nat) : Nat :=
  sumDiv n (fun d => d)

/-- Product $n \cdot \tau(n)$ (OEIS A038040). -/
def nTau (n : Nat) : Nat :=
  n * tau n

/-- Full divisor-count moment $S(n) = \sum_{d \mid n} d \cdot \tau(d)$ (OEIS A060640). -/
def fullMoment (n : Nat) : Nat :=
  sumDiv n (fun d => d * tau d)

/-- Proper-divisor moment $a(n) = \sum_{d \mid n,\, d < n} d \cdot \tau(d)$ (OEIS A245211). -/
def a (n : Nat) : Nat :=
  sumProperDiv n (fun d => d * tau d)

/-- Cantilever moment difference $n \cdot \tau(n) - a(n)$ (OEIS A245212). -/
def cantileverDiff (n : Nat) : Int :=
  (nTau n : Int) - (a n : Int)

/-- Fixed-point predicate for OEIS A245211: $0 < n$ and $a(n) = n$. -/
def IsFixedPoint (n : Nat) : Prop :=
  0 < n ∧ a n = n

instance instDecidableIsFixedPoint (n : Nat) : Decidable (IsFixedPoint n) :=
  inferInstanceAs (Decidable (0 < n ∧ a n = n))

/-- Membership predicate for OEIS A245213: $0 < n$ and $\text{A245212}(n) < n$. -/
def IsInA245213 (n : Nat) : Prop :=
  0 < n ∧ cantileverDiff n < (n : Int)

instance instDecidableIsInA245213 (n : Nat) : Decidable (IsInA245213 n) :=
  inferInstanceAs (Decidable (0 < n ∧ cantileverDiff n < (n : Int)))

/-- Membership predicate for OEIS A245214: $0 < n$ and $\text{A245212}(n) < 0$ ($n \cdot \tau(n) < a(n)$). -/
def IsInA245214 (n : Nat) : Prop :=
  0 < n ∧ cantileverDiff n < 0

instance instDecidableIsInA245214 (n : Nat) : Decidable (IsInA245214 n) :=
  inferInstanceAs (Decidable (0 < n ∧ cantileverDiff n < 0))

/-- Krizek's first OEIS A245211 identity: $\text{A060640}(n) = \text{A245211}(n) + \text{A038040}(n)$ for $0 < n$. -/
theorem fullMoment_eq_a_add_nTau {n : Nat} (hn : 0 < n) :
    fullMoment n = a n + nTau n := by
  unfold fullMoment a nTau
  exact sumDiv_eq_sumProperDiv_add hn (fun d => d * tau d)

/-- Krizek's subtraction identity: $a(n) = S(n) - n \cdot \tau(n)$ for $0 < n$. -/
theorem a_eq_fullMoment_sub_nTau {n : Nat} (hn : 0 < n) :
    a n = fullMoment n - nTau n := by
  rw [fullMoment_eq_a_add_nTau hn, Nat.add_sub_cancel]

/-- Krizek's second OEIS A245211 identity: $(a(n) : \mathbb{Z}) = \text{A038040}(n) - \text{A245212}(n)$. -/
theorem a_int_eq_nTau_sub_cantileverDiff (n : Nat) :
    (a n : Int) = (nTau n : Int) - cantileverDiff n := by
  unfold cantileverDiff
  omega

/-- Equivalent characterization of OEIS A245214: $0 < n$ and $n \cdot \tau(n) < a(n)$. -/
theorem isInA245214_iff (n : Nat) :
    IsInA245214 n ↔ 0 < n ∧ nTau n < a n := by
  unfold IsInA245214 cantileverDiff
  omega

/-- Equivalent characterization of OEIS A245213: $0 < n$ and $n \cdot \tau(n) < a(n) + n$. -/
theorem isInA245213_iff (n : Nat) :
    IsInA245213 n ↔ 0 < n ∧ nTau n < a n + n := by
  unfold IsInA245213 cantileverDiff
  omega

/-- Every member of OEIS A245214 belongs to OEIS A245213 ($\text{A245214} \subseteq \text{A245213}$). -/
theorem isInA245213_of_isInA245214 {n : Nat} (h : IsInA245214 n) :
    IsInA245213 n := by
  rw [isInA245214_iff] at h
  rw [isInA245213_iff]
  exact ⟨h.1, by omega⟩

/-- Fixed-point characterization in terms of the full divisor moment $S(n)$ (OEIS A060640):
for $0 < n$, $a(n) = n$ if and only if $S(n) = n \cdot (\tau(n) + 1)$. -/
theorem a_eq_self_iff_fullMoment {n : Nat} (hn : 0 < n) :
    a n = n ↔ fullMoment n = n * (tau n + 1) := by
  rw [fullMoment_eq_a_add_nTau hn]
  unfold nTau
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem isFixedPoint_iff_fullMoment (n : Nat) :
    IsFixedPoint n ↔ 0 < n ∧ fullMoment n = n * (tau n + 1) := by
  unfold IsFixedPoint
  constructor
  · rintro ⟨hn, ha⟩
    exact ⟨hn, (a_eq_self_iff_fullMoment hn).mp ha⟩
  · rintro ⟨hn, hS⟩
    exact ⟨hn, (a_eq_self_iff_fullMoment hn).mpr hS⟩

end ArithmeticFunctions

section ExplicitDivisorLists

/-- List of positive divisors of `n` in `1 ≤ d ≤ k` in strictly increasing order. -/
def divisorsUpTo (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 =>
    if dividesB (k + 1) n then
      divisorsUpTo n k ++ [k + 1]
    else
      divisorsUpTo n k

/-- Duplicate-free list of all positive divisors of `n`. -/
def divisors (n : Nat) : List Nat :=
  divisorsUpTo n n

/-- Duplicate-free list of all proper positive divisors of `n`. -/
def properDivisors (n : Nat) : List Nat :=
  divisorsUpTo n (n - 1)

/-- Sum of `w d` over a list of divisors `ds`. -/
def sumList (ds : List Nat) (w : Nat → Nat) : Nat :=
  match ds with
  | [] => 0
  | d :: rest => w d + sumList rest w

theorem sumList_append (xs ys : List Nat) (w : Nat → Nat) :
    sumList (xs ++ ys) w = sumList xs w + sumList ys w := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih =>
    simp only [List.cons_append, sumList, ih, Nat.add_assoc]

theorem mem_divisorsUpTo_iff (n : Nat) :
    ∀ k d, d ∈ divisorsUpTo n k ↔ 1 ≤ d ∧ d ≤ k ∧ d ∣ n
  | 0, d => by
    simp [divisorsUpTo]
    omega
  | k + 1, d => by
    unfold divisorsUpTo
    split
    · next hdiv =>
      rw [List.mem_append, List.mem_singleton, mem_divisorsUpTo_iff n k d]
      have hdvd : 0 < k + 1 ∧ (k + 1) ∣ n := (dividesB_eq_true (k + 1) n).mp hdiv
      constructor
      · rintro (⟨h1, h2, h3⟩ | rfl)
        · exact ⟨h1, by omega, h3⟩
        · exact ⟨by omega, Nat.le_refl _, hdvd.2⟩
      · rintro ⟨h1, h2, h3⟩
        by_cases hlt : d ≤ k
        · exact Or.inl ⟨h1, hlt, h3⟩
        · have heq : d = k + 1 := by omega
          exact Or.inr heq
    · next hndiv =>
      rw [mem_divisorsUpTo_iff n k d]
      have hnot : ¬ (0 < k + 1 ∧ (k + 1) ∣ n) := by
        intro h
        have := (dividesB_eq_true (k + 1) n).mpr h
        rw [this] at hndiv
        contradiction
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        by_cases hlt : d ≤ k
        · exact ⟨h1, hlt, h3⟩
        · have heq : d = k + 1 := by omega
          subst heq
          exact False.elim (hnot ⟨by omega, h3⟩)

/-- Membership in `divisors n` is equivalent to `1 ≤ d ≤ n ∧ d ∣ n`. -/
theorem mem_divisors_iff (n d : Nat) :
    d ∈ divisors n ↔ 1 ≤ d ∧ d ≤ n ∧ d ∣ n :=
  mem_divisorsUpTo_iff n n d

/-- Membership in `properDivisors n` is equivalent to `1 ≤ d < n ∧ d ∣ n` for `0 < n`. -/
theorem mem_properDivisors_iff {n : Nat} (hn : 0 < n) (d : Nat) :
    d ∈ properDivisors n ↔ 1 ≤ d ∧ d < n ∧ d ∣ n := by
  unfold properDivisors
  rw [mem_divisorsUpTo_iff]
  omega

theorem divisorsUpTo_nodup (n : Nat) :
    ∀ k, (divisorsUpTo n k).Nodup
  | 0 => List.Pairwise.nil
  | k + 1 => by
    unfold divisorsUpTo
    split
    · rw [List.nodup_append]
      refine ⟨divisorsUpTo_nodup n k, List.Pairwise.cons (by simp) List.Pairwise.nil, ?_⟩
      intro d hd x hx
      rw [List.mem_singleton] at hx
      subst hx
      have hmem := (mem_divisorsUpTo_iff n k d).mp hd
      omega
    · exact divisorsUpTo_nodup n k

theorem divisors_nodup (n : Nat) : (divisors n).Nodup :=
  divisorsUpTo_nodup n n

theorem properDivisors_nodup (n : Nat) : (properDivisors n).Nodup :=
  divisorsUpTo_nodup n (n - 1)

theorem sumList_divisorsUpTo_eq (n : Nat) (w : Nat → Nat) :
    ∀ k, sumList (divisorsUpTo n k) w = sumDivUpTo n w k
  | 0 => rfl
  | k + 1 => by
    unfold divisorsUpTo sumDivUpTo
    rw [sumUpTo_succ]
    split
    · next hdiv =>
      rw [sumList_append, sumList_divisorsUpTo_eq n w k]
      rfl
    · next hndiv =>
      rw [sumList_divisorsUpTo_eq n w k]
      rfl

/-- Equivalence between `a n` (`sumProperDiv`) and the list sum over `properDivisors n`. -/
theorem a_eq_sumList_properDivisors (n : Nat) :
    a n = sumList (properDivisors n) (fun d => d * tau d) := by
  unfold a sumProperDiv properDivisors
  exact (sumList_divisorsUpTo_eq n (fun d => d * tau d) (n - 1)).symm

/-- Equivalence between `fullMoment n` (`sumDiv`) and the list sum over `divisors n`. -/
theorem fullMoment_eq_sumList_divisors (n : Nat) :
    fullMoment n = sumList (divisors n) (fun d => d * tau d) := by
  unfold fullMoment sumDiv divisors
  exact (sumList_divisorsUpTo_eq n (fun d => d * tau d) n).symm

theorem length_divisorsUpTo_eq (n : Nat) :
    ∀ k, (divisorsUpTo n k).length = sumDivUpTo n (fun _ => 1) k
  | 0 => rfl
  | k + 1 => by
    unfold divisorsUpTo sumDivUpTo
    rw [sumUpTo_succ]
    split
    · next hdiv =>
      rw [List.length_append, length_divisorsUpTo_eq n k]
      rfl
    · next hndiv =>
      rw [length_divisorsUpTo_eq n k]
      rfl

/-- Equivalence between `tau n` and `(divisors n).length`. -/
theorem tau_eq_length_divisors (n : Nat) :
    tau n = (divisors n).length := by
  unfold tau sumDiv divisors
  exact (length_divisorsUpTo_eq n n).symm

end ExplicitDivisorLists

section RefutationAndWitnessChecks

/-- `a 0 = 0`. -/
theorem a_0 : a 0 = 0 := by decide

/-- `tau 1 = 1`. -/
theorem tau_1 : tau 1 = 1 := by decide

/-- Refutation check: `n = 0` is not a fixed point of OEIS A245211 (`0 < n` fails). -/
theorem not_isFixedPoint_0 : ¬ IsFixedPoint 0 := by decide

/-- Refutation check: `n = 1` is not a fixed point (`a 1 = 0 ≠ 1`). -/
theorem not_isFixedPoint_1 : ¬ IsFixedPoint 1 := by decide

/-- Refutation check: the smallest prime `n = 2` is not a fixed point (`a 2 = 1 ≠ 2`). -/
theorem not_isFixedPoint_2 : ¬ IsFixedPoint 2 := by decide

/-- Refutation check: the smallest odd prime `n = 3` is not a fixed point (`a 3 = 1 ≠ 3`). -/
theorem not_isFixedPoint_3 : ¬ IsFixedPoint 3 := by decide

/-- Refutation check: the smallest composite `n = 4` is not a fixed point (`a 4 = 5 ≠ 4`). -/
theorem not_isFixedPoint_4 : ¬ IsFixedPoint 4 := by decide

/-- Refutation check: the smallest even semiprime `n = 6` is not a fixed point (`a 6 = 11 ≠ 6`). -/
theorem not_isFixedPoint_6 : ¬ IsFixedPoint 6 := by decide

/-- Refutation check: the odd prime square `n = 9` is not a fixed point (`a 9 = 7 ≠ 9`). -/
theorem not_isFixedPoint_9 : ¬ IsFixedPoint 9 := by decide

/-- Refutation check: the smallest odd semiprime `n = 15` is not a fixed point (`a 15 = 17 ≠ 15`). -/
theorem not_isFixedPoint_15 : ¬ IsFixedPoint 15 := by decide

/-- Refutation check: the odd prime square `n = 25` is not a fixed point (`a 25 = 11 ≠ 25`). -/
theorem not_isFixedPoint_25 : ¬ IsFixedPoint 25 := by decide

/-- Refutation check: the odd semiprime `n = 33` is not a fixed point (`a 33 = 29 ≠ 33`). -/
theorem not_isFixedPoint_33 : ¬ IsFixedPoint 33 := by decide

/-- Refutation check: `n = 71` is not in OEIS A245213 (`cantileverDiff 71 = 141 ≥ 71`). -/
theorem not_isInA245213_71 : ¬ IsInA245213 71 := by decide

/-- Refutation check: `n = 72` is in OEIS A245213 (`cantileverDiff 72 = 62 < 72`) but not in
OEIS A245214 (`cantileverDiff 72 = 62 ≥ 0`), separating A245213 from A245214. -/
theorem isInA245213_72 : IsInA245213 72 := by decide

theorem not_isInA245214_72 : ¬ IsInA245214 72 := by decide

/-- Certified fixed point: `n = 21` has proper divisors `[1, 3, 7]`, `a 21 = 21`, and satisfies
`IsFixedPoint 21`. -/
theorem properDivisors_21 : properDivisors 21 = [1, 3, 7] := by decide

theorem a_21 : a 21 = 21 := by decide

theorem isFixedPoint_21 : IsFixedPoint 21 := by decide

end RefutationAndWitnessChecks

end OeisA245211
