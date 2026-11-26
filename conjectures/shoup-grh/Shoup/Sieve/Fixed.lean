import Mathlib

/-!
# Certified fixed-point upper bounds

A natural number `x` stands for the real `x / D`, `D = 2^48`. The operations below round so
that their results are upper (or, for `lowSum`, lower) bounds for the exact real values; each
comes with a soundness lemma. They are used to check a large table of sieve parameters by
`decide`, so they are written with plain structural recursion.

* `mulU`: `(x/D)(y/D) ≤ mulU x y / D`;
* `expU`: `exp(x/D) ≤ expU x / D` for `x ≤ 16 D` (Taylor at `x/16`, then four squarings);
* `lowSum`: `lowSum c 12 / D ≤ exp(c/D)`, so `a D ≤ b · lowSum c 12` gives `log(a/b) ≤ c/D`.
-/

namespace Shoup.Fixed

open Finset

/-- The scale `2^48`. -/
@[irreducible] def Dn : ℕ := 2 ^ 48

lemma Dn_eq : Dn = 2 ^ 48 := by unfold Dn; rfl

lemma Dn_pos : 0 < Dn := by rw [Dn_eq]; positivity

/-- Ceiling division. -/
def cdiv (x y : ℕ) : ℕ := (x + y - 1) / y

lemma le_cdiv_mul (x y : ℕ) (hy : 0 < y) : x ≤ cdiv x y * y := by
  unfold cdiv
  have h := Nat.div_add_mod (x + y - 1) y
  have h2 := Nat.mod_lt (x + y - 1) hy
  have : y * ((x + y - 1) / y) = (x + y - 1) / y * y := Nat.mul_comm _ _
  omega

lemma real_le_cdiv (x y : ℕ) (hy : 0 < y) : (x : ℝ) / y ≤ (cdiv x y : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hy)]
  exact_mod_cast le_cdiv_mul x y hy

/-- The real value `x / D`. -/
noncomputable def r (x : ℕ) : ℝ := (x : ℝ) / Dn

lemma r_nonneg (x : ℕ) : 0 ≤ r x := by unfold r; positivity

lemma r_mono {x y : ℕ} (h : x ≤ y) : r x ≤ r y := by
  unfold r; gcongr

lemma r_Dn : r Dn = 1 := by unfold r; have := Dn_pos; field_simp

lemma r_add (x y : ℕ) : r (x + y) = r x + r y := by unfold r; push_cast; ring

lemma r_sub {x y : ℕ} (h : y ≤ x) : r (x - y) = r x - r y := by
  unfold r; rw [Nat.cast_sub h]; ring

/-- Rounded-up product. -/
def mulU (x y : ℕ) : ℕ := cdiv (x * y) Dn

lemma mulU_ge (x y : ℕ) : r x * r y ≤ r (mulU x y) := by
  unfold r mulU
  have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
  have h := real_le_cdiv (x * y) Dn Dn_pos
  push_cast at h
  calc (x : ℝ) / Dn * (y / Dn) = (x * y / Dn) / Dn := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h hD.le

lemma mulU_ge_of {x y : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : a ≤ r x) (hy : b ≤ r y) :
    a * b ≤ r (mulU x y) :=
  (mul_le_mul hx hy hb (r_nonneg x)).trans (mulU_ge x y)

/-- `r (cdiv x k) ≥ r x / k`. -/
lemma cdiv_ge (x k : ℕ) (hk : 0 < k) : r x / k ≤ r (cdiv x k) := by
  unfold r
  have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
  have h := real_le_cdiv x k hk
  calc (x : ℝ) / Dn / k = (x / k) / Dn := by ring
    _ ≤ _ := div_le_div_of_nonneg_right h hD.le

/-- Rounded-up power. -/
def powU (x : ℕ) : ℕ → ℕ
  | 0 => Dn
  | m + 1 => mulU (powU x m) x

lemma powU_ge (x m : ℕ) : r x ^ m ≤ r (powU x m) := by
  induction m with
  | zero => simp [powU, r_Dn]
  | succ m ih =>
    rw [pow_succ]
    exact mulU_ge_of (pow_nonneg (r_nonneg x) _) (r_nonneg x) ih le_rfl

/-! ### The exponential -/

/-- `term y i ≥ D (y/D)^i / i!`. -/
def term (y : ℕ) : ℕ → ℕ
  | 0 => Dn
  | i + 1 => cdiv (term y i * y) ((i + 1) * Dn)

lemma term_ge (y i : ℕ) : r y ^ i / i.factorial ≤ r (term y i) := by
  induction i with
  | zero => simp [term, r_Dn]
  | succ i ih =>
    have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
    have hk : 0 < (i + 1) * Dn := Nat.mul_pos (Nat.succ_pos i) Dn_pos
    have h := real_le_cdiv (term y i * y) ((i + 1) * Dn) hk
    have hf : ((i + 1).factorial : ℝ) = (i + 1) * i.factorial := by
      push_cast [Nat.factorial_succ]; ring
    have hf0 : (0 : ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
    have hy := r_nonneg y
    calc r y ^ (i + 1) / ((i + 1).factorial : ℝ) = (r y ^ i / i.factorial) * r y / (i + 1) := by
          rw [hf, pow_succ]; field_simp
      _ ≤ r (term y i) * r y / (i + 1) := by gcongr
      _ = ((term y i * y : ℕ) : ℝ) / (((i + 1) * Dn : ℕ) : ℝ) / Dn := by
          unfold r; push_cast; field_simp
      _ ≤ (cdiv (term y i * y) ((i + 1) * Dn) : ℝ) / Dn :=
          div_le_div_of_nonneg_right h hD.le
      _ = r (term y (i + 1)) := rfl

def tsumU (y : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => tsumU y i + term y i

lemma tsumU_ge (y i : ℕ) : ∑ m ∈ range i, r y ^ m / m.factorial ≤ r (tsumU y i) := by
  induction i with
  | zero => simp [tsumU, r]
  | succ i ih =>
    rw [Finset.sum_range_succ, tsumU, r_add]
    exact add_le_add ih (term_ge y i)

/-- The Taylor bound at `y ≤ D`: `exp(y/D) ≤ taylorU y / D`. -/
def taylorU (y : ℕ) : ℕ := tsumU y 12 + cdiv (term y 12 * 13) 12

lemma exp_le_taylorU (y : ℕ) (hy : y ≤ Dn) : Real.exp (r y) ≤ r (taylorU y) := by
  have h0 := r_nonneg y
  have h1 : r y ≤ 1 := by rw [← r_Dn]; exact r_mono hy
  have hb := Real.exp_bound' h0 h1 (n := 12) (by norm_num)
  refine hb.trans ?_
  unfold taylorU
  rw [r_add]
  refine add_le_add (tsumU_ge y 12) ?_
  have ht := term_ge y 12
  have hc := cdiv_ge (term y 12 * 13) 12 (by norm_num)
  have e : r (term y 12 * 13) = r (term y 12) * 13 := by unfold r; push_cast; ring
  rw [e] at hc
  have hf : ((12 : ℕ).factorial : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at ht
  calc r y ^ 12 * ((12 : ℕ) + 1 : ℝ) / (((12 : ℕ).factorial : ℝ) * (12 : ℕ))
      = r y ^ 12 / 479001600 * 13 / 12 := by rw [hf]; push_cast; ring
    _ ≤ r (term y 12) * 13 / 12 := by gcongr
    _ ≤ _ := hc

/-- `exp(x/D) ≤ expU x / D` for `x ≤ 16 D`. -/
def expU (x : ℕ) : ℕ :=
  let t := taylorU (cdiv x 16)
  let t2 := mulU t t
  let t4 := mulU t2 t2
  let t8 := mulU t4 t4
  mulU t8 t8

lemma exp_le_expU (x : ℕ) (hx : x ≤ 16 * Dn) : Real.exp (r x) ≤ r (expU x) := by
  set y := cdiv x 16 with hy
  have hyD : y ≤ Dn := by
    rw [hy]; unfold cdiv
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]; omega
  have hxy : r x / 16 ≤ r y := cdiv_ge x 16 (by norm_num)
  have ht := exp_le_taylorU y hyD
  set t := taylorU y
  have he : Real.exp (r x) ≤ Real.exp (r y) ^ 16 := by
    rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; linarith
  have hE0 := (Real.exp_pos (r y)).le
  have h2 : Real.exp (r y) ^ 2 ≤ r (mulU t t) := by
    rw [sq]; exact mulU_ge_of hE0 hE0 ht ht
  have h4 : Real.exp (r y) ^ 4 ≤ r (mulU (mulU t t) (mulU t t)) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    exact mulU_ge_of (by positivity) (by positivity) h2 h2
  have h8 : Real.exp (r y) ^ 8 ≤ r (mulU (mulU (mulU t t) (mulU t t)) (mulU (mulU t t) (mulU t t))) := by
    rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add]
    exact mulU_ge_of (by positivity) (by positivity) h4 h4
  have h16 := mulU_ge_of (pow_nonneg hE0 8) (pow_nonneg hE0 8) h8 h8
  rw [← pow_add] at h16
  exact he.trans h16

lemma exp_le_expU_of {a : ℝ} {x : ℕ} (ha : a ≤ r x) (hx : x ≤ 16 * Dn) :
    Real.exp a ≤ r (expU x) :=
  (Real.exp_le_exp.mpr ha).trans (exp_le_expU x hx)

/-! ### Lower Taylor sums and logarithms -/

def lowTerm (c : ℕ) : ℕ → ℕ
  | 0 => Dn
  | i + 1 => lowTerm c i * c / ((i + 1) * Dn)

lemma lowTerm_le (c i : ℕ) : r (lowTerm c i) ≤ r c ^ i / i.factorial := by
  induction i with
  | zero => simp [lowTerm, r_Dn]
  | succ i ih =>
    have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
    have hf : ((i + 1).factorial : ℝ) = (i + 1) * i.factorial := by
      push_cast [Nat.factorial_succ]; ring
    have hf0 : (0 : ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos i
    have hc := r_nonneg c
    have h := Nat.cast_div_le (α := ℝ) (m := lowTerm c i * c) (n := (i + 1) * Dn)
    calc r (lowTerm c (i + 1)) = ((lowTerm c i * c / ((i + 1) * Dn) : ℕ) : ℝ) / Dn := rfl
      _ ≤ ((lowTerm c i * c : ℕ) : ℝ) / (((i + 1) * Dn : ℕ) : ℝ) / Dn :=
          div_le_div_of_nonneg_right h hD.le
      _ = r (lowTerm c i) * r c / (i + 1) := by unfold r; push_cast; field_simp
      _ ≤ (r c ^ i / i.factorial) * r c / (i + 1) := by gcongr
      _ = r c ^ (i + 1) / ((i + 1).factorial : ℝ) := by rw [hf, pow_succ]; field_simp

def lowSum (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => lowSum c i + lowTerm c i

lemma lowSum_le_exp (c i : ℕ) : r (lowSum c i) ≤ Real.exp (r c) := by
  have : r (lowSum c i) ≤ ∑ m ∈ range i, r c ^ m / m.factorial := by
    induction i with
    | zero => simp [lowSum, r]
    | succ i ih =>
      rw [Finset.sum_range_succ, lowSum, r_add]
      exact add_le_add ih (lowTerm_le c i)
  exact this.trans (Real.sum_le_exp_of_nonneg (r_nonneg c) i)

/-- If `a D ≤ b · lowSum c 12` then `log (a / b) ≤ c / D`. -/
lemma log_le_of_lowSum {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a * Dn ≤ b * lowSum c 12) :
    Real.log ((a : ℝ) / b) ≤ r c := by
  have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.log_le_iff_le_exp (by positivity)]
  refine le_trans ?_ (lowSum_le_exp c 12)
  unfold r
  rw [div_le_div_iff₀ hb' hD]
  have : ((a * Dn : ℕ) : ℝ) ≤ ((b * lowSum c 12 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this
  linarith

/-! ### Sieve-specific bounds -/

/-- `σ` bound for a block `(2^{bn}, 2^{an}]`, with `c / D ≥ log(a/b)`. -/
def sigq (a b c : ℕ) : ℕ := c + cdiv ((a - b) * Dn) (4096 * b) + cdiv Dn (10 ^ 5)

/-- `(1 + 10^{-6}) s`. -/
def xq (s : ℕ) : ℕ := cdiv (s * (10 ^ 6 + 1)) (10 ^ 6)

/-- The factor bound of a block `(a, b, k)` with log bound `c`. -/
def facN (a b k c : ℕ) : ℕ :=
  if k = 0 then expU (xq (sigq a b c))
  else Dn + mulU (cdiv (powU (sigq a b c) (2 * k + 1)) (2 * k + 1).factorial)
    (expU (xq (sigq a b c)))

/-- A table row is admissible. -/
def rowOK (a b k c : ℕ) : Bool :=
  0 < b && b < a && a ≤ 4 * b && a * Dn ≤ b * lowSum c 12 && xq (sigq a b c) ≤ 16 * Dn

end Shoup.Fixed
