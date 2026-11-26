import Cramer.Shift.Taylor
import Cramer.Sharp.Majorant

/-!
# A kernel-checkable majorant test

A *majorant* is a list of triples `(C, Sg, Tu)` of natural numbers, standing for
`M(x) = Σ (C/KC) (lor(σ, x − τ) + lor(σ, x + τ))`, `σ = Sg/NN`, `τ = Tu/NN`,
`lor(σ, y) = σ²/(σ² + y²)`.

A *cell* `(X0, X1, tag, k)` stands for the interval `[X0/NN, X1/NN]`. `cellOK` checks, in integer
arithmetic only, that one of three explicit envelopes is at most `M` on the cell:

* tag `0`: `U_T(x) = 802/(800 x²)`;
* tag `1`: `U_L(x) = ((1 − cos 2x) + w(x) + w(x)²)/(2x²)`, `w(x) = (1200 + 801x)/639200`;
* tag `2`: `U_S(x) = (800/799)(T(x²)² + (799 + 3200x)/638401)`, `T(y) = 1 − y/6 + y²/120`,
  for `x ≤ 1`.

The lower bound for `M` on a cell takes each Lorentzian at the worse endpoint, rounded down to
`1/KK`; `1 − cos 2x` is bounded above by writing `2x = kπ + t`, `|t| ≤ 3`, with
`3.141592 < π < 3.141593` and the Taylor bounds `cos ≥ T₁₀` (even `k`) or `cos ≤ T₈` (odd `k`).
Everything is evaluated by `decide` in the kernel: natural-number and integer arithmetic only.
-/

namespace Cramer.Shift

open Real

/-- The scale of `x`. -/
def NN : ℕ := 1000000
/-- The rounding scale for the Lorentzians. -/
def KK : ℕ := 1000000000000000
/-- The scale of the coefficients. -/
def KC : ℕ := 1000000000

/-- `⌊KK S² / (S² + (X − T)²)⌋`. -/
def lfl (S : ℕ) (T X : ℤ) : ℕ := KK * S ^ 2 / (S ^ 2 + (X - T).natAbs ^ 2)

/-- The rounded lower bound of one majorant term on `[X0, X1]`. -/
def termLo (c : ℕ × ℕ × ℕ) (X0 X1 : ℕ) : ℕ :=
  c.1 * (min (lfl c.2.1 c.2.2 X0) (lfl c.2.1 c.2.2 X1)
    + min (lfl c.2.1 (-(c.2.2 : ℤ)) X0) (lfl c.2.1 (-(c.2.2 : ℤ)) X1))

/-- The rounded lower bound of the majorant on `[X0, X1]`. -/
def rhsLo (maj : List (ℕ × ℕ × ℕ)) (X0 X1 : ℕ) : ℕ := (maj.map (fun c => termLo c X0 X1)).sum

/-- `π`, rounded down and up, at scale `NN`. -/
def PIL : ℕ := 3141592
/-- See `PIL`. -/
def PIH : ℕ := 3141593

/-- `10! NN^10 · T₁₀(M/NN)`. -/
def T10n (M : ℕ) : ℤ :=
  3628800 * (NN : ℤ) ^ 10 - 1814400 * (M : ℤ) ^ 2 * (NN : ℤ) ^ 8 + 151200 * (M : ℤ) ^ 4 * (NN : ℤ) ^ 6
    - 5040 * (M : ℤ) ^ 6 * (NN : ℤ) ^ 4 + 90 * (M : ℤ) ^ 8 * (NN : ℤ) ^ 2 - (M : ℤ) ^ 10
/-- `10! NN^10`. -/
def T10d : ℕ := 3628800 * NN ^ 10
/-- `8! NN^8 · T₈(m/NN)`. -/
def T8n (m : ℕ) : ℤ :=
  40320 * (NN : ℤ) ^ 8 - 20160 * (m : ℤ) ^ 2 * (NN : ℤ) ^ 6 + 1680 * (m : ℤ) ^ 4 * (NN : ℤ) ^ 4
    - 56 * (m : ℤ) ^ 6 * (NN : ℤ) ^ 2 + (m : ℤ) ^ 8
/-- `8! NN^8`. -/
def T8d : ℕ := 40320 * NN ^ 8

/-- The reduced argument `2x − kπ` lies in `[tl/NN, th/NN]`. -/
def tlo (X0 k : ℕ) : ℤ := 2 * (X0 : ℤ) - (k : ℤ) * PIH
/-- See `tlo`. -/
def thi (X1 k : ℕ) : ℤ := 2 * (X1 : ℤ) - (k : ℤ) * PIL

/-- `max |t|` and `min |t|` (at scale `NN`). -/
def tmax (X0 X1 k : ℕ) : ℕ := max (tlo X0 k).natAbs (thi X1 k).natAbs
/-- See `tmax`. -/
def tmin (X0 X1 k : ℕ) : ℕ :=
  if tlo X0 k ≤ 0 ∧ 0 ≤ thi X1 k then 0 else min (tlo X0 k).natAbs (thi X1 k).natAbs

/-- Numerator of the upper bound for `1 − cos 2x` (denominator `omcD k`). -/
def omcN (X0 X1 k : ℕ) : ℤ :=
  if k % 2 = 0 then (T10d : ℤ) - T10n (tmax X0 X1 k) else (T8d : ℤ) + T8n (tmin X0 X1 k)
/-- See `omcN`. -/
def omcD (k : ℕ) : ℕ := if k % 2 = 0 then T10d else T8d

/-- The check for one cell. -/
def cellOK (maj : List (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let X0 := c.1
  let X1 := c.2.1
  let tag := c.2.2.1
  let k := c.2.2.2
  let R := rhsLo maj X0 X1
  decide (X0 ≤ X1) &&
  (if tag = 0 then
    decide (0 < X0) && decide (802 * NN ^ 2 * KK * KC ≤ 800 * X0 ^ 2 * R)
  else if tag = 1 then
    let Wn : ℕ := 1200 * NN + 801 * X1
    let Wd : ℕ := 639200 * NN
    let P := omcN X0 X1 k
    let Q := omcD k
    decide (0 < X0) && decide (tmax X0 X1 k ≤ 3 * NN) && decide (Wn ≤ Wd) &&
      decide ((P * (Wd : ℤ) ^ 2 + (Q : ℤ) * Wn * Wd + (Q : ℤ) * Wn ^ 2) * KK * KC * NN ^ 2
        ≤ 2 * (X0 : ℤ) ^ 2 * R * Q * (Wd : ℤ) ^ 2)
  else
    let Tpn : ℤ := 120 * (NN : ℤ) ^ 4 + (X0 : ℤ) ^ 4 - 20 * (X0 : ℤ) ^ 2 * (NN : ℤ) ^ 2
    decide (X1 ≤ NN) &&
      decide (800 * (Tpn ^ 2 * 638401 * NN + (799 * (NN : ℤ) + 3200 * X1) * 14400 * (NN : ℤ) ^ 8)
        * KK * KC ≤ 799 * 14400 * (NN : ℤ) ^ 8 * 638401 * NN * R))

/-- The cells cover `[A, B]` consecutively. -/
def chainOK : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | _, _, [] => false
  | A, B, [c] => decide (c.1 = A) && decide (c.2.1 = B)
  | A, B, c :: d :: cs => decide (c.1 = A) && chainOK c.2.1 B (d :: cs)

/-! ## The real-valued side -/

/-- The Lorentzian `σ²/(σ² + y²)`. -/
noncomputable def lor (σ y : ℝ) : ℝ := σ ^ 2 / (σ ^ 2 + y ^ 2)

/-- The real majorant. -/
noncomputable def majF (maj : List (ℕ × ℕ × ℕ)) (x : ℝ) : ℝ :=
  (maj.map (fun c => ((c.1 : ℝ) / KC) * (lor ((c.2.1 : ℝ) / NN) (x - (c.2.2 : ℝ) / NN)
    + lor ((c.2.1 : ℝ) / NN) (x + (c.2.2 : ℝ) / NN)))).sum

/-- The envelope for tag 0. -/
noncomputable def envT (x : ℝ) : ℝ := 802 / (800 * x ^ 2)
/-- The error parameter `w(x)` at `ε = 1/800`. -/
noncomputable def wbx (x : ℝ) : ℝ := (1200 + 801 * x) / 639200
/-- The envelope for tag 1. -/
noncomputable def envL (x : ℝ) : ℝ := ((1 - Real.cos (2 * x)) + wbx x + wbx x ^ 2) / (2 * x ^ 2)
/-- The envelope for tag 2. -/
noncomputable def envS (x : ℝ) : ℝ := 800 / 799 * (Tpoly (x ^ 2) ^ 2 + (799 + 3200 * x) / 638401)

lemma lor_nonneg (σ y : ℝ) : 0 ≤ lor σ y := by unfold lor; positivity

lemma lor_anti {σ y z : ℝ} (h : y ^ 2 ≤ z ^ 2) : lor σ z ≤ lor σ y := by
  unfold lor
  rcases eq_or_ne σ 0 with rfl | hσ
  · simp
  · have : 0 < σ ^ 2 := by positivity
    apply div_le_div_of_nonneg_left this.le (by positivity) (by linarith)

/-- `lfl S T X / KK ≤ lor (S/NN) (X/NN − T/NN)`. -/
lemma lfl_le (S : ℕ) (T X : ℤ) :
    (lfl S T X : ℝ) / KK ≤ lor ((S : ℝ) / NN) ((X : ℝ) / NN - (T : ℝ) / NN) := by
  have hN : (0 : ℝ) < NN := by norm_num [NN]
  have hK : (0 : ℝ) < KK := by norm_num [KK]
  have e : lor ((S : ℝ) / NN) ((X : ℝ) / NN - (T : ℝ) / NN)
      = (S : ℝ) ^ 2 / ((S : ℝ) ^ 2 + ((X - T : ℤ) : ℝ) ^ 2) := by
    unfold lor; push_cast; field_simp
  rw [e]
  have hsq : ((X - T).natAbs : ℝ) ^ 2 = ((X - T : ℤ) : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · simp [lfl]
  · have hden : (0 : ℝ) < (S : ℝ) ^ 2 + ((X - T : ℤ) : ℝ) ^ 2 := by
      have : (0 : ℝ) < S := by exact_mod_cast hS
      positivity
    rw [div_le_iff₀ hK, div_mul_eq_mul_div, le_div_iff₀ hden]
    have h1 := Nat.div_mul_le_self (KK * S ^ 2) (S ^ 2 + (X - T).natAbs ^ 2)
    have h1' : ((lfl S T X : ℕ) : ℝ) * ((S ^ 2 + (X - T).natAbs ^ 2 : ℕ) : ℝ) ≤ ((KK * S ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    rw [hsq] at h1'
    linarith

/-- On `[x0, x1]`, `lor σ (x − τ) ≥ min (lor σ (x0 − τ)) (lor σ (x1 − τ))`. -/
lemma lor_ge_min {σ τ x0 x1 x : ℝ} (h0 : x0 ≤ x) (h1 : x ≤ x1) :
    min (lor σ (x0 - τ)) (lor σ (x1 - τ)) ≤ lor σ (x - τ) := by
  rcases le_total (x - τ) 0 with hb | hb
  · exact (min_le_left _ _).trans (lor_anti (by nlinarith))
  · exact (min_le_right _ _).trans (lor_anti (by nlinarith))

lemma termLo_le (c : ℕ × ℕ × ℕ) {X0 X1 : ℕ} {x : ℝ} (h0 : (X0 : ℝ) / NN ≤ x)
    (h1 : x ≤ (X1 : ℝ) / NN) :
    (termLo c X0 X1 : ℝ) / (KK * KC) ≤ ((c.1 : ℝ) / KC) * (lor ((c.2.1 : ℝ) / NN) (x - (c.2.2 : ℝ) / NN)
      + lor ((c.2.1 : ℝ) / NN) (x + (c.2.2 : ℝ) / NN)) := by
  obtain ⟨C, S, T⟩ := c
  simp only
  have hK : (0 : ℝ) < KK := by norm_num [KK]
  have hKC : (0 : ℝ) < KC := by norm_num [KC]
  have key : ∀ (T' : ℤ), ((min (lfl S T' X0) (lfl S T' X1) : ℕ) : ℝ) / KK
      ≤ lor ((S : ℝ) / NN) (x - (T' : ℝ) / NN) := by
    intro T'
    have a0 := lfl_le S T' X0
    have a1 := lfl_le S T' X1
    push_cast at a0 a1
    have hm := lor_ge_min (σ := (S : ℝ) / NN) (τ := (T' : ℝ) / NN) h0 h1
    rw [Nat.cast_min, ← min_div_div_right hK.le]
    exact (min_le_min a0 a1).trans hm
  have kp := key (T : ℤ)
  have km := key (-(T : ℤ))
  push_cast at kp km
  rw [neg_div, sub_neg_eq_add] at km
  unfold termLo
  simp only
  push_cast
  have e : ∀ A B : ℝ, (C : ℝ) * (A + B) / (KK * KC) = ((C : ℝ) / KC) * (A / KK + B / KK) := by
    intro A B; field_simp
  rw [e]
  have hC : (0 : ℝ) ≤ (C : ℝ) / KC := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add kp km) hC

lemma rhsLo_le (maj : List (ℕ × ℕ × ℕ)) {X0 X1 : ℕ} {x : ℝ} (h0 : (X0 : ℝ) / NN ≤ x)
    (h1 : x ≤ (X1 : ℝ) / NN) : (rhsLo maj X0 X1 : ℝ) / (KK * KC) ≤ majF maj x := by
  induction maj with
  | nil => simp [rhsLo, majF]
  | cons c cs ih =>
    simp only [rhsLo, majF, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.cast_add, add_div]
    exact add_le_add (by exact_mod_cast termLo_le c h0 h1) ih

lemma hNN : (0 : ℝ) < NN := by norm_num [NN]

lemma cos_add_nat_mul_pi (t : ℝ) (k : ℕ) : Real.cos (t + k * π) = (-1) ^ k * Real.cos t := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * π = (t + n * π) + π by push_cast; ring, Real.cos_add_pi, ih]
    ring

lemma T10n_eq (M : ℕ) : (T10n M : ℝ) / T10d = cosT10 ((M : ℝ) / NN) := by
  have := hNN
  unfold T10n T10d cosT10 cosT8 cosT6
  push_cast
  field_simp
  ring

lemma T8n_eq (m : ℕ) : (T8n m : ℝ) / T8d = cosT8 ((m : ℝ) / NN) := by
  have := hNN
  unfold T8n T8d cosT8 cosT6
  push_cast
  field_simp
  ring

/-- **The cosine enclosure.** -/
lemma one_sub_cos_le {X0 X1 k : ℕ} {x : ℝ} (h0 : (X0 : ℝ) / NN ≤ x) (h1 : x ≤ (X1 : ℝ) / NN)
    (hM : tmax X0 X1 k ≤ 3 * NN) :
    1 - Real.cos (2 * x) ≤ (omcN X0 X1 k : ℝ) / omcD k := by
  have hN := hNN
  set t := 2 * x - k * π with ht
  have hpl : (PIL : ℝ) / NN < π := by
    have := Real.pi_gt_d6; norm_num [PIL, NN]; linarith
  have hph : π < (PIH : ℝ) / NN := by
    have := Real.pi_lt_d6; norm_num [PIH, NN]; linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htl : ((tlo X0 k : ℤ) : ℝ) / NN ≤ t := by
    unfold tlo; push_cast
    rw [div_le_iff₀ hN]
    have h0' : (X0 : ℝ) ≤ x * NN := by rwa [div_le_iff₀ hN] at h0
    have : (k : ℝ) * π * NN ≤ k * PIH := by
      have := mul_le_mul_of_nonneg_left (le_of_lt ((lt_div_iff₀ hN).1 hph)) hk; linarith
    rw [ht]; nlinarith
  have hth : t ≤ ((thi X1 k : ℤ) : ℝ) / NN := by
    unfold thi; push_cast
    rw [le_div_iff₀ hN]
    have h1' : x * NN ≤ (X1 : ℝ) := by rwa [le_div_iff₀ hN] at h1
    have : (k : ℝ) * PIL ≤ k * π * NN := by
      have := mul_le_mul_of_nonneg_left (le_of_lt ((div_lt_iff₀ hN).1 hpl)) hk; linarith
    rw [ht]; nlinarith
  have habs_le : |t| ≤ (tmax X0 X1 k : ℝ) / NN := by
    have a1 : ((tlo X0 k : ℤ) : ℝ) ≥ -((tlo X0 k).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact neg_abs_le _
    have a2 : ((thi X1 k : ℤ) : ℝ) ≤ ((thi X1 k).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact le_abs_self _
    have m1 : ((tlo X0 k).natAbs : ℝ) ≤ tmax X0 X1 k := by exact_mod_cast le_max_left _ _
    have m2 : ((thi X1 k).natAbs : ℝ) ≤ tmax X0 X1 k := by exact_mod_cast le_max_right _ _
    rw [abs_le]
    constructor
    · have : -((tmax X0 X1 k : ℝ) / NN) ≤ ((tlo X0 k : ℤ) : ℝ) / NN := by
        rw [neg_div' , div_le_div_iff_of_pos_right hN]; linarith
      linarith
    · have : ((thi X1 k : ℤ) : ℝ) / NN ≤ (tmax X0 X1 k : ℝ) / NN := by
        rw [div_le_div_iff_of_pos_right hN]; linarith
      linarith
  have hMpi : (tmax X0 X1 k : ℝ) / NN ≤ π := by
    have : (tmax X0 X1 k : ℝ) ≤ 3 * NN := by exact_mod_cast hM
    rw [div_le_iff₀ hN]; nlinarith [Real.pi_gt_three]
  have hcos2 : Real.cos (2 * x) = (-1) ^ k * Real.cos t := by
    rw [← cos_add_nat_mul_pi]; congr 1; rw [ht]; ring
  have hct : Real.cos t = Real.cos |t| := (Real.cos_abs t).symm
  rcases Nat.even_or_odd k with he | ho
  · have hk2 : k % 2 = 0 := Nat.even_iff.mp he
    simp only [omcN, omcD, hk2, ite_true]
    rw [hcos2, he.neg_one_pow, one_mul]
    have h1c : Real.cos ((tmax X0 X1 k : ℝ) / NN) ≤ Real.cos t := by
      rw [hct]; exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t) hMpi habs_le
    have h2c := cosT10_le_cos ((tmax X0 X1 k : ℝ) / NN)
    rw [← T10n_eq] at h2c
    have hd : (0 : ℝ) < T10d := by norm_num [T10d, NN]
    push_cast
    rw [sub_div, div_self hd.ne']
    linarith
  · have hk2 : k % 2 = 1 := Nat.odd_iff.mp ho
    simp only [omcN, omcD, hk2]
    norm_num
    rw [hcos2, ho.neg_one_pow]
    have hmin : (tmin X0 X1 k : ℝ) / NN ≤ |t| := by
      unfold tmin
      split_ifs with hs
      · simp
      · rw [not_and_or, not_le, not_le] at hs
        rcases hs with hs | hs
        · have : ((tlo X0 k).natAbs : ℝ) = ((tlo X0 k : ℤ) : ℝ) := by
            rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hs)]
          have hmn : (min (tlo X0 k).natAbs (thi X1 k).natAbs : ℝ) ≤ (tlo X0 k).natAbs := by
            exact_mod_cast min_le_left _ _
          have hpos : 0 < t := lt_of_lt_of_le (by
            apply div_pos (by exact_mod_cast hs) hN) htl
          rw [abs_of_pos hpos]
          refine le_trans ?_ htl
          rw [div_le_div_iff_of_pos_right hN]; push_cast at hmn ⊢; linarith
        · have : ((thi X1 k).natAbs : ℝ) = -((thi X1 k : ℤ) : ℝ) := by
            rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hs)]
          have hmn : (min (tlo X0 k).natAbs (thi X1 k).natAbs : ℝ) ≤ (thi X1 k).natAbs := by
            exact_mod_cast min_le_right _ _
          have hneg : t < 0 := lt_of_le_of_lt hth (by
            apply div_neg_of_neg_of_pos (by exact_mod_cast hs) hN)
          rw [abs_of_neg hneg]
          have : -t ≥ -(((thi X1 k : ℤ) : ℝ) / NN) := by linarith
          refine le_trans ?_ this
          rw [← neg_div, div_le_div_iff_of_pos_right hN]; push_cast at hmn ⊢; linarith
    have h1c : Real.cos t ≤ Real.cos ((tmin X0 X1 k : ℝ) / NN) := by
      rw [hct]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (habs_le.trans hMpi) hmin
    have h2c := cos_le_cosT8 ((tmin X0 X1 k : ℝ) / NN)
    rw [← T8n_eq] at h2c
    have hd : (0 : ℝ) < T8d := by norm_num [T8d, NN]
    rw [add_div, div_self hd.ne']
    linarith

/-- What a checked cell gives at a point. -/
def CellGood (maj : List (ℕ × ℕ × ℕ)) (x : ℝ) : Prop :=
  (0 < x ∧ envT x ≤ majF maj x) ∨ (0 < x ∧ wbx x ≤ 1 ∧ envL x ≤ majF maj x) ∨
    (0 ≤ x ∧ x ≤ 1 ∧ envS x ≤ majF maj x)

lemma Tpoly_anti {y z : ℝ} (_hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 10) : Tpoly z ≤ Tpoly y := by
  unfold Tpoly; nlinarith

lemma Tpoly_nonneg {y : ℝ} (_hy : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ Tpoly y := by
  unfold Tpoly; nlinarith

/-- **Soundness of one cell.** -/
theorem cellOK_sound {maj : List (ℕ × ℕ × ℕ)} {c : ℕ × ℕ × ℕ × ℕ} (hc : cellOK maj c = true)
    {x : ℝ} (h0 : (c.1 : ℝ) / NN ≤ x) (h1 : x ≤ (c.2.1 : ℝ) / NN) : CellGood maj x := by
  obtain ⟨X0, X1, tag, k⟩ := c
  simp only at h0 h1
  have hN := hNN
  have hK : (0 : ℝ) < KK := by norm_num [KK]
  have hKC : (0 : ℝ) < KC := by norm_num [KC]
  have hR := rhsLo_le maj h0 h1
  set R := rhsLo maj X0 X1
  have hx0 : (0 : ℝ) ≤ (X0 : ℝ) / NN := by positivity
  unfold cellOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, hc⟩ := hc
  split_ifs at hc with ht0 ht1
  · -- tag 0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hX0, hchk⟩ := hc
    left
    have hX0r : (0 : ℝ) < X0 := by exact_mod_cast hX0
    have hx : 0 < x := lt_of_lt_of_le (by positivity) h0
    refine ⟨hx, le_trans ?_ hR⟩
    have hchk' : (802 : ℝ) * NN ^ 2 * KK * KC ≤ 800 * X0 ^ 2 * R := by exact_mod_cast hchk
    unfold envT
    have hxx : ((X0 : ℝ) / NN) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hx0 h0 2
    calc 802 / (800 * x ^ 2) ≤ 802 / (800 * ((X0 : ℝ) / NN) ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
      _ ≤ (R : ℝ) / (KK * KC) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          field_simp
          nlinarith
  · -- tag 1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hX0, hM⟩, hW⟩, hchk⟩ := hc
    right; left
    have hX0r : (0 : ℝ) < X0 := by exact_mod_cast hX0
    have hx : 0 < x := lt_of_lt_of_le (by positivity) h0
    have hw : wbx x ≤ (1200 * NN + 801 * X1 : ℕ) / (639200 * NN : ℕ) := by
      unfold wbx; push_cast
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : x * NN ≤ X1 := by rwa [le_div_iff₀ hN] at h1
      nlinarith
    have hW' : ((1200 * NN + 801 * X1 : ℕ) : ℝ) / (639200 * NN : ℕ) ≤ 1 := by
      rw [div_le_one (by push_cast; norm_num [NN])]; exact_mod_cast hW
    have hw0 : 0 ≤ wbx x := by unfold wbx; positivity
    refine ⟨hx, hw.trans hW', le_trans ?_ hR⟩
    have hcos := one_sub_cos_le h0 h1 hM
    set P := omcN X0 X1 k
    set Q := omcD k
    set Wn := 1200 * NN + 801 * X1
    set Wd := 639200 * NN
    have hQ : (0 : ℝ) < Q := by
      simp only [Q, omcD]; split_ifs <;> norm_num [T10d, T8d, NN]
    have hWd : (0 : ℝ) < Wd := by simp only [Wd]; push_cast; norm_num [NN]
    have hchk' : ((P : ℝ) * Wd ^ 2 + Q * Wn * Wd + Q * Wn ^ 2) * KK * KC * NN ^ 2
        ≤ 2 * X0 ^ 2 * R * Q * Wd ^ 2 := by exact_mod_cast hchk
    have hnum0 : 0 ≤ (1 - Real.cos (2 * x)) + wbx x + wbx x ^ 2 := by
      have := Real.cos_le_one (2 * x); positivity
    unfold envL
    have hxx : ((X0 : ℝ) / NN) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hx0 h0 2
    have hnum : (1 - Real.cos (2 * x)) + wbx x + wbx x ^ 2
        ≤ (P : ℝ) / Q + (Wn : ℝ) / Wd + ((Wn : ℝ) / Wd) ^ 2 := by
      have := pow_le_pow_left₀ hw0 hw 2
      linarith
    calc ((1 - Real.cos (2 * x)) + wbx x + wbx x ^ 2) / (2 * x ^ 2)
        ≤ ((P : ℝ) / Q + (Wn : ℝ) / Wd + ((Wn : ℝ) / Wd) ^ 2) / (2 * ((X0 : ℝ) / NN) ^ 2) := by
          apply div_le_div₀ (by linarith) hnum (by positivity) (by nlinarith)
      _ ≤ (R : ℝ) / (KK * KC) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have e : ((P : ℝ) / Q + (Wn : ℝ) / Wd + ((Wn : ℝ) / Wd) ^ 2) * (KK * KC)
              = ((P : ℝ) * Wd ^ 2 + Q * Wn * Wd + Q * Wn ^ 2) * KK * KC * NN ^ 2
                / (Q * Wd ^ 2 * NN ^ 2) := by
            field_simp
          rw [e, div_le_iff₀ (by positivity)]
          have e2 : (R : ℝ) * (2 * ((X0 : ℝ) / NN) ^ 2) * (Q * Wd ^ 2 * NN ^ 2)
              = 2 * X0 ^ 2 * R * Q * Wd ^ 2 := by field_simp
          rw [e2]; exact hchk'
  · -- tag 2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hX1, hchk⟩ := hc
    right; right
    have hX1r : (X1 : ℝ) ≤ NN := by exact_mod_cast hX1
    have hx1 : x ≤ 1 := h1.trans (by rw [div_le_one hN]; exact hX1r)
    have hx : 0 ≤ x := hx0.trans h0
    refine ⟨hx, hx1, le_trans ?_ hR⟩
    set Tpn : ℤ := 120 * (NN : ℤ) ^ 4 + (X0 : ℤ) ^ 4 - 20 * (X0 : ℤ) ^ 2 * (NN : ℤ) ^ 2
    have hTp : Tpoly (((X0 : ℝ) / NN) ^ 2) = (Tpn : ℝ) / (120 * NN ^ 4) := by
      simp only [Tpn, Tpoly]; push_cast; field_simp; ring
    have hchk' : 800 * ((Tpn : ℝ) ^ 2 * 638401 * NN + (799 * NN + 3200 * X1) * 14400 * NN ^ 8)
        * KK * KC ≤ 799 * 14400 * NN ^ 8 * 638401 * NN * R := by exact_mod_cast hchk
    have hxx : ((X0 : ℝ) / NN) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hx0 h0 2
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hT1 : Tpoly (x ^ 2) ≤ Tpoly (((X0 : ℝ) / NN) ^ 2) :=
      Tpoly_anti (by positivity) hxx (by linarith)
    have hT0 : 0 ≤ Tpoly (x ^ 2) := Tpoly_nonneg (by positivity) hx2
    have hT2 : Tpoly (x ^ 2) ^ 2 ≤ ((Tpn : ℝ) / (120 * NN ^ 4)) ^ 2 := by
      rw [← hTp]; exact pow_le_pow_left₀ hT0 hT1 2
    have hlin : (799 + 3200 * x) / 638401 ≤ (799 + 3200 * ((X1 : ℝ) / NN)) / 638401 := by
      gcongr
    unfold envS
    calc 800 / 799 * (Tpoly (x ^ 2) ^ 2 + (799 + 3200 * x) / 638401)
        ≤ 800 / 799 * (((Tpn : ℝ) / (120 * NN ^ 4)) ^ 2 + (799 + 3200 * ((X1 : ℝ) / NN)) / 638401) := by
          gcongr
      _ ≤ (R : ℝ) / (KK * KC) := by
          rw [le_div_iff₀ (by positivity)]
          have e : 800 / 799 * (((Tpn : ℝ) / (120 * NN ^ 4)) ^ 2
              + (799 + 3200 * ((X1 : ℝ) / NN)) / 638401) * (KK * KC)
              = 800 * ((Tpn : ℝ) ^ 2 * 638401 * NN + (799 * NN + 3200 * X1) * 14400 * NN ^ 8)
                * KK * KC / (799 * 14400 * NN ^ 8 * 638401 * NN) := by
            field_simp; ring
          rw [e, div_le_iff₀ (by positivity)]
          linarith

/-- **Soundness of a chain of cells.** -/
theorem chainOK_sound {maj : List (ℕ × ℕ × ℕ)} :
    ∀ (cs : List (ℕ × ℕ × ℕ × ℕ)) (A B : ℕ), chainOK A B cs = true →
      (∀ c ∈ cs, cellOK maj c = true) →
      ∀ x : ℝ, (A : ℝ) / NN ≤ x → x ≤ (B : ℝ) / NN → CellGood maj x
  | [], A, B, h, _, x, h0, h1 => by simp [chainOK] at h
  | [c], A, B, h, hall, x, h0, h1 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hA, hB⟩ := h
    exact cellOK_sound (hall c (List.mem_singleton_self _)) (by rw [hA]; exact h0)
      (by rw [hB]; exact h1)
  | c :: d :: cs, A, B, h, hall, x, h0, h1 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hA, hrest⟩ := h
    rcases le_or_gt x ((c.2.1 : ℝ) / NN) with hx | hx
    · exact cellOK_sound (hall c (List.mem_cons_self ..)) (by rw [hA]; exact h0) hx
    · exact chainOK_sound (d :: cs) c.2.1 B hrest (fun e he => hall e (List.mem_cons_of_mem _ he)) x
        hx.le h1

end Cramer.Shift
