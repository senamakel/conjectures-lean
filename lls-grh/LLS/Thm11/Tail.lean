import LLS.Thm11.NumCore

/-!
# The one-variable bounds for `x ≥ 10^16`

For `x ≥ 10^16`, `s = √x ≥ 10^8` and `l = log x = 8 log x^{1/8} ≤ 8 x^{1/8}`, so `l² ≤ s/100`
and `l ≤ s/10^4` (`LLS.Thm11.tail_facts`). The box lemmas applied to the one-point box
`[x, x]` then leave explicit expressions in `s` and `l` whose positivity follows from these two
inequalities: `F₁ ≥ 0.9 s − l² − …`, `F₂(x, 8) ≥ 6000 s − …`, `F₂(x, M) ≥ 0.18 s − l²`.
-/

namespace LLS.Thm11

open Real

lemma tail_facts (x : ℕ) (hx : 10 ^ 16 ≤ x) :
    10 ^ 8 ≤ √(x : ℝ) ∧ 36 ≤ Real.log x ∧ Real.log x ^ 2 ≤ √(x : ℝ) / 100 ∧
      Real.log x ≤ √(x : ℝ) / 10 ^ 4 := by
  have hxR : (10 : ℝ) ^ 16 ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 16 by norm_num]
  set s := √(x : ℝ) with hs_def
  have hs : 10 ^ 8 ≤ s := by
    rw [show (10 : ℝ) ^ 8 = √((10 : ℝ) ^ 16) by
      rw [show (10 : ℝ) ^ 16 = (10 ^ 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hxR
  have hl : 36 ≤ Real.log x := by
    have := log_ge_of_pow (10 ^ 16) 53 1 (by norm_num) (by norm_num)
    have h2 : Real.log (((10 ^ 16 : ℕ) : ℝ)) ≤ Real.log x :=
      Real.log_le_log (by positivity) (by exact_mod_cast hx)
    norm_num at this h2 ⊢
    linarith
  set u := √s with hu_def
  set w := √u with hw_def
  have hs0 : 0 < s := by linarith [show (0 : ℝ) < 10 ^ 8 by norm_num]
  have hu0 : 0 < u := Real.sqrt_pos.2 hs0
  have hw0 : 0 < w := Real.sqrt_pos.2 hu0
  have hsq : s ^ 2 = x := Real.sq_sqrt hx0.le
  have husq : u ^ 2 = s := Real.sq_sqrt hs0.le
  have hwsq : w ^ 2 = u := Real.sq_sqrt hu0.le
  have hlog : Real.log x = 8 * Real.log w := by
    rw [← hsq, ← husq, ← hwsq]
    simp only [Real.log_pow]; push_cast; ring
  have hlw : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hw0
  have hw4 : w ^ 4 = s := by rw [← husq, ← hwsq]; ring
  have hw100 : 100 ≤ w := by
    by_contra h; push Not at h
    have : w ^ 4 < 100 ^ 4 := pow_lt_pow_left₀ h hw0.le (by norm_num)
    rw [hw4] at this; norm_num at this; linarith
  have hl8 : Real.log x ≤ 8 * w := by rw [hlog]; linarith
  refine ⟨hs, hl, ?_, ?_⟩
  · have : Real.log x ^ 2 ≤ 64 * w ^ 2 := by nlinarith
    rw [← hw4]
    nlinarith
  · rw [← hw4]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) hw100 3]

lemma inBox_self (x : ℕ) (hx : 10 ^ 16 ≤ x) :
    InBox x x √(x : ℝ) √(x : ℝ) (Real.log x) (Real.log x) := by
  obtain ⟨hs, hl, -, -⟩ := tail_facts x hx
  have hxR : (10 : ℝ) ^ 16 ≤ x := by exact_mod_cast hx
  exact ⟨le_rfl, by linarith [show (64 : ℝ) ≤ 10 ^ 16 by norm_num], by linarith, le_rfl, le_rfl,
    le_rfl, le_rfl, by linarith⟩

/-- Small quantities in the tail. -/
lemma tail_small {X s l : ℝ} (hX : X = s ^ 2) (hs : 10 ^ 8 ≤ s) (hl : 36 ≤ l)
    (hl1 : l ≤ s / 10 ^ 4) :
    1 / X ≤ 1e-16 ∧ l / X ≤ 1e-12 ∧ 1 / s ≤ 1e-8 ∧ 1 / (s - 1) ≤ 2e-8 ∧ l / (s - 1) ≤ 2e-4 ∧
      0 < s - 1 := by
  have hs0 : 0 < s := by linarith
  have hX0 : 0 < X := by rw [hX]; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, by linarith⟩
  · rw [div_le_iff₀ hX0, hX]; nlinarith
  · rw [div_le_iff₀ hX0, hX]; nlinarith
  · rw [div_le_iff₀ hs0]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

lemma dlo_nonneg {s l : ℝ} (hs : 10 ^ 8 ≤ s) (hl : 36 ≤ l) :
    0 ≤ (3 + l / 2) * (s ^ 2 / (s - 1) ^ 2) - s / (s - 1) ^ 2 := by
  have hs1 : 0 < (s - 1) ^ 2 := by have : 0 < s - 1 := by linarith
                                   positivity
  rw [← mul_div_assoc, ← sub_div]
  apply div_nonneg _ hs1.le
  nlinarith

lemma V_tail {s l : ℝ} (hs : 10 ^ 8 ≤ s) (hl : 36 ≤ l) (hl1 : l ≤ s / 10 ^ 4) :
    -l ^ 2 - 3 * l - 10 ≤ (-3 + 1.144 / 2 + 0.57688 / 2 + 0.6931471803 / 2) * l - 3.5 - 3.1416 ^ 2 / 6
        - (l - 0.6931471803 / 2) ^ 2 / 2 - (l - 405 / 256 * 0.6931471803 / 2) ^ 2 / 2
        - (4 + l) / (2 * (s - 1)) := by
  have h1 : (4 + l) / (2 * (s - 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]; nlinarith
  nlinarith

lemma F1_tail (x : ℕ) (hx : 10 ^ 16 ≤ x) : 0 < F1 x := by
  have B := inBox_self x hx
  obtain ⟨hs, hl, hl2, hl1⟩ := tail_facts x hx
  have hF := F1_ge B (PcF_sub_big B (by have : (10 : ℝ) ^ 16 ≤ x := by exact_mod_cast hx
                                        linarith [show (100 : ℝ) ≤ 10 ^ 16 by norm_num]))
  refine lt_of_lt_of_le ?_ hF
  have hX : (x : ℝ) = √(x : ℝ) ^ 2 := (sq_sqrt_x x).symm
  set s := √(x : ℝ)
  set l := Real.log x
  set X := (x : ℝ)
  obtain ⟨a1, a2, a3, a4, a5, hs1⟩ := tail_small hX hs hl hl1
  have hd := dlo_nonneg hs hl
  have hV := V_tail hs hl hl1
  unfold F1Lo
  rw [min_self]
  have e1 : 2 * (l + 2) / X = 2 * (l / X) + 4 * (1 / X) := by ring
  have e2 : (12 : ℝ) / X = 12 * (1 / X) := by ring
  have e3 : (0.25 : ℝ) / s = 0.25 * (1 / s) := by ring
  have e4 : (4 : ℝ) / (s - 1) = 4 * (1 / (s - 1)) := by ring
  rw [e1, e2, e3, e4]
  have hQ : 0.9 ≤ (1 - 1 / X) * (1.144 + 0.57688) - (2 * (l / X) + 4 * (1 / X))
      + 2 * (-1 - 0.5774 - 0.25 * (1 / s) - 12 * (1 / X)) + 6.05 - 1 / X
      - 0.6931471808 * (1 + 1 / X) - (3 + 4 * (1 / (s - 1))) - l / (s - 1) := by
    have : 0 ≤ 1 / X := by positivity
    have : 0 ≤ l / X := by positivity
    linarith
  have hW : 0 ≤ l + ((1 - 1 / X) * (1.144 + 0.57688) - (2 * (l / X) + 4 * (1 / X)))
      + 2 * (-1 - 0.5774 - 0.25 * (1 / s) - 12 * (1 / X)) + 6.2 - 1 / X
      - 0.6931471808 * (1 + 1 / X) := by
    have : 0 ≤ 1 / X := by positivity
    have : 0 ≤ l / X := by positivity
    linarith
  have hdhi : 0 ≤ (3 + l / 2) * (s ^ 2 / (s - 1) ^ 2) := by positivity
  have hm : 0 ≤ min (((3 + l / 2) * (s ^ 2 / (s - 1) ^ 2) - s / (s - 1) ^ 2)
      * (l + ((1 - 1 / X) * (1.144 + 0.57688) - (2 * (l / X) + 4 * (1 / X)))
        + 2 * (-1 - 0.5774 - 0.25 * (1 / s) - 12 * (1 / X)) + 6.2 - 1 / X
        - 0.6931471808 * (1 + 1 / X)))
      ((3 + l / 2) * (s ^ 2 / (s - 1) ^ 2)
      * (l + ((1 - 1 / X) * (1.144 + 0.57688) - (2 * (l / X) + 4 * (1 / X)))
        + 2 * (-1 - 0.5774 - 0.25 * (1 / s) - 12 * (1 / X)) + 6.2 - 1 / X
        - 0.6931471808 * (1 + 1 / X))) :=
    le_min (mul_nonneg hd hW) (mul_nonneg hdhi hW)
  have hsQ := mul_le_mul_of_nonneg_left hQ (by linarith : (0 : ℝ) ≤ s)
  nlinarith

lemma F2aLo_tail {X s l : ℝ} (hX : X = s ^ 2) (hs : 10 ^ 8 ≤ s) (hl : 36 ≤ l)
    (hl2 : l ^ 2 ≤ s / 100) (hl1 : l ≤ s / 10 ^ 4) (hS : F2aSide X s s l l) :
    0 < F2aLo X s s l l := by
  obtain ⟨a1, a2, a3, a4, a5, hs1⟩ := tail_small hX hs hl hl1
  obtain ⟨hm0, hK0, -⟩ := hS
  unfold F2aLo
  -- the leading term
  have hlead : 1000 * s ≤ s ^ 2 * (0.6931471803 / 2 / l) * (2 - 0.6931471808 / 2 / l) := by
    have e1 : 1 ≤ 2 - 0.6931471808 / 2 / l := by
      have : 0.6931471808 / 2 / l ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have e2 : 0.6931471803 / 2 * 10 ^ 4 / s ≤ 0.6931471803 / 2 / l := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have e3 : s ^ 2 * (0.6931471803 / 2 * 10 ^ 4 / s) = 0.6931471803 / 2 * 10 ^ 4 * s := by
      field_simp
    have e4 : 0 ≤ s ^ 2 * (0.6931471803 / 2 / l) := by positivity
    have f1 := mul_le_mul_of_nonneg_left e2 (sq_nonneg s)
    have f2 := mul_le_mul_of_nonneg_left e1 e4
    have f3 : s ^ 2 * (0.6931471803 / 2 / l) * 1 ≤ s ^ 2 * (0.6931471803 / 2 / l)
        * (2 - 0.6931471808 / 2 / l) := f2
    rw [e3] at f1
    nlinarith
  have hKm := mul_nonneg hK0 hm0
  have hμ : 0 ≤ s * (1 - 0.6931471808 / 2 / l) ^ 2 * (11 + 6 * 0.6931471803) := by positivity
  have hr1 : s ^ 2 / (s - 1) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hr2 : s / (s - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hr3 : (4 : ℝ) / (s - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hX1 : 1 / X ≤ 1 := by linarith
  have hRC : (l - 0.6931471803 / 2) ^ 2 / 2
      + 0.6931471808 * ((s + (3 + l / 2) * (s ^ 2 / (s - 1) ^ 2)) * (1 + 1 / X) - l / 2)
      + (l - 405 / 256 * 0.6931471803 / 2) ^ 2 / 2 ≤ l ^ 2 + 2 * s + 4 * l + 10 := by
    have : (s + (3 + l / 2) * (s ^ 2 / (s - 1) ^ 2)) * (1 + 1 / X) ≤ (s + (3 + l / 2) * 2) * 2 := by
      have hX0 : 0 ≤ 1 / X := by rw [hX]; positivity
      apply mul_le_mul (by nlinarith) (by linarith) (by linarith) (by nlinarith)
    nlinarith
  have hκ : 8 * (s + (3 + 4 / (s - 1) + l * (s / (s - 1)))) ≤ 8 * s + 32 + 16 * l := by nlinarith
  have hfr : 1 / (4 * X) ≤ 1 := by
    have hX0 : 0 < X := by rw [hX]; positivity
    rw [div_le_one (by positivity)]; nlinarith
  have hpi : (3.1416 : ℝ) ^ 2 / 6 ≤ 2 := by norm_num
  linarith


lemma F2a_tail (x : ℕ) (hx : 10 ^ 16 ≤ x) : 0 < F2 x 8 := by
  have B := inBox_self x hx
  obtain ⟨hs, hl, hl2, hl1⟩ := tail_facts x hx
  have hX : (x : ℝ) = √(x : ℝ) ^ 2 := (sq_sqrt_x x).symm
  have hS : F2aSide x √(x : ℝ) √(x : ℝ) (Real.log x) (Real.log x) := by
    obtain ⟨a1, a2, -, -, -, -⟩ := tail_small hX hs hl hl1
    refine ⟨?_, ?_, ?_⟩
    · have e1 : 2 * (Real.log x + 2) / x = 2 * (Real.log x / x) + 4 * (1 / (x : ℝ)) := by ring
      rw [e1]; nlinarith
    · have := dlo_nonneg hs hl; linarith
    · rw [div_le_one (by linarith)]; linarith
  exact lt_of_lt_of_le (F2aLo_tail hX hs hl hl2 hl1 hS) (F2a_ge B hS)

lemma F2b_tail (x : ℕ) (hx : 10 ^ 16 ≤ x) : 0 < F2 x (nu x - 3 - 2 * Real.log 8) := by
  have B := inBox_self x hx
  obtain ⟨hs, hl, hl2, hl1⟩ := tail_facts x hx
  refine lt_of_lt_of_le ?_ (F2b_ge B (by linarith))
  have hX : (x : ℝ) = √(x : ℝ) ^ 2 := (sq_sqrt_x x).symm
  set s := √(x : ℝ)
  set l := Real.log x
  set X := (x : ℝ)
  obtain ⟨a1, a2, a3, a4, a5, hs1⟩ := tail_small hX hs hl hl1
  have hd := dlo_nonneg hs hl
  unfold F2bLo
  rw [min_self]
  have e1 : 2 * (l + 2) / X = 2 * (l / X) + 4 * (1 / X) := by ring
  have e4 : (4 : ℝ) / (s - 1) = 4 * (1 / (s - 1)) := by ring
  rw [e1, e4]
  have hc : (3 + 6 * 0.6931471808) / (s - (3 + 6 * 0.6931471808)) ≤ 1e-7 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hc0 : 0 ≤ (3 + 6 * 0.6931471808) / (s - (3 + 6 * 0.6931471808)) :=
    div_nonneg (by norm_num) (by linarith)
  have hη : (1 - 0.6931471803 / 2 / l) ^ 2 ≤ 1 := by
    have : 0 ≤ 0.6931471803 / 2 / l := by positivity
    have : 0.6931471803 / 2 / l ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have hX2 : 1 / (2 * X) ≤ 1e-16 := by
    have : 1 / (2 * X) = 1 / X / 2 := by ring
    rw [this]; linarith [show 0 ≤ 1 / X from by positivity]
  have hneg : -(3 + 6 * 0.6931471808) / (s - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808 ≤ 0 := by
    rw [neg_div]; linarith
  have ht : -(4.159 : ℝ) ≤ 2 * (1 + 1 / (2 * X)) * (1 - 0.6931471803 / 2 / l) ^ 2
      * (-(3 + 6 * 0.6931471808) / (s - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808) := by
    have hA : 2 * (1 + 1 / (2 * X)) * (1 - 0.6931471803 / 2 / l) ^ 2 ≤ 2 * (1 + 1e-16) := by
      have : 0 ≤ 1 / (2 * X) := by positivity
      nlinarith [sq_nonneg (1 - 0.6931471803 / 2 / l)]
    have hA0 : 0 ≤ 2 * (1 + 1 / (2 * X)) * (1 - 0.6931471803 / 2 / l) ^ 2 := by positivity
    have hB : -(1e-7 : ℝ) - 3 * 0.6931471808
        ≤ -(3 + 6 * 0.6931471808) / (s - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808 := by
      rw [neg_div]; linarith
    nlinarith
  have hQ : 0.15 ≤ (1 - 1 / X) * (1.144 + 0.57688) - (2 * (l / X) + 4 * (1 / X))
        - 0.6931471808 * (1 + 1 / X)
        - 3 / 20 + (3 + 6 * 0.6931471803) - (3 + 4 * (1 / (s - 1))) - l / (s - 1)
        + (-(0.6931471808 * (1 + 1 / (2 * X))) + (0.6931471803 / 2) ^ 2 / l)
        + 2 * (1 + 1 / (2 * X)) * (1 - 0.6931471803 / 2 / l) ^ 2
          * (-(3 + 6 * 0.6931471808) / (s - (3 + 6 * 0.6931471808)) - 3 * 0.6931471808) := by
    have : 0 ≤ 1 / X := by positivity
    have : 0 ≤ l / X := by positivity
    have : 0 ≤ (0.6931471803 / 2) ^ 2 / l := by positivity
    linarith
  have hW : 0 ≤ (1 - 1 / X) * (1.144 + 0.57688) - (2 * (l / X) + 4 * (1 / X))
      - 0.6931471808 * (1 + 1 / X) := by
    have : 0 ≤ l / X := by positivity
    linarith
  have hdhi : 0 ≤ (3 + l / 2) * (s ^ 2 / (s - 1) ^ 2) := by positivity
  have hm := le_min (mul_nonneg hd hW) (mul_nonneg hdhi hW)
  have hsQ := mul_le_mul_of_nonneg_left hQ (by linarith : (0 : ℝ) ≤ s)
  have hV := V_tail hs hl hl1
  nlinarith

lemma R5_tail (x : ℕ) (hx : 10 ^ 16 ≤ x) : R5OK x := by
  have B := inBox_self x hx
  obtain ⟨hs, hl, hl2, hl1⟩ := tail_facts x hx
  refine R5_of B ?_
  have hX : (x : ℝ) = √(x : ℝ) ^ 2 := (sq_sqrt_x x).symm
  set s := √(x : ℝ)
  set l := Real.log x
  set X := (x : ℝ)
  obtain ⟨a1, -, -, -, -, -⟩ := tail_small hX hs hl hl1
  have h1 : (l - 594 / 256 * 0.6931471803 / 2) ^ 2 / 2 ≤ l ^ 2 := by nlinarith
  have h2 : s * (1 / 2 - 1 / X) ≤ (s + 1 + l / 2) * (1 / 2 - 1 / X) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

end LLS.Thm11
