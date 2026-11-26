import LLS.Sharp.NumU

/-!
# Numerical part, lower bound

`HLu 𝔞 u y = u + 2u² + y·QL 𝔞 u y`, and the target is
`log(1 + V + Zz) ≥ 2V/(2+V) + 2W/(2+W)`, `W = Zz/(1 + V)`, `Zz = 7(1 + 2u log 2) y/(1 + y²/2)`.
`QL_le` bounds `QL` on a box by the explicit `QLhi`.
-/

namespace LLS.Sharp

open Real

/-- `Zz(u, y) = 7(1 + 2u log 2) y / (1 + y²/2)`. -/
noncomputable def Zz (u y : ℝ) : ℝ := 7 * (1 + 2 * Real.log 2 * u) * y / (1 + y ^ 2 / 2)

/-- The explicit upper bound for `QL` on `[u₁, u₂] × [0, y₂]`. -/
noncomputable def QLhi (u1 u2 y2 : ℝ) : ℝ :=
  (0.6 + 29 * y2) * u2 + 2 * y2 * u2 ^ 2
    + ((0.25 + 12 * y2) * u2 + 2.73 * y2 * u2 + y2) * (1 + 2 * y2 * u2) / (1 - y2) ^ 2
    + (2 + (4 - 2 * 2.437) * u1 + (4 - 2 * 2.437) * u1 ^ 2 + u2 * y2 * (1 + u2 + u2 * y2))
      / (1 - y2) ^ 2

lemma kL_ge (a : ℕ) (ha : a ≤ 1) : 2.437 ≤ kL a := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := consts
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    simp only [kL, Gpar, ↓reduceIte, one_ne_zero] <;> linarith

lemma cL_bounds (a : ℕ) (ha : a ≤ 1) : 0 ≤ cL a ∧ cL a ≤ 2.73 := by
  obtain ⟨g1, g2, g3, g4⟩ := G3par_bounds
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    simp only [cL, ↓reduceIte, one_ne_zero] <;> constructor <;> linarith

set_option maxHeartbeats 1000000 in
lemma QL_le (a : ℕ) (ha : a ≤ 1) {u y u1 u2 y2 : ℝ} (hu1 : u1 ≤ u) (hu2 : u ≤ u2)
    (hu10 : 0 ≤ u1) (hu2' : u2 ≤ 0.205) (hy0 : 0 ≤ y) (hy2 : y ≤ y2) (hy2' : y2 ≤ 0.09) :
    QL a u y ≤ QLhi u1 u2 y2 := by
  have hk := kL_ge a ha
  obtain ⟨hc0, hc1⟩ := cL_bounds a ha
  have hu0 : 0 ≤ u := hu10.trans hu1
  have hy20 : 0 ≤ y2 := hy0.trans hy2
  have hD : (1 - y2) ^ 2 ≤ (1 - y) ^ 2 := by nlinarith
  have hD0 : 0 < (1 - y2) ^ 2 := by nlinarith
  have hDy : 0 < 1 - y := by linarith
  -- T1, T2
  have hT1 : (0.6 + 29 * y) * u ≤ (0.6 + 29 * y2) * u2 := by
    apply mul_le_mul (by linarith) hu2 hu0 (by linarith)
  have hT2 : 2 * y * u ^ 2 ≤ 2 * y2 * u2 ^ 2 := by
    have : u ^ 2 ≤ u2 ^ 2 := pow_le_pow_left₀ hu0 hu2 2
    nlinarith [mul_le_mul hy2 this (sq_nonneg u) hy20]
  -- T3
  have hT3 : ((0.25 + 12 * y) * u + y * cL a * u + (if a = 0 then y else 0)) * (1 + 2 * y * u)
        / (1 - y) ^ 2
      ≤ ((0.25 + 12 * y2) * u2 + 2.73 * y2 * u2 + y2) * (1 + 2 * y2 * u2) / (1 - y2) ^ 2 := by
    have hn1 : (0.25 + 12 * y) * u + y * cL a * u + (if a = 0 then y else 0)
        ≤ (0.25 + 12 * y2) * u2 + 2.73 * y2 * u2 + y2 := by
      have h1 : (0.25 + 12 * y) * u ≤ (0.25 + 12 * y2) * u2 :=
        mul_le_mul (by linarith) hu2 hu0 (by linarith)
      have h2 : y * cL a * u ≤ y2 * 2.73 * u2 := by
        apply mul_le_mul (mul_le_mul hy2 hc1 hc0 hy20) hu2 hu0 (by positivity)
      have h3 : (if a = 0 then y else 0) ≤ y2 := by split_ifs <;> linarith
      nlinarith
    have hn0 : 0 ≤ (0.25 + 12 * y) * u + y * cL a * u + (if a = 0 then y else 0) := by
      have : 0 ≤ (if a = 0 then y else 0) := by split_ifs <;> linarith
      positivity
    have hm : 1 + 2 * y * u ≤ 1 + 2 * y2 * u2 := by nlinarith [mul_le_mul hy2 hu2 hu0 hy20]
    have hm0 : 0 ≤ 1 + 2 * y * u := by positivity
    have hu20 : 0 ≤ u2 := hu0.trans hu2
    have hn20 : 0 ≤ (0.25 + 12 * y2) * u2 + 2.73 * y2 * u2 + y2 := by positivity
    have hm20 : 0 ≤ 1 + 2 * y2 * u2 := by positivity
    calc _ ≤ ((0.25 + 12 * y2) * u2 + 2.73 * y2 * u2 + y2) * (1 + 2 * y2 * u2) / (1 - y) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul hn1 hm hm0 hn20
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hn20 hm20) hD0 hD
  -- T4 + T5
  have hT45 : (1 - kL a * u) * (2 + 2 * u - y) / (1 - y) ^ 2
        + 2 * u * ((1 + 2 * u) + y / 2 * (1 + u + u * y)) / (1 - y)
      ≤ (2 + (4 - 2 * 2.437) * u1 + (4 - 2 * 2.437) * u1 ^ 2 + u2 * y2 * (1 + u2 + u2 * y2))
        / (1 - y2) ^ 2 := by
    have hkL : kL a ≤ 3.2 := by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := consts
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
        simp only [kL, Gpar, ↓reduceIte, one_ne_zero] <;> linarith
    have hku : 0 ≤ 1 - kL a * u := by nlinarith
    have e : 2 * u * ((1 + 2 * u) + y / 2 * (1 + u + u * y)) / (1 - y)
        = 2 * u * ((1 + 2 * u) + y / 2 * (1 + u + u * y)) * (1 - y) / (1 - y) ^ 2 := by
      field_simp
    rw [e, ← add_div]
    have hN : (1 - kL a * u) * (2 + 2 * u - y)
          + 2 * u * ((1 + 2 * u) + y / 2 * (1 + u + u * y)) * (1 - y) ≤ 2 + (4 - 2 * 2.437) * u1 + (4 - 2 * 2.437) * u1 ^ 2
        + u2 * y2 * (1 + u2 + u2 * y2) := by
      have a1 : (1 - kL a * u) * (2 + 2 * u - y) ≤ (1 - kL a * u) * (2 + 2 * u) := by
        nlinarith [mul_nonneg hku hy0]
      have a2 : 2 * u * ((1 + 2 * u) + y / 2 * (1 + u + u * y)) * (1 - y)
          ≤ 2 * u * (1 + 2 * u) + u * y * (1 + u + u * y) := by
        have : 0 ≤ 2 * u * ((1 + 2 * u) + y / 2 * (1 + u + u * y)) := by positivity
        nlinarith
      have a3 : (1 - kL a * u) * (2 + 2 * u) + 2 * u * (1 + 2 * u)
          ≤ 2 + (4 - 2 * 2.437) * u1 + (4 - 2 * 2.437) * u1 ^ 2 := by
        have : (1 - kL a * u) * (2 + 2 * u) + 2 * u * (1 + 2 * u)
            = 2 + (4 - 2 * kL a) * u + (4 - 2 * kL a) * u ^ 2 := by ring
        rw [this]
        have hk0 : 0 ≤ kL a - 2.437 := by linarith
        nlinarith [mul_le_mul hu1 hu1 hu10 hu0, mul_nonneg hk0 hu0, mul_nonneg hk0 (sq_nonneg u)]
      have a4 : u * y * (1 + u + u * y) ≤ u2 * y2 * (1 + u2 + u2 * y2) := by
        have h1 : u * y ≤ u2 * y2 := mul_le_mul hu2 hy2 hy0 (hu0.trans hu2)
        have h2 : 1 + u + u * y ≤ 1 + u2 + u2 * y2 := by nlinarith
        exact mul_le_mul h1 h2 (by positivity) (by nlinarith)
      linarith
    have hN0 : 0 ≤ 2 + (4 - 2 * 2.437) * u1 + (4 - 2 * 2.437) * u1 ^ 2
        + u2 * y2 * (1 + u2 + u2 * y2) := by
      have : u1 ≤ 0.205 := hu1.trans (hu2.trans hu2')
      have : 0 ≤ u2 := hu0.trans hu2
      nlinarith [mul_nonneg this hy20]
    calc _ ≤ _ / (1 - y) ^ 2 := div_le_div_of_nonneg_right hN (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hN0 hD0 hD
  simp only [QL, QLhi]
  linarith

lemma Vf_le {u : ℝ} (hu0 : 0 ≤ u) : Vf u ≤ u + 4 * u ^ 2 / (1 + 1.3862 * u) := by
  have h := consts.2.2.2.2.1
  unfold Vf
  gcongr
  nlinarith

lemma Vf_nonneg {u : ℝ} (hu0 : 0 ≤ u) : 0 ≤ Vf u := by
  unfold Vf; have := consts.2.2.2.2.1; positivity

/-- `log(1 + V + Zz) ≥ 2V/(2+V) + 2W/(2+W)` with `W = Zz/(1+V)`. -/
lemma log_split {V Z : ℝ} (hV : 0 ≤ V) (hZ : 0 ≤ Z) :
    2 * V / (2 + V) + 2 * (Z / (1 + V)) / (2 + Z / (1 + V)) ≤ Real.log (1 + V + Z) := by
  have h1 := log_one_add_ge hV
  have h2 := log_one_add_ge (w := Z / (1 + V)) (by positivity)
  have e : 1 + V + Z = (1 + V) * (1 + Z / (1 + V)) := by field_simp
  rw [e, Real.log_mul (by positivity) (by positivity)]
  linarith

/-- The lower-bound core on a box, regime with the five primes up to `11`. -/
theorem HLu_le_log_S5 (a : ℕ) (ha : a ≤ 1) {u y u1 u2 y1 y2 s : ℝ} (hu1 : u1 ≤ u) (hu2 : u ≤ u2)
    (hu10 : 0 < u1) (hu2' : u2 ≤ 0.205) (hy1 : y1 ≤ y) (hy2 : y ≤ y2) (hy10 : 0 < y1)
    (hy2' : y2 ≤ 0.09) (hs : u2 ≤ 0.198 ∧ s = 0 ∨ s = 0.003)
    (hnum : s + y2 * QLhi u1 u2 y2 + 0.0229 + 50 / 3 * y2 ^ 2
      ≤ 2 * (7 * (1 + 1.3862 * u1) * y1 / ((1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2)))))
        / (2 + 7 * (1 + 1.3862 * u1) * y1 / ((1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2)))))) :
    HLu a u y + (0.0229 + 50 / 3 * y ^ 2) ≤ Real.log (1 + Vf u + Zz u y) := by
  have hu0 : 0 < u := hu10.trans_le hu1
  have hy0 : 0 < y := hy10.trans_le hy1
  rw [HLu_eq a ha u y (by linarith)]
  have hQ := QL_le a ha hu1 hu2 hu10.le hu2' hy0.le hy2 hy2'
  have hQ0 : 0 ≤ QLhi u1 u2 y2 := by
    unfold QLhi
    have hy20 : 0 ≤ y2 := hy0.le.trans hy2
    have hu20 : 0 ≤ u2 := hu0.le.trans hu2
    have hu1' : u1 ≤ 0.205 := hu1.trans (hu2.trans hu2')
    have hA : 0 ≤ 2 + (4 - 2 * 2.437) * u1 + (4 - 2 * 2.437) * u1 ^ 2
        + u2 * y2 * (1 + u2 + u2 * y2) := by
      have : 0 ≤ u2 * y2 * (1 + u2 + u2 * y2) := by positivity
      nlinarith [mul_nonneg hu10.le hu10.le]
    have h1 : 0 ≤ (0.6 + 29 * y2) * u2 + 2 * y2 * u2 ^ 2 := by positivity
    have h2 : 0 ≤ ((0.25 + 12 * y2) * u2 + 2.73 * y2 * u2 + y2) * (1 + 2 * y2 * u2)
        / (1 - y2) ^ 2 := by positivity
    have h3 := div_nonneg hA (sq_nonneg (1 - y2))
    linarith
  have hV0 := Vf_nonneg hu0.le
  have hlog := log_split hV0 (Z := Zz u y) (by unfold Zz; have := consts.2.2.2.2.1; positivity)
  -- the `V` part
  have hpade : u + 2 * u ^ 2 - s ≤ 2 * Vf u / (2 + Vf u) := by
    rcases hs with ⟨h, rfl⟩ | rfl
    · have := pade_ge hu0 (hu2.trans h); linarith
    · exact pade_ge' hu0 (hu2.trans hu2')
  -- the `Z` part: `W ≥ Wlo`
  set Wlo := 7 * (1 + 1.3862 * u1) * y1 / ((1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2))))
    with hWdef
  have hW : Wlo ≤ Zz u y / (1 + Vf u) := by
    rw [hWdef]
    have hl2 := consts.2.2.2.2.1
    unfold Zz
    rw [div_div]
    have hnum' : 7 * (1 + 1.3862 * u1) * y1 ≤ 7 * (1 + 2 * Real.log 2 * u) * y := by
      have : 1 + 1.3862 * u1 ≤ 1 + 2 * Real.log 2 * u := by nlinarith
      have : 0 ≤ 1 + 1.3862 * u1 := by positivity
      nlinarith [mul_le_mul this hy1 hy10.le (by nlinarith)]
    have hden : (1 + y ^ 2 / 2) * (1 + Vf u)
        ≤ (1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2))) := by
      have h1 : 1 + y ^ 2 / 2 ≤ 1 + y2 ^ 2 / 2 := by nlinarith
      have h2 : Vf u ≤ u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2) := by
        refine (Vf_le hu0.le).trans ?_
        have hu20 : 0 ≤ u2 := hu0.le.trans hu2
        have hq : 4 * u ^ 2 / (1 + 1.3862 * u) ≤ 4 * u2 ^ 2 / (1 + 1.3862 * u2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have e1 : u ^ 2 ≤ u2 ^ 2 := pow_le_pow_left₀ hu0.le hu2 2
          have e2 : 0 ≤ u * u2 * (u2 - u) :=
            mul_nonneg (mul_nonneg hu0.le hu20) (by linarith)
          nlinarith
        linarith
      exact mul_le_mul h1 (by linarith) (by linarith [hV0]) (by positivity)
    have hD20 : 0 < (1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2))) := by
      have : 0 ≤ u2 := hu0.le.trans hu2
      positivity
    have hD10 : 0 < (1 + y ^ 2 / 2) * (1 + Vf u) := by
      have : 0 < 1 + Vf u := by linarith
      positivity
    have hZ0 : 0 ≤ 7 * (1 + 2 * Real.log 2 * u) * y := by
      have : 0 ≤ 1 + 2 * Real.log 2 * u := by nlinarith
      positivity
    calc _ ≤ 7 * (1 + 2 * Real.log 2 * u) * y
          / ((1 + y2 ^ 2 / 2) * (1 + (u2 + 4 * u2 ^ 2 / (1 + 1.3862 * u2)))) :=
          div_le_div_of_nonneg_right hnum' hD20.le
      _ ≤ _ := div_le_div_of_nonneg_left hZ0 hD10 hden
  have hWlo0 : 0 ≤ Wlo := by
    rw [hWdef]
    have : 0 ≤ u2 := hu0.le.trans hu2
    positivity
  have hWmono := two_div_mono hWlo0 hW
  have hyQ : y * QL a u y ≤ y2 * QLhi u1 u2 y2 := by
    calc y * QL a u y ≤ y * QLhi u1 u2 y2 := mul_le_mul_of_nonneg_left hQ hy0.le
      _ ≤ y2 * QLhi u1 u2 y2 := mul_le_mul_of_nonneg_right hy2 hQ0
  have hy2sq : 50 / 3 * y ^ 2 ≤ 50 / 3 * y2 ^ 2 := by
    have := pow_le_pow_left₀ hy0.le hy2 2; linarith
  linarith

/-- The lower-bound core for `l ≥ 10`, regime with all primes `p ≤ √x`. -/
theorem HLu_le_log_asym (a : ℕ) (ha : a ≤ 1) {u y : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.1)
    (hy0 : 0 < y) (hy : y ≤ 0.00674) :
    HLu a u y + (10 / 3 * y + 4 / 3 * y / (1 - y)) ≤ Real.log (1 + Vf u + Zz u y) := by
  rw [HLu_eq a ha u y (by linarith)]
  have hQ' := QL_le a ha hu0.le hu le_rfl (by norm_num) hy0.le hy (by norm_num)
  have hQhi : QLhi 0 0.1 0.00674 ≤ 2.151 := by unfold QLhi; norm_num
  have hV0 := Vf_nonneg hu0.le
  have hlog := log_split hV0 (Z := Zz u y) (by unfold Zz; have := consts.2.2.2.2.1; positivity)
  have hpade := pade_ge hu0 (by linarith)
  -- `W ≥ 7y/(1 + y²/2)` since `1 + V ≤ 1 + 2u log 2` for `u ≤ 0.1`
  have hl2 := consts.2.2.2.2.1
  have hV1 : 1 + Vf u ≤ 1 + 2 * Real.log 2 * u := by
    unfold Vf
    have hc : 0 < 1 + 2 * Real.log 2 * u := by positivity
    have : 4 * u ^ 2 / (1 + 2 * Real.log 2 * u) ≤ 0.3862 * u := by
      rw [div_le_iff₀ hc]; nlinarith
    nlinarith
  have hW : 7 * y / (1 + y ^ 2 / 2) ≤ Zz u y / (1 + Vf u) := by
    unfold Zz
    rw [div_div, le_div_iff₀ (by positivity)]
    have : 7 * y / (1 + y ^ 2 / 2) * ((1 + y ^ 2 / 2) * (1 + Vf u)) = 7 * y * (1 + Vf u) := by
      field_simp
    rw [this]
    nlinarith
  have hWm := two_div_mono (by positivity) hW
  have hWe : 2 * (7 * y / (1 + y ^ 2 / 2)) / (2 + 7 * y / (1 + y ^ 2 / 2))
      = y * (14 / (2 + 7 * y + y ^ 2)) := by
    field_simp
    ring
  rw [hWe] at hWm
  have hR : 2.151 + 10 / 3 + 4 / 3 / (1 - y) ≤ 14 / (2 + 7 * y + y ^ 2) := by
    have h1 : 4 / 3 / (1 - y) ≤ 4 / 3 / (1 - 0.00674) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h2 : 14 / (2 + 7 * 0.00674 + 0.00674 ^ 2) ≤ 14 / (2 + 7 * y + y ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have h3 : (2.151 : ℝ) + 10 / 3 + 4 / 3 / (1 - 0.00674) ≤ 14 / (2 + 7 * 0.00674 + 0.00674 ^ 2) := by
      norm_num
    linarith
  have hE : 10 / 3 * y + 4 / 3 * y / (1 - y) = y * (10 / 3 + 4 / 3 / (1 - y)) := by
    have : 1 - y ≠ 0 := by intro h; linarith
    field_simp
  have : y * QL a u y + y * (10 / 3 + 4 / 3 / (1 - y)) ≤ y * (14 / (2 + 7 * y + y ^ 2)) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hy0.le
    linarith [hQ'.trans hQhi]
  linarith

end LLS.Sharp
