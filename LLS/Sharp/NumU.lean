import LLS.Sharp.NumBasic

/-!
# Numerical part, upper bound

`FUu 𝔞 u y = u + 2u² + y·QU 𝔞 u y` with `QU ≤ −1/2` on `0 < u ≤ 0.205`, `0 ≤ y ≤ 0.09`, and
`u + 2u² ≤ 2V/(2 + V) ≤ log(1 + V)` for `u ≤ 0.198` (`V = Vf u`), with slack `0.003` up to
`u = 0.205`.
-/

namespace LLS.Sharp

open Real

lemma G3par_bounds :
    -0.3612 ≤ G3par 1 ∧ G3par 1 ≤ -0.3604 ∧ -0.5544 ≤ G3par 0 ∧ G3par 0 ≤ -0.5535 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := consts
  simp only [G3par, ↓reduceIte, one_ne_zero]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma kU_bounds (a : ℕ) (ha : a ≤ 1) : 0.0228 ≤ kU a ∧ kU a ≤ 0.7167 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := consts
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    simp only [kU, Gpar, ↓reduceIte, one_ne_zero] <;> constructor <;> linarith

lemma QU_le (a : ℕ) (ha : a ≤ 1) {u y : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.205) (hy0 : 0 ≤ y)
    (hy : y ≤ 0.09) : QU a u y ≤ -1 / 2 := by
  obtain ⟨hk0, hk1⟩ := kU_bounds a ha
  obtain ⟨g1, g2, g3, g4⟩ := G3par_bounds
  set k := kU a
  set e := eU a u y with he
  -- bounds on `e`
  have he1 : -e ≤ 0.27 ∧ y * e ≤ 0.0081 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · simp only [he, eU, ↓reduceIte]
      constructor
      · nlinarith [mul_nonneg hy0 hu0.le]
      · nlinarith [mul_nonneg hy0 hu0.le, mul_nonneg (mul_nonneg hy0 hy0) hu0.le]
    · simp only [he, eU, one_ne_zero, ↓reduceIte]
      constructor
      · nlinarith [mul_nonneg hy0 hu0.le]
      · nlinarith [mul_nonneg hy0 hu0.le, mul_nonneg (mul_nonneg hy0 hy0) hu0.le]
  obtain ⟨he1, he2⟩ := he1
  have hku : 0.85 ≤ 1 - k * u := by nlinarith
  have hD1 : 1 ≤ (1 + y) ^ 2 := by nlinarith
  have hD2 : (1 + y) ^ 2 ≤ 1.1881 := by nlinarith
  -- first term
  have hN : -(1 - k * u) * (2 + y) - e - 2 * u * (1 - k * u - y * e) ≤ -1.43 := by
    have : 0 ≤ 2 * u * (1 - k * u - y * e) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  have hT1 : (-(1 - k * u) * (2 + y) - e - 2 * u * (1 - k * u - y * e)) / (1 + y) ^ 2
      ≤ -1.2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hT2 : 2 * u * (y / 2 * (1 + u) - 1 - 2 * u - y ^ 2 * u / 2) / (1 + y) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    nlinarith [mul_nonneg hy0 hu0.le]
  have hT3 : (0.6 + 29 * y) * u + 2 * y * u ^ 2 ≤ 0.69 := by
    nlinarith [mul_nonneg hy0 hu0.le, mul_le_mul hy hu hu0.le (by norm_num : (0:ℝ) ≤ 0.09)]
  simp only [QU]
  linarith

lemma Vf_ge {u : ℝ} (hu0 : 0 ≤ u) : u + 4 * u ^ 2 / (1 + 1.3863 * u) ≤ Vf u := by
  have h := consts.2.2.2.2.2
  unfold Vf
  gcongr
  nlinarith

lemma two_div_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : 2 * a / (2 + a) ≤ 2 * b / (2 + b) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma pade_ge {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.198) :
    u + 2 * u ^ 2 ≤ 2 * Vf u / (2 + Vf u) := by
  set V := u + 4 * u ^ 2 / (1 + 1.3863 * u)
  have hV : V ≤ Vf u := Vf_ge hu0.le
  have hV0 : 0 ≤ V := by positivity
  refine le_trans ?_ (two_div_mono hV0 hV)
  have hc : 0 < 1 + 1.3863 * u := by positivity
  have hVe : V * (1 + 1.3863 * u) = u * (1 + 1.3863 * u) + 4 * u ^ 2 := by
    simp only [V]; field_simp
  rw [le_div_iff₀ (by linarith)]
  -- `V (2 − u − 2u²) ≥ 2(u + 2u²)`
  have key : 2 * (u + 2 * u ^ 2) * (1 + 1.3863 * u) ≤ V * (2 - u - 2 * u ^ 2) * (1 + 1.3863 * u) := by
    have : V * (2 - u - 2 * u ^ 2) * (1 + 1.3863 * u)
        = (u * (1 + 1.3863 * u) + 4 * u ^ 2) * (2 - u - 2 * u ^ 2) := by rw [← hVe]; ring
    rw [this]
    have : 0 ≤ u * (3 - 12.9315 * u - 10.7726 * u ^ 2) := by
      apply mul_nonneg hu0.le; nlinarith
    nlinarith
  have := le_of_mul_le_mul_right key hc
  nlinarith

lemma pade_ge' {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.205) :
    u + 2 * u ^ 2 - 0.003 ≤ 2 * Vf u / (2 + Vf u) := by
  set V := u + 4 * u ^ 2 / (1 + 1.3863 * u)
  have hV : V ≤ Vf u := Vf_ge hu0.le
  have hV0 : 0 ≤ V := by positivity
  refine le_trans ?_ (two_div_mono hV0 hV)
  have hc : 0 < 1 + 1.3863 * u := by positivity
  have hVe : V * (1 + 1.3863 * u) = u * (1 + 1.3863 * u) + 4 * u ^ 2 := by
    simp only [V]; field_simp
  rw [le_div_iff₀ (by linarith)]
  have key : (u + 2 * u ^ 2 - 0.003) * (2 + V) * (1 + 1.3863 * u) ≤ 2 * V * (1 + 1.3863 * u) := by
    have e : (u + 2 * u ^ 2 - 0.003) * (2 + V) * (1 + 1.3863 * u)
        = (u + 2 * u ^ 2 - 0.003) * (2 * (1 + 1.3863 * u) + (u * (1 + 1.3863 * u) + 4 * u ^ 2)) := by
      rw [← hVe]; ring
    have e2 : 2 * V * (1 + 1.3863 * u) = 2 * (u * (1 + 1.3863 * u) + 4 * u ^ 2) := by
      rw [← hVe]; ring
    rw [e, e2]
    nlinarith [mul_nonneg hu0.le hu0.le, mul_nonneg (mul_nonneg hu0.le hu0.le) hu0.le]
  exact le_of_mul_le_mul_right key hc

/-- The upper-bound core: `FUu 𝔞 u y ≤ log(1 + V(u))` when `0 < u ≤ 0.205`, `0 ≤ y ≤ 0.09`,
and `y ≥ 0.006` whenever `u > 0.198`. -/
theorem FUu_le_log (a : ℕ) (ha : a ≤ 1) {u y : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.205) (hy0 : 0 ≤ y)
    (hy : y ≤ 0.09) (hy' : 0.198 < u → 0.006 ≤ y) :
    FUu a u y ≤ Real.log (1 + Vf u) := by
  rw [FUu_eq a ha u y hy0]
  have hQ := QU_le a ha hu0 hu hy0 hy
  have hV0 : 0 ≤ Vf u := by
    unfold Vf; have := consts.2.2.2.2.1; positivity
  have hlog := log_one_add_ge hV0
  have hyQ : y * QU a u y ≤ -(y / 2) := by nlinarith
  rcases le_or_gt u 0.198 with h | h
  · have := pade_ge hu0 h; nlinarith
  · have := pade_ge' hu0 hu; have := hy' h; nlinarith

end LLS.Sharp
