import Schoenfeld.PsiInt
import Schoenfeld.Statement

/-!
# `|ψ(x) − x| < √x log² x / 8` for `x ≥ 73.2`, under RH

`psi_real_bound` gives, for every natural `h ≥ 1` with `x ≥ h + 2`,
`|ψ(x) − x| ≤ h/2 + 3.6 + 1.5/h + √(x+h) F(2(x+h)/h)`. Two regimes:

* `psi_mid` (`73.2 ≤ x ≤ 2^18`): `F(T) ≤ T/20`, `h ≈ 0.447 x^{3/4}` constant on each of 15
  intervals; on each interval `[a, b]` the bound at `b` is compared with `√a log² a / 8`, using
  rational bounds for `√` and `log a ≥ k log 2 + 1 − 2^k/a` (`piece`). Worst ratio `0.98`.
* `psi_large` (`x ≥ 2^18`): `F(T) ≤ 0.9 Jb(10T) + 2 Vb(T) + 2.75 Vb(5)` with `h = ⌈4√x⌉`, so
  `T ≈ √x/2`; this reduces to a quadratic inequality in `u = log x ≥ 18 log 2`. Worst ratio
  `0.82` at `x = 2^18`, tending to `0.45` (so the constant would approach `0.056` for huge `x`).
-/

namespace Schoenfeld

open Real Chebyshev

lemma log_two_bounds : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

lemma log_ge_of_pow_le {a : ℝ} (k : ℕ) (hk : (2 : ℝ) ^ k ≤ a) :
    k * 0.6931471803 + (1 - 2 ^ k / a) ≤ Real.log a := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have ha : 0 < a := h2k.trans_le hk
  have e : Real.log a = Real.log (2 ^ k) + Real.log (a / 2 ^ k) := by
    rw [← Real.log_mul h2k.ne' (by positivity), mul_div_cancel₀ _ h2k.ne']
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < a / 2 ^ k by positivity)
  rw [inv_div] at h1
  rw [e, Real.log_pow]
  have := log_two_bounds.1
  have : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
    mul_le_mul_of_nonneg_left this.le (Nat.cast_nonneg k)
  linarith

/-- One interval of the middle range. -/
lemma piece (hRH : RiemannHypothesis) {a b p q : ℝ} (h k : ℕ) (hh : 1 ≤ h)
    (hha : (h : ℝ) + 2 ≤ a) (_hp : 0 ≤ p) (hpa : p ^ 2 ≤ a) (hq : 0 ≤ q) (hqb : b + h ≤ q ^ 2)
    (hk : (2 : ℝ) ^ k ≤ a) (hl : 0 ≤ k * 0.6931471803 + (1 - 2 ^ k / a))
    (hnum : (h : ℝ) / 2 + 3.6 + 1.5 / h + q * (b + h) / (10 * h)
      < 1 / 8 * (p * (k * 0.6931471803 + (1 - 2 ^ k / a)) ^ 2))
    {x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    |ψ x - x| < 1 / 8 * (√x * Real.log x ^ 2) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hB := psi_real_bound hRH x h hh (by linarith)
  have hT : 0 ≤ 2 * (x + h) / h := by
    have : 0 ≤ x := by linarith
    positivity
  have hF := fmin_tsum_le_triv hRH hT
  have hsq : √(x + h) ≤ q := by
    rw [show q = √(q ^ 2) from (Real.sqrt_sq hq).symm]; exact Real.sqrt_le_sqrt (by linarith)
  have hz : √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ ≤ q * (b + h) / (10 * h) := by
    have hF0 : 0 ≤ ∑' ρ, fmin (2 * (x + h) / h) ρ := tsum_nonneg (fmin_nonneg hT)
    calc √(x + h) * ∑' ρ, fmin (2 * (x + h) / h) ρ ≤ q * (2 * (x + h) / h / 20) :=
          mul_le_mul hsq hF (by positivity) hq
      _ = q * ((x + h) / (10 * h)) := by ring
      _ ≤ q * ((b + h) / (10 * h)) := by gcongr
      _ = q * (b + h) / (10 * h) := by ring
  have hpx : p ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
  have hlx : k * 0.6931471803 + (1 - 2 ^ k / a) ≤ Real.log x :=
    (log_ge_of_pow_le k hk).trans (Real.log_le_log (by linarith [pow_pos (two_pos (α := ℝ)) k]) hax)
  have hR : 1 / 8 * (p * (k * 0.6931471803 + (1 - 2 ^ k / a)) ^ 2)
      ≤ 1 / 8 * (√x * Real.log x ^ 2) := by
    gcongr
  linarith

theorem psi_mid (hRH : RiemannHypothesis) {x : ℝ} (h1 : 73.2 ≤ x) (h2 : x ≤ 262144) :
    |ψ x - x| < 1 / 8 * (√x * Real.log x ^ 2) := by
  rcases le_or_gt x (476/5 : ℝ) with hb | hb
  · exact piece hRH (a := (366/5 : ℝ)) (b := (476/5 : ℝ)) (p := (171/20 : ℝ)) (q := (1031/100 : ℝ)) 11 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (619/5 : ℝ) with hb | hb
  · exact piece hRH (a := (476/5 : ℝ)) (b := (619/5 : ℝ)) (p := (39/4 : ℝ)) (q := (587/50 : ℝ)) 14 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (1857/10 : ℝ) with hb | hb
  · exact piece hRH (a := (619/5 : ℝ)) (b := (1857/10 : ℝ)) (p := (278/25 : ℝ)) (q := (356/25 : ℝ)) 17 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (1393/5 : ℝ) with hb | hb
  · exact piece hRH (a := (1857/10 : ℝ)) (b := (1393/5 : ℝ)) (p := (681/50 : ℝ)) (q := (867/50 : ℝ)) 22 7 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (4179/10 : ℝ) with hb | hb
  · exact piece hRH (a := (1393/5 : ℝ)) (b := (4179/10 : ℝ)) (p := (1669/100 : ℝ)) (q := (2117/100 : ℝ)) 30 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (4179/5 : ℝ) with hb | hb
  · exact piece hRH (a := (4179/10 : ℝ)) (b := (4179/5 : ℝ)) (p := (511/25 : ℝ)) (q := (1481/50 : ℝ)) 41 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (8358/5 : ℝ) with hb | hb
  · exact piece hRH (a := (4179/5 : ℝ)) (b := (8358/5 : ℝ)) (p := (2891/100 : ℝ)) (q := (4173/100 : ℝ)) 69 9 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (16716/5 : ℝ) with hb | hb
  · exact piece hRH (a := (8358/5 : ℝ)) (b := (16716/5 : ℝ)) (p := (1022/25 : ℝ)) (q := (5883/100 : ℝ)) 117 10 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (33432/5 : ℝ) with hb | hb
  · exact piece hRH (a := (16716/5 : ℝ)) (b := (33432/5 : ℝ)) (p := (2891/50 : ℝ)) (q := (8297/100 : ℝ)) 197 11 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (66864/5 : ℝ) with hb | hb
  · exact piece hRH (a := (33432/5 : ℝ)) (b := (66864/5 : ℝ)) (p := (8177/100 : ℝ)) (q := (11707/100 : ℝ)) 331 12 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (133728/5 : ℝ) with hb | hb
  · exact piece hRH (a := (66864/5 : ℝ)) (b := (133728/5 : ℝ)) (p := (2891/25 : ℝ)) (q := (4131/25 : ℝ)) 556 13 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (267456/5 : ℝ) with hb | hb
  · exact piece hRH (a := (133728/5 : ℝ)) (b := (267456/5 : ℝ)) (p := (8177/50 : ℝ)) (q := (2333/10 : ℝ)) 935 14 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (534912/5 : ℝ) with hb | hb
  · exact piece hRH (a := (267456/5 : ℝ)) (b := (534912/5 : ℝ)) (p := (5782/25 : ℝ)) (q := (8237/25 : ℝ)) 1572 15 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  rcases le_or_gt x (1069824/5 : ℝ) with hb | hb
  · exact piece hRH (a := (534912/5 : ℝ)) (b := (1069824/5 : ℝ)) (p := (8177/25 : ℝ)) (q := (23271/50 : ℝ)) 2644 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) hb
  exact piece hRH (a := (1069824/5 : ℝ)) (b := (262144 : ℝ)) (p := (11564/25 : ℝ)) (q := (51633/100 : ℝ)) 4447 17 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num at h1 ⊢; linarith) (by norm_num at h1 ⊢; linarith)


lemma quad_mono {ℓ ℓp L : ℝ} (h1 : ℓ ≤ ℓp) (h2 : 2 * L ≤ ℓ + ℓp) :
    ℓ ^ 2 / 4 - L / 2 * ℓ ≤ ℓp ^ 2 / 4 - L / 2 * ℓp := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

lemma F_poly {u l5 L l2 : ℝ} (hu : 12 ≤ u) (hl5 : 0 ≤ l5) (hl5' : l5 ≤ 2 * l2 + 1 / 4)
    (hl2 : 0.6931471803 < l2) (hl2' : l2 < 0.6931471808) (hL : l2 + 1.144 ≤ L) (hL' : L ≤ 3 * l2) :
    0.9 * ((u / 2 + l5 + 1 / 128) ^ 2 / 4 - L / 2 * (u / 2 + l5 + 1 / 128)
        - (l2 ^ 2 / 4 - L / 2 * l2 - 6 / 5))
      + 2 * ((u / 2 - l2 + 1 / 128) / 2 - L / 2 + 0.0141) + 2.75 * (l5 / 2 - L / 2 + 12 / 25)
      ≤ 0.05625 * u ^ 2 + 0.4566 * u + 0.887 := by
  have hA : 0 ≤ (L - (l2 + 1.144)) * (0.45 * (u / 2 + l5 + 1 / 128 - l2) + 2.375) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hB : 0 ≤ u * (2 * l2 + 1 / 4 - l5) := mul_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ (2 * l2 + 1 / 4 - l5) * (2 * l2 + 1 / 4 + l5 + 1 / 64) :=
    mul_nonneg (by linarith) (by linarith)
  have hD : 0 ≤ (3 * l2 - L) * l2 := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma fin_ineq {s u hR : ℝ} (hs : 512 ≤ s) (hu : 12.47 ≤ u) (hh1 : 4 * s ≤ hR)
    (hh2 : hR < 4 * s + 1) :
    hR / 2 + 3.6 + 1.5 / hR + (s + 2.01) * (0.05625 * u ^ 2 + 0.4566 * u + 0.887)
      < 1 / 8 * (s * u ^ 2) := by
  have hR0 : 0 < hR := by linarith
  have h15 : 1.5 / hR ≤ 0.001 := by rw [div_le_iff₀ hR0]; linarith
  set P := 0.05625 * u ^ 2 + 0.4566 * u + 0.887 with hP
  set Q := u ^ 2 / 8 - P - 2 with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ, hP]; nlinarith
  have hPu : P ≤ 0.13 * u ^ 2 := by rw [hP]; nlinarith
  have hsQ : 512 * Q ≤ s * Q := mul_le_mul_of_nonneg_right hs hQ0
  have h512 : 2.01 * (0.13 * u ^ 2) + 4.101 < 512 * Q := by rw [hQ, hP]; nlinarith
  have : 1 / 8 * (s * u ^ 2) = s * Q + s * P + 2 * s := by rw [hQ]; ring
  nlinarith

/-- The analytic range `x ≥ 2^18`. -/
theorem psi_large (hRH : RiemannHypothesis) {x : ℝ} (hx : 262144 ≤ x) :
    |ψ x - x| < 1 / 8 * (√x * Real.log x ^ 2) := by
  obtain ⟨l2lo, l2hi⟩ := log_two_bounds
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs512 : 512 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs0 : 0 < s := by linarith
  set u := Real.log x with hu
  have hus : Real.log s = u / 2 := by
    rw [hu, ← hs2, Real.log_pow]; push_cast; ring
  have hu0 : 18 * 0.6931471803 ≤ u := by
    have h1 := Real.log_le_log (by norm_num) hx
    have e : Real.log (262144 : ℝ) = 18 * Real.log 2 := by
      rw [show (262144 : ℝ) = 2 ^ 18 by norm_num, Real.log_pow]; norm_num
    linarith
  -- the step `h = ⌈4√x⌉`
  set h : ℕ := ⌈4 * s⌉₊ with hhdef
  have hh1 : 4 * s ≤ h := Nat.le_ceil _
  have hh2 : (h : ℝ) < 4 * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hh0 : (0 : ℝ) < h := by linarith
  have hh : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  have hB := psi_real_bound hRH x h hh (by nlinarith)
  set T := 2 * (x + h) / h with hTdef
  have hTeq : T = 2 * x / h + 2 := by rw [hTdef]; field_simp
  have hT1 : T ≤ s / 2 + 2 := by
    have : 2 * x / h ≤ s / 2 := by
      rw [div_le_iff₀ hh0, ← hs2]; nlinarith
    linarith
  have hT2 : s / 3 ≤ T := by
    have : s / 3 ≤ 2 * x / h := by
      rw [le_div_iff₀ hh0, ← hs2]; nlinarith
    linarith
  have hT0 : 2 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hF := fmin_tsum_le hRH hT0
  have hF0 : 0 ≤ ∑' ρ, fmin T ρ := tsum_nonneg (fmin_nonneg (by linarith))
  -- logarithms
  set L := Real.log (2 * π) with hL
  have hlpi_lo : (1.144 : ℝ) < Real.log π := Erdos985.Analytic.PrincipalAux.log_pi_gt'
  have hlpi_hi : Real.log π < 2 * Real.log 2 := by
    rw [show 2 * Real.log 2 = Real.log (2 ^ 2) by rw [Real.log_pow]; push_cast; ring]
    exact Real.log_lt_log Real.pi_pos (by nlinarith [Real.pi_lt_d2])
  have hLe : L = Real.log 2 + Real.log π := Real.log_mul (by norm_num) Real.pi_pos.ne'
  set l5 := Real.log 5 with hl5
  have hl5_hi : l5 ≤ 2 * Real.log 2 + 1 / 4 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow] at h1
    norm_num at h1 ⊢; linarith
  have hl5_lo : 0 ≤ l5 := Real.log_nonneg (by norm_num)
  have hlT : Real.log T ≤ u / 2 - Real.log 2 + 1 / 128 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < T / (s / 2) by positivity)
    rw [Real.log_div hTpos.ne' (by positivity), Real.log_div hs0.ne' (by norm_num), hus] at h1
    have : T / (s / 2) - 1 ≤ 1 / 128 := by
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]; linarith
    linarith
  set ℓ := Real.log (10 * T) with hℓ
  have hℓe : ℓ = Real.log 2 + l5 + Real.log T := by
    rw [hℓ, Real.log_mul (by norm_num) hTpos.ne', show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hℓlo : 4 * Real.log 2 ≤ ℓ := by
    have := Real.log_le_log (by norm_num) (show (16 : ℝ) ≤ 10 * T by linarith)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  set ℓp := u / 2 + l5 + 1 / 128 with hℓpd
  have hℓp : ℓ ≤ ℓp := by rw [hℓe]; linarith
  -- the three pieces of `F`
  have hJ : Jb (10 * T) ≤ ℓp ^ 2 / 4 - L / 2 * ℓp - (Real.log 2 ^ 2 / 4 - L / 2 * Real.log 2 - 6 / 5) := by
    unfold Jb Jp
    rw [← hℓ, ← hL]
    have h1 : 0 ≤ 12 / 5 / (10 * T) := by positivity
    have h2 := quad_mono (L := L) hℓp (by linarith)
    linarith
  have hVT : Vb T ≤ (u / 2 - Real.log 2 + 1 / 128) / 2 - L / 2 + 0.0141 := by
    unfold Vb
    have : 12 / 5 / T ≤ 0.0141 := by
      rw [div_le_iff₀ hTpos]; nlinarith
    linarith
  have hV5 : Vb 5 = l5 / 2 - L / 2 + 12 / 25 := by rw [hl5, hL]; unfold Vb; norm_num
  have hP : ∑' ρ, fmin T ρ ≤ 0.05625 * u ^ 2 + 0.4566 * u + 0.887 := by
    have := F_poly (u := u) (l5 := l5) (L := L) (l2 := Real.log 2) (by linarith) hl5_lo hl5_hi
      l2lo l2hi (by linarith) (by linarith)
    rw [hV5] at hF
    rw [hℓpd] at hJ
    linarith
  -- assembly
  have hsq : √(x + h) ≤ s + 2.01 := by
    rw [show s + 2.01 = √((s + 2.01) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    have e : (s + 2.01) ^ 2 = s ^ 2 + 4.02 * s + 4.0401 := by ring
    have hle : x + h ≤ (s + 2.01) ^ 2 := by rw [e, hs2]; linarith
    exact Real.sqrt_le_sqrt hle
  have hz : √(x + h) * ∑' ρ, fmin T ρ ≤ (s + 2.01) * (0.05625 * u ^ 2 + 0.4566 * u + 0.887) :=
    mul_le_mul hsq hP hF0 (by linarith)
  have hu1 : (12.47 : ℝ) ≤ u := by linarith
  have hfin := fin_ineq (u := u) hs512 hu1 hh1 hh2
  calc |ψ x - x| ≤ h / 2 + 3.6 + 1.5 / h + √(x + h) * ∑' ρ, fmin T ρ := hB
    _ < 1 / 8 * (√x * u ^ 2) := by linarith

/-- **`|ψ(x) − x| < √x log² x / 8` for `x ≥ 73.2`, under RH.** -/
theorem psiBound_of_RH (hRH : RiemannHypothesis) : PsiBound (1 / 8) 73.2 := by
  intro x hx
  rcases le_or_gt x 262144 with h | h
  · exact psi_mid hRH hx h
  · exact psi_large hRH h.le

end Schoenfeld
