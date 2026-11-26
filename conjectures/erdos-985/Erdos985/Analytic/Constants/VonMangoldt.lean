import Mathlib
import Erdos985.Analytic.Digamma.EulerMascheroni

/-!
# Numerical bound for `∑ Λ(n) n^{-3/2}`

Strategy: with `S = ∑ Λ(n) n^{-3/2}`, `Z = ∑ n^{-3/2}` and `D = ∑ log n · n^{-3/2}`, the
Dirichlet convolution identity `Λ ⋆ 1 = log` gives `S · Z = D`. We bound `Z` from below and `D`
from above by the exact partial sums up to `n = 20` (with rational bounds on square roots and on
`log p` for primes `p ≤ 19`) plus elementary telescoping tail estimates:

* `n^{-3/2} ≥ 2/√n − 2/√(n+1)`;
* `log n · n^{-3/2} ≤ G(n−1) − G(n)` with `G(x) = (2 log x + 4)/√x` (mean value theorem and
  monotonicity of `log x / x^{3/2}` on `[2, ∞)`).

This yields `Z ≥ 2.6069`, `D ≤ 3.949`, hence `S ≤ 1.52` (the true value is `≈ 1.50523`).
-/

set_option linter.unusedSimpArgs false

open Real ArithmeticFunction

namespace Erdos985.Analytic.ConstantsAux

lemma rpow32 {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

lemma term_eq (f : ℕ → ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) (3 / 2) n = ((f n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rfl

lemma lseries_eq (f : ℕ → ℝ) :
    LSeries (fun n => (f n : ℂ)) (3 / 2) = ((∑' n : ℕ, f n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (term_eq f)

lemma summable_of_lseries (f : ℕ → ℝ) (h : LSeriesSummable (fun n => (f n : ℂ)) (3 / 2)) :
    Summable fun n : ℕ => f n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have : LSeries.term (fun n => (f n : ℂ)) (3 / 2) =
      fun n => ((f n / (n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := funext (term_eq f)
  rw [LSeriesSummable, this] at h
  exact Complex.summable_ofReal.mp h

lemma re32 : 1 < (3 / 2 : ℂ).re := by norm_num

lemma summable_Λ : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
  summable_of_lseries _ (LSeriesSummable_vonMangoldt re32)

lemma summable_one : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  refine summable_of_lseries (fun _ => 1) ?_
  have := LSeriesSummable_one_iff.mpr re32
  convert this using 2

lemma summable_log : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  refine summable_of_lseries (fun n => Real.log n) ?_
  have := (LSeriesSummable_vonMangoldt re32).convolution (LSeriesSummable_one_iff.mpr re32)
  rw [convolution_vonMangoldt_const_one] at this
  convert this using 2 with n
  simp [Complex.natCast_log]

lemma mul_eq :
    (∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)) =
      ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h := LSeries_convolution' (LSeriesSummable_vonMangoldt re32)
    (LSeriesSummable_one_iff.mpr re32)
  rw [convolution_vonMangoldt_const_one] at h
  have e1 := lseries_eq (fun n => (Λ n : ℝ))
  have e2 := lseries_eq (fun _ => (1 : ℝ))
  have e3 := lseries_eq (fun n : ℕ => Real.log n)
  have h1 : (1 : ℕ → ℂ) = fun _ => ((1 : ℝ) : ℂ) := by ext; simp
  have h3 : (fun n : ℕ => Complex.log n) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    ext n; simp [Complex.natCast_log]
  rw [h1, h3, e1, e2, e3] at h
  exact_mod_cast h.symm

lemma z_step {x : ℝ} (hx : 1 ≤ x) : 2 / √x - 2 / √(x + 1) ≤ 1 / (x * √x) := by
  have ha : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < √(x + 1) := Real.sqrt_pos.mpr (by linarith)
  have hab : √x ≤ √(x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hx2 : √x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hy2 : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  set a := √x
  set b := √(x + 1)
  rw [← hx2, div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have : b - a = 1 / (a + b) := by
    field_simp; nlinarith
  nlinarith [mul_pos ha hb, mul_pos (mul_pos ha ha) ha]

lemma g_anti {c y : ℝ} (hc : 2 ≤ c) (hcy : c ≤ y) :
    Real.log y / (y * √y) ≤ Real.log c / (c * √c) := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < y := by linarith
  have ha : 0 < √c := Real.sqrt_pos.mpr hc0
  have hb : 0 < √y := Real.sqrt_pos.mpr hy0
  have hab : √c ≤ √y := Real.sqrt_le_sqrt hcy
  have hx2 : √c ^ 2 = c := Real.sq_sqrt hc0.le
  have hy2 : √y ^ 2 = y := Real.sq_sqrt hy0.le
  have hL : 2 / 3 ≤ Real.log c := by
    have := Real.log_le_log (by norm_num) hc
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log y - Real.log c ≤ y / c - 1 := by
    rw [← Real.log_div hy0.ne' hc0.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  set a := √c
  set b := √y
  rw [← hx2, ← hy2] at hlog ⊢
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : b ^ 2 / a ^ 2 - 1 = (b ^ 2 - a ^ 2) / a ^ 2 := by field_simp
  rw [hq] at hlog
  have hlog' : (Real.log (b ^ 2) - Real.log (a ^ 2)) * a ^ 2 ≤ b ^ 2 - a ^ 2 := by
    rwa [le_div_iff₀ (by positivity)] at hlog
  have key : (b ^ 2 - a ^ 2) * a ≤ Real.log (a ^ 2) * (b ^ 3 - a ^ 3) := by
    have h1 : (b ^ 2 - a ^ 2) * a ≤ 2 / 3 * (b ^ 3 - a ^ 3) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab))
        (by positivity : (0 : ℝ) ≤ 2 * b + a)]
    have h2 : 0 ≤ b ^ 3 - a ^ 3 := by
      have := pow_le_pow_left₀ ha.le hab 3
      linarith
    have hL' : 2 / 3 ≤ Real.log (a ^ 2) := by rw [hx2]; exact hL
    nlinarith
  nlinarith [mul_pos ha (mul_pos ha ha)]

noncomputable def Gf (x : ℝ) : ℝ := (2 * Real.log x + 4) / √x

lemma hasDerivAt_Gf {t : ℝ} (ht : 0 < t) :
    HasDerivAt Gf (-(Real.log t / (t * √t))) t := by
  have hs : 0 < √t := Real.sqrt_pos.mpr ht
  have h1 : HasDerivAt (fun x => 2 * Real.log x + 4) (2 * t⁻¹) t :=
    ((Real.hasDerivAt_log ht.ne').const_mul 2).add_const 4
  have h2 := Real.hasDerivAt_sqrt ht.ne'
  have := h1.div h2 hs.ne'
  unfold Gf
  convert this using 1
  have hst : √t ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  rw [hst]
  ring

lemma d_step {x : ℝ} (hx : 2 ≤ x) :
    Real.log (x + 1) / ((x + 1) * √(x + 1)) ≤ Gf x - Gf (x + 1) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Gf (fun t => -(Real.log t / (t * √t)))
    (by linarith : x < x + 1)
    (fun t ht => (hasDerivAt_Gf (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_Gf (by linarith [ht.1]))
  have : Gf x - Gf (x + 1) = Real.log c / (c * √c) := by
    rw [show x + 1 - x = 1 by ring, div_one] at hcd
    linarith
  rw [this]
  exact g_anti (by linarith [hc.1]) hc.2.le

lemma Gf_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Gf x := by
  unfold Gf
  have := Real.log_nonneg hx
  positivity

lemma z_tail (K M : ℕ) (hK : 1 ≤ K) :
    2 / √(K : ℝ) - 2 / √((K : ℝ) + M) ≤
      ∑' i : ℕ, (1 : ℝ) / (((i + K : ℕ) : ℝ)) ^ (3 / 2 : ℝ) := by
  have hs : Summable fun i : ℕ => (1 : ℝ) / (((i + K : ℕ) : ℝ)) ^ (3 / 2 : ℝ) :=
    (summable_nat_add_iff K).mpr summable_one
  refine le_trans ?_ (hs.sum_le_tsum (Finset.range M) (fun i _ => by positivity))
  have htel := Finset.sum_range_sub' (fun i : ℕ => 2 / √((K : ℝ) + i)) M
  simp only [Nat.cast_zero, add_zero] at htel
  rw [← htel]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hx : (1 : ℝ) ≤ (K : ℝ) + i := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
  have := z_step hx
  rw [rpow32 (by positivity)]
  push_cast
  rw [show (K : ℝ) + ((i : ℝ) + 1) = (K : ℝ) + i + 1 by ring, add_comm (i : ℝ) (K : ℝ)]
  exact this

lemma d_tail (K : ℕ) (hK : 3 ≤ K) :
    ∑' i : ℕ, Real.log ((i + K : ℕ) : ℝ) / (((i + K : ℕ) : ℝ)) ^ (3 / 2 : ℝ) ≤
      Gf ((K : ℝ) - 1) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  refine Real.tsum_le_of_sum_range_le (fun i => ?_) (fun M => ?_)
  · have : (1 : ℝ) ≤ ((i + K : ℕ) : ℝ) := by push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := Real.log_nonneg this
    positivity
  · have htel := Finset.sum_range_sub' (fun i : ℕ => Gf ((K : ℝ) - 1 + i)) M
    simp only [Nat.cast_zero, add_zero] at htel
    have hG : 0 ≤ Gf ((K : ℝ) - 1 + M) :=
      Gf_nonneg (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)])
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (le_of_eq_of_le htel (by linarith))
    have hx : (2 : ℝ) ≤ (K : ℝ) - 1 + i := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := d_step hx
    rw [rpow32 (by positivity)]
    push_cast
    rw [show (K : ℝ) - 1 + ((i : ℝ) + 1) = (K : ℝ) - 1 + i + 1 by ring,
      show (i : ℝ) + K = (K : ℝ) - 1 + i + 1 by ring]
    exact this

lemma log_succ_le' (m : ℝ) (hm : 0 < m) :
    Real.log (m + 1) ≤ Real.log m + (1 / (2 * m) + 1 / (2 * (m + 1))) := by
  have h := Erdos985.Analytic.DigammaAux.log_one_add_inv_le hm
  have e : Real.log (m + 1) = Real.log m + Real.log (1 + m⁻¹) := by
    rw [← Real.log_mul hm.ne' (by positivity)]
    congr 1
    field_simp
  linarith

lemma zb (n u : ℝ) (hn : 0 < n) (hu0 : 0 ≤ u) (hu : n ≤ u ^ 2) :
    1 / (n * u) ≤ 1 / (n * √n) := by
  have hs : √n ≤ u := by
    rw [show u = √(u ^ 2) from (Real.sqrt_sq hu0).symm]; exact Real.sqrt_le_sqrt hu
  have : 0 < √n := Real.sqrt_pos.mpr hn
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hs hn.le)

lemma db (n l : ℝ) (hn : 1 ≤ n) (hl0 : 0 < l) (hl : l ^ 2 ≤ n) :
    Real.log n / (n * √n) ≤ Real.log n / (n * l) := by
  have hs : l ≤ √n := Real.le_sqrt_of_sq_le hl
  exact div_le_div_of_nonneg_left (Real.log_nonneg hn) (by positivity)
    (mul_le_mul_of_nonneg_left hs (by linarith))

lemma log_primes_le :
    Real.log 2 ≤ 0.6931471808 ∧ Real.log 3 ≤ 1.098749 ∧ Real.log 5 ≤ 1.609512 ∧
    Real.log 7 ≤ 1.945980 ∧ Real.log 11 ≤ 2.398001 ∧ Real.log 13 ≤ 2.565052 ∧
    Real.log 17 ≤ 2.833350 ∧ Real.log 19 ≤ 2.944613 := by
  have p2 := Real.log_two_lt_d9.le
  have p3 : 2 * Real.log 3 ≤ 3 * Real.log 2 + (1 / (2 * 8) + 1 / (2 * (8 + 1))) := by
    have h := log_succ_le' 8 (by norm_num)
    have e1 : Real.log (8 + 1) = 2 * Real.log 3 := by
      rw [show (8 : ℝ) + 1 = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2^3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p5 : 2 * Real.log 5 ≤ 3 * Real.log 2 + Real.log 3 + (1 / (2 * 24) + 1 / (2 * (24 + 1))) := by
    have h := log_succ_le' 24 (by norm_num)
    have e1 : Real.log (24 + 1) = 2 * Real.log 5 := by
      rw [show (24 : ℝ) + 1 = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
      rw [show (24 : ℝ) = 2^3 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p7 : 2 * Real.log 7 ≤ 4 * Real.log 2 + Real.log 3 + (1 / (2 * 48) + 1 / (2 * (48 + 1))) := by
    have h := log_succ_le' 48 (by norm_num)
    have e1 : Real.log (48 + 1) = 2 * Real.log 7 := by
      rw [show (48 : ℝ) + 1 = 7 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
      rw [show (48 : ℝ) = 2^4 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p11 : 2 * Real.log 11 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 5 + (1 / (2 * 120) + 1 / (2 * (120 + 1))) := by
    have h := log_succ_le' 120 (by norm_num)
    have e1 : Real.log (120 + 1) = 2 * Real.log 11 := by
      rw [show (120 : ℝ) + 1 = 11 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 120 = 3 * Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (120 : ℝ) = 2^3 * 3 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p13 : 2 * Real.log 13 ≤ 3 * Real.log 2 + Real.log 3 + Real.log 7 + (1 / (2 * 168) + 1 / (2 * (168 + 1))) := by
    have h := log_succ_le' 168 (by norm_num)
    have e1 : Real.log (168 + 1) = 2 * Real.log 13 := by
      rw [show (168 : ℝ) + 1 = 13 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 168 = 3 * Real.log 2 + Real.log 3 + Real.log 7 := by
      rw [show (168 : ℝ) = 2^3 * 3 * 7 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p17 : 2 * Real.log 17 ≤ 5 * Real.log 2 + 2 * Real.log 3 + (1 / (2 * 288) + 1 / (2 * (288 + 1))) := by
    have h := log_succ_le' 288 (by norm_num)
    have e1 : Real.log (288 + 1) = 2 * Real.log 17 := by
      rw [show (288 : ℝ) + 1 = 17 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 288 = 5 * Real.log 2 + 2 * Real.log 3 := by
      rw [show (288 : ℝ) = 2^5 * 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  have p19 : 2 * Real.log 19 ≤ 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + (1 / (2 * 360) + 1 / (2 * (360 + 1))) := by
    have h := log_succ_le' 360 (by norm_num)
    have e1 : Real.log (360 + 1) = 2 * Real.log 19 := by
      rw [show (360 : ℝ) + 1 = 19 ^ 2 by norm_num, Real.log_pow]; norm_num
    have e2 : Real.log 360 = 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
      rw [show (360 : ℝ) = 2^3 * 3^2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
    rw [e1, e2] at h; exact h
  norm_num at *
  refine ⟨p2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma finite_bounds :
    2.6069 ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ∧
    ∑' n : ℕ, Real.log n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 3.9490 := by
  obtain ⟨l2, l3, l5, l7, l11, l13, l17, l19⟩ := log_primes_le
  have hZ := (summable_one.sum_add_tsum_nat_add 21).symm
  have hD := (summable_log.sum_add_tsum_nat_add 21).symm
  have hzt := z_tail 21 399999979 (by norm_num)
  have hdt := d_tail 21 (by norm_num)
  have hsq : √((21 : ℕ) + (399999979 : ℕ) : ℝ) = 20000 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]; norm_num
  rw [hsq] at hzt
  have hrs (f : ℝ → ℝ) : ∑ i ∈ Finset.range 21, f (i : ℝ) / (i : ℝ) ^ (3 / 2 : ℝ) =
      ∑ i ∈ Finset.range 21, f (i : ℝ) / ((i : ℝ) * √(i : ℝ)) :=
    Finset.sum_congr rfl (fun i _ => by rw [rpow32 (Nat.cast_nonneg i)])
  rw [hrs (fun _ => 1)] at hZ
  rw [hrs Real.log] at hD
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hZ hD
  norm_num at hZ hD hzt hdt
  unfold Gf at hdt
  have z21 : 2 / (45826 / 10000 : ℝ) ≤ 2 / √21 := by
    have hs : √21 ≤ (45826 / 10000 : ℝ) := by
      rw [show (45826 / 10000 : ℝ) = √((45826 / 10000) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
  have g20 : (2 * Real.log 20 + 4) / √20 ≤ (2 * Real.log 20 + 4) / (44721/10000) := by
    have : (0 : ℝ) ≤ 2 * Real.log 20 + 4 := by have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 20); linarith
    exact div_le_div_of_nonneg_left this (by norm_num)
      (Real.le_sqrt_of_sq_le (by norm_num))
  have z1 := zb 1 (10000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z2 := zb 2 (14143/10000) (by norm_num) (by norm_num) (by norm_num)
  have d2 := db 2 (14142/10000) (by norm_num) (by norm_num) (by norm_num)
  have z3 := zb 3 (17321/10000) (by norm_num) (by norm_num) (by norm_num)
  have d3 := db 3 (17320/10000) (by norm_num) (by norm_num) (by norm_num)
  have z4 := zb 4 (20000/10000) (by norm_num) (by norm_num) (by norm_num)
  have d4 := db 4 (20000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z5 := zb 5 (22361/10000) (by norm_num) (by norm_num) (by norm_num)
  have d5 := db 5 (22360/10000) (by norm_num) (by norm_num) (by norm_num)
  have z6 := zb 6 (24495/10000) (by norm_num) (by norm_num) (by norm_num)
  have d6 := db 6 (24494/10000) (by norm_num) (by norm_num) (by norm_num)
  have z7 := zb 7 (26458/10000) (by norm_num) (by norm_num) (by norm_num)
  have d7 := db 7 (26457/10000) (by norm_num) (by norm_num) (by norm_num)
  have z8 := zb 8 (28285/10000) (by norm_num) (by norm_num) (by norm_num)
  have d8 := db 8 (28284/10000) (by norm_num) (by norm_num) (by norm_num)
  have z9 := zb 9 (30000/10000) (by norm_num) (by norm_num) (by norm_num)
  have d9 := db 9 (30000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z10 := zb 10 (31623/10000) (by norm_num) (by norm_num) (by norm_num)
  have d10 := db 10 (31622/10000) (by norm_num) (by norm_num) (by norm_num)
  have z11 := zb 11 (33167/10000) (by norm_num) (by norm_num) (by norm_num)
  have d11 := db 11 (33166/10000) (by norm_num) (by norm_num) (by norm_num)
  have z12 := zb 12 (34642/10000) (by norm_num) (by norm_num) (by norm_num)
  have d12 := db 12 (34641/10000) (by norm_num) (by norm_num) (by norm_num)
  have z13 := zb 13 (36056/10000) (by norm_num) (by norm_num) (by norm_num)
  have d13 := db 13 (36055/10000) (by norm_num) (by norm_num) (by norm_num)
  have z14 := zb 14 (37417/10000) (by norm_num) (by norm_num) (by norm_num)
  have d14 := db 14 (37416/10000) (by norm_num) (by norm_num) (by norm_num)
  have z15 := zb 15 (38730/10000) (by norm_num) (by norm_num) (by norm_num)
  have d15 := db 15 (38729/10000) (by norm_num) (by norm_num) (by norm_num)
  have z16 := zb 16 (40000/10000) (by norm_num) (by norm_num) (by norm_num)
  have d16 := db 16 (40000/10000) (by norm_num) (by norm_num) (by norm_num)
  have z17 := zb 17 (41232/10000) (by norm_num) (by norm_num) (by norm_num)
  have d17 := db 17 (41231/10000) (by norm_num) (by norm_num) (by norm_num)
  have z18 := zb 18 (42427/10000) (by norm_num) (by norm_num) (by norm_num)
  have d18 := db 18 (42426/10000) (by norm_num) (by norm_num) (by norm_num)
  have z19 := zb 19 (43589/10000) (by norm_num) (by norm_num) (by norm_num)
  have d19 := db 19 (43588/10000) (by norm_num) (by norm_num) (by norm_num)
  have z20 := zb 20 (44722/10000) (by norm_num) (by norm_num) (by norm_num)
  have d20 := db 20 (44721/10000) (by norm_num) (by norm_num) (by norm_num)
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e12 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12 : ℝ) = 2^2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e14 : Real.log 14 = Real.log 2 + Real.log 7 := by
    rw [show (14 : ℝ) = 2 * 7 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2^4 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e18 : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    rw [show (18 : ℝ) = 2 * 3^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
    rw [show (20 : ℝ) = 2^2 * 5 by norm_num]; simp [Real.log_mul, Real.log_pow]
  norm_num at *
  constructor <;> linarith

end Erdos985.Analytic.ConstantsAux
