import Erdos969.MV.Twisted
import Erdos969.KFree.Hyperbola

/-!
# The coefficients of `ζ(s) · ∑_{d > Y} μ(d) d^{-ks}`

Let `h(n) = μ(d)` when `n = d^k` with `d > Y`, and `h(n) = 0` otherwise, and `b = h * 1`
(Dirichlet convolution with the constant function `1`). Then:

* `sum_Icc_b`: `∑_{n ≤ N} b(n) = ∑_{Y < d ≤ N} μ(d) ⌊N/d^k⌋`, the part of `Q_k(N)` with `d > Y`;
* `LSeries_b`: `L(b, s) = ζ(s) G_Y(ks)` for `σ > 1`, where
  `G_Y(w) = 1/ζ(w) - ∑_{d ≤ Y} μ(d) d^{-w}` is the tail of `1/ζ`;
* `norm_b_le`: `‖b(n)‖ ≤ n`.
-/

namespace Erdos969.MV

open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta LSeries.notation

/-- `G_Y(w) = 1/ζ(w) - ∑_{d ≤ Y} μ(d) d^{-w}`, holomorphic on `σ > 1/2` under RH. -/
noncomputable def G (Y : ℕ) (w : ℂ) : ℂ :=
  Mertens.invZ w - ∑ d ∈ Icc 1 Y, (μ d : ℂ) * (d : ℂ) ^ (-w)

lemma iroot_zero (k : ℕ) : KFree.iroot k 0 = 0 := Nat.le_zero.1 (KFree.iroot_le k 0)

lemma iroot_pow {k d : ℕ} (hk : 1 ≤ k) : KFree.iroot k (d ^ k) = d := by
  apply le_antisymm
  · have h := (KFree.le_iroot_iff hk).1 (le_refl (KFree.iroot k (d ^ k)))
    exact (Nat.pow_le_pow_iff_left (by omega)).1 h
  · exact (KFree.le_iroot_iff hk).2 le_rfl

/-- `h(n) = μ(d)` if `n = d^k` with `d > Y`, else `0`. -/
noncomputable def hFun (k Y n : ℕ) : ℂ :=
  if Y < KFree.iroot k n ∧ KFree.iroot k n ^ k = n then (μ (KFree.iroot k n) : ℂ) else 0

lemma hFun_zero (k Y : ℕ) : hFun k Y 0 = 0 := by
  simp [hFun, iroot_zero]

lemma hFun_pow {k Y : ℕ} (hk : 1 ≤ k) (d : ℕ) :
    hFun k Y (d ^ k) = if Y < d then (μ d : ℂ) else 0 := by
  simp [hFun, iroot_pow hk]

lemma norm_hFun_le (k Y n : ℕ) : ‖hFun k Y n‖ ≤ 1 := by
  unfold hFun
  split_ifs
  · rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- `h` as an arithmetic function. -/
noncomputable def hAF (k Y : ℕ) : ArithmeticFunction ℂ := ⟨hFun k Y, hFun_zero k Y⟩

lemma hAF_apply (k Y n : ℕ) : hAF k Y n = hFun k Y n := rfl

/-- `b = h * ζ`, the coefficients of `ζ(s) G_Y(ks)`. -/
noncomputable def b (k Y : ℕ) : ℕ → ℂ := ⇑(hAF k Y * (ζ : ArithmeticFunction ℂ))

theorem sum_Icc_b {k : ℕ} (hk : 1 ≤ k) (Y N : ℕ) :
    ∑ n ∈ Icc 1 N, b k Y n = ∑ d ∈ Ioc Y N, (μ d : ℂ) * ((N / d ^ k : ℕ) : ℂ) := by
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  rw [hI, b, sum_Ioc_mul_zeta_eq_sum]
  refine sum_bij_ne_zero (fun n _ _ => KFree.iroot k n) ?_ ?_ ?_ ?_
  · intro n hn hne
    rw [hAF_apply] at hne
    have hh : hFun k Y n ≠ 0 := left_ne_zero_of_mul hne
    unfold hFun at hh
    split_ifs at hh with hc
    · simp only [mem_Ioc] at hn ⊢
      exact ⟨hc.1, (KFree.iroot_le k n).trans hn.2⟩
    · exact absurd rfl hh
  · intro n₁ _ h₁ n₂ _ h₂ heq
    rw [hAF_apply] at h₁ h₂
    have hh₁ : hFun k Y n₁ ≠ 0 := left_ne_zero_of_mul h₁
    have hh₂ : hFun k Y n₂ ≠ 0 := left_ne_zero_of_mul h₂
    unfold hFun at hh₁ hh₂
    split_ifs at hh₁ hh₂ with hc₁ hc₂
    · rw [← hc₁.2, ← hc₂.2, heq]
    all_goals exact absurd rfl (by assumption)
  · intro d hd hne
    simp only [mem_Ioc] at hd
    have hdk : d ^ k ≤ N := by
      by_contra hlt
      push Not at hlt
      apply hne
      rw [Nat.div_eq_of_lt hlt]; simp
    have hd1 : 1 ≤ d := by omega
    refine ⟨d ^ k, ?_, ?_, iroot_pow hk⟩
    · simp only [mem_Ioc]; exact ⟨Nat.pow_pos hd1, hdk⟩
    · rw [hAF_apply, hFun_pow hk, if_pos hd.1]; exact hne
  · intro n _ hne
    rw [hAF_apply] at hne ⊢
    have hh : hFun k Y n ≠ 0 := left_ne_zero_of_mul hne
    unfold hFun at hh ⊢
    split_ifs with hc
    · rw [hc.2]
    · simp [hc] at hh

lemma norm_b_le (k Y n : ℕ) : ‖b k Y n‖ ≤ n := by
  rw [b, coe_mul_zeta_apply]
  calc ‖∑ i ∈ n.divisors, hAF k Y i‖ ≤ ∑ i ∈ n.divisors, ‖hAF k Y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ n.divisors, (1 : ℝ) := sum_le_sum fun i _ => norm_hFun_le k Y i
    _ = (n.divisors.card : ℝ) := by simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

lemma moebius_mul_cpow_eq_term' (w : ℂ) (d : ℕ) :
    (μ d : ℂ) * (d : ℂ) ^ (-w) = LSeries.term (fun n => (μ n : ℂ)) w d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [LSeries.term_of_ne_zero hd.ne', cpow_neg, div_eq_mul_inv]

lemma summable_term_moebius {w : ℂ} (hw : 1 < w.re) :
    Summable (LSeries.term (fun n => (μ n : ℂ)) w) :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one) hw

/-- `L(h, s) = G_Y(ks)` for `σ > 1`. -/
theorem LSeries_hAF {k : ℕ} (hk : 1 ≤ k) (Y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => hAF k Y n) s = G Y ((k : ℂ) * s) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hw : 1 < ((k : ℂ) * s).re := by
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]; nlinarith
  set w := (k : ℂ) * s with hwdef
  have hinj : Function.Injective fun d : ℕ => d ^ k := Nat.pow_left_injective (by omega)
  have hsupp : Function.support (LSeries.term (fun n => hAF k Y n) s) ⊆
      Set.range fun d : ℕ => d ^ k := by
    intro n hn
    rw [Function.mem_support] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact absurd (LSeries.term_zero _ _) hn
    rw [LSeries.term_of_ne_zero hn0.ne', hAF_apply] at hn
    have hh : hFun k Y n ≠ 0 := fun h => hn (by rw [h, zero_div])
    unfold hFun at hh
    split_ifs at hh with hc
    · exact ⟨_, hc.2⟩
    · exact absurd rfl hh
  have hterm : ∀ d : ℕ, LSeries.term (fun n => hAF k Y n) s (d ^ k) =
      if Y < d then LSeries.term (fun n => (μ n : ℂ)) w d else 0 := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [zero_pow (by omega : k ≠ 0)]
    · have hdk : d ^ k ≠ 0 := (Nat.pow_pos hd).ne'
      rw [LSeries.term_of_ne_zero hdk, hAF_apply, hFun_pow hk, LSeries.term_of_ne_zero hd.ne',
        hwdef, natCast_cpow_natCast_mul, Nat.cast_pow]
      split_ifs <;> simp
  unfold LSeries
  rw [← hinj.tsum_eq hsupp]
  simp_rw [hterm]
  have hsum := summable_term_moebius hw
  have hsum' : Summable fun d : ℕ =>
      if Y < d then LSeries.term (fun n => (μ n : ℂ)) w d else 0 := by
    refine Summable.of_norm_bounded hsum.norm fun d => ?_
    split_ifs <;> simp
  rw [← hsum'.sum_add_tsum_nat_add (Y + 1)]
  have h1 : ∑ i ∈ range (Y + 1),
      (if Y < i then LSeries.term (fun n => (μ n : ℂ)) w i else 0) = 0 :=
    sum_eq_zero fun i hi => by rw [if_neg (by simp at hi; omega)]
  have h2 : ∀ i : ℕ, (if Y < i + (Y + 1) then LSeries.term (fun n => (μ n : ℂ)) w (i + (Y + 1))
      else 0) = LSeries.term (fun n => (μ n : ℂ)) w (i + (Y + 1)) := fun i => if_pos (by omega)
  simp_rw [h2]
  rw [h1, zero_add]
  have h3 := hsum.sum_add_tsum_nat_add (Y + 1)
  have hL : ∑' n, LSeries.term (fun n => (μ n : ℂ)) w n = Mertens.invZ w := by
    have := Mertens.LSeries_moebius_eq_invZ hw
    rw [LSeries] at this; exact this
  rw [hL] at h3
  rw [G, ← h3, sum_Icc_eq_sum_range _ (by simp)]
  simp_rw [moebius_mul_cpow_eq_term' w]
  ring

/-- `L(b, s) = ζ(s) G_Y(ks)` for `σ > 1`. -/
theorem LSeries_b {k : ℕ} (hk : 1 ≤ k) (Y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (b k Y) s = riemannZeta s * G Y ((k : ℂ) * s) := by
  have hh : LSeriesSummable (fun n => hAF k Y n) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => norm_hFun_le k Y n) hs
  have hz : LSeriesSummable (fun n => (ζ : ArithmeticFunction ℂ) n) s := by
    have := LSeriesSummable_zeta_iff.2 hs
    convert this using 2 with n
    simp [natCoe_apply]
  have e := LSeries_mul' hh hz
  have hzeta : LSeries (fun n => (ζ : ArithmeticFunction ℂ) n) s = riemannZeta s := by
    rw [← LSeries_zeta_eq_riemannZeta hs]
    congr 1
  rw [b]
  change LSeries (fun n => (hAF k Y * (ζ : ArithmeticFunction ℂ)) n) s = _
  rw [e, hzeta, LSeries_hAF hk Y hs, mul_comm]

end Erdos969.MV
