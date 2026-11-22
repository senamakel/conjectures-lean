import Mathlib

/-!
# A growth class `‖F s‖ ≤ K exp(a (‖s‖ + b) log (‖s‖ + b))`

Auxiliary for `Erdos985.Analytic.XiOrder`: closure properties of this class and the fact that it
implies the bound `‖F z‖ ≤ C exp(‖z‖ ^ (1 + ε))` for every `ε > 0`.
-/

namespace Erdos985.Analytic.XiOrderAux

open Real

/-- `F` grows at most like `exp(a (‖s‖ + b) log (‖s‖ + b))`. -/
def LogGrowth (F : ℂ → ℂ) : Prop :=
  ∃ K a b : ℝ, 0 ≤ a ∧ 3 ≤ b ∧ ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))

lemma one_le_log_of_three_le {u : ℝ} (hu : 3 ≤ u) : 1 ≤ log u := by
  have h3 : exp 1 < 3 := lt_of_lt_of_le exp_one_lt_d9 (by norm_num)
  rw [le_log_iff_exp_le (by linarith)]
  linarith

lemma ulogu_mono {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : u * log u ≤ v * log v :=
  mul_le_mul huv (log_le_log (by linarith) huv) (log_nonneg hu) (by linarith)

lemma expo_mono {a a' b b' y y' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (hb : 3 ≤ b) (hy : 0 ≤ y)
    (hle : y + b ≤ y' + b') :
    a * ((y + b) * log (y + b)) ≤ a' * ((y' + b') * log (y' + b')) := by
  have h1 : 1 ≤ log (y + b) := one_le_log_of_three_le (by linarith)
  have h2 : (y + b) * log (y + b) ≤ (y' + b') * log (y' + b') :=
    ulogu_mono (by linarith) hle
  have h3 : 0 ≤ (y' + b') * log (y' + b') := by nlinarith
  exact mul_le_mul haa h2 (by nlinarith) (ha.trans haa)

lemma LogGrowth.nonneg_K {F : ℂ → ℂ} {K a b : ℝ}
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) : 0 ≤ K :=
  nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h 0)) (exp_pos _)

lemma LogGrowth.mono {F : ℂ → ℂ} {K a b : ℝ} (ha : 0 ≤ a) (hb : 3 ≤ b)
    (h : ∀ s, ‖F s‖ ≤ K * exp (a * ((‖s‖ + b) * log (‖s‖ + b)))) {a' b' : ℝ} (haa : a ≤ a')
    (hbb : b ≤ b') : ∀ s, ‖F s‖ ≤ K * exp (a' * ((‖s‖ + b') * log (‖s‖ + b'))) := by
  intro s
  refine (h s).trans (mul_le_mul_of_nonneg_left ?_ (LogGrowth.nonneg_K h))
  exact exp_le_exp.2 (expo_mono ha haa hb (norm_nonneg _) (by linarith))

lemma LogGrowth.congr {F G : ℂ → ℂ} (hF : LogGrowth F) (h : ∀ s, F s = G s) : LogGrowth G := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  exact ⟨K, a, b, ha, hb, fun s => h s ▸ hK s⟩

lemma LogGrowth.const (c : ℂ) : LogGrowth (fun _ => c) :=
  ⟨‖c‖, 0, 3, le_rfl, le_rfl, fun s => by simp⟩

lemma LogGrowth.add {F G : ℂ → ℂ} (hF : LogGrowth F) (hG : LogGrowth G) :
    LogGrowth (fun s => F s + G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K + K', max a a', max b b', le_max_of_le_left ha, le_max_of_le_left hb, fun s => ?_⟩
  have h1 := LogGrowth.mono ha hb hK (le_max_left a a') (le_max_left b b') s
  have h2 := LogGrowth.mono ha' hb' hK' (le_max_right a a') (le_max_right b b') s
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2

lemma LogGrowth.mul {F G : ℂ → ℂ} (hF : LogGrowth F) (hG : LogGrowth G) :
    LogGrowth (fun s => F s * G s) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  obtain ⟨K', a', b', ha', hb', hK'⟩ := hG
  refine ⟨K * K', a + a', max b b', add_nonneg ha ha', le_max_of_le_left hb, fun s => ?_⟩
  have h1 := LogGrowth.mono ha hb hK le_rfl (le_max_left b b') s
  have h2 := LogGrowth.mono ha' hb' hK' le_rfl (le_max_right b b') s
  rw [norm_mul]
  calc ‖F s‖ * ‖G s‖ ≤ _ := mul_le_mul h1 h2 (norm_nonneg _)
        (mul_nonneg (LogGrowth.nonneg_K hK) (exp_pos _).le)
    _ = _ := by rw [add_mul a a', exp_add]; ring

lemma LogGrowth.sum {ι : Type*} (S : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ S, LogGrowth (F i)) : LogGrowth (fun s => ∑ i ∈ S, F i s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact (LogGrowth.const 0).congr (fun s => by simp)
  | insert i S hi ih =>
    refine ((hF i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))).congr (fun s => ?_)
    rw [Finset.sum_insert hi]

lemma LogGrowth.comp {F : ℂ → ℂ} (hF : LogGrowth F) {g : ℂ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hg : ∀ s, ‖g s‖ ≤ ‖s‖ + d) : LogGrowth (fun s => F (g s)) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  refine ⟨K, a, b + d, ha, by linarith, fun s => (hK (g s)).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (LogGrowth.nonneg_K hK)
  exact expo_mono ha le_rfl hb (norm_nonneg _) (by linarith [hg s])

lemma LogGrowth.natCast_cpow_neg {N : ℕ} (hN : 0 < N) : LogGrowth (fun s => (N : ℂ) ^ (-s)) := by
  refine ⟨1, log N, 3, log_natCast_nonneg N, le_rfl, fun s => ?_⟩
  rw [Complex.norm_natCast_cpow_of_pos hN, one_mul]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg hN1
  calc (N : ℝ) ^ (-s).re ≤ (N : ℝ) ^ ‖s‖ :=
        rpow_le_rpow_of_exponent_le hN1 (by
          rw [Complex.neg_re]; exact (neg_le_abs _).trans (Complex.abs_re_le_norm s))
    _ = exp (log N * ‖s‖) := by
        rw [rpow_def_of_pos (by exact_mod_cast hN)]
    _ ≤ _ := by
        refine exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hlog)
        have h1 : 1 ≤ log (‖s‖ + 3) := one_le_log_of_three_le (by linarith [norm_nonneg s])
        nlinarith [norm_nonneg s]

/-- The growth class implies order at most one in the `exp (‖z‖ ^ (1 + ε))` form. -/
lemma LogGrowth.order {F : ℂ → ℂ} (hF : LogGrowth F) :
    ∀ ε : ℝ, ε > 0 → ∃ C, ∀ z, ‖F z‖ ≤ C * exp (‖z‖ ^ (1 + ε)) := by
  obtain ⟨K, a, b, ha, hb, hK⟩ := hF
  intro ε hε
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set A := a * 2 ^ (1 + δ) / δ with hA
  have hA0 : 0 ≤ A := by positivity
  set X := max b (A ^ δ⁻¹) with hX
  have hXb : b ≤ X := le_max_left _ _
  -- key: for `x ≥ X`, the exponent is at most `x ^ (1 + ε)`.
  have key : ∀ x : ℝ, X ≤ x → a * ((x + b) * log (x + b)) ≤ x ^ (1 + ε) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hxb : 0 < x + b := by linarith
    have hlog : log (x + b) ≤ (x + b) ^ δ / δ := log_le_rpow_div hxb.le hδ0
    have e1 : (x + b) * log (x + b) ≤ (x + b) ^ (1 + δ) / δ := by
      rw [rpow_add hxb, rpow_one, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlog hxb.le
    have e2 : (x + b) ^ (1 + δ) ≤ 2 ^ (1 + δ) * x ^ (1 + δ) := by
      rw [← mul_rpow (by norm_num) hx0.le]
      exact rpow_le_rpow hxb.le (by linarith) (by linarith)
    have e3 : A ≤ x ^ δ := by
      calc A = (A ^ δ⁻¹) ^ δ := (rpow_inv_rpow hA0 hδ0.ne').symm
        _ ≤ x ^ δ := rpow_le_rpow (by positivity) ((le_max_right _ _).trans hx) hδ0.le
    have e4 : x ^ (1 + ε) = x ^ (1 + δ) * x ^ δ := by
      rw [← rpow_add hx0]; congr 1; rw [hδ]; ring
    calc a * ((x + b) * log (x + b)) ≤ a * ((x + b) ^ (1 + δ) / δ) :=
          mul_le_mul_of_nonneg_left e1 ha
      _ ≤ a * (2 ^ (1 + δ) * x ^ (1 + δ) / δ) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right e2 hδ0.le) ha
      _ = A * x ^ (1 + δ) := by rw [hA]; ring
      _ ≤ x ^ δ * x ^ (1 + δ) := mul_le_mul_of_nonneg_right e3 (by positivity)
      _ = x ^ (1 + ε) := by rw [e4, mul_comm]
  set M := a * ((X + b) * log (X + b)) with hM
  refine ⟨K * exp M, fun z => (hK z).trans ?_⟩
  have hK0 : 0 ≤ K := LogGrowth.nonneg_K hK
  rw [mul_assoc, ← exp_add]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) hK0
  have hpow : 0 ≤ ‖z‖ ^ (1 + ε) := by positivity
  rcases le_total X ‖z‖ with h | h
  · have hM0 : 0 ≤ M := by
      have : 1 ≤ log (X + b) := one_le_log_of_three_le (by linarith)
      have : 0 ≤ X + b := by linarith
      positivity
    linarith [key _ h]
  · have := expo_mono (y := ‖z‖) (y' := X) (b' := b) ha le_rfl hb (norm_nonneg _) (by linarith)
    linarith

/-- Variant of `LogGrowth.order` with a natural-number exponent. -/
lemma LogGrowth.order_nat {F : ℂ → ℂ} (hF : LogGrowth F) :
    ∀ ε : ℕ, ε > 0 → ∃ C, ∀ z, ‖F z‖ ≤ C * exp (‖z‖ ^ (1 + ε)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hF.order (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨C, fun z => ?_⟩
  have h := hC z
  rwa [show (1 : ℝ) + ε = ((1 + ε : ℕ) : ℝ) by push_cast; ring, rpow_natCast] at h

end Erdos985.Analytic.XiOrderAux
