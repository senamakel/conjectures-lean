import Littlewood.Kernel
import Erdos985.Analytic.ExplicitFormula.Identity.Zeros

/-!
# Step 2: the Perron integral of a function with a pole expansion, term by term

If `G(z) - G(s) = Σ_i m_i (1/(z - a_i) - 1/(s - a_i))` on the line `z = s + w`, `Re w = 2`, with
every pole at most one unit right of `s` and `Σ |m_i| / (|b_i| (1 + |b_i|)^{1/2}) < ∞`
(`b_i = a_i - s`), then

    (1/2π) ∫ G(s + w) x^w / w² dv = G(s) log x + Σ_i m_i (x^{b_i} - 1) / b_i²     (x ≥ 1).

Each term is `(m_i / b_i) · x^w / ((w - b_i) w)`, evaluated by `perron_pole`; the interchange
of sum and integral is dominated by `kerPole_bound`. No contour is shifted.
-/

open Complex MeasureTheory

namespace Littlewood

open Erdos985.Analytic

lemma pole_diff_eq {s w a : ℂ} (hw : w ≠ 0) (hwb : w - (a - s) ≠ 0) (hb : a - s ≠ 0) :
    (1 / (s + w - a) - 1 / (s - a)) * (1 / w ^ 2) = 1 / (a - s) * (1 / ((w - (a - s)) * w)) := by
  have h1 : s + w - a ≠ 0 := by
    intro h; apply hwb; linear_combination h
  have h2 : s - a ≠ 0 := by
    intro h; apply hb; linear_combination -h
  field_simp
  ring

/-- **Term-by-term Perron formula** for a pole expansion. -/
theorem perron_termwise {ι : Type*} [Countable ι] {G : ℂ → ℂ} {s : ℂ} {x : ℝ} (hx : 1 ≤ x)
    (a m : ι → ℂ) (ha : ∀ i, (a i - s).re ≤ 1) (has : ∀ i, a i ≠ s)
    (hsum : Summable fun i => ‖m i‖ / ‖a i - s‖ * (1 + ‖a i - s‖) ^ (-(1 / 2 : ℝ)))
    (hG : ∀ v : ℝ, HasSum (fun i => m i * (1 / (s + lineP v - a i) - 1 / (s - a i)))
      (G (s + lineP v) - G s))
    (hGc : Continuous fun v : ℝ => G (s + lineP v)) :
    Integrable (fun v : ℝ => G (s + lineP v) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))) ∧
    (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, G (s + lineP v) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2))
      = G s * Real.log x + ∑' i, m i * (((x : ℂ) ^ (a i - s) - 1) / (a i - s) ^ 2) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨K, hK0, hK⟩ := kerPole_bound
  set b : ι → ℂ := fun i => a i - s with hb
  have hb0 : ∀ i, b i ≠ 0 := fun i => sub_ne_zero.2 (has i)
  set k0 : ℝ → ℂ := fun v => (x : ℂ) ^ lineP v * (1 / lineP v ^ 2) with hk0
  set ker : ι → ℝ → ℂ := fun i v => (x : ℂ) ^ lineP v * (1 / ((lineP v - b i) * lineP v))
    with hker
  set F : ι → ℝ → ℂ := fun i v => m i / b i * ker i v with hF
  have hker_int : ∀ i, Integrable (ker i) := fun i => (hK x hx0 (b i) (ha i)).1
  have hF_int : ∀ i, Integrable (F i) := fun i => (hker_int i).const_mul _
  have hF_sum : Summable fun i => ∫ v, ‖F i v‖ := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) (hsum.mul_left (K * x ^ (2 : ℝ)))
    simp only [hF, norm_mul, integral_const_mul, norm_div]
    have h := (hK x hx0 (b i) (ha i)).2
    calc ‖m i‖ / ‖b i‖ * ∫ v, ‖ker i v‖
        ≤ ‖m i‖ / ‖b i‖ * (K * x ^ (2 : ℝ) * (1 + ‖b i‖) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K * x ^ (2 : ℝ) * (‖m i‖ / ‖a i - s‖ * (1 + ‖a i - s‖) ^ (-(1 / 2 : ℝ))) := by
          simp only [hb]; ring
  have hwb : ∀ i (v : ℝ), lineP v - b i ≠ 0 := fun i v h => by
    have := congrArg re h; simp at this; linarith [ha i]
  have hF_hasSum : ∀ v, HasSum (fun i => F i v) ((G (s + lineP v) - G s) * k0 v) := by
    intro v
    have := (hG v).mul_right (k0 v)
    convert this using 1
    funext i
    simp only [hF, hker, hk0]
    have e := pole_diff_eq (s := s) (a := a i) (lineP_ne_zero v) (hwb i v) (hb0 i)
    calc m i / b i * ((x : ℂ) ^ lineP v * (1 / ((lineP v - b i) * lineP v)))
        = m i * ((x : ℂ) ^ lineP v * (1 / (a i - s) * (1 / ((lineP v - (a i - s)) * lineP v)))) := by
          simp only [hb]; ring
      _ = m i * ((x : ℂ) ^ lineP v * ((1 / (s + lineP v - a i) - 1 / (s - a i)) *
            (1 / lineP v ^ 2))) := by rw [e]
      _ = _ := by ring
  have hk0_int : Integrable k0 := integrable_kerLog hx0
  have hk0c : Continuous k0 :=
    (continuous_lineP.const_cpow (Or.inl (by exact_mod_cast hx0.ne'))).mul
      (Continuous.div (f := fun _ => (1 : ℂ)) continuous_const (continuous_lineP.pow 2)
        fun v => pow_ne_zero 2 (lineP_ne_zero v))
  have hD_int : Integrable fun v => (G (s + lineP v) - G s) * k0 v :=
    IdentityAux.integrable_of_hasSum ((hGc.sub continuous_const).mul hk0c).aestronglyMeasurable
      hF_int hF_sum hF_hasSum
  have hD_integral : ∫ v, (G (s + lineP v) - G s) * k0 v = ∑' i, ∫ v, F i v := by
    rw [show (fun v => (G (s + lineP v) - G s) * k0 v) = fun v => ∑' i, F i v from
      funext fun v => (hF_hasSum v).tsum_eq.symm,
      ← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hFi : ∀ i, ∫ v, F i v = 2 * Real.pi * (m i * (((x : ℂ) ^ (a i - s) - 1) / (a i - s) ^ 2)) := by
    intro i
    simp only [hF]
    rw [integral_const_mul]
    have hp := perron_pole hx (ha i) (hb0 i)
    have : ∫ v, ker i v = 2 * Real.pi * (((x : ℂ) ^ b i - 1) / b i) := by
      rw [← hp, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    rw [this]
    simp only [hb]
    field_simp [hb0 i]
  have hk0i : ∫ v, k0 v = 2 * Real.pi * Real.log x := by
    have hp := perron_log hx0
    rw [ite_eq_left_iff.2 (fun h => absurd hx h)] at hp
    rw [← hp, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have hsplit : (fun v : ℝ => G (s + lineP v) * k0 v)
      = fun v => G s * k0 v + (G (s + lineP v) - G s) * k0 v := by
    funext v; ring
  have hint : Integrable fun v : ℝ => G (s + lineP v) * k0 v := by
    rw [hsplit]; exact (hk0_int.const_mul _).add hD_int
  refine ⟨hint, ?_⟩
  change (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, G (s + lineP v) * k0 v = _
  rw [hsplit, integral_add (hk0_int.const_mul _) hD_int, integral_const_mul, hk0i, hD_integral]
  simp_rw [hFi]
  rw [tsum_mul_left]
  field_simp

end Littlewood
