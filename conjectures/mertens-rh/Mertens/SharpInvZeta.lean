import Mertens.SharpLower
import Mertens.SharpSmall
import Mertens.Statement3

/-!
# `1/ζ(s) ≪ exp(C log t / log log t)` near the half line (RH)

`norm_invZ_le_sharp` (RH) joins the two ranges: for every `l ≥ 2` and `1/2 + 4/l ≤ σ ≤ 2`,

    ‖invZ(σ + it)‖ ≤ exp(A (l² e^l + 1)) · (|t| + 3)^{4/l},

uniformly in `t`. Here `l = log x` is the length parameter of littlewood-rh's explicit formula
(`|t| ≥ 1`, `norm_inv_zeta_le_large`), and `|t| ≤ 1` comes from `norm_invZ_le_small`.

With `l = ½ log log t` this gives `InvZetaSharpBoundWith 8`: the bound `exp(C log t/log log t)`
on `σ ≥ 1/2 + 8/log log t`. Titchmarsh's region is `σ ≥ 1/2 + 1/log log t`; this argument
needs `(σ - 1/2) l ≥ 4` and `l < log log t`, so it cannot reach `c = 1` (see the README).
-/

open Complex Filter Set Asymptotics

namespace Mertens

/-- `A ((log u)² √u + 1) + B ≤ u / log u` for large `u`. -/
lemma eventually_le_div_log (A B : ℝ) : ∀ᶠ u : ℝ in atTop,
    A * (Real.log u ^ 2 * u ^ (1 / 2 : ℝ) + 1) + B ≤ u / Real.log u := by
  set c := 2 * |A| + |B| + 1 with hc
  have hc0 : 0 < c := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop 3 (show (0 : ℝ) < 1 / 2 by norm_num)).def
    (show 0 < 1 / c by positivity)
  filter_upwards [hlo, eventually_ge_atTop (Real.exp 1)] with u h1 hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu
  have hℓ : 1 ≤ Real.log u := by rw [Real.le_log_iff_exp_le hu0]; exact hu
  set ℓ := Real.log u
  set r := u ^ (1 / 2 : ℝ) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by norm_num)
  have hrr : r * r = u := by
    rw [hr, ← Real.rpow_add hu0]; norm_num
  have h3 : ℓ ^ (3 : ℝ) = ℓ ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _), h3] at h1
  have hℓ3 : c * ℓ ^ 3 ≤ r := by
    have := mul_le_mul_of_nonneg_left h1 hc0.le
    rw [← mul_assoc, mul_one_div_cancel hc0.ne', one_mul] at this
    exact this
  have hℓ1 : ℓ ≤ ℓ ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ - 1) (by positivity : (0 : ℝ) ≤ ℓ * (ℓ + 1))]
  have hℓ2 : ℓ ^ 2 * ℓ = ℓ ^ 3 := by ring
  rw [le_div_iff₀ (by linarith)]
  have hA : A * (ℓ ^ 2 * r + 1) ≤ |A| * (ℓ ^ 2 * r + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
  have hB := le_abs_self B
  have hpos : 0 ≤ ℓ ^ 3 * r := by positivity
  calc (A * (ℓ ^ 2 * r + 1) + B) * ℓ ≤ (|A| * (ℓ ^ 2 * r + 1) + |B|) * ℓ := by gcongr
    _ = |A| * (ℓ ^ 3 * r) + |A| * ℓ + |B| * ℓ := by rw [← hℓ2]; ring
    _ ≤ |A| * (ℓ ^ 3 * r) + |A| * (ℓ ^ 3 * r) + |B| * (ℓ ^ 3 * r) := by
        have e1 : ℓ ≤ ℓ ^ 3 * r := by nlinarith
        gcongr
    _ ≤ c * ℓ ^ 3 * r := by rw [hc]; nlinarith [abs_nonneg A, abs_nonneg B]
    _ ≤ r * r := by nlinarith
    _ = u := hrr

/-- `‖ζ(s)⁻¹‖` depends only on `Re s` and `|Im s|`. -/
lemma norm_inv_zeta_abs_im (s : ℂ) :
    ‖(riemannZeta s)⁻¹‖ = ‖(riemannZeta ((s.re : ℂ) + (|s.im| : ℝ) * I))⁻¹‖ := by
  rcases le_or_gt 0 s.im with h | h
  · rw [abs_of_nonneg h, re_add_im]
  · rw [abs_of_neg h]
    have hc : (starRingEnd ℂ) s = (s.re : ℂ) + ((-s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [← hc, riemannZeta_conj, ← map_inv₀, Complex.norm_conj]

/-- **`1/ζ` near the half line, uniformly in `t`** (RH). -/
theorem norm_invZ_le_sharp (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ l : ℝ, 2 ≤ l → ∀ s : ℂ, 1 / 2 + 4 / l ≤ s.re → s.re ≤ 2 →
      ‖invZ s‖ ≤ Real.exp (A * (l ^ 2 * Real.exp l + 1)) * (|s.im| + 3) ^ (4 / l) := by
  obtain ⟨A₀, hA₀, hL⟩ := norm_inv_zeta_le_large hRH
  obtain ⟨K₁, K₂, hK₁, hK₂, hSm⟩ := norm_invZ_le_small hRH
  set S := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set A := A₀ + 2 * S + 16 + |Real.log K₁| + K₂ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A, hA0, fun l hl s h0 h2 => ?_⟩
  have hl0 : 0 < l := by linarith
  have hη : 4 / l ≤ s.re - 1 / 2 := by linarith
  have h4l : 0 < 4 / l := by positivity
  have hre : 1 / 2 < s.re := by linarith
  have hpow1 : 1 ≤ (|s.im| + 3) ^ (4 / l) :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) h4l.le
  set E := Real.exp l with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hl0.le
  have hl2E : l ≤ l ^ 2 * E := by nlinarith
  have hexp0 : 0 < Real.exp (A * (l ^ 2 * E + 1)) := Real.exp_pos _
  by_cases ht : |s.im| ≤ 1
  · have hb := hSm s hre h2 ht
    have h3 : 3 / (2 * (s.re - 1 / 2)) ≤ l := by
      rw [div_le_iff₀ (by linarith)]
      have : 8 / l ≤ 2 * (s.re - 1 / 2) := by
        have e : 8 / l = 2 * (4 / l) := by ring
        linarith
      have h8 : 8 = l * (8 / l) := by field_simp
      nlinarith
    have hp : (3 / (2 * (s.re - 1 / 2))) ^ K₂ ≤ Real.exp (K₂ * l) := by
      calc (3 / (2 * (s.re - 1 / 2))) ^ K₂ ≤ l ^ K₂ :=
            Real.rpow_le_rpow (by have : 0 < s.re - 1 / 2 := by linarith
                                  positivity) h3 hK₂
        _ = Real.exp (Real.log l * K₂) := Real.rpow_def_of_pos hl0 _
        _ ≤ Real.exp (K₂ * l) := by
            apply Real.exp_le_exp.2
            have := Real.log_le_sub_one_of_pos hl0
            nlinarith
    have hK : K₁ ≤ Real.exp |Real.log K₁| := by
      calc K₁ = Real.exp (Real.log K₁) := (Real.exp_log hK₁).symm
        _ ≤ _ := Real.exp_le_exp.2 (le_abs_self _)
    have hsum : |Real.log K₁| + K₂ * l ≤ A * (l ^ 2 * E + 1) := by
      have : K₂ * l ≤ K₂ * (l ^ 2 * E) := mul_le_mul_of_nonneg_left hl2E hK₂
      have hAK : K₂ ≤ A := by rw [hA]; linarith [abs_nonneg (Real.log K₁)]
      have hAK1 : |Real.log K₁| ≤ A := by rw [hA]; linarith
      nlinarith [mul_le_mul_of_nonneg_right hAK (show 0 ≤ l ^ 2 * E by positivity)]
    calc ‖invZ s‖ ≤ K₁ * (3 / (2 * (s.re - 1 / 2))) ^ K₂ := hb
      _ ≤ Real.exp |Real.log K₁| * Real.exp (K₂ * l) := by
          gcongr
      _ = Real.exp (|Real.log K₁| + K₂ * l) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (A * (l ^ 2 * E + 1)) := Real.exp_le_exp.2 hsum
      _ ≤ Real.exp (A * (l ^ 2 * E + 1)) * (|s.im| + 3) ^ (4 / l) := le_mul_of_one_le_right hexp0.le hpow1
  · push Not at ht
    have hs1 : s ≠ 1 := fun h => by rw [h] at ht; norm_num at ht
    rw [invZ_eq hs1, norm_inv_zeta_abs_im]
    set t := |s.im| with htdef
    have hx : Real.exp 2 ≤ Real.exp l := Real.exp_le_exp.2 hl
    have h4 : 4 ≤ (s.re - 1 / 2) * Real.log (Real.exp l) := by
      rw [Real.log_exp]
      have := mul_le_mul_of_nonneg_right hη hl0.le
      rwa [div_mul_cancel₀ _ hl0.ne'] at this
    have hb := hL t (Real.exp l) s.re ht.le hx hre h2 h4
    rw [Real.log_exp] at hb
    refine hb.trans ?_
    set C := (E + 1) * l ^ 2 + (E + 1 + S) with hC
    have hsplit : A₀ + (4 * C + 4 * Real.log (3 + t) + 20) / l =
        (A₀ + (4 * C + 20) / l) + Real.log (t + 3) * (4 / l) := by
      rw [add_comm 3 t]; field_simp; ring
    have hrp : (t + 3) ^ (4 / l) = Real.exp (Real.log (t + 3) * (4 / l)) :=
      Real.rpow_def_of_pos (by linarith) _
    rw [hsplit, Real.exp_add, hrp]
    gcongr
    -- `A₀ + (4C + 20)/l ≤ A (l² E + 1)`
    have hl3 : 8 ≤ l ^ 3 := by nlinarith
    have hnum : 4 * C + 20 ≤ (16 * E * l ^ 2 + 2 * S) * l := by
      rw [hC]
      have e1 : 4 * ((E + 1) * l ^ 2) ≤ 8 * E * l ^ 3 := by nlinarith
      have e2 : 4 * E + 24 ≤ 8 * E * l ^ 3 := by nlinarith
      have e3 : 4 * S ≤ 2 * S * l := by nlinarith
      nlinarith
    have hdiv : (4 * C + 20) / l ≤ 16 * E * l ^ 2 + 2 * S := by
      rw [div_le_iff₀ hl0]; exact hnum
    have h16 : 16 ≤ A := by rw [hA]; linarith [abs_nonneg (Real.log K₁)]
    have hA2 : A₀ + 2 * S ≤ A := by rw [hA]; linarith [abs_nonneg (Real.log K₁)]
    have hmul : 16 * E * l ^ 2 ≤ A * (l ^ 2 * E) := by
      have := mul_le_mul_of_nonneg_right h16 (show 0 ≤ l ^ 2 * E by positivity)
      linarith
    have e : A * (l ^ 2 * E + 1) = A * (l ^ 2 * E) + A := by ring
    rw [e]
    linarith

/-- **`1/ζ(s) ≤ exp(C log t / log log t)` on `σ ≥ 1/2 + 8/log log t`** (RH). -/
theorem invZetaSharpWith_of_RH (hRH : RiemannHypothesis) : InvZetaSharpBoundWith 8 := by
  obtain ⟨A, hA0, hA⟩ := norm_invZ_le_sharp hRH
  obtain ⟨C₂, hC₂⟩ := norm_inv_zeta_le_of_two_le
  set B := 4 + Real.log (max C₂ 1) with hB
  have hB0 : 0 ≤ Real.log (max C₂ 1) := Real.log_nonneg (le_max_right _ _)
  obtain ⟨U, hU⟩ := eventually_atTop.1 (eventually_le_div_log A B)
  set U' := max U (Real.exp 4) with hU'
  refine ⟨9, Real.exp U', fun s hts hre => ?_⟩
  set t := |s.im| with htdef
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) hts
  set u := Real.log t with hudef
  have hu : U' ≤ u := by rw [hudef, Real.le_log_iff_exp_le ht0]; exact hts
  have hu4 : Real.exp 4 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 4) hu4
  set v := Real.log u with hvdef
  have hv4 : 4 ≤ v := by rw [hvdef, Real.le_log_iff_exp_le hu0]; exact hu4
  have hv0 : 0 < v := by linarith
  have hkey := hU u (le_trans (le_max_left _ _) hu)
  have hlog1 : 1 ≤ u := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hu4
  have ht1 : 1 ≤ t := by
    rw [hudef] at hlog1
    by_contra h; push Not at h
    have := Real.log_lt_log ht0 h
    rw [Real.log_one] at this; linarith
  have hfin_pos : 0 ≤ u / v := by positivity
  rcases le_or_gt s.re 2 with h2 | h2
  · set l := v / 2 with hl
    have hl2 : 2 ≤ l := by rw [hl]; linarith
    have h48 : 4 / l = 8 / v := by rw [hl]; field_simp; ring
    have hs : 1 / 2 + 4 / l ≤ s.re := by rw [h48]; exact hre
    have hb := hA l hl2 s hs h2
    have hs1 : s ≠ 1 := fun h => by
      have : t = 0 := by rw [htdef, h]; simp
      linarith
    rw [invZ_eq hs1, h48] at hb
    refine hb.trans ?_
    -- `e^l = √u` and `l² ≤ v²`
    have hEl : Real.exp l = u ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hu0, hl, hvdef]; ring_nf
    have hl2v : l ^ 2 ≤ v ^ 2 := by rw [hl]; nlinarith
    have hsq0 : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu0.le _
    have hlogt3 : Real.log (t + 3) ≤ u + 2 := by
      have h1 : Real.log (t + 3) ≤ Real.log (4 * t) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) ht0.ne'] at h1
      have : Real.log 4 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
        have h2' : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have := Real.log_two_lt_d9
        linarith
      linarith
    have hrp : (t + 3) ^ (8 / v) = Real.exp (Real.log (t + 3) * (8 / v)) :=
      Real.rpow_def_of_pos (by linarith) _
    rw [hrp, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have e1 : A * (l ^ 2 * Real.exp l + 1) ≤ A * (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) := by
      rw [hEl]; gcongr
    have e2 : Real.log (t + 3) * (8 / v) ≤ 8 * (u / v) + 4 := by
      have : Real.log (t + 3) * (8 / v) ≤ (u + 2) * (8 / v) :=
        mul_le_mul_of_nonneg_right hlogt3 (by positivity)
      have h16 : 16 / v ≤ 4 := by rw [div_le_iff₀ hv0]; linarith
      have : (u + 2) * (8 / v) = 8 * (u / v) + 16 / v := by field_simp; ring
      linarith
    have : 9 * u / v = 9 * (u / v) := by ring
    rw [this]
    have hk : A * (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) + 4 ≤ u / v := by
      have := hkey; rw [hB] at this; linarith
    linarith
  · have hb := hC₂ s h2.le
    refine hb.trans ?_
    have hk : Real.log (max C₂ 1) ≤ u / v := by
      have hA' : 0 ≤ A * (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) := by
        have := Real.rpow_nonneg hu0.le (1 / 2 : ℝ); positivity
      have := hkey; rw [hB] at this; linarith
    calc C₂ ≤ max C₂ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max C₂ 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (9 * u / v) := by
          apply Real.exp_le_exp.2
          have : 9 * u / v = 9 * (u / v) := by ring
          rw [this]; linarith

end Mertens
