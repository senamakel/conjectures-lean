import Artin.Analytic.Core.Xi

/-!
# Zeros of `ξ_K`: the sum `∑ 1/|ρ(ρ+1)|` and local counting (blueprint A2)

Under RH for `ζ_K`, with `n = [K : ℚ]` and `d = d_K`:

* `zeroSum_le`: `∑_ρ m_ρ / |ρ(ρ+1)| ≤ log |d| + 6 n`;
* `zeroCount_le`: `∑_{|Im ρ - T| ≤ 1} m_ρ ≤ 6 (log |d| + n log(|T| + 3))`.

Both come from `Re ξ'/ξ(s) = ∑_ρ m_ρ Re 1/(s - ρ)` (`hasSum_re_logDeriv_xi`, all terms `≥ 0`) at
`s = 2 + iT`, and the upper bound
`Re ξ'/ξ(2 + iT) = Re ζ_K'/ζ_K + Re 1/s + Re 1/(s - 1) + Re G_K(s)
  ≤ 0.6 n + 3/2 + ½ log |d| + ½ n log(|T| + 3)` (`re_logDeriv_xi_le`), using
`|ζ_K'/ζ_K(s)| ≤ n ∑ Λ(m)/m² ≤ 0.6 n` (`norm_logDeriv_Z_le`, from `Λ_K ≤ n Λ` and erdos-985's
`S2_le`) and `Re ψ(w) ≤ log(|w| + 1)` for `Re w ≥ 1` (`re_digamma_le`). For `Re ρ = 1/2`,
`1/|ρ(ρ+1)| ≤ 2 Re 1/(2 - ρ)`, and `Re 1/(2 + iT - ρ) ≥ 6/13` when `|Im ρ - T| ≤ 1`.
This is the argument of Davenport, *Multiplicative Number Theory*, §15, for `ζ`, and of
Lagarias–Odlyzko (1977), Lemma 5.4, for `ζ_K`.
-/

namespace Artin.Analytic

open Complex NumberField ArtinPrimitiveRootsConjecture Filter Topology ArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

/-- `Re ψ(w) ≤ log(|w| + 1)` for `Re w ≥ 1`. From Stirling's series
`ψ(w) = log w - 1/(2w) - ∫_0^∞ (⌊t⌋ - t + ½)/(t + w)² dt`, valid for `Re w > 0`, whose last term is
`≤ 1/(4 Re w)` hmm in modulus; a cruder route is `ψ(w) - ψ(1) = ∑_k (1/(k+1) - 1/(k+w))`
(erdos-985's `hasSum_digamma`) compared with `∑_{k < |w|} 1/(k+1) ≤ log(|w|+1) + 1` and a tail
`O(1)`. See Whittaker–Watson, *Modern Analysis*, 12.33, or Olver, *Asymptotics and Special
Functions*, Ch. 8 §4. -/
theorem re_digamma_le {w : ℂ} (hw : 1 ≤ w.re) : (digamma w).re ≤ Real.log (‖w‖ + 1) := by
  sorry

lemma re_gR_le {a : ℕ} (ha : a ≤ 1) (T : ℝ) :
    (gR a (2 + T * I)).re ≤ (1 / 2) * Real.log (|T| + 3) := by
  have hre : (gR a (2 + T * I)).re =
      -(1 / 2) * Real.log Real.pi + (1 / 2) * (digamma ((2 + T * I + a) / 2)).re := by
    simp [gR]
  have hw : 1 ≤ ((2 + T * I + a) / 2 : ℂ).re := by
    simp; have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith
  have hnorm : ‖((2 + T * I + a) / 2 : ℂ)‖ ≤ (3 + |T|) / 2 := by
    rw [norm_div, Complex.norm_two]
    have h1 : ‖(2 + T * I + a : ℂ)‖ ≤ ‖((2 + a : ℕ) : ℂ)‖ + ‖(T * I : ℂ)‖ := by
      have : (2 + T * I + a : ℂ) = ((2 + a : ℕ) : ℂ) + T * I := by push_cast; ring
      rw [this]; exact norm_add_le _ _
    rw [Complex.norm_natCast, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs] at h1
    have : ((2 + a : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : 2 + a ≤ 3)
    linarith
  have hd := re_digamma_le hw
  have hlog : Real.log (‖((2 + T * I + a) / 2 : ℂ)‖ + 1) ≤ Real.log (|T| + 3) :=
    Real.log_le_log (by positivity) (by linarith [abs_nonneg T])
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [hre]
  nlinarith

/-- For a zero on the critical line, `1/|ρ(ρ+1)| ≤ 2 Re 1/(2 - ρ)`. -/
lemma inv_norm_mul_le_two {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / ‖ρ * (ρ + 1)‖ ≤ 2 * (1 / ((2 : ℂ) - ρ)).re := by
  obtain ⟨a, γ⟩ := ρ
  simp only at hρ
  subst hρ
  have hre : (1 / ((2 : ℂ) - ⟨1 / 2, γ⟩)).re = (3 / 2) / (9 / 4 + γ ^ 2) := by
    simp [normSq_apply]
    ring
  rw [hre]
  set t := ‖(⟨1 / 2, γ⟩ : ℂ) * (⟨1 / 2, γ⟩ + 1)‖ with ht
  have hsq : t ^ 2 = (1 / 4 + γ ^ 2) * (9 / 4 + γ ^ 2) := by
    rw [ht, ← normSq_eq_norm_sq, normSq_mul]
    simp [normSq_apply]
    ring
  have hlow : (1 / 3) * (9 / 4 + γ ^ 2) ≤ t := by
    have h1 : ((1 / 3) * (9 / 4 + γ ^ 2)) ^ 2 ≤ t ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg γ]
    nlinarith [norm_nonneg ((⟨1 / 2, γ⟩ : ℂ) * (⟨1 / 2, γ⟩ + 1)), sq_nonneg γ]
  have hpos : 0 < (1 / 3) * (9 / 4 + γ ^ 2) := by positivity
  calc 1 / t ≤ 1 / ((1 / 3) * (9 / 4 + γ ^ 2)) := one_div_le_one_div_of_le hpos hlow
    _ = 2 * (3 / 2 / (9 / 4 + γ ^ 2)) := by field_simp

lemma one_le_abs_discr : (1 : ℝ) ≤ |(discr K : ℝ)| := by
  have h := discr_ne_zero K
  have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs h
  exact_mod_cast this

lemma log_abs_discr_nonneg : 0 ≤ Real.log |(discr K : ℝ)| :=
  Real.log_nonneg one_le_abs_discr

lemma one_le_finrank : (1 : ℝ) ≤ Module.finrank ℚ K := by
  have : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact_mod_cast this

namespace ContinuationData

variable (D : ContinuationData K)

/-- `|ζ_K'/ζ_K(s)| ≤ 0.6 n` for `Re s ≥ 2`. -/
theorem norm_logDeriv_Z_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖deriv D.Z s / D.Z s‖ ≤ 0.6 * Module.finrank ℚ K := by
  have hs1 : 1 < s.re := by linarith
  have hev : D.Z =ᶠ[𝓝 s] dedekindZeta K := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show s ∈ {w : ℂ | 1 < w.re} from hs1)] with w hw
    exact D.Z_eq_dedekindZeta hw
  rw [hev.deriv_eq, D.Z_eq_dedekindZeta hs1, ← neg_neg (deriv (dedekindZeta K) s / _),
    ← LSeries_vonMangoldtK K hs1, norm_neg]
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  have hsum := LSeriesSummable_vonMangoldtK K hs1
  have hb : ∀ m : ℕ, ‖LSeries.term (fun m => (vonMangoldtK K m : ℂ)) s m‖ ≤
      n * ((Λ m : ℝ) / (m : ℝ) ^ 2) := by
    intro m
    rw [LSeries.norm_term_eq]
    split_ifs with hm
    · simp [hm]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
    rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldtK_nonneg K m)]
    have h2 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ s.re := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hm1 (by simpa using hs)
    calc vonMangoldtK K m / (m : ℝ) ^ s.re ≤ n * Λ m / (m : ℝ) ^ 2 :=
          div_le_div₀ (mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg)
            (vonMangoldtK_le K m) (pow_pos (by linarith) 2) h2
      _ = _ := by ring
  calc ‖LSeries (fun m => (vonMangoldtK K m : ℂ)) s‖
      ≤ ∑' m, ‖LSeries.term (fun m => (vonMangoldtK K m : ℂ)) s m‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' m : ℕ, n * ((Λ m : ℝ) / (m : ℝ) ^ 2) :=
        hsum.norm.tsum_le_tsum hb (Erdos985.Analytic.BoundsAux.summable_Λ2.mul_left n)
    _ = n * ∑' m : ℕ, (Λ m : ℝ) / (m : ℝ) ^ 2 := tsum_mul_left
    _ ≤ n * 0.6 := mul_le_mul_of_nonneg_left Erdos985.Analytic.BoundsAux.S2_le (by positivity)
    _ = 0.6 * n := by ring

/-- `Re ξ'/ξ(2 + iT) ≤ 0.6 n + 3/2 + ½ log |d| + ½ n log(|T| + 3)`. -/
theorem re_logDeriv_xi_le (T : ℝ) :
    (deriv D.ξ (2 + T * I) / D.ξ (2 + T * I)).re ≤
      0.6 * Module.finrank ℚ K + 3 / 2 + (1 / 2) * Real.log |(discr K : ℝ)| +
        (1 / 2) * Module.finrank ℚ K * Real.log (|T| + 3) := by
  set s : ℂ := 2 + T * I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hL := D.logDeriv_Z_eq (s := s) (by rw [hsre]; norm_num)
  have hD : deriv D.ξ s / D.ξ s = deriv D.Z s / D.Z s + 1 / s + 1 / (s - 1) +
      gammaLogDerivK K s := by rw [hL]; ring
  rw [hD]
  simp only [add_re]
  have h1 : (deriv D.Z s / D.Z s).re ≤ 0.6 * Module.finrank ℚ K :=
    (re_le_norm _).trans (D.norm_logDeriv_Z_le (by rw [hsre]))
  have h2 : (1 / s).re ≤ 1 / 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hsre]
    have : s.im = T := by simp [hs]
    rw [this, div_le_iff₀ (by nlinarith [sq_nonneg T])]; nlinarith [sq_nonneg T]
  have h3 : (1 / (s - 1)).re ≤ 1 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have e1 : (s - 1).re = 1 := by simp [hsre]; norm_num
    have e2 : (s - 1).im = T := by simp [hs]
    rw [e1, e2, div_le_iff₀ (by nlinarith [sq_nonneg T])]; nlinarith [sq_nonneg T]
  have hG : (gammaLogDerivK K s).re ≤ (1 / 2) * Real.log |(discr K : ℝ)| +
      (1 / 2) * Module.finrank ℚ K * Real.log (|T| + 3) := by
    have g0 := re_gR_le (a := 0) (by norm_num) T
    have g1 := re_gR_le (a := 1) (by norm_num) T
    rw [← hs] at g0 g1
    have hrk : (InfinitePlace.nrRealPlaces K : ℝ) + 2 * InfinitePlace.nrComplexPlaces K =
        Module.finrank ℚ K := by exact_mod_cast InfinitePlace.card_add_two_mul_card_eq_rank K
    simp only [gammaLogDerivK, add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero,
      ofReal_re, ofReal_im]
    norm_num
    have hr1 : (0 : ℝ) ≤ InfinitePlace.nrRealPlaces K := Nat.cast_nonneg _
    have hr2 : (0 : ℝ) ≤ InfinitePlace.nrComplexPlaces K := Nat.cast_nonneg _
    rw [← hrk]
    nlinarith
  linarith

/-- **Zero sum** (blueprint A2): `∑_ρ m_ρ / |ρ(ρ+1)| ≤ log |d_K| + 6 n` under RH. -/
theorem zeroSum_le (hRH : DedekindZetaRH K) :
    Summable (fun ρ : {ρ : ℂ // D.ξ ρ = 0} => (D.mult ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ ≤
      Real.log |(discr K : ℝ)| + 6 * Module.finrank ℚ K := by
  have h2 : ((2 : ℂ)) = 2 + ((0 : ℝ) : ℂ) * I := by simp
  have hξ2 : D.ξ 2 ≠ 0 := D.xi_ne_zero_of_one_le_re (by norm_num)
  have hS := D.hasSum_re_logDeriv_xi hRH hξ2
  have hcmp : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0}, (D.mult ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ ≤
      2 * ((D.mult ρ : ℝ) * (1 / ((2 : ℂ) - ρ)).re) := by
    intro ρ
    have h := inv_norm_mul_le_two (D.xi_zero_re_eq_half hRH ρ.2)
    rw [div_eq_mul_one_div]
    have : (0 : ℝ) ≤ D.mult ρ := Nat.cast_nonneg _
    nlinarith
  have hnn : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0}, 0 ≤ (D.mult ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hS2 := hS.mul_left 2
  have hsum := Summable.of_nonneg_of_le hnn hcmp hS2.summable
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum hcmp hS2.summable
  rw [hS2.tsum_eq] at hle
  have hb := D.re_logDeriv_xi_le 0
  rw [← h2] at hb
  simp only [abs_zero, zero_add] at hb
  have hl3 : Real.log 3 < 1.4 := by
    have := Real.log_two_lt_d9
    have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hn := one_le_finrank (K := K)
  nlinarith

/-- **Local zero count** (blueprint A2): `∑_{|Im ρ - T| ≤ 1} m_ρ ≤ 6 (log |d_K| + n log(|T| + 3))`
under RH. -/
theorem zeroCount_le (hRH : DedekindZetaRH K) (T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // D.ξ ρ = 0} =>
        if |(ρ : ℂ).im - T| ≤ 1 then (D.mult ρ : ℝ) else 0) ∧
    ∑' ρ : {ρ : ℂ // D.ξ ρ = 0}, (if |(ρ : ℂ).im - T| ≤ 1 then (D.mult ρ : ℝ) else 0) ≤
      6 * (Real.log |(discr K : ℝ)| + Module.finrank ℚ K * Real.log (|T| + 3)) := by
  set s : ℂ := 2 + T * I with hs
  have hξs : D.ξ s ≠ 0 := D.xi_ne_zero_of_one_le_re (by simp [hs])
  have hS := D.hasSum_re_logDeriv_xi hRH hξs
  have hcmp : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0},
      (if |(ρ : ℂ).im - T| ≤ 1 then (D.mult ρ : ℝ) else 0) ≤
        (13 / 6) * ((D.mult ρ : ℝ) * (1 / (s - ρ)).re) := by
    intro ρ
    have hρ := D.xi_zero_re_eq_half hRH ρ.2
    have hm : (0 : ℝ) ≤ D.mult ρ := Nat.cast_nonneg _
    generalize (ρ : ℂ) = z at hρ ⊢
    obtain ⟨β, γ⟩ := z
    simp only at hρ
    subst hρ
    have hre : (1 / (s - ⟨1 / 2, γ⟩)).re = (3 / 2) / (9 / 4 + (T - γ) ^ 2) := by
      rw [hs]; simp [normSq_apply]; ring
    have hpos : 0 ≤ (3 / 2) / (9 / 4 + (T - γ) ^ 2) := by positivity
    split_ifs with h
    · rw [hre]
      have hsq : (T - γ) ^ 2 ≤ 1 := by
        have : |γ - T| ≤ 1 := h
        rw [abs_le] at this; nlinarith
      have : 6 / 13 ≤ (3 / 2) / (9 / 4 + (T - γ) ^ 2) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      nlinarith
    · rw [hre]; positivity
  have hnn : ∀ ρ : {ρ : ℂ // D.ξ ρ = 0},
      0 ≤ (if |(ρ : ℂ).im - T| ≤ 1 then (D.mult ρ : ℝ) else 0) := by
    intro ρ; split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl
  have hS2 := hS.mul_left (13 / 6)
  have hsum := Summable.of_nonneg_of_le hnn hcmp hS2.summable
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum hcmp hS2.summable
  rw [hS2.tsum_eq] at hle
  have hb := D.re_logDeriv_xi_le T
  have hn := one_le_finrank (K := K)
  have hd := log_abs_discr_nonneg (K := K)
  have hl3 : 1 ≤ Real.log (|T| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith [abs_nonneg T]
  nlinarith

end ContinuationData

end Artin.Analytic
