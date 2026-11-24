import LLS.Sharp.Defs
import LLS.Sharp.AssemblyAux.Gamma
import LLS.Sharp.AssemblyAux.Shift

/-!
# LLS §5 assembly with the paper's elimination of `|Re B(χ)|`

The zero sum `Z` is eliminated exactly as in the paper: `Re D(1, χ⁻¹) = Re D(1, χ)`
(`AssemblyAux.re_D_inv_one`), so Lemma 2.3 reads
`Z (1 − y)² ≤ (1 − 1/x) log N − 2 Re S' + 2Γ ≤ Z (1 + y)²` with `y = 1/√x`
(`AssemblyAux.cesShift_two_sided`), the gamma part `Γ` is bounded per parity
(`AssemblyAux.gamma_shift_bounds`), and Lemma 2.5 (`LLS.l1_core`) is combined with these.
-/

namespace LLS.Sharp

open Real Erdos985 Erdos985.Analytic

variable {N : ℕ} [NeZero N]

/-- Upper bound, LLS §5.1, before the prime sums are estimated. -/
theorem log_norm_L1_le_sharp (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 16 ≤ x) :
    Real.log ‖DirichletCharacter.LFunction χ 1‖ ≤
      l1Sum1 x + (Real.log N / 2 + Gpar (parity χ)) / Real.log x
      - (1 / (2 * Real.log x) - 1 / √(x : ℝ) / Real.log x ^ 2)
          * ((1 - 1 / (x : ℝ)) * Real.log N - 2 * P2sum x + 2 * ELpar (parity χ) x)
          / (1 + 1 / √(x : ℝ)) ^ 2
      + 2 / ((x : ℝ) * Real.log x ^ 2) := by
  have hx2 : 2 ≤ x := by omega
  obtain ⟨h1, h2, -, -⟩ := LLS.l1_core hGRH hprim hχ x hx2
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx16 : (16 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 2 < Real.log x := by
    have := Real.add_one_le_exp (2 : ℝ)
    have h3 : Real.exp 2 < 16 := by
      have := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    rw [Real.lt_log_iff_exp_lt hx0]; linarith
  have hsx : 4 ≤ √(x : ℝ) := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hb0 : 0 ≤ 1 / √(x : ℝ) := by positivity
  have hb1 : 1 / √(x : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  rw [abs_le] at h1
  have hZ2 := AssemblyAux.Z2_eq_two hGRH hprim hχ
  have hG1 := AssemblyAux.re_gammaLogDeriv_one_eq χ
  rw [hG1] at h2
  obtain ⟨hlo, hhi⟩ := AssemblyAux.cesShift_two_sided hGRH hprim hχ x hx2
  obtain ⟨hEL, hEU⟩ := AssemblyAux.gamma_shift_bounds χ x (by omega)
  have hS := LLS.abs_re_cesShift_le χ x
  rw [abs_le] at hS
  have hl1 := LLS.abs_re_l1Sum_le χ x
  rw [abs_le] at hl1
  set Z := LLS.Z2 χ
  set l := Real.log (x : ℝ)
  set b := 1 / √(x : ℝ) with hb
  set U := (LLS.D χ 1).re
  set ℓ := (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
  set R := (1 - 1 / (x : ℝ)) * Real.log N - 2 * P2sum x + 2 * ELpar (parity χ) x
  set c := 1 / (2 * l) - b / l ^ 2
  have hc : 0 ≤ c := by
    have : b / l ^ 2 ≤ 1 / (2 * l) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    simp only [c]; linarith
  have hR : R ≤ Z * (1 + b) ^ 2 := by simp only [R]; linarith
  have hRZ : c * R / (1 + b) ^ 2 ≤ c * Z := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    rw [div_le_iff₀ (by positivity)]; linarith
  have eℓ : ℓ / l = Z * (1 / (2 * l)) - (Real.log N / 2 + Gpar (parity χ)) / l := by
    rw [h2, hZ2]; field_simp; ring
  have eZ : (Z / √(x : ℝ) + 2 / x) / l ^ 2 = Z * (b / l ^ 2) + 2 / ((x : ℝ) * l ^ 2) := by
    rw [hb]; field_simp
  have ecZ : c * Z = Z * (1 / (2 * l)) - Z * (b / l ^ 2) := by simp only [c]; ring
  linarith [h1.2]

/-- Lower bound, LLS §5.2, before the prime sums are estimated. -/
theorem log_norm_L1_ge_sharp (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 16 ≤ x) :
    (Wsum χ x).re
      - ((1 / Real.log x + 2 * (1 / √(x : ℝ)) / Real.log x ^ 2) / (1 - 1 / √(x : ℝ)) ^ 2
          - 1 / Real.log x) * P2sum x
      + (Real.log N / 2 + Gpar (parity χ)) / Real.log x
      - (1 / (2 * Real.log x) + 1 / √(x : ℝ) / Real.log x ^ 2)
          * ((1 - 1 / (x : ℝ)) * Real.log N + 2 * EUpar (parity χ) x) / (1 - 1 / √(x : ℝ)) ^ 2
      - 2 / ((x : ℝ) * Real.log x ^ 2)
      ≤ Real.log ‖DirichletCharacter.LFunction χ 1‖ := by
  have hx2 : 2 ≤ x := by omega
  obtain ⟨h1, h2, -, -⟩ := LLS.l1_core hGRH hprim hχ x hx2
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hx16 : (16 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 2 < Real.log x := by
    have := Real.add_one_le_exp (2 : ℝ)
    have h3 : Real.exp 2 < 16 := by
      have := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    rw [Real.lt_log_iff_exp_lt hx0]; linarith
  have hsx : 4 ≤ √(x : ℝ) := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hb0 : 0 ≤ 1 / √(x : ℝ) := by positivity
  have hb1 : 1 / √(x : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  rw [abs_le] at h1
  have hZ2 := AssemblyAux.Z2_eq_two hGRH hprim hχ
  have hG1 := AssemblyAux.re_gammaLogDeriv_one_eq χ
  rw [hG1] at h2
  obtain ⟨hlo, hhi⟩ := AssemblyAux.cesShift_two_sided hGRH hprim hχ x hx2
  obtain ⟨hEL, hEU⟩ := AssemblyAux.gamma_shift_bounds χ x (by omega)
  have hS := LLS.abs_re_cesShift_le χ x
  rw [abs_le] at hS
  have hW := congrArg Complex.re (AssemblyAux.l1Sum_add_cesShift χ x hx2)
  rw [Complex.add_re, Complex.div_ofReal_re] at hW
  set Z := LLS.Z2 χ
  set l := Real.log (x : ℝ)
  set b := 1 / √(x : ℝ) with hb
  set U := (LLS.D χ 1).re
  set ℓ := (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
  set S := (LLS.cesShift χ x).re
  set W := (1 - 1 / (x : ℝ)) * Real.log N + 2 * EUpar (parity χ) x
  set d := 1 / (2 * l) + b / l ^ 2
  set A := (1 / l + 2 * b / l ^ 2) / (1 - b) ^ 2
  have hd : 0 ≤ d := by positivity
  have h1b : 0 < (1 - b) ^ 2 := by nlinarith
  have hZW : Z ≤ (W - 2 * S) / (1 - b) ^ 2 := by
    rw [le_div_iff₀ h1b]; simp only [W]; linarith
  have f1 : d * Z ≤ d * ((W - 2 * S) / (1 - b) ^ 2) := mul_le_mul_of_nonneg_left hZW hd
  have f2 : d * ((W - 2 * S) / (1 - b) ^ 2) = d * W / (1 - b) ^ 2 - A * S := by
    simp only [d, A]; field_simp
  have hA : 1 / l ≤ A := by
    simp only [A]
    rw [le_div_iff₀ h1b]
    have : (1 - b) ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ 2 * b / l ^ 2 := by positivity
    have : 1 / l * (1 - b) ^ 2 ≤ 1 / l := by
      have := one_div_pos.mpr hl
      nlinarith
    linarith
  have f4 : -(A - 1 / l) * P2sum x ≤ (A - 1 / l) * S := by
    have := mul_le_mul_of_nonneg_left hS.1 (sub_nonneg.mpr hA)
    linarith
  have f5 : (A - 1 / l) * S = A * S - S / l := by ring
  have eℓ : ℓ / l = Z * (1 / (2 * l)) - (Real.log N / 2 + Gpar (parity χ)) / l := by
    rw [h2, hZ2]; field_simp; ring
  have eZ : (Z / √(x : ℝ) + 2 / x) / l ^ 2 = Z * (b / l ^ 2) + 2 / ((x : ℝ) * l ^ 2) := by
    rw [hb]; field_simp
  have edZ : d * Z = Z * (1 / (2 * l)) + Z * (b / l ^ 2) := by simp only [d]; ring
  linarith [h1.1]

end LLS.Sharp
