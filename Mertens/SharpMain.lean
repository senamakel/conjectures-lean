import Mertens.Main
import Mertens.SharpInvZeta

/-!
# Titchmarsh's bound `M(x) ≤ √x exp(C log x / log log x)` under RH

The Cesàro–Perron route of `Mertens.Littlewood` (Steps D–E), with the contour at
`σ₀ = 1/2 + 4/l` and the bound of `norm_invZ_le_sharp` on it:
`‖invZ(σ₀+it)‖ ≤ 3 e^{A(l²e^l+1)} (1+|t|)^{4/l}`. Interpolating with `θ = 8/l` leaves
`∫ (1+|t|)^{-1-4/l} dt = l/2`, so

    |M(N)| ≤ 8 l e^{A(l² e^l + 1)} (N+1)^{1/2 + 12/l}          (l ≥ 8, N ≥ 1).

With `l = ½ log log x`, `e^l = √(log x)` and the exponent is
`½ log x + 24 log x / log log x + O(√(log x) (log log x)²)`.
-/

open Complex MeasureTheory Filter Set Topology Asymptotics

namespace Mertens

/-- Step E with an explicit bound `‖invZ‖ ≤ E (1+|t|)^ε` on the line. -/
theorem norm_diff_F_le_of {E ε θ σ₀ : ℝ} (hE : 0 ≤ E) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h1 : 1 / 2 < σ₀)
    (hinv : ∀ t : ℝ, ‖invZ ((σ₀ : ℂ) + t * I)‖ ≤ E * (1 + |t|) ^ ε) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) :
    ‖((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) - (N : ℂ) * F N ((σ₀ : ℂ) + t * I)‖
      ≤ E * 2 * 2 * (2 / min σ₀ 1) * ((N : ℝ) + 1) ^ (σ₀ + θ) * (1 + |t|) ^ (ε - θ - 1) := by
  set m := min σ₀ 1 with hm
  have hm0 : 0 < m := lt_min (by linarith) one_pos
  set s : ℂ := (σ₀ : ℂ) + t * I with hsdef
  have hsre : s.re = σ₀ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hre0 : 0 < s.re := by linarith
  set u := 1 + |t| with hu
  have hu0 : 0 < u := by positivity
  set P : ℝ := (N : ℝ) + 1 with hP
  have hP0 : 0 < P := by positivity
  have ha : m * u / 2 ≤ ‖s‖ := by
    have := norm_ge_of_re_pos hre0
    rw [hsre, hsim] at this
    exact this
  have hb : u / 2 ≤ ‖s + 1‖ := by
    have := norm_add_one_ge hre0.le
    rwa [hsim] at this
  have ha0 : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) ha
  have hb0 : 0 < ‖s + 1‖ := lt_of_lt_of_le (by positivity) hb
  set d : ℂ := ((N + 1 : ℕ) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ s - (N : ℂ) * (N : ℂ) ^ s with hd
  have hD : ((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) s - (N : ℂ) * F N s = invZ s * d / (s * (s + 1)) := by
    simp only [F, hd]
    push_cast
    ring
  rw [hD, norm_div, norm_mul, norm_mul]
  have hinv' : ‖invZ s‖ ≤ E * u ^ ε := hinv t
  have hdX := norm_diff_le_triv hre0.le N
  have hdY := norm_diff_le_mvt hre0.le N hN
  rw [hsre] at hdX hdY
  have hdI := le_rpow_mul_rpow (by positivity) (by positivity) hdX hdY hθ0 hθ1
  have hPexp : P ^ ((σ₀ + 1) * θ) * P ^ (σ₀ * (1 - θ)) = P ^ (σ₀ + θ) := by
    rw [← Real.rpow_add hP0]; ring_nf
  have h2θ : (2 : ℝ) ^ θ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hθ1
  have hdI' : ‖d‖ ≤ 2 * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ)) := by
    calc ‖d‖ ≤ (2 * P ^ (σ₀ + 1)) ^ θ * (‖s + 1‖ * P ^ σ₀) ^ (1 - θ) := hdI
      _ = 2 ^ θ * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le, ← hPexp]
        ring
      _ ≤ 2 * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ)) := by gcongr
  have hbθ : ‖s + 1‖ ^ (1 - θ) / ‖s + 1‖ ≤ 2 * u ^ (-θ) := by
    have e1 : ‖s + 1‖ ^ (1 - θ) / ‖s + 1‖ = (‖s + 1‖ ^ θ)⁻¹ := by
      rw [Real.rpow_sub hb0, Real.rpow_one]
      have : 0 < ‖s + 1‖ ^ θ := Real.rpow_pos_of_pos hb0 θ
      field_simp
    have e2 : ((u / 2) ^ θ)⁻¹ = 2 ^ θ * u ^ (-θ) := by
      rw [Real.div_rpow hu0.le (by norm_num), Real.rpow_neg hu0.le]
      have : 0 < u ^ θ := Real.rpow_pos_of_pos hu0 θ
      have : 0 < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
      field_simp
    rw [e1]
    calc (‖s + 1‖ ^ θ)⁻¹ ≤ ((u / 2) ^ θ)⁻¹ := by
          apply inv_anti₀ (Real.rpow_pos_of_pos (by positivity) θ)
          exact Real.rpow_le_rpow (by positivity) hb hθ0
      _ = 2 ^ θ * u ^ (-θ) := e2
      _ ≤ 2 * u ^ (-θ) := by gcongr
  have ha' : 1 / ‖s‖ ≤ 2 / m * u ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    calc 1 / ‖s‖ ≤ 1 / (m * u / 2) := one_div_le_one_div_of_le (by positivity) ha
      _ = 2 / m * u⁻¹ := by field_simp
  have hinv0 : 0 ≤ E * u ^ ε := by positivity
  calc ‖invZ s‖ * ‖d‖ / (‖s‖ * ‖s + 1‖)
      = ‖invZ s‖ * ‖d‖ * (1 / ‖s‖) * (1 / ‖s + 1‖) := by field_simp
    _ ≤ (E * u ^ ε) * (2 * (P ^ (σ₀ + θ) * ‖s + 1‖ ^ (1 - θ))) * (1 / ‖s‖) *
          (1 / ‖s + 1‖) := by gcongr
    _ = (E * u ^ ε) * (2 * P ^ (σ₀ + θ)) * (1 / ‖s‖) *
          (‖s + 1‖ ^ (1 - θ) / ‖s + 1‖) := by ring
    _ ≤ (E * u ^ ε) * (2 * P ^ (σ₀ + θ)) * (2 / m * u ^ (-1 : ℝ)) *
          (2 * u ^ (-θ)) := by gcongr
    _ = E * 2 * 2 * (2 / m) * P ^ (σ₀ + θ) * (u ^ ε * u ^ (-1 : ℝ) * u ^ (-θ)) := by ring
    _ = E * 2 * 2 * (2 / m) * P ^ (σ₀ + θ) * u ^ (ε - θ - 1) := by
        rw [show ε - θ - 1 = ε + (-1) + (-θ) by ring, Real.rpow_add hu0, Real.rpow_add hu0]

/-- `∫ (1 + |t|)^{-(1+α)} dt = 2/α` for `α > 0`. -/
theorem integral_one_add_abs_rpow_neg {α : ℝ} (hα : 0 < α) :
    ∫ t : ℝ, (1 + |t|) ^ (-(1 + α)) = 2 / α := by
  rw [integral_comp_abs (f := fun x : ℝ => (1 + x) ^ (-(1 + α)))]
  set f : ℝ → ℝ := fun x => -(1 + x) ^ (-α) / α with hf
  have hd : ∀ x : ℝ, -1 < x → HasDerivAt f ((1 + x) ^ (-(1 + α))) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have h2 := h1.rpow_const (p := -α) (Or.inl (by linarith))
    have h3 := (h2.neg).div_const α
    convert h3 using 1
    rw [show -α - 1 = -(1 + α) by ring]
    field_simp
  have hint : IntegrableOn (fun x : ℝ => (1 + x) ^ (-(1 + α))) (Ioi 0) := by
    have := (Erdos985.Analytic.PerronAux.integrable_one_add_abs_rpow
      (show (1 : ℝ) < 1 + α by linarith) 0).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [abs_of_pos (show (0 : ℝ) < x from hx)]
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hα).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).neg.div_const α
    simpa [hf, Function.comp] using h
  have := integral_Ioi_of_hasDerivAt_of_tendsto (f := f)
    (f' := fun x : ℝ => (1 + x) ^ (-(1 + α))) (a := 0)
    (hd 0 (by norm_num)).continuousAt.continuousWithinAt
    (fun x hx => hd x (by linarith [show (0 : ℝ) < x from hx])) hint hlim
  rw [this, hf]
  simp
  field_simp

/-- **The Mertens function, with the length parameter explicit** (RH):
`|M(N)| ≤ 8 l exp(A(l² e^l + 1)) (N+1)^{1/2+12/l}` for `l ≥ 8`, `N ≥ 1`. -/
theorem abs_mertens_nat_le_sharp (hRH : RiemannHypothesis) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ l : ℝ, 8 ≤ l → ∀ N : ℕ, 1 ≤ N →
      |(mertens N : ℝ)| ≤ 8 * l * Real.exp (A * (l ^ 2 * Real.exp l + 1)) *
        ((N : ℝ) + 1) ^ (1 / 2 + 12 / l) := by
  obtain ⟨A, hA0, hA⟩ := norm_invZ_le_sharp hRH
  refine ⟨A, hA0, fun l hl N hN => ?_⟩
  have hl0 : 0 < l := by linarith
  set ε : ℝ := 4 / l with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := by rw [hεdef, div_le_iff₀ hl0]; linarith
  set σ₀ : ℝ := 1 / 2 + ε with hσ₀
  have h1 : 1 / 2 < σ₀ := by linarith
  have h2 : σ₀ < 2 := by linarith
  set θ : ℝ := 8 / l with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_iff₀ hl0]; linarith
  set X := Real.exp (A * (l ^ 2 * Real.exp l + 1)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  set E := 3 * X with hE
  have hinv : ∀ t : ℝ, ‖invZ ((σ₀ : ℂ) + t * I)‖ ≤ E * (1 + |t|) ^ ε := by
    intro t
    have hb := hA l (by linarith) ((σ₀ : ℂ) + t * I) (by simp [hσ₀, hεdef]) (by simp; linarith)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at hb
    refine hb.trans ?_
    have hu : 0 ≤ 1 + |t| := by positivity
    have : (|t| + 3) ^ (4 / l) ≤ 3 * (1 + |t|) ^ ε := by
      calc (|t| + 3) ^ (4 / l) ≤ (3 * (1 + |t|)) ^ ε :=
            Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) hε0.le
        _ = 3 ^ ε * (1 + |t|) ^ ε := Real.mul_rpow (by norm_num) hu
        _ ≤ 3 * (1 + |t|) ^ ε := by
            gcongr
            exact Real.rpow_le_self_of_one_le (by norm_num) (by linarith)
    calc X * (|t| + 3) ^ (4 / l) ≤ X * (3 * (1 + |t|) ^ ε) := by gcongr
      _ = E * (1 + |t|) ^ ε := by rw [hE]; ring
  have hmin : min σ₀ 1 = σ₀ := min_eq_left (by linarith)
  set K := E * 2 * 2 * (2 / min σ₀ 1) with hK
  have hK0 : 0 ≤ K := by rw [hK, hmin]; positivity
  have hKle : K ≤ 48 * X := by
    rw [hK, hmin, hE]
    have : 2 / σ₀ ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  set J : ℝ := ∫ t : ℝ, (1 + |t|) ^ (ε - θ - 1) with hJ
  have hexpo : ε - θ - 1 = -(1 + 4 / l) := by rw [hεdef, hθdef]; ring
  have hJv : J = l / 2 := by
    rw [hJ, hexpo, integral_one_add_abs_rpow_neg (by positivity)]; field_simp; norm_num
  have hint : Integrable fun t : ℝ => (1 + |t|) ^ (ε - θ - 1) := by
    rw [hexpo]
    have h4 : 0 < 4 / l := by positivity
    have h14 : (1 : ℝ) < 1 + 4 / l := by linarith
    simpa using Erdos985.Analytic.PerronAux.integrable_one_add_abs_rpow h14 0
  have hpos : ∀ M : ℕ, 1 ≤ M → (0 : ℝ) < M := fun M hM => by exact_mod_cast hM
  have e := mertens_nat_eq N
  have hi1 : Integrable fun t : ℝ =>
      ((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) :=
    (integrable_F_line hRH (hpos _ (by omega)) h1 h2 le_rfl h2.le).const_mul _
  have hi2 : Integrable fun t : ℝ => (N : ℂ) * F N ((σ₀ : ℂ) + t * I) :=
    (integrable_F_line hRH (hpos _ hN) h1 h2 le_rfl h2.le).const_mul _
  rw [cesA_eq hRH h1 h2 (N + 1) (by omega), cesA_eq hRH h1 h2 N hN, ← mul_sub,
    ← integral_sub hi1 hi2] at e
  have hnorm : |(mertens N : ℝ)| = ‖((mertens N : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
  set β : ℝ := 1 / 2 + 12 / l
  have hβ : σ₀ + θ = β := by rw [hσ₀, hεdef, hθdef]; ring
  have hbound : ‖∫ t : ℝ, (((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) -
      (N : ℂ) * F N ((σ₀ : ℂ) + t * I))‖ ≤ K * ((N : ℝ) + 1) ^ β * J := by
    rw [hJ, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun t => ?_)
    have := norm_diff_F_le_of (ε := ε) (by rw [hE]; positivity) hθ0 hθ1 h1 hinv N hN t
    rwa [hβ] at this
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hnorm, e, norm_mul, hpi]
  have hP : 0 ≤ ((N : ℝ) + 1) ^ β := by positivity
  have hpi6 : 1 / (2 * Real.pi) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [Real.pi_gt_three]
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, (((N + 1 : ℕ) : ℂ) * F (N + 1 : ℕ) ((σ₀ : ℂ) + t * I) -
        (N : ℂ) * F N ((σ₀ : ℂ) + t * I))‖
      ≤ 1 / (2 * Real.pi) * (K * ((N : ℝ) + 1) ^ β * J) := by gcongr
    _ ≤ 1 / 6 * (48 * X * ((N : ℝ) + 1) ^ β * (l / 2)) := by
        rw [hJv]
        have : K * ((N : ℝ) + 1) ^ β * (l / 2) ≤ 48 * X * ((N : ℝ) + 1) ^ β * (l / 2) := by
          gcongr
        have h0' : 0 ≤ K * ((N : ℝ) + 1) ^ β * (l / 2) := by positivity
        nlinarith
    _ = 4 * l * X * ((N : ℝ) + 1) ^ β := by ring
    _ ≤ 8 * l * X * ((N : ℝ) + 1) ^ β := by
        have : 0 ≤ l * X * ((N : ℝ) + 1) ^ β := by positivity
        nlinarith

/-- **Titchmarsh (1927)**: under RH, `|M(x)| ≤ √x exp(25 log x / log log x)` for large `x`. -/
theorem mertensSharp_of_RH (hRH : RiemannHypothesis) : MertensSharpBound := by
  obtain ⟨A, hA0, hA⟩ := abs_mertens_nat_le_sharp hRH
  obtain ⟨U, hU⟩ := eventually_atTop.1 (eventually_le_div_log (A + 1) 4)
  set U' := max U (Real.exp 16) with hU'
  refine ⟨25, Real.exp U', fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set u := Real.log x with hudef
  have hu : U' ≤ u := by rw [hudef, Real.le_log_iff_exp_le hx0]; exact hx
  have hu16 : Real.exp 16 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 16) hu16
  set v := Real.log u with hvdef
  have hv16 : 16 ≤ v := by rw [hvdef, Real.le_log_iff_exp_le hu0]; exact hu16
  have hv0 : 0 < v := by linarith
  have hkey := hU u (le_trans (le_max_left _ _) hu)
  have hx1 : 1 ≤ x := by
    have : 0 ≤ u := hu0.le
    rw [hudef] at this
    by_contra h; push Not at h
    have := Real.log_neg hx0 h; linarith
  set l := v / 2 with hl
  have hl8 : 8 ≤ l := by rw [hl]; linarith
  have hl0 : 0 < l := by linarith
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.one_le_floor_iff _ |>.mpr hx1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hm : mertens x = mertens (N : ℝ) := by rw [mertens, mertens, Nat.floor_natCast]
  rw [hm]
  have hb := hA l hl8 N hN
  refine hb.trans ?_
  set β := 1 / 2 + 12 / l with hβ
  have hβ2 : β ≤ 2 := by
    have : 12 / l ≤ 3 / 2 := by rw [div_le_iff₀ hl0]; linarith
    linarith
  have hβ0 : 0 ≤ β := by positivity
  -- `(N+1)^β ≤ 4 √x x^{12/l}`
  have hP : ((N : ℝ) + 1) ^ β ≤ 4 * (Real.sqrt x * Real.exp (24 * u / v)) := by
    have h1 : ((N : ℝ) + 1) ^ β ≤ (2 * x) ^ β :=
      Real.rpow_le_rpow (by positivity) (by linarith) hβ0
    have h2 : (2 * x) ^ β = 2 ^ β * x ^ β := Real.mul_rpow (by norm_num) hx0.le
    have h3 : (2 : ℝ) ^ β ≤ 4 := by
      calc (2 : ℝ) ^ β ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ2
        _ = 4 := by norm_num
    have h4 : x ^ β = Real.sqrt x * Real.exp (24 * u / v) := by
      rw [hβ, Real.rpow_add hx0, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0 (12 / l), hl]
      congr 2; rw [← hudef]; field_simp; ring
    rw [h4] at h2
    calc ((N : ℝ) + 1) ^ β ≤ 2 ^ β * (Real.sqrt x * Real.exp (24 * u / v)) := h1.trans h2.le
      _ ≤ 4 * (Real.sqrt x * Real.exp (24 * u / v)) := by gcongr
  -- `32 l e^{A(l²e^l+1)} ≤ exp(u/v)`
  have hEl : Real.exp l = u ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hu0, hl, hvdef]; ring_nf
  have hl2v : l ^ 2 ≤ v ^ 2 := by rw [hl]; nlinarith
  have hsq0 : 0 ≤ u ^ (1 / 2 : ℝ) := Real.rpow_nonneg hu0.le _
  have h32 : 32 * l ≤ Real.exp (4 + l) := by
    rw [Real.exp_add]
    have e4 : (32 : ℝ) ≤ Real.exp 4 := by
      have := Real.exp_one_gt_d9
      have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]
      have h27 : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      norm_num at h27 ⊢; linarith
    have el : l ≤ Real.exp l := by linarith [Real.add_one_le_exp l]
    nlinarith [Real.exp_pos l]
  have hlle : l ≤ l ^ 2 * Real.exp l := by
    have := Real.one_le_exp hl0.le
    nlinarith
  have hexpo : 4 + l + A * (l ^ 2 * Real.exp l + 1) ≤ u / v := by
    have e1 : 4 + l + A * (l ^ 2 * Real.exp l + 1) ≤
        (A + 1) * (l ^ 2 * Real.exp l + 1) + 4 := by nlinarith
    have e2 : (A + 1) * (l ^ 2 * Real.exp l + 1) ≤ (A + 1) * (v ^ 2 * u ^ (1 / 2 : ℝ) + 1) := by
      rw [hEl]; gcongr
    linarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc 8 * l * Real.exp (A * (l ^ 2 * Real.exp l + 1)) * ((N : ℝ) + 1) ^ β
      ≤ 8 * l * Real.exp (A * (l ^ 2 * Real.exp l + 1)) *
          (4 * (Real.sqrt x * Real.exp (24 * u / v))) := by gcongr
    _ = Real.sqrt x * ((32 * l) * Real.exp (A * (l ^ 2 * Real.exp l + 1)) *
          Real.exp (24 * u / v)) := by ring
    _ ≤ Real.sqrt x * (Real.exp (4 + l) * Real.exp (A * (l ^ 2 * Real.exp l + 1)) *
          Real.exp (24 * u / v)) := by gcongr
    _ = Real.sqrt x * Real.exp (4 + l + A * (l ^ 2 * Real.exp l + 1) + 24 * u / v) := by
          rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.sqrt x * Real.exp (25 * Real.log x / Real.log (Real.log x)) := by
          gcongr
          rw [← hudef, ← hvdef]
          have : 25 * u / v = u / v + 24 * u / v := by ring
          linarith

end Mertens
