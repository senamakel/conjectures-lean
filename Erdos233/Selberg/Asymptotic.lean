import Erdos233.Selberg.Window
import Erdos233.Statement2

/-!
# Selberg 1943, asymptotic form: `π(x + h) − π(x) ~ h / log x` for almost all `x`, under RH

1. `pi_window_of_psi`: from `|ψ(y(1+δ)) − ψ(y) − δy| ≤ 3κδy` to
   `(1−6κ) δy/log y ≤ π(y(1+δ)) − π(y) ≤ (1+3κ) δy/log y`, through `θ` (the proper prime
   powers cost `≤ 2κδy`, `psi_sub_theta_window`) and `log p ∈ [log y, log y + δ]`.
2. `pi_window_measure`: for `δ ∈ [K₀ log² X / X, κ/2]` the `y ∈ [X, 2X]` where step 1 fails have
   measure `≤ C log² X / δ` (`waves_measure`, `psi_window_of_waves`).
3. `selberg_asymptotic_of_RH`: the variable `h` is handled by a geometric grid
   `δ_j = δ₀(1+η)^j`, `δ₀ = K log² X / (2X)`. Each `x ∈ [X, 2X]` has a `j` with
   `δ_j x ≤ h(x) < δ_{j+1} x`; if both `δ_j` and `δ_{j+1}` behave at `x`, monotonicity of `π`
   sandwiches `π(x + h(x)) − π(x)` within a factor `1 ± ε` of `h(x)/log x`. The exceptional
   measure is `≤ Σ_j C log² X / δ_j ≤ C log² X (1+η)/(η δ₀) = 2C(1+η) X/(ηK)`, a geometric
   series, and `K → ∞`. Neither the monotonicity of `h` nor any regularity of `h` on `[X, 2X]`
   is used: `h(x) ≥ K log² x` and `h(x) ≤ ε₀ x` for large `x` suffice.
-/

namespace Erdos233

open Complex Erdos985.Analytic MeasureTheory Chebyshev ArithmeticFunction Filter Topology Finset

lemma prime_window_sums {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    θ B - θ A = ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, Real.log p ∧
    ((Nat.primeCounting ⌊B⌋₊ : ℝ) - Nat.primeCounting ⌊A⌋₊)
      = ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, (1 : ℝ) := by
  have hfl : ⌊A⌋₊ ≤ ⌊B⌋₊ := Nat.floor_le_floor hAB
  constructor
  · have hsplit : θ B = θ A + ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, Real.log p := by
      simp only [theta, sum_filter]
      rw [sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
    rw [hsplit]; ring
  · have key : ∀ n : ℕ, (Nat.primeCounting n : ℝ)
        = ∑ p ∈ Ioc 0 n, if p.Prime then (1 : ℝ) else 0 := by
      intro n
      rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Ioc_zero, card_filter]
      push_cast
      rfl
    rw [key, key, ← sum_Ioc_consecutive _ (Nat.zero_le _) hfl, sum_filter]
    ring

lemma psi_sub_theta_mono {A B : ℝ} (hAB : A ≤ B) : ψ A - θ A ≤ ψ B - θ B := by
  rw [psi_sub_theta_eq_sum_not_prime, psi_sub_theta_eq_sum_not_prime]
  exact sum_le_sum_of_subset_of_nonneg
    (filter_subset_filter _ (Ioc_subset_Ioc_right (Nat.floor_le_floor hAB)))
    (fun n _ _ => vonMangoldt_nonneg)

/-- Step 1: from `ψ` to `π` on `(y, y(1+δ)]`. -/
lemma pi_window_of_psi {y δ κ : ℝ} (hy : 3 ≤ y) (hκ : 0 < κ) (hκ8 : κ ≤ 1 / 8) (hδ : 0 < δ)
    (hδκ : δ ≤ κ / 2) (hψ : |ψ (y * (1 + δ)) - ψ y - δ * y| ≤ 3 * κ * δ * y)
    (hL1 : Real.log (2 * y) ^ 2 / Real.log 2 ≤ κ * Real.sqrt y)
    (hL2 : Real.log (2 * y) ^ 2 / Real.log 2 ≤ κ * δ * y) :
    (1 - 6 * κ) * δ * y / Real.log y
        ≤ (Nat.primeCounting ⌊y * (1 + δ)⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊ ∧
      (Nat.primeCounting ⌊y * (1 + δ)⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊
        ≤ (1 + 3 * κ) * δ * y / Real.log y := by
  have hy0 : 0 < y := by linarith
  have hly : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; have := Real.exp_one_lt_d9; linarith
  set B := y * (1 + δ) with hB
  have hyB : y ≤ B := by rw [hB]; nlinarith
  have hB2 : B ≤ 2 * y := by rw [hB]; nlinarith
  obtain ⟨hθ, hπ⟩ := prime_window_sums (by linarith : (1 : ℝ) ≤ y) hyB
  set S := (Ioc ⌊y⌋₊ ⌊B⌋₊).filter Nat.Prime with hS
  set S1 := ∑ p ∈ S, (1 : ℝ) with hS1
  have hS10 : 0 ≤ S1 := sum_nonneg fun _ _ => zero_le_one
  have hmem : ∀ p ∈ S, y < p ∧ (p : ℝ) ≤ B := by
    intro p hp
    rw [hS, mem_filter, mem_Ioc] at hp
    exact ⟨(Nat.floor_lt hy0.le).1 hp.1.1, (Nat.le_floor_iff (by linarith)).1 hp.1.2⟩
  have hlo : Real.log y * S1 ≤ θ B - θ y := by
    rw [hθ, hS1, mul_sum, mul_one]
    exact sum_le_sum fun p hp => Real.log_le_log hy0 (hmem p hp).1.le
  have hlB : Real.log B ≤ Real.log y + δ := by
    rw [hB, Real.log_mul hy0.ne' (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + δ by linarith)
    linarith
  have hhi : θ B - θ y ≤ (Real.log y + δ) * S1 := by
    rw [hθ, hS1, mul_sum, mul_one]
    exact sum_le_sum fun p hp => (Real.log_le_log (by linarith [(hmem p hp).1]) (hmem p hp).2).trans hlB
  have hψθ : θ B - θ y ≤ ψ B - ψ y := by linarith [psi_sub_theta_mono hyB]
  -- proper prime powers
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpp := psi_sub_theta_window (A := y) (B := B) (by linarith) hyB
  have hlB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hlB2 : Real.log B ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hB2
  set Lx := Real.log (2 * y) ^ 2 / Real.log 2 with hLx
  have hsy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hBA : (B - y) / Real.sqrt y = δ * Real.sqrt y := by
    rw [hB, div_eq_iff hsy0.ne']; nlinarith
  have hpp2 : (ψ B - θ B) - (ψ y - θ y) ≤ 2 * κ * δ * y := by
    refine hpp.trans ?_
    rw [hBA]
    have h1 : Real.log B / Real.log 2 * Real.log B ≤ Lx := by
      rw [hLx, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2, sq]
      exact mul_le_mul hlB2 hlB2 hlB0 (hlB0.trans hlB2)
    have h0 : 0 ≤ δ * Real.sqrt y + 1 := by positivity
    calc Real.log B / Real.log 2 * Real.log B * (δ * Real.sqrt y + 1)
        ≤ Lx * (δ * Real.sqrt y + 1) := mul_le_mul_of_nonneg_right h1 h0
      _ = Lx * δ * Real.sqrt y + Lx := by ring
      _ ≤ κ * Real.sqrt y * δ * Real.sqrt y + κ * δ * y := by
          have := mul_le_mul_of_nonneg_right hL1 (by positivity : 0 ≤ δ * Real.sqrt y)
          nlinarith
      _ = 2 * κ * δ * y := by
          have : κ * Real.sqrt y * δ * Real.sqrt y = κ * δ * (Real.sqrt y * Real.sqrt y) := by ring
          rw [this, hsy]; ring
  have hψ' := abs_le.1 hψ
  have hly0 : 0 < Real.log y := by linarith
  rw [hπ]
  constructor
  · rw [div_le_iff₀ hly0]
    have hup : Real.log y * S1 ≤ (1 + 3 * κ) * δ * y := by linarith
    have hκdy : κ * (δ * y) ≤ 1 / 8 * (δ * y) := mul_le_mul_of_nonneg_right hκ8 (by positivity)
    have hS1le : S1 ≤ 2 * δ * y := by
      have : S1 ≤ Real.log y * S1 := le_mul_of_one_le_left hS10 hly
      linarith
    have hθlo : (1 - 5 * κ) * δ * y ≤ θ B - θ y := by linarith
    have : δ * S1 ≤ κ * δ * y := by
      have h1 : δ * S1 ≤ δ * (2 * δ * y) := mul_le_mul_of_nonneg_left hS1le hδ.le
      have h2 : 2 * δ * (δ * y) ≤ κ * (δ * y) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    linarith
  · rw [le_div_iff₀ hly0]
    linarith

/-- The `y ∈ [X, 2X]` at which `π(y(1+δ)) − π(y)` is not within `[1−6κ, 1+3κ]` times
`δy / log y`. -/
def piBad (κ δ X : ℝ) : Set ℝ :=
  {y : ℝ | y ∈ Set.Icc X (2 * X) ∧ ¬ ((1 - 6 * κ) * δ * y / Real.log y
        ≤ (Nat.primeCounting ⌊y * (1 + δ)⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊ ∧
      (Nat.primeCounting ⌊y * (1 + δ)⌋₊ : ℝ) - Nat.primeCounting ⌊y⌋₊
        ≤ (1 + 3 * κ) * δ * y / Real.log y)}

/-- Step 2. -/
theorem pi_window_measure (hRH : RiemannHypothesis) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ ≤ 1 / 8) :
    ∃ C K₀ X₀ : ℝ, 0 < C ∧ 0 < K₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ δ : ℝ,
      K₀ * Real.log X ^ 2 / X ≤ δ → δ ≤ κ / 2 →
      volume.real (piBad κ δ X) ≤ C * Real.log X ^ 2 / δ := by
  obtain ⟨C, hC, hW⟩ := waves_measure hRH
  obtain ⟨X₁, hX₁⟩ := eventually_log_sq_le_c_sqrt hκ
  refine ⟨C / κ ^ 2, 30 / κ, max X₁ 5, by positivity, by positivity, fun X hX δ hδ1 hδ2 => ?_⟩
  have hX5 : 5 ≤ X := le_of_max_le_right hX
  have hX0 : 0 < X := by linarith
  have hlX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; have := Real.exp_one_lt_d9; linarith
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hδX : 30 / κ * Real.log X ^ 2 ≤ δ * X := by rwa [div_le_iff₀ hX0] at hδ1
  have hδ0 : 0 < δ := by
    have : 0 < 30 / κ * Real.log X ^ 2 := by positivity
    nlinarith
  have hκδX : 30 * Real.log X ^ 2 ≤ κ * δ * X := by
    have := mul_le_mul_of_nonneg_left hδX hκ.le
    have e : κ * (30 / κ * Real.log X ^ 2) = 30 * Real.log X ^ 2 := by field_simp
    nlinarith
  have hlX2 : 1 ≤ Real.log X ^ 2 := by nlinarith
  have hXδ : 1 / X ≤ δ := by
    rw [div_le_iff₀ hX0]; nlinarith
  have h3 : 3 ≤ κ ^ 2 * δ ^ 2 * X ^ 2 := by nlinarith
  have hsub : piBad κ δ X ⊆ {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      (κ * (κ * δ) * δ * X ^ 2 ≤ y ^ (3 / 2 : ℝ) * ‖TW (1 - κ * δ) (κ * δ) (δ + κ * δ) (Real.log y)‖ ∨
       κ * (κ * δ) * δ * X ^ 2 ≤ y ^ (3 / 2 : ℝ) * ‖TW 1 (κ * δ) (δ - κ * δ) (Real.log y)‖)} := by
    rintro y ⟨hy, hbad⟩
    refine ⟨hy, ?_⟩
    by_contra hw
    push_neg at hw
    apply hbad
    have hyX := hy.1
    have hy0 : 0 < y := by linarith
    have hψ := psi_window_of_waves hRH (by linarith) hyX hκ hκ8 hδ0 (by linarith) h3 hw.1 hw.2
    refine pi_window_of_psi (by linarith) hκ hκ8 hδ0 hδ2 hψ ?_ ?_
    · refine le_trans ?_ (hX₁ y (le_trans (le_max_left _ _) (hX.trans hyX)))
      have h1 : Real.log (2 * y) ≤ Real.log (5 * y) := Real.log_le_log (by linarith) (by linarith)
      have h0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
      gcongr
    · have h4 : Real.log (2 * y) ≤ 2 * Real.log X := by
        calc Real.log (2 * y) ≤ Real.log (X ^ 2) :=
              Real.log_le_log (by linarith) (by nlinarith [hy.2])
          _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
      have h0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
      have hsq : Real.log (2 * y) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
      rw [div_le_iff₀ (by linarith)]
      have : κ * δ * X ≤ κ * δ * y := mul_le_mul_of_nonneg_left hyX (by positivity)
      nlinarith
  have hfin : volume {y : ℝ | y ∈ Set.Icc X (2 * X) ∧
      (κ * (κ * δ) * δ * X ^ 2 ≤ y ^ (3 / 2 : ℝ) * ‖TW (1 - κ * δ) (κ * δ) (δ + κ * δ) (Real.log y)‖ ∨
       κ * (κ * δ) * δ * X ^ 2 ≤ y ^ (3 / 2 : ℝ) * ‖TW 1 (κ * δ) (δ - κ * δ) (Real.log y)‖)} ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 2 * X)).ne
      (measure_mono fun y hy => hy.1)
  refine (measureReal_mono hsub hfin).trans ((hW X (by linarith) δ κ hκ hκ8 hδ0 (by linarith)
    hXδ).trans (le_of_eq ?_))
  field_simp

/-- The sandwich of step 3, as real arithmetic. -/
lemma sandwich {ε' κ η g x hx lx P : ℝ} (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1) (hκ : κ = ε' / 8)
    (hη : η = ε' / 8) (hg : 0 < g) (hx0 : 0 < x) (hlx : 0 < lx) (h1 : g * x ≤ hx)
    (h2 : hx < (1 + η) * g * x) (hlo : (1 - 6 * κ) * g * x ≤ P * lx)
    (hup : P * lx ≤ (1 + 3 * κ) * ((1 + η) * g) * x) :
    |P - hx / lx| ≤ ε' * (hx / lx) := by
  subst hκ hη
  have hgx : 0 < g * x := mul_pos hg hx0
  have hhx0 : 0 < hx := lt_of_lt_of_le hgx h1
  have hupper : P * lx ≤ (1 + ε') * hx := by
    have e : (1 + 3 * (ε' / 8)) * ((1 + ε' / 8) * g) * x
        = (1 + 3 * (ε' / 8)) * (1 + ε' / 8) * (g * x) := by ring
    have hc : (1 + 3 * (ε' / 8)) * (1 + ε' / 8) ≤ 1 + ε' := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (1 + 3 * (ε' / 8)) * (1 + ε' / 8))
    have h4 := mul_le_mul_of_nonneg_right hc hhx0.le
    linarith
  have hlower : (1 - ε') * hx ≤ P * lx := by
    have hle : hx ≤ (1 + ε' / 8) * (g * x) := by linarith [show (1 + ε' / 8) * g * x = (1 + ε' / 8) * (g * x) by ring]
    have h3 : (1 - ε') * hx ≤ (1 - ε') * ((1 + ε' / 8) * (g * x)) :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    have hc : (1 - ε') * (1 + ε' / 8) ≤ 1 - 6 * (ε' / 8) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_right hc hgx.le
    have e : (1 - ε') * ((1 + ε' / 8) * (g * x)) = (1 - ε') * (1 + ε' / 8) * (g * x) := by ring
    have e2 : (1 - 6 * (ε' / 8)) * g * x = (1 - 6 * (ε' / 8)) * (g * x) := by ring
    linarith
  rw [abs_le]
  constructor
  · have : (1 - ε') * (hx / lx) ≤ P := by
      rw [← div_le_iff₀ hlx] at hlower
      have e2 : (1 - ε') * hx / lx = (1 - ε') * (hx / lx) := by ring
      linarith
    linarith
  · have : P ≤ (1 + ε') * (hx / lx) := by
      rw [← le_div_iff₀ hlx] at hupper
      have e2 : (1 + ε') * hx / lx = (1 + ε') * (hx / lx) := by ring
      linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- **Selberg 1943 (asymptotic form), under RH.** -/
theorem selberg_asymptotic_of_RH (hRH : RiemannHypothesis) : SelbergAsymptoticStatement := by
  intro h _hmono hh hhx ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set κ := ε' / 8 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ8 : κ ≤ 1 / 8 := by rw [hκ]; linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε' / 8 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨C, K₀, X₀, hC, hK₀, hA⟩ := pi_window_measure hRH hκ0 hκ8
  rw [Metric.tendsto_atTop]
  intro τ hτ
  set K : ℝ := max (2 * K₀) (4 * C * (1 + η) / (η * τ) + 1) with hK
  have hK1 : 2 * K₀ ≤ K := le_max_left _ _
  have hK2 : 4 * C * (1 + η) / (η * τ) + 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  set ε₀ := κ / 2 / (1 + η) with hε₀
  have hε₀0 : 0 < ε₀ := div_pos (by positivity) (by linarith)
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.1 (hh.eventually_ge_atTop K)
  obtain ⟨Y₂, hY₂⟩ := eventually_atTop.1 (hhx.eventually (Iio_mem_nhds hε₀0))
  refine ⟨max (max X₀ 5) (max Y₁ Y₂), fun X hX => ?_⟩
  have hX5 : 5 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXY₁ : Y₁ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXY₂ : Y₂ ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  have hlX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; have := Real.exp_one_lt_d9; linarith
  set δ₀ := K * Real.log X ^ 2 / (2 * X) with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  have hη1 : 1 < 1 + η := by linarith
  -- the window ratios of `h` on `[X, 2X]`
  have hratio : ∀ x ∈ Set.Icc X (2 * X), δ₀ ≤ h x / x ∧ h x / x < ε₀ := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hlx : Real.log X ≤ Real.log x := Real.log_le_log hX0 hx.1
    have hlx0 : 0 < Real.log x := by linarith
    constructor
    · have := hY₁ x (hXY₁.trans hx.1)
      rw [le_div_iff₀ (by positivity)] at this
      rw [hδ₀, div_le_div_iff₀ (by positivity) hx0]
      have h1 : K * Real.log X ^ 2 ≤ K * Real.log x ^ 2 := by gcongr
      have h2 : 0 ≤ K * Real.log X ^ 2 := by positivity
      nlinarith [hx.2]
    · exact hY₂ x (hXY₂.trans hx.1)
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (ε₀ / δ₀) hη1
  set grid : ℕ → ℝ := fun j => δ₀ * (1 + η) ^ j with hgrid
  set I := (range (J + 1)).filter (fun j => grid j ≤ κ / 2) with hI
  -- every bad point is bad for a grid ratio
  have hcover : selbergBadSet h ε X ⊆ ⋃ j ∈ I, piBad κ (grid j) X := by
    rintro x ⟨hx, hbad⟩
    obtain ⟨hr1, hr2⟩ := hratio x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hr : 1 ≤ h x / x / δ₀ := by rw [le_div_iff₀ hδ₀0]; linarith
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hr hη1
    have hjJ : j < J := by
      have : (1 + η) ^ j < (1 + η) ^ J := by
        refine lt_of_le_of_lt hj1 (lt_of_le_of_lt ?_ hJ)
        exact div_le_div_of_nonneg_right hr2.le hδ₀0.le
      exact (pow_lt_pow_iff_right₀ hη1).1 this
    have hgj : grid j ≤ h x / x := by
      simp only [hgrid]; rw [le_div_iff₀ hδ₀0] at hj1; linarith
    have hgj1 : h x / x < grid (j + 1) := by
      simp only [hgrid]; rw [div_lt_iff₀ hδ₀0] at hj2; linarith
    have hgs : grid (j + 1) = (1 + η) * grid j := by simp only [hgrid]; ring
    have hgj0 : 0 < grid j := by simp only [hgrid]; positivity
    have hgk : grid (j + 1) ≤ κ / 2 := by
      rw [hgs]
      have : (1 + η) * (h x / x) ≤ (1 + η) * ε₀ := by gcongr
      have e : (1 + η) * ε₀ = κ / 2 := by rw [hε₀]; field_simp
      nlinarith
    have hgk' : grid j ≤ κ / 2 := by nlinarith
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    have hn1 := hnot j (by rw [hI, mem_filter, mem_range]; exact ⟨by omega, hgk'⟩)
    have hn2 := hnot (j + 1) (by rw [hI, mem_filter, mem_range]; exact ⟨by omega, hgk⟩)
    simp only [piBad, Set.mem_ofPred_eq] at hn1 hn2
    push_neg at hn1 hn2
    obtain ⟨l1, -⟩ := hn1 hx
    obtain ⟨-, u2⟩ := hn2 hx
    have hlx0 : 0 < Real.log x := by
      have : Real.log X ≤ Real.log x := Real.log_le_log hX0 hx.1
      linarith
    have hhj : grid j * x ≤ h x := by rwa [le_div_iff₀ hx0] at hgj
    have hhj1 : h x < grid (j + 1) * x := by rwa [div_lt_iff₀ hx0] at hgj1
    have hP1 := Nat.cast_le (α := ℝ) |>.2 (Nat.monotone_primeCounting
      (Nat.floor_le_floor (show x * (1 + grid j) ≤ x + h x by linarith [show x * (1 + grid j) = x + grid j * x by ring])))
    have hP2 := Nat.cast_le (α := ℝ) |>.2 (Nat.monotone_primeCounting
      (Nat.floor_le_floor (show x + h x ≤ x * (1 + grid (j + 1)) by linarith [show x * (1 + grid (j + 1)) = x + grid (j + 1) * x by ring])))
    rw [div_le_iff₀ hlx0] at l1
    rw [le_div_iff₀ hlx0] at u2
    rw [hgs] at u2 hhj1 hP2
    have habs := sandwich (P := (Nat.primeCounting ⌊x + h x⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊)
      hε'0 hε'1 hκ hη hgj0 hx0 hlx0 hhj hhj1
      (l1.trans (mul_le_mul_of_nonneg_right (by linarith) hlx0.le))
      ((mul_le_mul_of_nonneg_right (by linarith) hlx0.le).trans u2)
    have : ε' * (h x / Real.log x) ≤ ε * (h x / Real.log x) :=
      mul_le_mul_of_nonneg_right hε'ε (div_nonneg ((mul_pos hgj0 hx0).le.trans hhj) hlx0.le)
    exact (habs.trans this).not_gt hbad
  -- the measure
  have hfin : volume (⋃ j ∈ I, piBad κ (grid j) X) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := X) (b := 2 * X)).ne (measure_mono ?_)
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨j, -, hj⟩ := hy
    exact hj.1
  have hm1 : volume.real (selbergBadSet h ε X)
      ≤ ∑ j ∈ I, volume.real (piBad κ (grid j) X) :=
    (measureReal_mono hcover hfin).trans (measureReal_biUnion_finset_le _ _)
  set r := 1 / (1 + η) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; linarith
  have hm2 : ∑ j ∈ I, volume.real (piBad κ (grid j) X)
      ≤ ∑ j ∈ range (J + 1), C * Real.log X ^ 2 / δ₀ * r ^ j := by
    refine (sum_le_sum fun j hj => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => by positivity)
    rw [hI, mem_filter] at hj
    have hgj0 : δ₀ ≤ grid j := by
      simp only [hgrid]
      exact le_mul_of_one_le_right hδ₀0.le (one_le_pow₀ hη1.le)
    refine (hA X hXX₀ (grid j) ?_ hj.2).trans (le_of_eq ?_)
    · refine le_trans ?_ hgj0
      rw [hδ₀, div_le_div_iff₀ hX0 (by positivity)]
      have := mul_le_mul_of_nonneg_right hK1 (by positivity : 0 ≤ Real.log X ^ 2 * X)
      nlinarith
    · simp only [hgrid, hr, one_div, inv_pow]
      field_simp
  have hgeom : ∑ j ∈ range (J + 1), r ^ j ≤ (1 + η) / η := by
    refine ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _
      (fun j _ => pow_nonneg hr0 j)).trans (le_of_eq ?_)
    rw [tsum_geometric_of_lt_one hr0 hr1, hr]
    field_simp
    ring
  have hm3 : ∑ j ∈ range (J + 1), C * Real.log X ^ 2 / δ₀ * r ^ j
      ≤ C * Real.log X ^ 2 / δ₀ * ((1 + η) / η) := by
    rw [← mul_sum]; gcongr
  have hval : C * Real.log X ^ 2 / δ₀ * ((1 + η) / η) = 2 * C * (1 + η) / (η * K) * X := by
    rw [hδ₀]; field_simp
  have hKτ : 2 * C * (1 + η) / (η * K) < τ := by
    rw [div_lt_iff₀ (by positivity)]
    have : 4 * C * (1 + η) / (η * τ) < K := by linarith
    rw [div_lt_iff₀ (by positivity)] at this
    have : 0 < C * (1 + η) := by positivity
    linarith
  have hnn : 0 ≤ (volume (selbergBadSet h ε X)).toReal / X := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, div_lt_iff₀ hX0]
  have : (volume (selbergBadSet h ε X)).toReal = volume.real (selbergBadSet h ε X) := rfl
  rw [this]
  have := mul_lt_mul_of_pos_right hKτ hX0
  linarith [hm1.trans (hm2.trans hm3)]

end Erdos233
