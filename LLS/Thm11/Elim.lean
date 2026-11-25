import LLS.Thm11.Budget

/-!
# Eliminating `ω(q)` and `σ(q)` from the budget

The budget `Φ = base0(x) + 2K max(0, Pc − σ) − κ L − ω m − R` of `LLS.Thm11.budget11` depends on
`q` through `L = log q`, `ω = ω(q)` and `σ = σ(q)`; the point `x = ⌊(L + B(q))²⌋` depends on the
same three numbers through LLS's `B(q)`. Write `ν = √x + 1/(2√x) ≥ √(x + 1) > L + B(q)`,
`u = 2ω (log L)²/L` and `a = 2 log L − 8/5`.

* If `σ ≤ a` then `L + 6.2 − 2 log L + 2σ + u < ν`; as `ω m ≤ K u` the costs `2Kσ + ω m` are at
  most `K(ν − L − 6.2 + 2 log L)`, which leaves `H₁(L)`, decreasing in `L`, so `Φ ≥ F₁(x) = H₁(ν)`.
* If `σ > a` then `A(q) = 0`, `L + 3 + 2 log L + u < ν`, and with `μ = 2mν/(log x)²`,
  `ω m ≤ μ u`, which leaves `H₂(L) = base0 − R − μ(ν − 3) + (μ − κ)L + 2μ log L`, concave in
  `L` on `[8, ν − 3 − 2 log 8]`, so `Φ ≥ min(F₂(x, 8), F₂(x, ν − 3 − 2 log 8))`.

`ω m ≤ μ u` is `L/(log L)² ≤ ν/(log ν)²` (`t/(log t)²` increases on `t ≥ e²`) and
`log ν ≥ ½ log x`.
-/

namespace LLS.Thm11

open Real

/-- `ν(x) = √x + 1/(2√x)`. -/
noncomputable def nu (x : ℝ) : ℝ := √x + 1 / (2 * √x)

/-- `μ(x) = 2 m(x) ν(x)/(log x)²`. -/
noncomputable def muB (x : ℝ) : ℝ := 2 * mC x * nu x / Real.log x ^ 2

/-- The bound in the case `σ ≤ a`. -/
noncomputable def F1 (x : ℝ) : ℝ :=
  base0 x + 2 * Kc x * PcF x - RC x + 6.2 * Kc x - kap x * nu x - 2 * Kc x * Real.log (nu x)

/-- The bound in the case `σ > a`, as a function of `L`. -/
noncomputable def F2 (x L : ℝ) : ℝ :=
  base0 x - RC x - muB x * (nu x - 3) + (muB x - kap x) * L + 2 * muB x * Real.log L

/-- LLS's `B`, as a function of `L = log q`, `ω` and `σ`. -/
noncomputable def Bf (L ω σ : ℝ) : ℝ :=
  max 0 (2 * Real.log L + 3 + 2 * ω * Real.log L ^ 2 / L
    - 2 * max 0 (2 * Real.log L - 8 / 5 - σ))

/-- `log t / √t` decreases on `t ≥ e²`. -/
lemma log_div_sqrt_anti {a b : ℝ} (ha : 8 ≤ a) (hab : a ≤ b) :
    Real.log b / √b ≤ Real.log a / √a := by
  have he : Real.exp 1 ≤ √a := by
    have := Real.exp_one_lt_d9
    have : (2.75 : ℝ) ≤ √a := by
      rw [show (2.75 : ℝ) = √(2.75 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hsab : √a ≤ √b := Real.sqrt_le_sqrt hab
  have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hsab)) hsab
  have hla : Real.log a = 2 * Real.log √a := by
    rw [Real.log_sqrt (by linarith)]; ring
  have hlb : Real.log b = 2 * Real.log √b := by
    rw [Real.log_sqrt (by linarith)]; ring
  simp only at h
  rw [hla, hlb, mul_div_assoc, mul_div_assoc]
  linarith

/-- `t/(log t)²` increases on `t ≥ 8`: `a (log b)² ≤ b (log a)²`. -/
lemma mul_log_sq_le {a b : ℝ} (ha : 8 ≤ a) (hab : a ≤ b) :
    a * Real.log b ^ 2 ≤ b * Real.log a ^ 2 := by
  have h := log_div_sqrt_anti ha hab
  have ha0 : 0 < √a := Real.sqrt_pos.2 (by linarith)
  have hb0 : 0 < √b := Real.sqrt_pos.2 (by linarith)
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  rw [div_le_div_iff₀ hb0 ha0] at h
  have h0 : 0 ≤ Real.log b * √a := by positivity
  have hsq := pow_le_pow_left₀ h0 h 2
  have e1 : (Real.log b * √a) ^ 2 = a * Real.log b ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
  have e2 : (Real.log a * √b) ^ 2 = b * Real.log a ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
  linarith

lemma sqrt_succ_le_nu {x : ℝ} (hx : 1 ≤ x) : √(x + 1) ≤ nu x := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hsq : √x ^ 2 = x := Real.sq_sqrt (by linarith)
  unfold nu
  rw [Real.sqrt_le_left (by positivity)]
  have : (√x + 1 / (2 * √x)) ^ 2 = √x ^ 2 + 1 + 1 / (4 * √x ^ 2) := by
    field_simp; ring
  rw [hsq] at this
  rw [this]
  have : 0 ≤ 1 / (4 * x) := by positivity
  linarith

lemma fin1 (b R K κ P M σ ω m ν L ll lν : ℝ)
    (h1 : 0 < b + 2 * K * P - R + 6.2 * K - κ * ν - 2 * K * lν)
    (hm : 2 * K * (P - σ) ≤ 2 * K * M) (hc : 2 * K * σ + ω * m ≤ K * (ν - L - 6.2 + 2 * ll))
    (hmono : (κ - K) * (ν - L) + 2 * K * (lν - ll) ≥ 0) :
    0 < b + 2 * K * M - κ * L - ω * m - R := by
  nlinarith

lemma fin2 (b R μ ν κ L ll K M ω m : ℝ)
    (h2 : 0 < b - R - μ * (ν - 3) + (μ - κ) * L + 2 * μ * ll) (hm : 0 ≤ 2 * K * M)
    (hc : ω * m ≤ μ * (ν - L - 3 - 2 * ll)) :
    0 < b + 2 * K * M - κ * L - ω * m - R := by
  nlinarith

/-- **The elimination.** -/
theorem phi_pos (x : ℕ) (hx : 64 ≤ x) (L σ ω : ℝ) (hL : 8 ≤ L) (hω : 0 ≤ ω)
    (hB : L + Bf L ω σ < √((x : ℝ) + 1)) (h1 : 0 < F1 x)
    (h2 : 8 ≤ nu x - 3 - 2 * Real.log 8 → 0 < F2 x 8 ∧ 0 < F2 x (nu x - 3 - 2 * Real.log 8)) :
    0 < base0 x + 2 * Kc x * max 0 (PcF x - σ) - kap x * L - ω * mC x - RC x := by
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx
  set s := √(x : ℝ) with hs_def
  set l := Real.log (x : ℝ) with hl_def
  have hs8 : 8 ≤ s := sqrt_ge_eight hxR
  have hl4 : 4 ≤ l := log_ge_four hxR
  have hK0 := Kc_pos hxR
  have hKx := Kc_div_le hxR
  have hden := den_pos hxR
  set ν := nu x with hν
  have hνs : ν = s + 1 / (2 * s) := rfl
  have hνB : L + Bf L ω σ < ν := lt_of_lt_of_le hB (sqrt_succ_le_nu (by linarith))
  have hB0 : 0 ≤ Bf L ω σ := le_max_left _ _
  have hLν : L ≤ ν := by linarith
  have hν0 : 0 < ν := by linarith
  have hlν : l / 2 ≤ Real.log ν := by
    have : l / 2 = Real.log s := by
      rw [hl_def, hs_def, Real.log_sqrt (by linarith)]
    rw [this]
    have : 0 < 1 / (2 * s) := by positivity
    exact Real.log_le_log (by linarith) (by rw [hνs]; linarith)
  -- `K ≥ ν`
  have hKν : ν ≤ Kc x := by
    have hd1 : 1 + 1 / (x : ℝ) - 2 / s ≤ 1 := by
      have : 1 / (x : ℝ) ≤ 2 / s := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        have : s ≤ x := by
          have := Real.sqrt_le_sqrt (show (x : ℝ) ≤ x ^ 2 by nlinarith)
          rwa [Real.sqrt_sq (by linarith)] at this
        linarith
      linarith
    have : s + 1 + l / 2 ≤ Kc x := by
      unfold Kc
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have : 1 / (2 * s) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  set m := mC x
  set μ := muB x
  have hm0 : 0 ≤ m := by unfold m mC; positivity
  have hμ0 : 0 ≤ μ := by unfold μ muB; positivity
  have hμν : μ ≤ ν := by
    unfold μ muB mC
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    rw [div_le_iff₀ (by positivity)]
    have : (l - Real.log 2 / 2) ^ 2 ≤ l ^ 2 := by nlinarith
    nlinarith
  have hμK : μ ≤ Kc x := hμν.trans hKν
  -- `ω m ≤ μ u`
  set ll := Real.log L
  have hll : Real.log 8 ≤ ll := Real.log_le_log (by norm_num) hL
  have hll0 : 0 < ll := lt_of_lt_of_le (Real.log_pos (by norm_num)) hll
  set u := 2 * ω * ll ^ 2 / L
  have hu0 : 0 ≤ u := by positivity
  have hωm : ω * m ≤ μ * u := by
    have hmono := mul_log_sq_le hL hLν
    -- `L / ll² ≤ ν / (log ν)² ≤ ν/(l/2)²`
    have hlν2 : (l / 2) ^ 2 ≤ Real.log ν ^ 2 := pow_le_pow_left₀ (by linarith) hlν 2
    have key : m * L ≤ μ * (2 * ll ^ 2) := by
      unfold μ muB
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      -- `m L l² ≤ 2 m ν · 2 ll²`
      have h3 : L * l ^ 2 ≤ 4 * ν * ll ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 hm0]
    have : ω * (m * L) ≤ ω * (μ * (2 * ll ^ 2)) := mul_le_mul_of_nonneg_left key hω
    unfold u
    rw [le_div_iff₀ (by linarith)] at *
    calc ω * m = ω * (m * L) / L := by field_simp
      _ ≤ ω * (μ * (2 * ll ^ 2)) / L := by gcongr
      _ = μ * (2 * ω * ll ^ 2 / L) := by ring
  have hκK : Kc x ≤ kap x := by
    unfold kap
    have : Kc x * (1 - 1 / x) = Kc x - Kc x / x := by ring
    linarith
  set a := 2 * ll - 8 / 5 with ha
  have hinner : 2 * ll + 3 + u - 2 * max 0 (a - σ) ≤ Bf L ω σ := by
    unfold Bf; exact le_max_right _ _
  by_cases hσa : σ ≤ a
  · -- the case `A(q) = a − σ`
    have hmx : max 0 (a - σ) = a - σ := max_eq_right (by linarith)
    rw [hmx] at hinner
    have hc : 2 * σ + u ≤ ν - L - 6.2 + 2 * ll := by linarith
    have hmax : PcF x - σ ≤ max 0 (PcF x - σ) := le_max_right _ _
    have hcost : 2 * Kc x * σ + ω * m ≤ Kc x * (ν - L - 6.2 + 2 * ll) := by
      have : μ * u ≤ Kc x * u := mul_le_mul_of_nonneg_right hμK hu0
      nlinarith
    -- `H₁(L) ≥ H₁(ν) = F₁`
    have hlog : ll ≤ Real.log ν := Real.log_le_log (by linarith) hLν
    have hmono : (kap x - Kc x) * (ν - L) + 2 * Kc x * (Real.log ν - ll) ≥ 0 := by
      have := mul_nonneg (by linarith : 0 ≤ kap x - Kc x) (by linarith : 0 ≤ ν - L)
      have := mul_nonneg (by linarith : 0 ≤ 2 * Kc x) (by linarith : 0 ≤ Real.log ν - ll)
      linarith
    have hF1 : F1 x = base0 x + 2 * Kc x * PcF x - RC x + 6.2 * Kc x - kap x * ν
        - 2 * Kc x * Real.log ν := rfl
    rw [hF1] at h1
    have hm1 := mul_le_mul_of_nonneg_left hmax (mul_nonneg zero_le_two hK0.le)
    exact fin1 _ _ _ _ _ _ _ _ _ _ _ _ _ h1 hm1 hcost hmono
  · -- the case `A(q) = 0`
    push Not at hσa
    have hmx : max 0 (a - σ) = 0 := max_eq_left (by linarith)
    rw [hmx] at hinner
    have hc : u ≤ ν - L - 3 - 2 * ll := by linarith
    set M := ν - 3 - 2 * Real.log 8
    have hLM : L ≤ M := by linarith
    obtain ⟨hF8, hFM⟩ := h2 (hL.trans hLM)
    have hmax : 0 ≤ max 0 (PcF x - σ) := le_max_left _ _
    have hcost : ω * m ≤ μ * (ν - L - 3 - 2 * ll) := hωm.trans (mul_le_mul_of_nonneg_left hc hμ0)
    have e : ∀ y, F2 x y = (base0 x - RC x - μ * (ν - 3)) + (μ - kap x) * y
        + 2 * μ * Real.log y := fun y => by unfold F2; rfl
    -- concavity in `L`
    have hF2 : 0 < F2 x L := by
      rcases eq_or_lt_of_le hL with h8 | h8
      · rw [← h8]; exact hF8
      have hM8 : 8 < M := lt_of_lt_of_le h8 hLM
      set θ := (M - L) / (M - 8)
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
      have hθ1 : θ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hLθ : L = θ * 8 + (1 - θ) * M := by
        simp only [θ]; field_simp; ring
      have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show M ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith) hθ0 (by linarith : 0 ≤ 1 - θ)
        (by ring)
      simp only [smul_eq_mul] at hconc
      rw [← hLθ] at hconc
      have hconv : θ * F2 x 8 + (1 - θ) * F2 x M ≤ F2 x L := by
        rw [e 8, e M, e L]
        have h2μ := mul_le_mul_of_nonneg_left hconc (by linarith : (0 : ℝ) ≤ 2 * μ)
        have hL' : (μ - kap x) * L = θ * ((μ - kap x) * 8) + (1 - θ) * ((μ - kap x) * M) := by
          rw [hLθ]; ring
        linarith only [h2μ, hL']
      have hpos : 0 < θ * F2 x 8 + (1 - θ) * F2 x M := by
        rcases eq_or_lt_of_le hθ1 with h | h
        · rw [h, sub_self, zero_mul, add_zero, one_mul]; exact hF8
        · have h3 := mul_pos (by linarith : 0 < 1 - θ) hFM
          have h4 := mul_nonneg hθ0 hF8.le
          linarith only [h3, h4]
      exact lt_of_lt_of_le hpos hconv
    rw [e L] at hF2
    have hm2 : 0 ≤ 2 * Kc x * max 0 (PcF x - σ) := mul_nonneg (mul_nonneg zero_le_two hK0.le) hmax
    exact fin2 _ _ _ _ _ _ _ _ _ _ _ hF2 hm2 hcost

end LLS.Thm11
