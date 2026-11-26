import Erdos969.MV.Coeff
import Erdos969.KFree.Main

/-!
# Montgomery–Vaughan: RH implies `E_k(x) = O(x^{1/(k+1)+ε})`

Split `Q_k(N) = ∑_{d ≤ N} μ(d) ⌊N/d^k⌋` at `Y`. Then

    E_k(N) = -∑_{d ≤ Y} μ(d) {N/d^k} + B(N),
    B(N) = ∑_{Y < d ≤ N} μ(d) ⌊N/d^k⌋ - N ∑_{d > Y} μ(d)/d^k.

The first sum is at most `Y`. `B(N) = ∑_{n ≤ N} a(n)` with `a(n) = b(n) - G_Y(k)`, and the
Dirichlet series of `a` is `ζ(s) (G_Y(ks) - G_Y(k))`: subtracting the constant `G_Y(k)` removes
the pole of `ζ` at `s = 1`. Its holomorphic continuation is
`Φ(s) = ζ₁(s) · dslope (G_Y(k ·)) 1 s` with `ζ₁(s) = (s-1)ζ(s)`. On `σ₀ = 1/2 + ε`, under RH,

    ‖ζ(σ₀ + it)‖ ≪ (|t|+2)^ε                 (lindelof-rh's logarithm of ζ),
    ‖G_Y(k(σ₀ + it))‖ ≪ (|t|+2)^ε Y^{β - kσ₀}  (`Erdos969.MV.tail_le`, β = 1/2 + 3ε),

and the Cesàro–Perron bound (`Erdos969.MV.norm_sum_Icc_le`) gives
`|B(N)| ≪ Y^{β-kσ₀} (N+1)^{1/2+5ε}`. With `Y ≍ N^{1/(k+1)}` both terms are
`≪ N^{1/(k+1)+6ε}`.
-/

namespace Erdos969.MV

open Complex Filter Finset Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The continuation of `ζ(s) (G_Y(ks) - G_Y(k))`. -/
noncomputable def Φ (k Y : ℕ) (s : ℂ) : ℂ :=
  riemannZeta₁ s * dslope (fun s => G Y ((k : ℂ) * s)) 1 s

lemma Φ_eq {k Y : ℕ} {s : ℂ} (hs : s ≠ 1) :
    Φ k Y s = riemannZeta s * (G Y ((k : ℂ) * s) - G Y (k : ℂ)) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hz : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ hs1, one_mul]
  rw [Φ, dslope_of_ne _ hs, slope_def_field, hz, mul_one]
  field_simp

theorem differentiableOn_G (hRH : RiemannHypothesis) (Y : ℕ) :
    DifferentiableOn ℂ (G Y) Lindelof.halfPlane := by
  have h1 := Mertens.differentiableOn_invZ hRH
  have h2 : DifferentiableOn ℂ (fun w : ℂ => ∑ d ∈ Icc 1 Y, (μ d : ℂ) * (d : ℂ) ^ (-w))
      Lindelof.halfPlane := by
    intro w _
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun d hd => ?_
    have hd0 : (d : ℂ) ≠ 0 := by
      have := (mem_Icc.1 hd).1; exact_mod_cast (show d ≠ 0 by omega)
    exact (differentiableAt_id.neg.const_cpow (Or.inl hd0)).const_mul _
  exact h1.sub h2

theorem differentiableOn_Φ (hRH : RiemannHypothesis) {k : ℕ} (hk : 1 ≤ k) (Y : ℕ) {σ₀ : ℝ}
    (hσ₀ : 1 / 2 < σ₀) : DifferentiableOn ℂ (Φ k Y) (strip σ₀) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set U : Set ℂ := {s : ℂ | 1 / 2 < ((k : ℂ) * s).re} with hU
  have hUo : IsOpen U :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul continuous_id))
  have hre : ∀ s : ℂ, ((k : ℂ) * s).re = k * s.re := fun s => by simp
  have h1U : (1 : ℂ) ∈ U := by
    show 1 / 2 < ((k : ℂ) * 1).re
    rw [hre]; simp; linarith
  have hsub : strip σ₀ ⊆ U := fun s hs => by
    show 1 / 2 < ((k : ℂ) * s).re
    rw [hre]; have := hs.1; nlinarith
  have hf : DifferentiableOn ℂ (fun s => G Y ((k : ℂ) * s)) U :=
    (differentiableOn_G hRH Y).comp (by fun_prop) fun s hs => hs
  have hd : DifferentiableOn ℂ (dslope (fun s => G Y ((k : ℂ) * s)) 1) U :=
    (differentiableOn_dslope (hUo.mem_nhds h1U)).2 hf
  exact (differentiable_riemannZeta₁.differentiableOn.mul hd).mono hsub

lemma norm_G_le (Y : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : ‖G Y w‖ ≤ ‖Mertens.invZ w‖ + Y := by
  rw [G]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  calc ‖∑ d ∈ Icc 1 Y, (μ d : ℂ) * (d : ℂ) ^ (-w)‖
      ≤ ∑ d ∈ Icc 1 Y, ‖(μ d : ℂ) * (d : ℂ) ^ (-w)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Icc 1 Y, (1 : ℝ) := by
        refine sum_le_sum fun d hd => ?_
        have hd1 : 0 < d := (mem_Icc.1 hd).1
        rw [norm_mul, Complex.norm_intCast, norm_natCast_cpow_of_pos hd1]
        have h1 : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have h2 : (d : ℝ) ^ (-w).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by simp; linarith)
        calc |(μ d : ℝ)| * (d : ℝ) ^ (-w).re ≤ 1 * 1 :=
              mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = 1 := one_mul 1
    _ = Y := by simp

lemma rpow_mul_add_two_le {k : ℕ} (hk : 1 ≤ k) {t ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (|(k : ℝ) * t| + 2) ^ ε ≤ k * (|t| + 2) ^ ε := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : |(k : ℝ) * t| + 2 ≤ k * (|t| + 2) := by
    rw [abs_mul, Nat.abs_cast]; nlinarith [abs_nonneg t]
  calc (|(k : ℝ) * t| + 2) ^ ε ≤ ((k : ℝ) * (|t| + 2)) ^ ε :=
        Real.rpow_le_rpow (by positivity) h1 hε
    _ = (k : ℝ) ^ ε * (|t| + 2) ^ ε := Real.mul_rpow (by positivity) (by positivity)
    _ ≤ k * (|t| + 2) ^ ε := by
        gcongr
        exact Real.rpow_le_self_of_one_le hk' hε1

/-- `1/ζ(k)` as a complex number is the real `1/(ζ(k)).re`. -/
lemma invZ_natCast {k : ℕ} (hk : 2 ≤ k) :
    Mertens.invZ (k : ℂ) = ((1 / (riemannZeta k).re : ℝ) : ℂ) := by
  have hs : 1 < ((k : ℂ)).re := by simp only [natCast_re]; exact_mod_cast hk
  have h := (KFree.hasSum_moebius_pow hk)
  have hc : HasSum (fun n : ℕ => (((μ n : ℝ) / ((n : ℝ) ^ k) : ℝ) : ℂ))
      ((1 / (riemannZeta k).re : ℝ) : ℂ) := Complex.hasSum_ofReal.2 h
  have hterm : (fun n : ℕ => (((μ n : ℝ) / ((n : ℝ) ^ k) : ℝ) : ℂ)) =
      LSeries.term (fun n => (μ n : ℂ)) k := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [zero_pow (by omega : k ≠ 0)]
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      rw [Complex.cpow_natCast]
  rw [hterm] at hc
  rw [← Mertens.LSeries_moebius_eq_invZ hs, LSeries, hc.tsum_eq]

lemma G_natCast {k : ℕ} (hk : 2 ≤ k) (Y : ℕ) :
    G Y (k : ℂ) = ((1 / (riemannZeta k).re - ∑ d ∈ Icc 1 Y, (μ d : ℝ) / ((d : ℝ) ^ k) : ℝ) : ℂ) := by
  rw [G, invZ_natCast hk]
  push_cast
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [cpow_neg, cpow_natCast, div_eq_mul_inv]

/-- **The main estimate.** For `1 ≤ Y ≤ N`,
`|E_k(N)| ≤ Y + C Y^{1/2+3ε-k(1/2+ε)} (N+1)^{1/2+5ε}`. -/
theorem abs_error_le_mv (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 12) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ Y : ℕ, 1 ≤ Y → Y ≤ N →
      |kFreeCountingError k N| ≤
        Y + C * (Y : ℝ) ^ (1 / 2 + 3 * ε - k * (1 / 2 + ε)) * ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε) := by
  have hk1 : 1 ≤ k := by omega
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set σ₀ : ℝ := 1 / 2 + ε with hσ₀
  set β : ℝ := 1 / 2 + 3 * ε with hβ
  have hσ₀1 : 1 / 2 < σ₀ := by linarith
  have hkσ : 1 < (k : ℝ) * σ₀ := by nlinarith
  have hkσβ : β < (k : ℝ) * σ₀ := by nlinarith
  have hkβ : β < k := by linarith
  obtain ⟨K, hK0, hK⟩ := norm_sum_Icc_le (ε := 2 * ε) (σ₀ := σ₀) (by positivity) (by linarith)
    (by linarith) (by linarith)
  obtain ⟨KT, hKT0, hKT⟩ := tail_le hRH hε (by linarith)
  obtain ⟨Cζ, hCζ0, hCζ⟩ := norm_zeta_le_line hRH hε hσ₀1 (by linarith)
  obtain ⟨Ci, hCi0, hCi⟩ := norm_invZ_le_right hRH (ε := 1 / 2) (by norm_num) (δ := 1 / 2)
    (by norm_num) (by norm_num)
  obtain ⟨Cp, hCp⟩ := Lindelof.norm_zeta_le_poly hRH
  set c₁ : ℝ := 1 + k * σ₀ / (k * σ₀ - β) with hc₁
  set c₂ : ℝ := 1 + k / (k - β) with hc₂
  have hc₁0 : 0 ≤ c₁ := by have : 0 < (k : ℝ) * σ₀ - β := by linarith
                           positivity
  have hc₂0 : 0 ≤ c₂ := by have : 0 < (k : ℝ) - β := by linarith
                           positivity
  set A₀ : ℝ := Cζ * KT * (c₁ * k + c₂ * 2) with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  refine ⟨K * A₀, by positivity, fun N hN Y hY hYN => ?_⟩
  set eY : ℝ := β - k * σ₀ with heY
  have heY0 : eY < 0 := by linarith
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  set g : ℂ := G Y (k : ℂ) with hg
  set a : ℕ → ℂ := fun n => b k Y n - g with ha
  -- the bound for `g`
  have hgb : ‖g‖ ≤ KT * c₂ * 2 * (Y : ℝ) ^ eY := by
    have h := hKT (k : ℝ) 0 (by linarith) hkβ Y hY
    have e : ((k : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = (k : ℂ) := by simp
    rw [e] at h
    have h2 : (|(0 : ℝ)| + 2) ^ ε ≤ 2 := by
      rw [abs_zero, zero_add]; exact Real.rpow_le_self_of_one_le (by norm_num) (by linarith)
    have h3 : (Y : ℝ) ^ (β - k) ≤ (Y : ℝ) ^ eY :=
      Real.rpow_le_rpow_of_exponent_le hY' (by rw [heY]; nlinarith)
    calc ‖g‖ ≤ KT * c₂ * (|(0 : ℝ)| + 2) ^ ε * (Y : ℝ) ^ (β - k) := h
      _ ≤ KT * c₂ * 2 * (Y : ℝ) ^ eY := by gcongr
  -- the hypotheses of the Cesàro–Perron bound
  have hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ (3 : ℝ) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 2)).mul_left (1 + ‖g‖))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : ‖a n‖ ≤ (1 + ‖g‖) * n := by
        calc ‖a n‖ ≤ ‖b k Y n‖ + ‖g‖ := norm_sub_le _ _
          _ ≤ n + ‖g‖ := by linarith [norm_b_le k Y n]
          _ ≤ (1 + ‖g‖) * n := by nlinarith [norm_nonneg g]
      have e3 : (n : ℝ) ^ (3 : ℝ) = n * (n : ℝ) ^ (2 : ℝ) := by
        rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add hn', Real.rpow_one]
      rw [e3]
      calc ‖a n‖ / (n * (n : ℝ) ^ (2 : ℝ)) ≤ (1 + ‖g‖) * n / (n * (n : ℝ) ^ (2 : ℝ)) := by
            gcongr
        _ = (1 + ‖g‖) * (1 / (n : ℝ) ^ (2 : ℝ)) := by field_simp
  have hd := differentiableOn_Φ hRH hk1 Y hσ₀1
  have hne3 : ∀ t : ℝ, ((3 : ℝ) : ℂ) + t * I ≠ 1 := fun t h => by
    have := congrArg re h; simp at this
  have hL : ∀ t : ℝ, Φ k Y ((3 : ℝ) + t * I) = LSeries a ((3 : ℝ) + t * I) := by
    intro t
    have hre : 1 < (((3 : ℝ) : ℂ) + t * I).re := by simp
    rw [Φ_eq (hne3 t)]
    have hb := LSeries_b hk1 Y hre
    have hbs : LSeriesSummable (b k Y) (((3 : ℝ) : ℂ) + t * I) := by
      refine LSeriesSummable_of_le_const_mul_rpow (x := 2) (by simpa using (by norm_num :
        (2 : ℝ) < 3)) ⟨1, fun n hn => ?_⟩
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul]
      exact norm_b_le k Y n
    have hcs : LSeriesSummable (fun _ : ℕ => g) (((3 : ℝ) : ℂ) + t * I) :=
      LSeriesSummable_of_bounded_of_one_lt_re (m := ‖g‖) (fun _ _ => le_rfl) hre
    have hc : LSeries (fun _ : ℕ => g) (((3 : ℝ) : ℂ) + t * I) = g * riemannZeta (((3 : ℝ) : ℂ) + t * I) := by
      have : (fun _ : ℕ => g) = g • (1 : ℕ → ℂ) := by funext n; simp
      rw [this, LSeries_smul, LSeries_one_eq_riemannZeta hre]
    have ha' : a = b k Y - fun _ => g := rfl
    rw [ha', LSeries_sub hbs hcs, hb, hc]
    ring
  obtain ⟨C₂, hC₂⟩ := Mertens.norm_inv_zeta_le_of_two_le
  have hinvZ2 : ∀ w : ℂ, 2 ≤ w.re → ‖Mertens.invZ w‖ ≤ C₂ := fun w hw => by
    have hw1 : w ≠ 1 := by rintro rfl; simp at hw
    rw [Mertens.invZ_eq hw1]; exact hC₂ w hw
  have hmulre : ∀ s : ℂ, ((k : ℂ) * s).re = k * s.re := fun s => by simp
  have hmulim : ∀ s : ℂ, ((k : ℂ) * s).im = k * s.im := fun s => by simp
  set Z : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 with hZ
  have hB : ∀ t : ℝ, ‖Φ k Y ((3 : ℝ) + t * I)‖ ≤ Z * (C₂ + Y + ‖g‖) := by
    intro t
    rw [Φ_eq (hne3 t), norm_mul]
    have hre3 : (((3 : ℝ) : ℂ) + t * I).re = 3 := by simp
    have hz := Lindelof.norm_zeta_le_of_two_le (s := ((3 : ℝ) : ℂ) + t * I) (by rw [hre3]; norm_num)
    have hkre : 2 ≤ ((k : ℂ) * (((3 : ℝ) : ℂ) + t * I)).re := by rw [hmulre, hre3]; nlinarith
    have hG := norm_G_le Y (w := (k : ℂ) * (((3 : ℝ) : ℂ) + t * I)) (by linarith)
    have hi := hinvZ2 _ hkre
    calc _ ≤ Z * (‖G Y ((k : ℂ) * (((3 : ℝ) : ℂ) + t * I))‖ + ‖g‖) :=
          mul_le_mul hz (norm_sub_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ Z * (C₂ + Y + ‖g‖) := by gcongr; linarith
  have hD : ∀ s ∈ strip σ₀, 1 ≤ |s.im| →
      ‖Φ k Y s‖ ≤ |Cp| * (Ci * k + Y + ‖g‖) * (|s.im| + 2) ^ (3 / 2 : ℝ) := by
    intro s hs him
    have hs1 : s ≠ 1 := by rintro rfl; simp at him; norm_num at him
    rw [Φ_eq hs1, norm_mul]
    have hz : ‖riemannZeta s‖ ≤ |Cp| * (|s.im| + 2) :=
      (hCp s (by linarith [hs.1]) him).trans (by
        apply mul_le_mul (le_abs_self _) (by linarith) (abs_nonneg _) (abs_nonneg _))
    have hkre : 1 / 2 + 1 / 2 ≤ ((k : ℂ) * s).re := by rw [hmulre]; have := hs.1; nlinarith
    have hi := hCi _ hkre
    rw [hmulim] at hi
    have hi' : ‖Mertens.invZ ((k : ℂ) * s)‖ ≤ Ci * k * (|s.im| + 2) ^ (1 / 2 : ℝ) := by
      refine hi.trans ?_
      have := rpow_mul_add_two_le hk1 (t := s.im) (ε := 1 / 2) (by norm_num) (by norm_num)
      calc Ci * (|(k : ℝ) * s.im| + 2) ^ (1 / 2 : ℝ) ≤ Ci * (k * (|s.im| + 2) ^ (1 / 2 : ℝ)) := by
            gcongr
        _ = _ := by ring
    have hG := norm_G_le Y (w := (k : ℂ) * s) (by linarith)
    have hp1 : 1 ≤ (|s.im| + 2) ^ (1 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by norm_num)
    have hGg : ‖G Y ((k : ℂ) * s) - g‖ ≤ (Ci * k + Y + ‖g‖) * (|s.im| + 2) ^ (1 / 2 : ℝ) := by
      have hY0 : (0 : ℝ) ≤ Y := by positivity
      calc ‖G Y ((k : ℂ) * s) - g‖ ≤ ‖G Y ((k : ℂ) * s)‖ + ‖g‖ := norm_sub_le _ _
        _ ≤ Ci * k * (|s.im| + 2) ^ (1 / 2 : ℝ) + Y + ‖g‖ := by linarith
        _ ≤ Ci * k * (|s.im| + 2) ^ (1 / 2 : ℝ) + Y * (|s.im| + 2) ^ (1 / 2 : ℝ) +
              ‖g‖ * (|s.im| + 2) ^ (1 / 2 : ℝ) := by
            gcongr
            · exact le_mul_of_one_le_right hY0 hp1
            · exact le_mul_of_one_le_right (norm_nonneg _) hp1
        _ = _ := by ring
    have hpow : (|s.im| + 2) * (|s.im| + 2) ^ (1 / 2 : ℝ) = (|s.im| + 2) ^ (3 / 2 : ℝ) := by
      have hp : 0 < |s.im| + 2 := by positivity
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one]
    calc ‖riemannZeta s‖ * ‖G Y ((k : ℂ) * s) - g‖
        ≤ (|Cp| * (|s.im| + 2)) * ((Ci * k + Y + ‖g‖) * (|s.im| + 2) ^ (1 / 2 : ℝ)) :=
          mul_le_mul hz hGg (norm_nonneg _) (by positivity)
      _ = |Cp| * (Ci * k + Y + ‖g‖) * ((|s.im| + 2) * (|s.im| + 2) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [hpow]
  have hA : ∀ t : ℝ, ‖Φ k Y ((σ₀ : ℂ) + t * I)‖ ≤
      (A₀ * (Y : ℝ) ^ eY) * (|t| + 2) ^ (2 * ε) := by
    intro t
    have hne : (σ₀ : ℂ) + t * I ≠ 1 := fun h => by
      have := congrArg re h; simp at this; linarith
    rw [Φ_eq hne, norm_mul]
    have hz := hCζ t
    have e : (k : ℂ) * ((σ₀ : ℂ) + t * I) = (((k : ℝ) * σ₀ : ℝ) : ℂ) + (((k : ℝ) * t : ℝ) : ℂ) * I := by
      push_cast; ring
    have hT := hKT ((k : ℝ) * σ₀) ((k : ℝ) * t) hkσ hkσβ Y hY
    rw [← e] at hT
    have hT' : ‖G Y ((k : ℂ) * ((σ₀ : ℂ) + t * I))‖ ≤ KT * c₁ * k * (|t| + 2) ^ ε * (Y : ℝ) ^ eY := by
      have h := rpow_mul_add_two_le hk1 (t := t) hε.le (by linarith)
      calc _ ≤ KT * c₁ * (|(k : ℝ) * t| + 2) ^ ε * (Y : ℝ) ^ eY := hT
        _ ≤ KT * c₁ * (k * (|t| + 2) ^ ε) * (Y : ℝ) ^ eY := by gcongr
        _ = _ := by ring
    have hp1 : 1 ≤ (|t| + 2) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg t]) hε.le
    have hGg : ‖G Y ((k : ℂ) * ((σ₀ : ℂ) + t * I)) - g‖ ≤
        KT * (c₁ * k + c₂ * 2) * (|t| + 2) ^ ε * (Y : ℝ) ^ eY := by
      have hYe : 0 ≤ (Y : ℝ) ^ eY := by positivity
      calc _ ≤ ‖G Y ((k : ℂ) * ((σ₀ : ℂ) + t * I))‖ + ‖g‖ := norm_sub_le _ _
        _ ≤ KT * c₁ * k * (|t| + 2) ^ ε * (Y : ℝ) ^ eY + KT * c₂ * 2 * (Y : ℝ) ^ eY :=
            add_le_add hT' hgb
        _ ≤ KT * c₁ * k * (|t| + 2) ^ ε * (Y : ℝ) ^ eY +
              KT * c₂ * 2 * (|t| + 2) ^ ε * (Y : ℝ) ^ eY := by
            have h0 : 0 ≤ KT * c₂ * 2 := by positivity
            have := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right h0 hp1) hYe
            linarith
        _ = _ := by ring
    have hpow : (|t| + 2) ^ ε * (|t| + 2) ^ ε = (|t| + 2) ^ (2 * ε) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    calc ‖riemannZeta ((σ₀ : ℂ) + t * I)‖ * ‖G Y ((k : ℂ) * ((σ₀ : ℂ) + t * I)) - g‖
        ≤ (Cζ * (|t| + 2) ^ ε) * (KT * (c₁ * k + c₂ * 2) * (|t| + 2) ^ ε * (Y : ℝ) ^ eY) :=
          mul_le_mul hz hGg (norm_nonneg _) (by positivity)
      _ = A₀ * (Y : ℝ) ^ eY * ((|t| + 2) ^ ε * (|t| + 2) ^ ε) := by rw [hA₀]; ring
      _ = _ := by rw [hpow]
  have hmain := hK a (Φ k Y) _ _ _ hsum hd hL hB hD hA N hN
  rw [show σ₀ + 2 * (2 * ε) = 1 / 2 + 5 * ε by rw [hσ₀]; ring] at hmain
  -- the real decomposition `E = -R + B`
  have hQ : (kFreeCounting k N : ℝ) =
      ∑ d ∈ Icc 1 N, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) (KFree.kFreeCounting_eq hk1 N)
    push_cast at this
    exact this
  have hsplit : Icc 1 N = Icc 1 Y ∪ Ioc Y N := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 Y) (Ioc Y N) := by
    rw [Finset.disjoint_left]; intro d h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj] at hQ
  set T := ∑ d ∈ Ioc Y N, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) with hT
  set P := ∑ d ∈ Icc 1 Y, (μ d : ℝ) / ((d : ℝ) ^ k) with hP
  set R := ∑ d ∈ Icc 1 Y, (μ d : ℝ) * ((N : ℝ) / ((d : ℝ) ^ k) - ((N / d ^ k : ℕ) : ℝ)) with hR
  have hE : kFreeCountingError k N = -R + (T - (N : ℝ) * (1 / (riemannZeta k).re - P)) := by
    unfold kFreeCountingError
    rw [hQ]
    have : ∑ d ∈ Icc 1 Y, (μ d : ℝ) * ((N / d ^ k : ℕ) : ℝ) = (N : ℝ) * P - R := by
      rw [hP, hR, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun d _ => ?_
      ring
    rw [this]; ring
  have hRb : |R| ≤ Y := by
    calc |R| ≤ ∑ d ∈ Icc 1 Y,
          |(μ d : ℝ) * ((N : ℝ) / ((d : ℝ) ^ k) - ((N / d ^ k : ℕ) : ℝ))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 Y, (1 : ℝ) := by
          refine sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
          have hdd : (0 : ℝ) < ((d ^ k : ℕ) : ℝ) := by
            have : 0 < d ^ k := Nat.pow_pos hd1
            exact_mod_cast this
          have hfl : ((N / d ^ k : ℕ) : ℝ) = ⌊(N : ℝ) / ((d ^ k : ℕ) : ℝ)⌋₊ := by
            rw [Nat.floor_div_eq_div]
          have hx : (N : ℝ) / ((d : ℝ) ^ k) = (N : ℝ) / ((d ^ k : ℕ) : ℝ) := by
            push_cast; ring_nf
          rw [abs_mul, hx, hfl]
          have h0 : 0 ≤ (N : ℝ) / ((d ^ k : ℕ) : ℝ) - ⌊(N : ℝ) / ((d ^ k : ℕ) : ℝ)⌋₊ :=
            sub_nonneg.2 (Nat.floor_le (by positivity))
          have h1 : (N : ℝ) / ((d ^ k : ℕ) : ℝ) - ⌊(N : ℝ) / ((d ^ k : ℕ) : ℝ)⌋₊ ≤ 1 := by
            have := Nat.lt_floor_add_one ((N : ℝ) / ((d ^ k : ℕ) : ℝ)); linarith
          rw [abs_of_nonneg h0]
          have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
          calc |(μ d : ℝ)| * _ ≤ 1 * 1 := mul_le_mul hmu h1 h0 zero_le_one
            _ = 1 := one_mul 1
      _ = Y := by simp
  -- `B` is the partial sum of `a`
  have hBeq : (((T - (N : ℝ) * (1 / (riemannZeta k).re - P)) : ℝ) : ℂ) = ∑ n ∈ Icc 1 N, a n := by
    rw [show ∑ n ∈ Icc 1 N, a n = ∑ n ∈ Icc 1 N, b k Y n - ∑ _n ∈ Icc 1 N, g from
      sum_sub_distrib .., sum_Icc_b hk1, sum_const, Nat.card_Icc, Nat.add_sub_cancel, hg,
      G_natCast hk Y, hT, hP]
    push_cast
    simp [nsmul_eq_mul]
  have hBb : |T - (N : ℝ) * (1 / (riemannZeta k).re - P)| ≤
      K * (A₀ * (Y : ℝ) ^ eY) * ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hBeq]; exact hmain
  rw [hE]
  calc |-R + (T - (N : ℝ) * (1 / (riemannZeta k).re - P))|
      ≤ |-R| + |T - (N : ℝ) * (1 / (riemannZeta k).re - P)| := abs_add_le _ _
    _ ≤ Y + K * (A₀ * (Y : ℝ) ^ eY) * ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε) := by
        rw [abs_neg]; linarith
    _ = _ := by rw [heY, hβ, hσ₀]; ring

/-- **Montgomery–Vaughan (1981)**: under RH, `E_k(x) = O(x^{1/(k+1)+ε})` for every `ε > 0` and
every `k ≥ 2`. -/
theorem montgomeryVaughan_of_RH (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) :
    MontgomeryVaughanBound k := by
  intro ε' hε'
  set ε : ℝ := min (ε' / 6) (1 / 12) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 / 12 := min_le_right _ _
  have hε6 : 6 * ε ≤ ε' := by have := min_le_left (ε' / 6) (1 / 12); linarith
  obtain ⟨C, hC0, hC⟩ := abs_error_le_mv hRH hk hε hε1
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set θ : ℝ := 1 / ((k : ℝ) + 1) with hθ
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hk1]; linarith
  set e : ℝ := 1 / 2 + 3 * ε - k * (1 / 2 + ε) with he
  have he0 : e < 0 := by rw [he]; nlinarith
  -- the exponent bookkeeping: `θ e + 1/2 + 5ε ≤ θ + 6ε`
  have hexp : θ * e + (1 / 2 + 5 * ε) ≤ θ + 6 * ε := by
    have h1 : θ * e + 1 / 2 = θ + θ * (3 - k) * ε := by
      rw [he, hθ]; field_simp; ring
    have h2 : θ * (3 - k) ≤ 1 := by
      rw [hθ, div_mul_eq_mul_div, one_mul, div_le_one hk1]; linarith
    nlinarith
  refine IsBigO.of_bound (2 + 4 * C) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  simp only [Real.norm_eq_abs, abs_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  set y : ℝ := (N : ℝ) ^ θ with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hN' hθ0.le
  have hyN : y ≤ N := by
    calc y ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN' hθ1
      _ = N := Real.rpow_one _
  set Y : ℕ := ⌈y⌉₊ with hYdef
  have hYy : y ≤ Y := Nat.le_ceil y
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := hy1.trans hYy
    exact_mod_cast this
  have hYle : (Y : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hYN : Y ≤ N := by
    calc Y = ⌈y⌉₊ := rfl
      _ ≤ ⌈(N : ℝ)⌉₊ := Nat.ceil_mono hyN
      _ = N := Nat.ceil_natCast N
  have h := hC N hN Y hY1 hYN
  -- `Y^e ≤ y^e = N^{θe}`
  have hYe : (Y : ℝ) ^ e ≤ (N : ℝ) ^ (θ * e) := by
    calc (Y : ℝ) ^ e ≤ y ^ e := Real.rpow_le_rpow_of_nonpos (by linarith) hYy he0.le
      _ = (N : ℝ) ^ (θ * e) := by rw [hy, ← Real.rpow_mul hN0.le]
  -- `(N+1)^{1/2+5ε} ≤ 2 N^{1/2+5ε}`
  have hN1 : ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε) ≤ 2 * (N : ℝ) ^ (1 / 2 + 5 * ε) := by
    calc ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε) ≤ (2 * (N : ℝ)) ^ (1 / 2 + 5 * ε) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = 2 ^ (1 / 2 + 5 * ε) * (N : ℝ) ^ (1 / 2 + 5 * ε) := Real.mul_rpow (by norm_num) hN0.le
      _ ≤ 2 * (N : ℝ) ^ (1 / 2 + 5 * ε) := by
          gcongr
          exact Real.rpow_le_self_of_one_le (by norm_num) (by linarith)
  have hfinal : (N : ℝ) ^ (θ + 6 * ε) ≤ (N : ℝ) ^ (θ + ε') :=
    Real.rpow_le_rpow_of_exponent_le hN' (by linarith)
  have hB : C * (Y : ℝ) ^ e * ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε) ≤ 2 * C * (N : ℝ) ^ (θ + 6 * ε) := by
    calc C * (Y : ℝ) ^ e * ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε)
        ≤ C * (N : ℝ) ^ (θ * e) * (2 * (N : ℝ) ^ (1 / 2 + 5 * ε)) := by gcongr
      _ = 2 * C * ((N : ℝ) ^ (θ * e) * (N : ℝ) ^ (1 / 2 + 5 * ε)) := by ring
      _ = 2 * C * (N : ℝ) ^ (θ * e + (1 / 2 + 5 * ε)) := by rw [← Real.rpow_add hN0]
      _ ≤ 2 * C * (N : ℝ) ^ (θ + 6 * ε) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN' hexp) (by positivity)
  have hYb : (Y : ℝ) ≤ 2 * (N : ℝ) ^ (θ + 6 * ε) := by
    have : y ≤ (N : ℝ) ^ (θ + 6 * ε) := Real.rpow_le_rpow_of_exponent_le hN' (by linarith)
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (θ + 6 * ε) := Real.one_le_rpow hN' (by positivity)
    linarith
  have hpos : 0 ≤ (N : ℝ) ^ (θ + 6 * ε) := by positivity
  calc |kFreeCountingError k N| ≤ Y + C * (Y : ℝ) ^ e * ((N : ℝ) + 1) ^ (1 / 2 + 5 * ε) := h
    _ ≤ 2 * (N : ℝ) ^ (θ + 6 * ε) + 2 * C * (N : ℝ) ^ (θ + 6 * ε) := add_le_add hYb hB
    _ = (2 + 2 * C) * (N : ℝ) ^ (θ + 6 * ε) := by ring
    _ ≤ (2 + 4 * C) * (N : ℝ) ^ (θ + ε') := by
        apply mul_le_mul (by linarith) hfinal hpos (by positivity)

/-- The squarefree case: under RH, `E(x) = O(x^{1/3+ε})` for every `ε > 0`. -/
theorem squarefreeError_mv_of_RH (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε → (fun x : ℕ => |squarefreeCountingError x|) =O[atTop]
      fun x : ℕ => (x : ℝ) ^ (1 / 3 + ε) := by
  intro ε hε
  have h := montgomeryVaughan_of_RH hRH (le_refl 2) ε hε
  have e : (1 : ℝ) / (((2 : ℕ) : ℝ) + 1) = 1 / 3 := by norm_num
  simpa only [KFree.kFreeCountingError_two, e] using h

end Erdos969.MV
