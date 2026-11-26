import Erdos233.Explicit
import Erdos233.MeanSquare
import Erdos233.PrimePowers
import Erdos233.Primes

/-!
# Step 8. Large gaps force the zero contribution to be large

Fix `x`, `h` with `16 L ≤ h ≤ x/8` (`L = log²(5x)/log 2`) and `δ = h/x`. For a gap
`p_n < p_{n+1}` with `x ≤ p_n < 2x` and `d_n ≥ 16h`, every `y ∈ G_n = (p_n, p_{n+1}/(1+2δ))`
has a window `(y, y(1+2δ))` free of primes, so `D2 δ y ≤ δy · (proper prime powers) ≤ δ²y²/4`
(`D2_le`, `psi_sub_theta_window`), and `D2_bound` gives `y^{3/2}|F δ (log y)| ≥ δ²y²/2 ≥ h²/2`.
The `G_n` are disjoint, lie in `[x, 4x]`, and `|G_n| ≥ d_n/2`; `mean_square` then gives
`Σ_{d_n ≥ 16h} d_n ≤ C x log² x / h`.
-/

namespace Erdos233

open Complex Erdos985.Analytic MeasureTheory intervalIntegral Chebyshev ArithmeticFunction

lemma psi1_eq_sum_pos {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : ⌊t⌋₊ + 1 ≤ M) :
    psi1 t = ∑ n ∈ Finset.range M, (Λ n : ℝ) * max (t - n) 0 := by
  unfold psi1
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hM)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hn
    have : (n : ℝ) ≤ t := (Nat.cast_le.2 hn).trans (Nat.floor_le ht)
    rw [max_eq_left (by linarith)]
  · intro n _ hn
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hn
    have : t < n := (Nat.floor_lt ht).1 hn
    rw [max_eq_right (by linarith), mul_zero]

lemma tent_le (y H a : ℝ) (hH : 0 < H) :
    max (y + 2 * H - a) 0 - 2 * max (y + H - a) 0 + max (y - a) 0
      ≤ if y < a ∧ a < y + 2 * H then H else 0 := by
  rcases le_or_gt a y with h1 | h1
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
      if_neg (show ¬(y < a ∧ a < y + 2 * H) by intro h; linarith [h.1])]
    linarith
  rcases lt_or_ge a (y + H) with h2 | h2
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
      if_pos ⟨h1, by linarith⟩]
    linarith
  rcases lt_or_ge a (y + 2 * H) with h3 | h3
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
      if_pos ⟨h1, h3⟩]
    linarith
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  split_ifs <;> linarith

/-- The Λ-side of `D2` when the window `(y, y(1+2δ))` contains no prime. -/
lemma D2_le {δ y : ℝ} (hy : 0 < y) (hδ : 0 < δ)
    (hnp : ∀ n : ℕ, y < n → (n : ℝ) < y * (1 + 2 * δ) → ¬ n.Prime) :
    D2 δ y ≤ δ * y * ((ψ (y * (1 + 2 * δ)) - θ (y * (1 + 2 * δ))) - (ψ y - θ y)) := by
  set B := y * (1 + 2 * δ) with hB
  set H := δ * y with hH
  have hH0 : 0 < H := mul_pos hδ hy
  set M := ⌊B⌋₊ + 1 with hM
  have hyB : y ≤ B := by rw [hB]; nlinarith
  have hyM : y * (1 + δ) ≤ B := by rw [hB]; nlinarith
  have e1 := psi1_eq_sum_pos (t := B) (by linarith) (M := M) le_rfl
  have e2 := psi1_eq_sum_pos (t := y * (1 + δ)) (by nlinarith) (M := M)
    (by have := Nat.floor_le_floor hyM; omega)
  have e3 := psi1_eq_sum_pos (t := y) hy.le (M := M)
    (by have := Nat.floor_le_floor hyB; omega)
  have hD : D2 δ y = ∑ n ∈ Finset.range M, (Λ n : ℝ) *
      (max (y + 2 * H - n) 0 - 2 * max (y + H - n) 0 + max (y - n) 0) := by
    unfold D2
    rw [← hB, e1, e2, e3, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show y + 2 * H = B by rw [hB, hH]; ring, show y + H = y * (1 + δ) by rw [hH]; ring]
    ring
  set P : ℕ → Prop := fun n => ⌊y⌋₊ < n ∧ n ≤ ⌊B⌋₊ ∧ ¬ n.Prime with hP
  have hstep : D2 δ y ≤ ∑ n ∈ Finset.range M, (Λ n : ℝ) * (if P n then H else 0) := by
    rw [hD]
    refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
    refine (tent_le y H n hH0).trans ?_
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      apply h2
      refine ⟨(Nat.floor_lt hy.le).2 h1.1, Nat.le_floor ?_, hnp n h1.1 ?_⟩
      · have : y + 2 * H = B := by rw [hB, hH]; ring
        linarith [h1.2]
      · have : y + 2 * H = B := by rw [hB, hH]; ring
        linarith [h1.2]
    · exact hH0.le
    · exact le_rfl
  have hsum : ∑ n ∈ Finset.range M, (Λ n : ℝ) * (if P n then H else 0)
      = H * ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊B⌋₊ with ¬ n.Prime, (Λ n : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    rw [← Finset.sum_subset (s₁ := Finset.Ioc ⌊y⌋₊ ⌊B⌋₊) (s₂ := Finset.range M)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      by_cases hp : n.Prime
      · simp [hP, hp]
      · simp [hP, hp, hn.1, hn.2, mul_comm]
    · intro n hn; rw [Finset.mem_Ioc] at hn; rw [Finset.mem_range]; omega
    · intro n _ hn
      rw [Finset.mem_Ioc] at hn
      have : ¬ P n := fun h => hn ⟨h.1, h.2.1⟩
      simp [this]
  have hpt : (ψ B - θ B) - (ψ y - θ y) = ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊B⌋₊ with ¬ n.Prime, (Λ n : ℝ) := by
    rw [psi_sub_theta_eq_sum_not_prime, psi_sub_theta_eq_sum_not_prime, Finset.sum_filter,
      Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊y⌋₊) (Nat.floor_le_floor hyB)]
    ring
  rw [hpt]
  exact hstep.trans hsum.le

/-- Eventually `16 log²(5x)/log 2 ≤ √x`. -/
lemma eventually_log_sq_le_sqrt :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 16 * (Real.log (5 * X) ^ 2 / Real.log 2) ≤ Real.sqrt X := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho := (isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show 0 < Real.log 2 / 64 by positivity)
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 ho
  refine ⟨max X₁ 5, fun X hX => ?_⟩
  have hX5 : 5 ≤ X := le_of_max_le_right hX
  have hX0 : 0 < X := by linarith
  have h := hX₁ X (le_of_max_le_left hX)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlX _),
    abs_of_nonneg (Real.rpow_nonneg hX0.le _), Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have h5 : Real.log (5 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 5 ≤ Real.log X := Real.log_le_log (by norm_num) hX5
    linarith
  have h5' : 0 ≤ Real.log (5 * X) := Real.log_nonneg (by linarith)
  have hsq : Real.log (5 * X) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  rw [div_eq_mul_inv]
  have : 16 * (Real.log (5 * X) ^ 2 * (Real.log 2)⁻¹) ≤ 64 * Real.log X ^ 2 / Real.log 2 := by
    rw [mul_comm (Real.log (5 * X) ^ 2), ← mul_assoc, le_div_iff₀ hl2]
    field_simp
    nlinarith
  refine this.trans ?_
  rw [div_le_iff₀ hl2]
  nlinarith

lemma gap_arith {Sg Cm X h δ : ℝ} (hCm : 0 < Cm) (hX5 : 5 ≤ X) (hh0 : 0 < h) (hh1 : 1 ≤ h)
    (hhx : h ≤ X / 8) (hδdef : δ = h / X) (_hSnn : 0 ≤ Sg)
    (htot : Sg * (h ^ 4 / 4 / 2) ≤ Cm * X ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2) :
    Sg ≤ 32 * Cm * X * Real.log X ^ 2 / h := by
  have hX0 : 0 < X := by linarith
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hlog2δ : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0, one_mul, hδdef, div_le_iff₀ hX0]; linarith)
  have hlog2δ' : Real.log (2 / δ) ≤ 2 * Real.log X := by
    have : 2 / δ ≤ X ^ 2 := by
      rw [div_le_iff₀ hδ0, hδdef]
      field_simp
      nlinarith
    calc Real.log (2 / δ) ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) this
      _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
  have hL2 : Real.log (2 / δ) ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
  have hX4 : X ^ 4 * δ ^ 3 = X * h ^ 3 := by rw [hδdef]; field_simp
  rw [mul_assoc Cm, mul_assoc Cm, hX4] at htot
  rw [le_div_iff₀ hh0]
  have hh3 : 0 < h ^ 3 := by positivity
  have key : Sg * h * (h ^ 3 / 8) ≤ (32 * Cm * X * Real.log X ^ 2) * (h ^ 3 / 8) := by
    have e : Sg * h * (h ^ 3 / 8) = Sg * (h ^ 4 / 4 / 2) := by ring
    rw [e]
    refine htot.trans ?_
    have : Cm * (X * h ^ 3 * Real.log (2 / δ) ^ 2) ≤ Cm * (X * h ^ 3 * (4 * Real.log X ^ 2)) := by
      gcongr
    nlinarith
  have := le_of_mul_le_mul_right key (by positivity)
  linarith

theorem gap_sum (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x →
    ∀ h : ℝ, 16 * (Real.log (5 * x) ^ 2 / Real.log 2) ≤ h → h ≤ x / 8 →
    ∑ n ∈ (block x).filter (fun n => 16 * h ≤ primeGap n), (primeGap n : ℝ)
      ≤ C * x * Real.log x ^ 2 / h := by
  obtain ⟨Cm, hCm, hms⟩ := mean_square hRH
  obtain ⟨X₁, hX₁⟩ := eventually_log_sq_le_sqrt
  refine ⟨32 * Cm, max X₁ 5, by positivity, fun x hx h hh hhx => ?_⟩
  set X : ℝ := (x : ℝ) with hXdef
  have hX5 : 5 ≤ X := le_of_max_le_right hx
  have hX0 : 0 < X := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  set Lx := Real.log (5 * X) ^ 2 / Real.log 2 with hLx
  have hl5 : 1 ≤ Real.log (5 * X) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hLx1 : 1 ≤ Lx := by
    rw [hLx, le_div_iff₀ hl2]; nlinarith
  have hsqrt : 16 * Lx ≤ Real.sqrt X := hX₁ X (le_of_max_le_left hx)
  have hh16 : 16 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  set δ := h / X with hδdef
  have hδ0 : 0 < δ := div_pos hh0 hX0
  have hδ8 : δ ≤ 1 / 8 := by rw [hδdef, div_le_iff₀ hX0]; linarith
  have hδX : δ * X = h := by rw [hδdef]; field_simp
  obtain ⟨hII, hMS⟩ := hms X (by linarith) δ hδ0 (by linarith)
  set W : ℝ → ℝ := fun y => (y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖) ^ 2 with hW
  set S := (block x).filter (fun n => 16 * h ≤ primeGap n) with hS
  set a : ℕ → ℝ := fun n => (Nat.nth Nat.Prime n : ℝ) with ha
  set b : ℕ → ℝ := fun n => (Nat.nth Nat.Prime (n + 1) : ℝ) / (1 + 2 * δ) with hb
  set c : ℝ := h ^ 4 / 4 with hc
  have hc0 : 0 ≤ c := by positivity
  have han : ∀ k, a k = (Nat.nth Nat.Prime k : ℝ) := fun k => by rw [ha]
  have hbn : ∀ k, b k = (Nat.nth Nat.Prime (k + 1) : ℝ) / (1 + 2 * δ) := fun k => by rw [hb]
  clear_value W S a b c
  -- facts about one gap
  have hgap : ∀ n ∈ S, X ≤ a n ∧ a n ≤ b n ∧ b n ≤ 4 * X ∧
      (primeGap n : ℝ) / 2 ≤ b n - a n ∧ (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 4 * X := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨hn1, hn2⟩ := mem_block hn.1
    have hd := hn.2
    have h2 := nth_succ_le_two_mul n
    have hq4 : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 4 * X := by
      rw [hXdef]; exact_mod_cast (by omega : Nat.nth Nat.Prime (n + 1) ≤ 4 * x)
    have hxa : X ≤ a n := by rw [han, hXdef]; exact_mod_cast hn1
    have hpg := primeGap_cast n
    have hq0 : (0 : ℝ) ≤ Nat.nth Nat.Prime (n + 1) := Nat.cast_nonneg _
    have hbq : b n ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) := by
      rw [hbn, div_le_iff₀ (by linarith)]; nlinarith
    have hbl : (Nat.nth Nat.Prime (n + 1) : ℝ) * (1 - 2 * δ) ≤ b n := by
      rw [hbn, le_div_iff₀ (by linarith)]
      have e : (Nat.nth Nat.Prime (n + 1) : ℝ) * (1 - 2 * δ) * (1 + 2 * δ)
          = (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime (n + 1) : ℝ) * (4 * δ ^ 2) := by ring
      rw [e]
      have : 0 ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) * (4 * δ ^ 2) := by positivity
      linarith
    have hlen : (primeGap n : ℝ) / 2 ≤ b n - a n := by
      have : (Nat.nth Nat.Prime (n + 1) : ℝ) * (2 * δ) ≤ 8 * h := by
        have : (Nat.nth Nat.Prime (n + 1) : ℝ) * δ ≤ 4 * X * δ :=
          mul_le_mul_of_nonneg_right hq4 hδ0.le
        nlinarith
      have hd' : 16 * h ≤ (primeGap n : ℝ) := by exact_mod_cast hd
      rw [han]
      linarith
    have hpg0 : (0 : ℝ) ≤ primeGap n := Nat.cast_nonneg _
    exact ⟨hxa, by linarith, by linarith, hlen, hq4⟩
  -- on `G_n` the zero contribution is large
  have hbig : ∀ n ∈ S, ∀ y ∈ Set.Ioo (a n) (b n), c ≤ W y := by
    intro n hn y hy
    obtain ⟨hxa, -, hb4, -, hq4⟩ := hgap n hn
    have hyX : X ≤ y := by linarith [hy.1]
    have hy0 : 0 < y := by linarith
    set B := y * (1 + 2 * δ) with hBdef
    have hBq : B < (Nat.nth Nat.Prime (n + 1) : ℝ) := by
      have := hy.2; rw [hbn, lt_div_iff₀ (by linarith)] at this; rw [hBdef]; linarith
    have hnp : ∀ m : ℕ, y < m → (m : ℝ) < B → ¬ m.Prime := by
      intro m h1 h2
      refine not_prime_between (n := n) ?_ ?_
      · have : (Nat.nth Nat.Prime n : ℝ) < m := by
          have := hy.1; rw [han] at this; linarith
        exact_mod_cast this
      · exact_mod_cast h2.trans hBq
    have hD2 : D2 δ y ≤ δ * y * ((ψ B - θ B) - (ψ y - θ y)) := D2_le hy0 hδ0 hnp
    have hyB : y ≤ B := by rw [hBdef]; nlinarith
    have hwin := psi_sub_theta_window (A := y) (B := B) (by linarith) hyB
    have hDb := D2_bound hRH hδ0 (show 1 ≤ y by linarith)
    set H := δ * y with hHdef
    clear_value H B
    have hHh : h ≤ H := by rw [hHdef, ← hδX]; exact mul_le_mul_of_nonneg_left hyX hδ0.le
    have hB5 : B ≤ 5 * X := by linarith
    have hlB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    have hlB5 : Real.log B ≤ Real.log (5 * X) := Real.log_le_log (by linarith) hB5
    have hLw : Real.log B / Real.log 2 * Real.log B ≤ Lx := by
      rw [hLx, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2, sq]
      exact mul_le_mul hlB5 hlB5 hlB (hlB.trans hlB5)
    have hsy : Real.sqrt X ≤ Real.sqrt y := Real.sqrt_le_sqrt hyX
    have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
    have hT : (B - y) / Real.sqrt y = 2 * H / Real.sqrt y := by
      congr 1; rw [hBdef, hHdef]; ring
    set T := 2 * H / Real.sqrt y with hTdef
    have hT0 : 0 ≤ T := div_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hHT : H * Lx * T ≤ H ^ 2 / 8 := by
      rw [hTdef]
      have : H * Lx * (2 * H / Real.sqrt y) = 2 * Lx * H ^ 2 / Real.sqrt y := by ring
      rw [this, div_le_iff₀ hsy0]
      have hH2 : 0 ≤ H ^ 2 := sq_nonneg H
      have := mul_le_mul_of_nonneg_left (hsqrt.trans hsy) hH2
      linarith
    have hP : (ψ B - θ B) - (ψ y - θ y) ≤ Lx * (T + 1) := by
      rw [← hT]
      refine hwin.trans ?_
      have : 0 ≤ (B - y) / Real.sqrt y + 1 := by
        have : 0 ≤ (B - y) / Real.sqrt y := div_nonneg (by linarith) (Real.sqrt_nonneg _)
        linarith
      exact mul_le_mul_of_nonneg_right hLw this
    have hH0 : 0 < H := by linarith
    have hDle : D2 δ y ≤ H * (Lx * (T + 1)) := hD2.trans (mul_le_mul_of_nonneg_left hP hH0.le)
    have hHL : H * Lx ≤ H ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_left (show 8 * Lx ≤ H by linarith) hH0.le
      have hsq : H ^ 2 = H * H := sq H
      linarith
    have hab := (abs_le.1 hDb).1
    have hWy : H ^ 2 / 2 ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖ := by
      have e : δ ^ 2 * y ^ 2 = H ^ 2 := by rw [hHdef]; ring
      rw [e] at hab
      have e2 : H * (Lx * (T + 1)) = H * Lx * T + H * Lx := by ring
      have h16 : 16 ≤ H := by linarith
      have h256 : 256 ≤ H ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num) h16 2; norm_num at this; linarith
      linarith
    have hh2 : h ^ 2 / 2 ≤ H ^ 2 / 2 := by
      have := pow_le_pow_left₀ hh0.le hHh 2; linarith
    rw [hW, hc]
    have h3 : h ^ 2 / 2 ≤ y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖ := hh2.trans hWy
    have h4 := pow_le_pow_left₀ (by positivity) h3 2
    have e3 : (h ^ 2 / 2) ^ 2 = h ^ 4 / 4 := by ring
    linarith
  -- disjointness
  have hdisj : ∀ n ∈ S, ∀ n' ∈ S, ∀ y, y ∈ Set.Ioo (a n) (b n) →
      y ∈ Set.Ioo (a n') (b n') → n = n' := by
    intro n hn n' hn' y hy hy'
    by_contra hne
    have hbq : ∀ k ∈ S, b k ≤ (Nat.nth Nat.Prime (k + 1) : ℝ) := by
      intro k hk
      obtain ⟨hxa, hab, -, -, hq4⟩ := hgap k hk
      rw [hbn, div_le_iff₀ (by linarith)]
      have : (0 : ℝ) ≤ Nat.nth Nat.Prime (k + 1) := Nat.cast_nonneg _
      nlinarith
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Nat.nth Nat.Prime n' := by
        exact_mod_cast (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hlt
      have := hbq n hn
      have h1 := hy.2; have h2 := hy'.1; rw [han] at h2; linarith
    · have : (Nat.nth Nat.Prime (n' + 1) : ℝ) ≤ Nat.nth Nat.Prime n := by
        exact_mod_cast (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hlt
      have := hbq n' hn'
      have h1 := hy'.2; have h2 := hy.1; rw [han] at h2; linarith
  -- the lower function
  set g : ℝ → ℝ := fun y => ∑ n ∈ S, (Set.Ioo (a n) (b n)).indicator (fun _ => c) y with hg
  have hind_int : ∀ n, IntervalIntegrable ((Set.Ioo (a n) (b n)).indicator fun _ => c)
      volume X (4 * X) := by
    intro n
    refine Integrable.intervalIntegrable ?_
    exact (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))
  have hgI : IntervalIntegrable g volume X (4 * X) := by
    rw [hg]
    have := IntervalIntegrable.sum S fun n _ => hind_int n
    convert this using 1
    funext y; simp [Finset.sum_apply]
  have hgW : ∀ y ∈ Set.Icc X (4 * X), g y ≤ W y := by
    intro y _
    have hW0 : 0 ≤ W y := by rw [hW]; positivity
    rw [hg]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    set K := S.filter (fun n => y ∈ Set.Ioo (a n) (b n)) with hK
    have hK1 : K.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro n hn n' hn'
      rw [hK, Finset.mem_filter] at hn hn'
      exact hdisj n hn.1 n' hn'.1 y hn.2 hn'.2
    rcases Nat.eq_zero_or_pos K.card with h0 | h0
    · rw [h0]; simp [hW0]
    · obtain ⟨n, hn⟩ := Finset.card_pos.1 h0
      rw [hK, Finset.mem_filter] at hn
      have := hbig n hn.1 y hn.2
      have hK1' : (K.card : ℝ) ≤ 1 := by exact_mod_cast hK1
      nlinarith
  have hint_ind : ∀ n ∈ S, ∫ y in X..4 * X, (Set.Ioo (a n) (b n)).indicator (fun _ => c) y
      = c * (b n - a n) := by
    intro n hn
    obtain ⟨hxa, hab, hb4, -, -⟩ := hgap n hn
    rw [integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioo]
    have hset : Set.Ioc X (4 * X) ∩ Set.Ioo (a n) (b n) = Set.Ioo (a n) (b n) := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨⟨by linarith [h.1], by linarith [h.2]⟩, h⟩
    rw [hset, setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul, mul_comm]
  have hint_g : ∫ y in X..4 * X, g y = ∑ n ∈ S, c * (b n - a n) := by
    rw [hg, intervalIntegral.integral_finsetSum fun n _ => hind_int n]
    exact Finset.sum_congr rfl hint_ind
  have hmono : ∫ y in X..4 * X, g y ≤ ∫ y in X..4 * X, W y :=
    integral_mono_on (by linarith) hgI hII hgW
  have hlow : (∑ n ∈ S, (primeGap n : ℝ)) * (c / 2) ≤ ∑ n ∈ S, c * (b n - a n) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    have h1 := mul_le_mul_of_nonneg_left (hgap n hn).2.2.2.1 hc0
    have e : (primeGap n : ℝ) * (c / 2) = c * ((primeGap n : ℝ) / 2) := by ring
    rw [e]; exact h1
  have htot : (∑ n ∈ S, (primeGap n : ℝ)) * (c / 2)
      ≤ Cm * X ^ 4 * δ ^ 3 * Real.log (2 / δ) ^ 2 := by
    calc _ ≤ ∑ n ∈ S, c * (b n - a n) := hlow
      _ = ∫ y in X..4 * X, g y := hint_g.symm
      _ ≤ ∫ y in X..4 * X, W y := hmono
      _ ≤ _ := hMS
  have hSnn : 0 ≤ ∑ n ∈ S, (primeGap n : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [hc] at htot
  exact gap_arith hCm hX5 hh0 (by linarith) hhx hδdef hSnn htot

end Erdos233
