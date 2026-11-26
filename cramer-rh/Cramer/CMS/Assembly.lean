import Cramer.CMS.Trig
import Cramer.CMS.PerZero
import Cramer.CMS.ZeroSum

/-!
# The zero sum of the weight, from the checked cells

For the symmetric data `c` (`c_j = φ_{|j−L|}`) and a checked cell list, every zero
`ρ = 1/2 + iγ` has, with `h = s/m`, `θ = |γ|h` and `T_ρ = Σ_j a_j g_ρ(t_j)`:

* `‖T_ρ‖ ≤ s² m^{−1/2} (G_i + h e_i)` when `θ` lies in the `i`-th cell (`norm_T_le_cell`):
  the first bound of `Cramer.CMS.PerZero` for `θ ≤ 1`, the second beyond, the cell check for
  `(2 − 2cos θ)|Q(cos θ)|/θ² ≤ G_i` and the error check for `e_i`;
* `‖T_ρ‖ ≤ s² m^{−1/2} (1 + Lh)^{3/2} Σ|a_j| / θ²` beyond the last cell (the trivial bound).

`zeroSum_le` sums these with `Cramer.CMS.tsum_le_of_step`.
-/

namespace Cramer.CMS

open Finset Complex Real
open Schoenfeld (Zeros mult)
open CramerCompute (D0 SS Ent posOK boundOK chk endOK eOK rOK chainB)

/-! ### Constants of the data -/

/-- `Σ |c_j| (|j−L|+1)`. -/
def C1a (c : ℕ → ℤ) (J L : ℕ) : ℕ :=
  ∑ j ∈ range (J + 1), (c j).natAbs * (Int.natAbs ((j : ℤ) - L) + 1)
/-- `Σ |c_j| (|j−L|+1)²`. -/
def C1b (c : ℕ → ℤ) (J L : ℕ) : ℕ :=
  ∑ j ∈ range (J + 1), (c j).natAbs * (Int.natAbs ((j : ℤ) - L) + 1) ^ 2
/-- `Σ |a_j| |j−L|`. -/
def C2a (c : ℕ → ℤ) (J L : ℕ) : ℕ :=
  ∑ j ∈ range (J + 1), (aco c j).natAbs * Int.natAbs ((j : ℤ) - L)
/-- `Σ |a_j| |j−L|²`. -/
def C2b (c : ℕ → ℤ) (J L : ℕ) : ℕ :=
  ∑ j ∈ range (J + 1), (aco c j).natAbs * Int.natAbs ((j : ℤ) - L) ^ 2
/-- `Σ |a_j|`. -/
def Asum (c : ℕ → ℤ) (J : ℕ) : ℕ := ∑ j ∈ range (J + 1), (aco c j).natAbs

lemma natAbs_sub_cast (j L : ℕ) : ((Int.natAbs ((j : ℤ) - L) : ℕ) : ℝ) = |(j : ℝ) - L| := by
  rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl

/-! ### One zero -/

lemma norm_mul_ge_im_sq {ρ : ℂ} : ρ.im ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
  rw [norm_mul]
  have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have h2 : |ρ.im| ≤ ‖ρ + 1‖ := by
    have := Complex.abs_im_le_norm (ρ + 1); simpa using this
  rw [← sq_abs]
  nlinarith [abs_nonneg ρ.im]

/-- **One zero in one cell.** -/
theorem norm_T_le_cell {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hγ : ρ.im ≠ 0) {m s : ℝ} (hm : 0 < m)
    (hs : 0 < s) (c : ℕ → ℤ) {L D : ℕ} (hc0 : c 0 = 0) (hcJ : ∀ j, 2 * L ≤ j → c j = 0)
    (hsym : ∀ j, j ≤ 2 * L → c (2 * L - j) = c j) (hLD : L ≤ D) {qs : List ℤ}
    (hcoef : coefOK c (2 * L) L D qs = true) (hsmall : ((L : ℝ) + 1) * (s / m) ≤ 1 / 2)
    {GD : ℕ} {e e' : Ent} (hcell : CellGood qs GD e e')
    (heok : eOK (C1a c (2 * L) L) (C1b c (2 * L) L) (C2a c (2 * L) L) (C2b c (2 * L) L) e e' = true)
    (h1 : (e.N : ℝ) / D0 < |ρ.im| * (s / m)) (h2 : |ρ.im| * (s / m) ≤ (e'.N : ℝ) / D0) :
    ‖∑ j ∈ range (2 * L + 1), (aco c j : ℂ) * gρ ρ (tk m s L j)‖ ≤
      s ^ 2 * m ^ (-(1 / 2) : ℝ) * ((e.Gn : ℝ) / GD + s / m * ((e.en : ℝ) / D0)) := by
  set h := s / m with hh
  have hh0 : 0 < h := div_pos hs hm
  set θ := |ρ.im| * h with hθ
  have hθ0 : 0 < θ := mul_pos (abs_pos.2 hγ) hh0
  have hD0 : (0 : ℝ) < D0 := by simp [D0]
  -- the main term: `m^{3/2}/γ² · A = s² m^{−1/2} Fq(θ)`
  have hA : ‖∑ j ∈ range (2 * L + 1), (aco c j : ℂ) * exp (I * (((j : ℝ) * (ρ.im * s / m) : ℝ) : ℂ))‖
      = (2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| := by
    rw [norm_sum_aco_exp c hc0 hcJ hsym hLD hcoef]
    have : Real.cos (ρ.im * s / m) = Real.cos θ := by
      rcases le_total 0 ρ.im with hp | hn
      · rw [hθ, abs_of_nonneg hp, hh]; ring_nf
      · rw [hθ, abs_of_nonpos hn, hh, ← Real.cos_neg]; ring_nf
    rw [this]
  have hpow : m ^ (3 / 2 : ℝ) / ρ.im ^ 2 = s ^ 2 * m ^ (-(1 / 2) : ℝ) / θ ^ 2 := by
    rw [hθ, mul_pow, sq_abs, hh, div_pow]
    have hm32 : m ^ (3 / 2 : ℝ) = m ^ (-(1 / 2) : ℝ) * m ^ (2 : ℝ) := by
      rw [← Real.rpow_add hm]; norm_num
    rw [hm32, Real.rpow_two]
    have : ρ.im ^ 2 ≠ 0 := pow_ne_zero 2 hγ
    field_simp
  have hFq := hcell θ (by linarith) h2 hθ0
  unfold Fq at hFq
  have hS : 0 < s ^ 2 * m ^ (-(1 / 2) : ℝ) := by positivity
  by_cases hreg : e'.N ≤ D0
  · -- `θ ≤ 1`: the first bound
    simp only [eOK, hreg, if_true, decide_eq_true_eq] at heok
    have heok' : (C1a c (2 * L) L : ℝ) * D0 + 2 * e'.N * C1b c (2 * L) L ≤ e.en := by
      exact_mod_cast heok
    have key := norm_T_le_small hρ hγ hm hs.le c hc0 (fun j hj => hcJ j hj) le_rfl hsmall
    rw [hpow, hA] at key
    -- the error sum
    have herr : ∑ j ∈ range (2 * L + 1), |(c j : ℝ)| *
        ((|(j : ℝ) - L| + 1) * (s / m) + 2 * |ρ.im| * ((|(j : ℝ) - L| + 1) * (s / m)) ^ 2) =
        h * ((C1a c (2 * L) L : ℝ) + 2 * θ * (C1b c (2 * L) L : ℝ)) := by
      unfold C1a C1b
      push_cast
      rw [mul_add, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, hθ, ← hh]
      ring
    rw [herr] at key
    have hθ1 : θ ≤ 1 := by
      have : (e'.N : ℝ) / D0 ≤ 1 := by rw [div_le_one hD0]; exact_mod_cast hreg
      linarith
    have hC1b : (0 : ℝ) ≤ C1b c (2 * L) L := Nat.cast_nonneg _
    have he1 : (C1a c (2 * L) L : ℝ) + 2 * θ * C1b c (2 * L) L ≤ (e.en : ℝ) / D0 := by
      rw [le_div_iff₀ hD0]
      have : θ * D0 ≤ e'.N := by rw [← le_div_iff₀ hD0]; exact h2
      nlinarith
    calc _ ≤ s ^ 2 * m ^ (-(1 / 2) : ℝ) / θ ^ 2 * ((2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)|) +
          s ^ 2 * m ^ (-(1 / 2) : ℝ) * (h * ((C1a c (2 * L) L : ℝ) + 2 * θ * C1b c (2 * L) L)) := key
      _ = s ^ 2 * m ^ (-(1 / 2) : ℝ) * ((2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| / θ ^ 2 +
          h * ((C1a c (2 * L) L : ℝ) + 2 * θ * C1b c (2 * L) L)) := by ring
      _ ≤ _ := by
          gcongr
  · -- `θ > θ_a > 0`: the second bound
    simp only [eOK, hreg, if_false, Bool.and_eq_true, decide_eq_true_eq] at heok
    obtain ⟨hN0, heok⟩ := heok
    have heok' : ((2 * C2a c (2 * L) L * D0 ^ 2 + 2 * e.N * C2b c (2 * L) L * D0) * D0 : ℝ) ≤
        e.en * (e.N : ℝ) ^ 2 := by exact_mod_cast heok
    have hsmall' : (L : ℝ) * (s / m) ≤ 1 / 2 := by nlinarith [div_pos hs hm]
    have key := norm_T_le_large hρ hm hs.le c (le_refl (2 * L)) hsmall'
    rw [hA] at key
    have herr : ∑ j ∈ range (2 * L + 1), |(aco c j : ℝ)| *
        (2 * (|(j : ℝ) - L| * (s / m)) + 2 * |ρ.im| * (|(j : ℝ) - L| * (s / m)) ^ 2) =
        h * (2 * (C2a c (2 * L) L : ℝ) + 2 * θ * (C2b c (2 * L) L : ℝ)) := by
      unfold C2a C2b
      push_cast
      rw [mul_add, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, hθ, ← hh]
      ring
    rw [herr] at key
    have hnorm : m ^ (3 / 2 : ℝ) / ‖ρ * (ρ + 1)‖ ≤ m ^ (3 / 2 : ℝ) / ρ.im ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) norm_mul_ge_im_sq
    have hnn : 0 ≤ (2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| +
        h * (2 * (C2a c (2 * L) L : ℝ) + 2 * θ * C2b c (2 * L) L) := by
      have hc : 0 ≤ 2 - 2 * Real.cos θ := by linarith [Real.cos_le_one θ]
      have h1 : (0 : ℝ) ≤ C2a c (2 * L) L := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ C2b c (2 * L) L := Nat.cast_nonneg _
      exact add_nonneg (mul_nonneg hc (abs_nonneg _))
        (mul_nonneg hh0.le (add_nonneg (by linarith) (mul_nonneg (by linarith) h2)))
    have key2 := key.trans (mul_le_mul_of_nonneg_right hnorm hnn)
    rw [hpow] at key2
    have hNa : (0 : ℝ) < e.N := by exact_mod_cast hN0
    have hθa : (e.N : ℝ) / D0 ≤ θ := h1.le
    have he2 : (2 * (C2a c (2 * L) L : ℝ) + 2 * θ * C2b c (2 * L) L) / θ ^ 2 ≤ (e.en : ℝ) / D0 := by
      -- decreasing in `θ`, and the check at `θ_a`
      set a := (e.N : ℝ) / D0
      have ha0 : 0 < a := by positivity
      have hC2a : (0 : ℝ) ≤ C2a c (2 * L) L := Nat.cast_nonneg _
      have hC2b : (0 : ℝ) ≤ C2b c (2 * L) L := Nat.cast_nonneg _
      set A := (C2a c (2 * L) L : ℝ)
      set B := (C2b c (2 * L) L : ℝ)
      have hsplit : ∀ t : ℝ, 0 < t → (2 * A + 2 * t * B) / t ^ 2 = 2 * A / t ^ 2 + 2 * B / t := by
        intro t ht; field_simp
      have hdec : (2 * A + 2 * θ * B) / θ ^ 2 ≤ (2 * A + 2 * a * B) / a ^ 2 := by
        rw [hsplit θ hθ0, hsplit a ha0]
        have e1 : 2 * A / θ ^ 2 ≤ 2 * A / a ^ 2 :=
          div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ ha0.le hθa 2)
        have e2 : 2 * B / θ ≤ 2 * B / a :=
          div_le_div_of_nonneg_left (by linarith) ha0 hθa
        linarith
      refine hdec.trans ?_
      have hval : (2 * A + 2 * a * B) / a ^ 2 = (2 * A * D0 ^ 2 + 2 * e.N * B * D0) / (e.N : ℝ) ^ 2 := by
        simp only [a]; field_simp
      rw [hval, div_le_div_iff₀ (by positivity) hD0]
      simp only [A, B]
      linarith [heok']
    calc _ ≤ s ^ 2 * m ^ (-(1 / 2) : ℝ) / θ ^ 2 * ((2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| +
          h * (2 * (C2a c (2 * L) L : ℝ) + 2 * θ * C2b c (2 * L) L)) := key2
      _ = s ^ 2 * m ^ (-(1 / 2) : ℝ) * ((2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| / θ ^ 2 +
          h * ((2 * (C2a c (2 * L) L : ℝ) + 2 * θ * C2b c (2 * L) L) / θ ^ 2)) := by
          field_simp
      _ ≤ _ := by gcongr

/-! ### Chains of checks -/

lemma chainB_sound (P : Ent → Ent → Bool) :
    ∀ L : List Ent, chainB P L = true → List.IsChain (fun a b => P a b = true) L
  | [], _ => List.IsChain.nil
  | [a], _ => List.IsChain.singleton a
  | a :: b :: l, h => by
    simp only [CramerCompute.chainB, Bool.and_eq_true] at h
    exact List.IsChain.cons_cons h.1 (chainB_sound P (b :: l) h.2)

/-- Locating `t ∈ (0, Tₙ]` in a cell. -/
lemma exists_cell (T : ℕ → ℝ) : ∀ n : ℕ, T 0 = 0 → (∀ i, i < n → T i ≤ T (i + 1)) →
    ∀ t : ℝ, 0 < t → t ≤ T n → ∃ i, i < n ∧ T i < t ∧ t ≤ T (i + 1)
  | 0, h0, _, t, ht, htn => by rw [h0] at htn; linarith
  | n + 1, h0, hm, t, ht, htn => by
    by_cases h : t ≤ T n
    · obtain ⟨i, hi, h1, h2⟩ := exists_cell T n h0 (fun i hi => hm i (by omega)) t ht h
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨n, by omega, lt_of_not_ge h, htn⟩

/-- **The zero sum.** -/
theorem zeroSum_le (hRH : RiemannHypothesis) (hR : Schoenfeld.RosserZeroCount)
    (c : ℕ → ℤ) {L D : ℕ} (hc0 : c 0 = 0) (hcJ : ∀ j, 2 * L ≤ j → c j = 0)
    (hsym : ∀ j, j ≤ 2 * L → c (2 * L - j) = c j) (hLD : L ≤ D) {qs : List ℤ} (hqs : qs ≠ [])
    (hcoef : coefOK c (2 * L) L D qs = true) {GD : ℕ} (hGD : 0 < GD) (cells : List Ent)
    (hlen : 2 ≤ cells.length) (hchk : chk qs GD cells = true)
    (heok : chainB (eOK (C1a c (2 * L) L) (C1b c (2 * L) L) (C2a c (2 * L) L) (C2b c (2 * L) L))
      cells = true)
    (hfirst : (cells[0]'(by omega)).N = 0)
    {m s : ℝ} (hm : 0 < m) (hs : 0 < s) (hsmall : ((L : ℝ) + 1) * (s / m) ≤ 1 / 2)
    (h2 : 2 * (s / m) ≤ ((cells[1]'(by omega)).N : ℝ) / D0)
    (h44 : 4.4 * (s / m) ≤ ((cells[cells.length - 1]'(by omega)).N : ℝ) / D0) :
    Summable (fun ρ : Zeros => mult ρ *
        ‖∑ j ∈ range (2 * L + 1), (aco c j : ℂ) * gρ (ρ : ℂ) (tk m s L j)‖) ∧
    ∑' ρ : Zeros, mult ρ * ‖∑ j ∈ range (2 * L + 1), (aco c j : ℂ) * gρ (ρ : ℂ) (tk m s L j)‖ ≤
      s ^ 2 * m ^ (-(1 / 2) : ℝ) * (2 * (
        ∑ i ∈ range (cells.length - 1),
          ((cells.getD i default).Gn / GD + s / m * ((cells.getD i default).en / D0) : ℝ) *
          (N0 (((cells.getD (i + 1) default).N : ℝ) / D0 / (s / m)) -
            N0 (((cells.getD i default).N : ℝ) / D0 / (s / m))) +
        Ero (((cells.getD (cells.length - 1) default).N : ℝ) / D0 / (s / m)) *
          (|((cells.getD 0 default).Gn / GD + s / m * ((cells.getD 0 default).en / D0) : ℝ)| +
           |((cells.getD (cells.length - 1 - 1) default).Gn / GD +
              s / m * ((cells.getD (cells.length - 1 - 1) default).en / D0) : ℝ)| +
           ∑ i ∈ range (cells.length - 1 - 1),
             |((cells.getD (i + 1) default).Gn / GD + s / m * ((cells.getD (i + 1) default).en / D0) : ℝ) -
               ((cells.getD i default).Gn / GD + s / m * ((cells.getD i default).en / D0))|) +
        ((1 + L * (s / m)) ^ (3 / 2 : ℝ) * Asum c (2 * L) / (s / m) ^ 2) *
          (tau (((cells.getD (cells.length - 1) default).N : ℝ) / D0 / (s / m)) /
            (((cells.getD (cells.length - 1) default).N : ℝ) / D0 / (s / m))))) := by
  set h := s / m with hh
  have hh0 : 0 < h := div_pos hs hm
  set n := cells.length - 1 with hn
  have hn1 : 1 ≤ n := by omega
  set d : Ent := default
  set Tf : ℕ → ℝ := fun i => ((cells.getD i d).N : ℝ) / D0 / h
  set Bf : ℕ → ℝ := fun i => (cells.getD i d).Gn / GD + h * ((cells.getD i d).en / D0)
  set Cc : ℝ := (1 + L * h) ^ (3 / 2 : ℝ) * Asum c (2 * L) / h ^ 2
  have hD0 : (0 : ℝ) < D0 := by simp [D0]
  have hGD' : (0 : ℝ) < GD := by exact_mod_cast hGD
  have hchain := chk_sound qs hqs GD hGD cells hchk
  have hechain := chainB_sound _ cells heok
  have hget : ∀ i (hi : i < cells.length), cells.getD i d = cells[i] := fun i hi => by
    rw [List.getD_eq_getElem]
  have hgood : ∀ i, i < n → CellGood qs GD (cells.getD i d) (cells.getD (i + 1) d) := by
    intro i hi
    rw [hget i (by omega), hget (i + 1) (by omega)]
    exact hchain.getElem i (by omega)
  have heg : ∀ i, i < n → eOK (C1a c (2 * L) L) (C1b c (2 * L) L) (C2a c (2 * L) L)
      (C2b c (2 * L) L) (cells.getD i d) (cells.getD (i + 1) d) = true := by
    intro i hi
    rw [hget i (by omega), hget (i + 1) (by omega)]
    exact hechain.getElem i (by omega)
  -- monotonicity of the endpoints (from the position checks)
  have hmonoN : ∀ i, i < n → (cells.getD i d).N ≤ (cells.getD (i + 1) d).N := by
    intro i hi
    have hc := hchk
    -- extract `posOK` from the chain of checks
    have hpos : ∀ L' : List Ent, chk qs GD L' = true → List.IsChain (fun a b => posOK a b = true) L' := by
      intro L'
      induction L' with
      | nil => intro _; exact List.IsChain.nil
      | cons a rest ih =>
        intro h
        cases rest with
        | nil => exact List.IsChain.singleton a
        | cons b rest' =>
          simp only [chk, Bool.and_eq_true] at h
          exact List.IsChain.cons_cons h.1.1.2 (ih h.2)
    have := (hpos cells hc).getElem i (by omega)
    rw [hget i (by omega), hget (i + 1) (by omega)]
    simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  have hT0 : Tf 0 = 0 := by simp only [Tf]; rw [hget 0 (by omega), hfirst]; simp
  have hmono : ∀ i, i < n → Tf i ≤ Tf (i + 1) := by
    intro i hi
    simp only [Tf]
    gcongr
    exact_mod_cast hmonoN i hi
  have hTmono : ∀ i j, i ≤ j → j ≤ n → Tf i ≤ Tf j := by
    intro i j hij hjn
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (ih (by omega)).trans (hmono k (by omega))
  have hT2 : ∀ i, 1 ≤ i → i ≤ n → 2 ≤ Tf i := by
    intro i hi1 hin
    refine le_trans ?_ (hTmono 1 i hi1 hin)
    simp only [Tf]
    rw [hget 1 (by omega), le_div_iff₀ hh0]
    linarith
  have hTn : 4.4 ≤ Tf n := by
    simp only [Tf]
    rw [hget n (by omega), le_div_iff₀ hh0]
    simpa [n] using h44
  have hB : ∀ i, i < n → 0 ≤ Bf i := fun i _ => by simp only [Bf]; positivity
  have hCc : 0 ≤ Cc := by simp only [Cc]; positivity
  -- the per-zero bound
  set f : Zeros → ℝ := fun ρ => ‖∑ j ∈ range (2 * L + 1), (aco c j : ℂ) * gρ (ρ : ℂ) (tk m s L j)‖ /
    (s ^ 2 * m ^ (-(1 / 2) : ℝ))
  have hS : 0 < s ^ 2 * m ^ (-(1 / 2) : ℝ) := by positivity
  have hf0 : ∀ ρ, 0 ≤ f ρ := fun ρ => div_nonneg (norm_nonneg _) hS.le
  have hf : ∀ ρ : Zeros, f ρ ≤ ∑ i ∈ range n, Bf i *
      (if Tf i < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ Tf (i + 1) then 1 else 0) +
      Cc * (if Tf n < |(ρ : ℂ).im| then 1 / (ρ : ℂ).im ^ 2 else 0) := by
    intro ρ
    have hρ := Schoenfeld.re_eq_half hRH ρ
    have hp := Schoenfeld.im_sq_pos hRH ρ
    have hγ : (ρ : ℂ).im ≠ 0 := fun h => by rw [h] at hp; norm_num at hp
    have hγ0 : 0 < |(ρ : ℂ).im| := abs_pos.2 hγ
    have hsumnn : 0 ≤ ∑ i ∈ range n, Bf i *
        (if Tf i < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ Tf (i + 1) then (1 : ℝ) else 0) :=
      sum_nonneg fun i hi => mul_nonneg (hB i (mem_range.1 hi)) (by split_ifs <;> norm_num)
    by_cases htail : Tf n < |(ρ : ℂ).im|
    · -- the trivial bound
      rw [if_pos htail]
      have hLs : (L : ℝ) * s < m := by
        have h1 : ((L : ℝ) + 1) * s ≤ m / 2 := by
          have := mul_le_mul_of_nonneg_right hsmall hm.le
          rw [mul_assoc, div_mul_cancel₀ _ hm.ne'] at this; linarith
        nlinarith
      have key := norm_T_le_trivial hρ hs.le c (le_refl (2 * L)) hLs
      have hnorm := norm_mul_ge_im_sq (ρ := (ρ : ℂ))
      have hA0 : (0 : ℝ) ≤ ∑ j ∈ range (2 * L + 1), |(aco c j : ℝ)| := sum_nonneg fun _ _ => abs_nonneg _
      have hAs : ∑ j ∈ range (2 * L + 1), |(aco c j : ℝ)| = Asum c (2 * L) := by
        unfold Asum; push_cast
        refine sum_congr rfl fun j _ => ?_
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hfb : f ρ ≤ Cc * (1 / (ρ : ℂ).im ^ 2) := by
        simp only [f]
        rw [div_le_iff₀ hS]
        refine key.trans ?_
        rw [hAs]
        have hmL : (m + L * s) ^ (3 / 2 : ℝ) = m ^ (3 / 2 : ℝ) * (1 + L * h) ^ (3 / 2 : ℝ) := by
          rw [← Real.mul_rpow hm.le (by positivity)]; congr 1; simp only [hh]; field_simp
        rw [hmL]
        have hm32 : m ^ (3 / 2 : ℝ) = s ^ 2 * m ^ (-(1 / 2) : ℝ) / h ^ 2 := by
          have : m ^ (3 / 2 : ℝ) = m ^ (-(1 / 2) : ℝ) * m ^ (2 : ℝ) := by
            rw [← Real.rpow_add hm]; norm_num
          rw [this, Real.rpow_two]; simp only [hh]; field_simp
        rw [hm32]
        have hAsn : (0 : ℝ) ≤ Asum c (2 * L) := Nat.cast_nonneg _
        have hγ2 : 0 < (ρ : ℂ).im ^ 2 := hp
        calc s ^ 2 * m ^ (-(1 / 2) : ℝ) / h ^ 2 * (1 + L * h) ^ (3 / 2 : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖ *
              (Asum c (2 * L) : ℝ)
            ≤ s ^ 2 * m ^ (-(1 / 2) : ℝ) / h ^ 2 * (1 + L * h) ^ (3 / 2 : ℝ) / (ρ : ℂ).im ^ 2 *
              (Asum c (2 * L) : ℝ) := by
              gcongr
          _ = Cc * (1 / (ρ : ℂ).im ^ 2) * (s ^ 2 * m ^ (-(1 / 2) : ℝ)) := by
              simp only [Cc]; field_simp
      linarith
    · rw [if_neg htail, mul_zero, add_zero]
      push Not at htail
      obtain ⟨i, hi, hi1, hi2⟩ := exists_cell Tf n hT0 hmono _ hγ0 htail
      have hcell := norm_T_le_cell hρ hγ hm hs c hc0 hcJ hsym hLD hcoef hsmall (hgood i hi)
        (heg i hi) (by simp only [Tf] at hi1; rwa [div_lt_iff₀ hh0] at hi1)
        (by simp only [Tf] at hi2; rwa [le_div_iff₀ hh0] at hi2)
      have hfi : f ρ ≤ Bf i := by
        simp only [f, Bf]
        rw [div_le_iff₀ hS]
        calc _ ≤ _ := hcell
          _ = _ := by ring
      refine hfi.trans ?_
      rw [← sum_erase_add _ _ (mem_range.2 hi), if_pos ⟨hi1, hi2⟩, mul_one]
      have : 0 ≤ ∑ x ∈ (range n).erase i, Bf x *
          (if Tf x < |(ρ : ℂ).im| ∧ |(ρ : ℂ).im| ≤ Tf (x + 1) then (1 : ℝ) else 0) :=
        sum_nonneg fun x hx => mul_nonneg (hB x (mem_range.1 (mem_of_mem_erase hx)))
          (by split_ifs <;> norm_num)
      linarith
  obtain ⟨hsum, hle⟩ := tsum_le_of_step hRH hR hn1 Tf Bf hCc hT0 hT2 hmono hTn hB f hf0 hf
  have hfeq : ∀ ρ : Zeros, mult ρ * ‖∑ j ∈ range (2 * L + 1), (aco c j : ℂ) * gρ (ρ : ℂ) (tk m s L j)‖ =
      (s ^ 2 * m ^ (-(1 / 2) : ℝ)) * (mult ρ * f ρ) := by
    intro ρ; simp only [f]; field_simp
  refine ⟨(hsum.mul_left (s ^ 2 * m ^ (-(1 / 2) : ℝ))).congr fun ρ => (hfeq ρ).symm, ?_⟩
  rw [tsum_congr hfeq, tsum_mul_left]
  refine mul_le_mul_of_nonneg_left (le_trans hle (le_of_eq ?_)) hS.le
  simp only [Bf, Tf, Cc, hn]

end Cramer.CMS
