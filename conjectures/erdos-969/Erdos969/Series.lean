import Erdos969.Statement
import Mertens.Abel

/-!
# The Dirichlet series for `1/ζ(2)` and its tail, from a Mertens bound

* `hasSum_moebius_sq`: `∑ μ(n)/n² = 6/π²`.
* `sum_rpow_neg_le`, `sum_rpow_neg_le_of_gt`: sums of negative powers against integrals.
* `abs_tail_le`: if `|M(k)| ≤ K (k+1)^α` with `0 ≤ α < 2`, then the tail
  `|6/π² - ∑_{d ≤ Y} μ(d)/d²|` is at most `C Y^{α-2}` (Abel summation).
-/

namespace Erdos969

open Finset ArithmeticFunction LSeries Nat Complex
open scoped LSeries.notation ArithmeticFunction.Moebius ArithmeticFunction.zeta

theorem hasSum_moebius_sq :
    HasSum (fun n : ℕ => (μ n : ℝ) / ((n : ℝ) ^ 2)) (6 / Real.pi ^ 2) := by
  have hsum : LSeriesSummable ↗μ 2 := LSeriesSummable_moebius_iff.2 (by simp)
  have h := hsum.LSeriesHasSum
  have hz : L ↗ζ 2 = (Real.pi : ℂ) ^ 2 / 6 := by
    rw [LSeries_zeta_eq_riemannZeta (by norm_num)]; exact riemannZeta_two
  have hmul := LSeries_zeta_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [hz] at hmul
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hL : L ↗μ 2 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
    linear_combination 6 * hmul
  rw [hL] at h
  have : ∀ n : ℕ, LSeries.term ↗μ 2 n = (((μ n : ℝ) / ((n : ℝ) ^ 2) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      rw [Complex.cpow_ofNat]
  have h' : HasSum (fun n : ℕ => (((μ n : ℝ) / ((n : ℝ) ^ 2) : ℝ) : ℂ)) ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    have e : (fun n : ℕ => (((μ n : ℝ) / ((n : ℝ) ^ 2) : ℝ) : ℂ)) = LSeries.term ↗μ 2 :=
      (funext this).symm
    rw [e]; exact h
  exact Complex.hasSum_ofReal.1 h'


lemma sum_rpow_neg_le {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (X : ℕ) :
    ∑ m ∈ range X, ((m : ℝ) + 1) ^ (-β) ≤ (X : ℝ) ^ (1 - β) / (1 - β) := by
  have hb : 0 < 1 - β := by linarith
  induction X with
  | zero => simp [Real.zero_rpow hb.ne']
  | succ X ih =>
    rw [sum_range_succ]
    have hX : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    have ht : (0 : ℝ) < (X : ℝ) + 1 := by positivity
    have e : (X : ℝ) = ((X : ℝ) + 1) * (1 + (-1 / ((X : ℝ) + 1))) := by field_simp; ring
    have hs : (-1 : ℝ) ≤ -1 / ((X : ℝ) + 1) := by
      rw [neg_div, neg_le_neg_iff, div_le_one ht]; linarith
    set t : ℝ := (X : ℝ) + 1 with htdef
    have h1s : 0 ≤ 1 + (-1 / t) := by linarith
    have key : (X : ℝ) ^ (1 - β) ≤ t ^ (1 - β) * (1 - (1 - β) / t) := by
      calc (X : ℝ) ^ (1 - β) = (t * (1 + (-1 / t))) ^ (1 - β) := by rw [← e]
        _ = t ^ (1 - β) * (1 + (-1 / t)) ^ (1 - β) := Real.mul_rpow ht.le h1s
        _ ≤ t ^ (1 - β) * (1 + (1 - β) * (-1 / t)) :=
          mul_le_mul_of_nonneg_left (rpow_one_add_le_one_add_mul_self hs (by linarith) (by linarith)) (by positivity)
        _ = t ^ (1 - β) * (1 - (1 - β) / t) := by ring
    have hpow : t ^ (-β) = t ^ (1 - β) / t := by
      rw [← Real.rpow_sub_one ht.ne']; ring_nf
    have : t ^ (-β) ≤ (t ^ (1 - β) - (X : ℝ) ^ (1 - β)) / (1 - β) := by
      rw [le_div_iff₀ hb, hpow]
      have : t ^ (1 - β) / t * (1 - β) = t ^ (1 - β) * ((1 - β) / t) := by ring
      rw [this]; nlinarith [key]
    have ih' := ih
    calc ∑ m ∈ range X, ((m : ℝ) + 1) ^ (-β) + ((X : ℝ) + 1) ^ (-β)
        ≤ (X : ℝ) ^ (1 - β) / (1 - β) + (t ^ (1 - β) - (X : ℝ) ^ (1 - β)) / (1 - β) := add_le_add ih' this
      _ = ((X + 1 : ℕ) : ℝ) ^ (1 - β) / (1 - β) := by push_cast; ring

lemma sum_rpow_neg_le_of_gt {γ : ℝ} (hγ : 1 < γ) (Y : ℕ) (hY : 1 ≤ Y) (N : ℕ) :
    ∑ n ∈ range N, ((Y : ℝ) + n + 1) ^ (-γ) ≤ (Y : ℝ) ^ (1 - γ) / (γ - 1) := by
  have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-γ)) (Set.Icc (Y : ℝ) (Y + N)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
  have h := hanti.sum_le_integral
  have hint : ∫ x in (Y : ℝ)..(Y + N), x ^ (-γ) = ((Y + N : ℝ) ^ (-γ + 1) - (Y : ℝ) ^ (-γ + 1)) / (-γ + 1) := by
    apply integral_rpow
    right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])]
    intro hm; linarith [hm.1]
  rw [hint] at h
  calc ∑ n ∈ range N, ((Y : ℝ) + n + 1) ^ (-γ)
      = ∑ i ∈ range N, (fun x : ℝ => x ^ (-γ)) ((Y : ℝ) + ↑(i + 1)) := by
        refine sum_congr rfl fun i _ => ?_; push_cast; ring_nf
    _ ≤ _ := h
    _ ≤ (Y : ℝ) ^ (1 - γ) / (γ - 1) := by
      have hpos : 0 ≤ ((Y : ℝ) + N) ^ (-γ + 1) := by positivity
      have : ((Y + N : ℝ) ^ (-γ + 1) - (Y : ℝ) ^ (-γ + 1)) / (-γ + 1)
          = ((Y : ℝ) ^ (-γ + 1) - (Y + N : ℝ) ^ (-γ + 1)) / (γ - 1) := by
        rw [← neg_div_neg_eq]; ring_nf
      rw [this, show 1 - γ = -γ + 1 by ring]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Partial sums of the Möbius function: `M(k) = ∑_{d ≤ k} μ(d)`. -/
noncomputable def Mr (k : ℕ) : ℝ := ∑ d ∈ range (k + 1), (μ d : ℝ)

/-- A polynomial bound on the Mertens function. -/
def MBound (K α : ℝ) : Prop := ∀ k : ℕ, |Mr k| ≤ K * ((k : ℝ) + 1) ^ α

lemma abs_Mr_sub_le {K α : ℝ} (hα : 0 ≤ α) (hM : MBound K α) (Y n : ℕ) :
    |Mr (Y + n + 1) - Mr Y| ≤ 2 * K * ((Y : ℝ) + n + 2) ^ α := by
  have h1 := hM (Y + n + 1)
  have h2 := hM Y
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have e1 : ((Y + n + 1 : ℕ) : ℝ) + 1 = (Y : ℝ) + n + 2 := by push_cast; ring
  rw [e1] at h1
  have h3 : ((Y : ℝ) + 1) ^ α ≤ ((Y : ℝ) + n + 2) ^ α :=
    Real.rpow_le_rpow (by positivity) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hα
  calc |Mr (Y + n + 1) - Mr Y| ≤ |Mr (Y + n + 1)| + |Mr Y| := abs_sub _ _
    _ ≤ K * ((Y : ℝ) + n + 2) ^ α + K * ((Y : ℝ) + 1) ^ α := add_le_add h1 h2
    _ ≤ K * ((Y : ℝ) + n + 2) ^ α + K * ((Y : ℝ) + n + 2) ^ α := by
        gcongr
    _ = 2 * K * ((Y : ℝ) + n + 2) ^ α := by ring


lemma abs_Mr_sub_le' {K α : ℝ} (hα : 0 ≤ α) (hM : MBound K α) (Y n : ℕ) :
    |Mr (Y + n + 1) - Mr Y| ≤ 2 * K * 2 ^ α * ((Y : ℝ) + n + 1) ^ α := by
  have h := abs_Mr_sub_le hα hM Y n
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have hu : (0 : ℝ) ≤ (Y : ℝ) + n + 1 := by positivity
  have : ((Y : ℝ) + n + 2) ^ α ≤ 2 ^ α * ((Y : ℝ) + n + 1) ^ α := by
    rw [← Real.mul_rpow (by norm_num) hu]
    refine Real.rpow_le_rpow (by positivity) ?_ hα
    nlinarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ Y), (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  calc _ ≤ 2 * K * ((Y : ℝ) + n + 2) ^ α := h
    _ ≤ 2 * K * (2 ^ α * ((Y : ℝ) + n + 1) ^ α) := by gcongr
    _ = _ := by ring

lemma abs_weight_diff_le (u : ℝ) (hu : 1 ≤ u) :
    |1 / (u + 1) ^ 2 - 1 / u ^ 2| ≤ 3 / u ^ 3 := by
  have h0 : 0 < u := by linarith
  have : 1 / (u + 1) ^ 2 - 1 / u ^ 2 ≤ 0 := by
    rw [sub_nonpos]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  rw [abs_of_nonpos this, neg_sub, div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, mul_pos h0 h0, pow_pos h0 6]

/-- The tail of the series for `1/ζ(2) = 6/π²`, from a Mertens bound. -/
theorem abs_tail_le {K α : ℝ} (hα0 : 0 ≤ α) (hα2 : α < 2) (hM : MBound K α) {Y : ℕ} (hY : 1 ≤ Y) :
    |6 / Real.pi ^ 2 - ∑ d ∈ Icc 1 Y, (μ d : ℝ) / ((d : ℝ) ^ 2)| ≤
      (2 * K * 2 ^ α * (1 + 3 / (2 - α))) * (Y : ℝ) ^ (α - 2) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Mr 0)).trans (hM 0); simpa using this
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  set K1 : ℝ := 2 * K * 2 ^ α with hK1
  have hK1' : 0 ≤ K1 := by positivity
  set c : ℕ → ℝ := fun k => (μ (Y + 1 + k) : ℝ) with hc
  set w : ℕ → ℝ := fun k => 1 / (((Y + 1 + k : ℕ) : ℝ)) ^ 2 with hw
  set a : ℕ → ℝ := fun d => (μ d : ℝ) / ((d : ℝ) ^ 2) with ha
  have hB : ∀ n, ∑ k ∈ range (n + 1), c k = Mr (Y + n + 1) - Mr Y := by
    intro n
    unfold Mr
    have : Y + n + 1 + 1 = (Y + 1) + (n + 1) := by omega
    rw [this, sum_range_add (fun x => (μ x : ℝ)) (Y + 1) (n + 1)]; simp only [hc]; ring
  have hcw : ∀ k, c k * w k = a (Y + 1 + k) := by
    intro k; simp only [hc, hw, ha]; rw [mul_one_div]
  -- the bound for each partial sum
  have hpart : ∀ N : ℕ, |∑ k ∈ range (N + 1), a (Y + 1 + k)| ≤
      K1 * (1 + 3 / (2 - α)) * (Y : ℝ) ^ (α - 2) := by
    intro N
    have hab := Mertens.abel_identity c w N
    rw [show ∑ k ∈ range (N + 1), a (Y + 1 + k) = ∑ k ∈ range (N + 1), c k * w k from
      sum_congr rfl fun k _ => (hcw k).symm, hab]
    have hu : ∀ n : ℕ, (1 : ℝ) ≤ (Y : ℝ) + n + 1 := fun n => by
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hw0 : ∀ n : ℕ, w n = 1 / ((Y : ℝ) + n + 1) ^ 2 := fun n => by
      simp only [hw]; push_cast; ring_nf
    have hwd : ∀ n : ℕ, |w (n + 1) - w n| ≤ 3 / ((Y : ℝ) + n + 1) ^ 3 := fun n => by
      have : w (n + 1) = 1 / (((Y : ℝ) + n + 1) + 1) ^ 2 := by
        simp only [hw]; push_cast; ring_nf
      rw [this, hw0 n]; exact abs_weight_diff_le _ (hu n)
    have hterm : ∀ n : ℕ, |(∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n)| ≤
        3 * K1 * ((Y : ℝ) + n + 1) ^ (-(3 - α)) := fun n => by
      have hpos : 0 < (Y : ℝ) + n + 1 := by linarith [hu n]
      rw [abs_mul, hB n]
      have h1 := abs_Mr_sub_le' hα0 hM Y n
      have h2 := hwd n
      calc |Mr (Y + n + 1) - Mr Y| * |w (n + 1) - w n|
          ≤ (K1 * ((Y : ℝ) + n + 1) ^ α) * (3 / ((Y : ℝ) + n + 1) ^ 3) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 3 * K1 * ((Y : ℝ) + n + 1) ^ (-(3 - α)) := by
            rw [show -(3 - α) = α - (3 : ℕ) by push_cast; ring, Real.rpow_sub hpos, Real.rpow_natCast]
            ring
    have hfirst : |(∑ k ∈ range (N + 1), c k) * w N| ≤ K1 * (Y : ℝ) ^ (α - 2) := by
      have hpos : 0 < (Y : ℝ) + N + 1 := by linarith [hu N]
      rw [abs_mul, hB N, hw0 N, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((Y : ℝ) + N + 1) ^ 2)]
      calc |Mr (Y + N + 1) - Mr Y| * (1 / ((Y : ℝ) + N + 1) ^ 2)
          ≤ (K1 * ((Y : ℝ) + N + 1) ^ α) * (1 / ((Y : ℝ) + N + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right (abs_Mr_sub_le' hα0 hM Y N) (by positivity)
        _ = K1 * ((Y : ℝ) + N + 1) ^ (α - 2) := by
            rw [show α - 2 = α - ((2 : ℕ) : ℝ) by norm_num, Real.rpow_sub hpos, Real.rpow_natCast]
            ring
        _ ≤ K1 * (Y : ℝ) ^ (α - 2) := by
            exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < Y)
              (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)] : (Y : ℝ) ≤ (Y : ℝ) + N + 1)
              (by linarith : α - 2 ≤ 0)) hK1'
    have hsum : |∑ n ∈ range N, (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n)| ≤
        3 * K1 / (2 - α) * (Y : ℝ) ^ (α - 2) := by
      calc _ ≤ ∑ n ∈ range N, |(∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n)| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ range N, 3 * K1 * ((Y : ℝ) + n + 1) ^ (-(3 - α)) := sum_le_sum fun n _ => hterm n
        _ = 3 * K1 * ∑ n ∈ range N, ((Y : ℝ) + n + 1) ^ (-(3 - α)) := by rw [mul_sum]
        _ ≤ 3 * K1 * ((Y : ℝ) ^ (1 - (3 - α)) / ((3 - α) - 1)) :=
            mul_le_mul_of_nonneg_left (sum_rpow_neg_le_of_gt (by linarith) Y hY N) (by positivity)
        _ = 3 * K1 / (2 - α) * (Y : ℝ) ^ (α - 2) := by
            rw [show 1 - (3 - α) = α - 2 by ring, show (3 - α) - 1 = 2 - α by ring]; ring
    calc |(∑ k ∈ range (N + 1), c k) * w N - ∑ n ∈ range N, (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n)|
        ≤ |(∑ k ∈ range (N + 1), c k) * w N| + |∑ n ∈ range N, (∑ k ∈ range (n + 1), c k) * (w (n + 1) - w n)| := abs_sub _ _
      _ ≤ K1 * (Y : ℝ) ^ (α - 2) + 3 * K1 / (2 - α) * (Y : ℝ) ^ (α - 2) := add_le_add hfirst hsum
      _ = K1 * (1 + 3 / (2 - α)) * (Y : ℝ) ^ (α - 2) := by ring
  -- pass to the limit
  have hS := hasSum_moebius_sq.tendsto_sum_nat
  have hSY : ∑ d ∈ Icc 1 Y, a d = ∑ d ∈ range (Y + 1), a d := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    simp [ha]
    rfl
  rw [hSY]
  have hlim : Filter.Tendsto (fun N : ℕ => ∑ d ∈ range (Y + 1 + (N + 1)), a d) Filter.atTop
      (nhds (6 / Real.pi ^ 2)) :=
    hS.comp (Filter.tendsto_atTop_mono (fun N : ℕ => (by omega : N ≤ Y + 1 + (N + 1))) Filter.tendsto_id)
  have h2 : Filter.Tendsto (fun N : ℕ => |∑ d ∈ range (Y + 1 + (N + 1)), a d - ∑ d ∈ range (Y + 1), a d|)
      Filter.atTop (nhds |6 / Real.pi ^ 2 - ∑ d ∈ range (Y + 1), a d|) :=
    (hlim.sub_const _).abs
  refine le_of_tendsto' h2 fun N => ?_
  have h3 := hpart N
  have h4 := sum_range_add a (Y + 1) (N + 1)
  rw [h4]
  simpa using h3


end Erdos969
