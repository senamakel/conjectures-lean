import Mathlib
import SchoenfeldCompute.Psi

/-!
# Soundness of the fixed-point logarithms

Copied from robin-rh (`Robin/Compute/Log.lean` at `343518c`, same authors), restricted to
`logLoS` and `logUpS`. Everything rests on Mathlib's `Real.hasSum_log_one_add_inv`:
`log(1 + 1/a) = Σ_k 2/(2k+1) · (1/(2a+1))^{2k+1}` for `a > 0`. All terms are positive, so
partial sums are lower bounds, and the tail after `J` terms is at most
`2/(2J+1) · z^{2J+1}/(1 − z²)`.
-/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute Real Finset

lemma D_pos : (0 : ℝ) < (D : ℝ) := by
  have : 0 < D := by unfold D; positivity
  exact_mod_cast this
/-- `a/b ≤ ⌈a/b⌉`. -/
lemma le_cdiv (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  have h : a ≤ cdiv a b * b := by
    unfold cdiv
    have h1 := Nat.div_add_mod (a + b - 1) b
    have h2 := Nat.mod_lt (a + b - 1) hb
    rw [Nat.mul_comm] at h1
    generalize (a + b - 1) / b * b = X at h1 ⊢
    omega
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast h

/-- `⌊a/b⌋ ≤ a/b`. -/
lemma div_le' (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

/-- The series term `2/(2k+1) z^{2k+1}`. -/
noncomputable def sterm (z : ℝ) (k : ℕ) : ℝ := 2 * (1 / (2 * k + 1)) * z ^ (2 * k + 1)

lemma sterm_nonneg {z : ℝ} (hz : 0 ≤ z) (k : ℕ) : 0 ≤ sterm z k := by
  unfold sterm; positivity

lemma term_div_eq (p q k : ℕ) (hq : 0 < q) :
    ((termNum p k : ℕ) : ℝ) / (termDen q k : ℕ) = D * sterm ((p : ℝ) / q) k := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold termNum termDen sterm
  push_cast
  rw [div_pow]
  field_simp

lemma seriesLo_le_sum (p q : ℕ) (hq : 0 < q) :
    ∀ J, (seriesLo p q J : ℝ) ≤ D * ∑ k ∈ range J, sterm ((p : ℝ) / q) k
  | 0 => by simp [seriesLo]
  | J + 1 => by
    rw [seriesLo, Finset.sum_range_succ, mul_add]
    push_cast
    have := seriesLo_le_sum p q hq J
    have h2 := div_le' (termNum p J) (termDen q J)
    rw [term_div_eq p q J hq] at h2
    linarith

lemma sum_le_seriesUpPart (p q : ℕ) (hq : 0 < q) :
    ∀ J, D * ∑ k ∈ range J, sterm ((p : ℝ) / q) k ≤ (seriesUpPart p q J : ℝ)
  | 0 => by simp [seriesUpPart]
  | J + 1 => by
    rw [seriesUpPart, Finset.sum_range_succ, mul_add]
    push_cast
    have := sum_le_seriesUpPart p q hq J
    have hd : 0 < termDen q J := by unfold termDen; positivity
    have h2 := le_cdiv (termNum p J) (termDen q J) hd
    rw [term_div_eq p q J hq] at h2
    linarith

/-- The series for `log(1 + 1/a)` in our variables. -/
lemma hasSum_log (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    HasSum (sterm ((s : ℝ) / (2 * r + s : ℕ))) (Real.log (1 + (s : ℝ) / r)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h := Real.hasSum_log_one_add_inv (a := (r : ℝ) / s) (div_pos hr' hs')
  have hz : (1 : ℝ) / (2 * ((r : ℝ) / s) + 1) = (s : ℝ) / (2 * r + s : ℕ) := by
    push_cast; field_simp
  have ha : ((r : ℝ) / s)⁻¹ = (s : ℝ) / r := by rw [inv_div]
  rw [hz, ha] at h
  exact h

lemma z_lt_one (r s : ℕ) (hr : 0 < r) :
    (s : ℝ) / (2 * r + s : ℕ) < 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_lt_one (by push_cast; positivity)]
  push_cast; linarith

theorem seriesLo_le_log (r s J : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (seriesLo s (2 * r + s) J : ℝ) ≤ D * Real.log (1 + (s : ℝ) / r) := by
  have hq : 0 < 2 * r + s := by omega
  have h1 := seriesLo_le_sum s (2 * r + s) hq J
  have h2 : ∑ k ∈ range J, sterm ((s : ℝ) / (2 * r + s : ℕ)) k ≤ Real.log (1 + (s : ℝ) / r) :=
    sum_le_hasSum _ (fun k _ => sterm_nonneg (by positivity) k) (hasSum_log r s hr hs)
  nlinarith [D_pos]

/-- Tail bound: `log(1 + s/r) ≤ Σ_{k<J} t_k + 2/(2J+1) z^{2J+1}/(1−z²)`. -/
theorem log_le_sum_tail (r s J : ℕ) (hr : 0 < r) (hs : 0 < s) :
    Real.log (1 + (s : ℝ) / r) ≤
      ∑ k ∈ range J, sterm ((s : ℝ) / (2 * r + s : ℕ)) k +
        2 * (1 / (2 * J + 1)) * ((s : ℝ) / (2 * r + s : ℕ)) ^ (2 * J + 1) /
          (1 - ((s : ℝ) / (2 * r + s : ℕ)) ^ 2) := by
  set z := (s : ℝ) / (2 * r + s : ℕ) with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z < 1 := z_lt_one r s hr
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hH := hasSum_log r s hr hs
  rw [← hzdef] at hH
  have hsum := hH.summable
  rw [← hH.tsum_eq, ← hsum.sum_add_tsum_nat_add J]
  gcongr
  have hg : HasSum (fun k : ℕ => 2 * (1 / (2 * J + 1)) * z ^ (2 * J + 1) * (z ^ 2) ^ k)
      (2 * (1 / (2 * J + 1)) * z ^ (2 * J + 1) * (1 - z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hz2).mul_left _
  rw [div_eq_mul_inv]
  refine (hsum.comp_injective (add_left_injective J)).tsum_le_tsum ?_ hg.summable |>.trans
    hg.tsum_eq.le
  intro k
  simp only [Function.comp, sterm]
  have hk : (1 : ℝ) / (2 * ((k + J : ℕ) : ℝ) + 1) ≤ 1 / (2 * J + 1) := by
    apply one_div_le_one_div_of_le (by positivity); push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hp : z ^ (2 * (k + J) + 1) = z ^ (2 * J + 1) * (z ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [hp]
  have : 0 ≤ z ^ (2 * J + 1) * (z ^ 2) ^ k := by positivity
  nlinarith

theorem log_le_seriesUp (r s J : ℕ) (hr : 0 < r) (hs : 0 < s) :
    D * Real.log (1 + (s : ℝ) / r) ≤ (seriesUp s (2 * r + s) J : ℝ) := by
  have hq : 0 < 2 * r + s := by omega
  have hz1 := z_lt_one r s hr
  set q := 2 * r + s with hqdef
  have hsq : s ^ 2 < q ^ 2 := by
    have : s < q := by omega
    exact Nat.pow_lt_pow_left this (by norm_num)
  have hden : 0 < termDen q J * (q ^ 2 - s ^ 2) := by
    unfold termDen; have : 0 < q ^ 2 - s ^ 2 := by omega
    positivity
  have h1 := sum_le_seriesUpPart s q hq J
  have h2 := le_cdiv (termNum s J * q ^ 2) (termDen q J * (q ^ 2 - s ^ 2)) hden
  have h3 := log_le_sum_tail r s J hr hs
  rw [← hqdef] at h3
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have htail : ((termNum s J * q ^ 2 : ℕ) : ℝ) / (termDen q J * (q ^ 2 - s ^ 2) : ℕ) =
      D * (2 * (1 / (2 * J + 1)) * ((s : ℝ) / q) ^ (2 * J + 1) / (1 - ((s : ℝ) / q) ^ 2)) := by
    have hsq' : ((q ^ 2 - s ^ 2 : ℕ) : ℝ) = (q : ℝ) ^ 2 - (s : ℝ) ^ 2 := by
      rw [Nat.cast_sub hsq.le]; push_cast; ring
    have hne : (q : ℝ) ^ 2 - (s : ℝ) ^ 2 ≠ 0 := by
      have : (s : ℝ) ^ 2 < (q : ℝ) ^ 2 := by exact_mod_cast hsq
      linarith
    have hne' : 1 - ((s : ℝ) / q) ^ 2 ≠ 0 := by
      rw [div_pow, one_sub_div (by positivity)]; exact div_ne_zero hne (by positivity)
    have hq2 : (q : ℝ) ^ 2 ≠ 0 := by positivity
    have e1 : 1 - ((s : ℝ) / q) ^ 2 = ((q : ℝ) ^ 2 - (s : ℝ) ^ 2) / (q : ℝ) ^ 2 := by
      field_simp
    rw [Nat.cast_mul, Nat.cast_mul, hsq', e1, div_pow]
    unfold termNum termDen
    push_cast
    field_simp
  unfold seriesUp
  push_cast
  rw [htail] at h2
  nlinarith [D_pos]

theorem logLoS_le (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (logLoS r s : ℝ) ≤ D * Real.log (1 + (s : ℝ) / r) :=
  seriesLo_le_log r s _ hr hs

theorem le_logUpS (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    D * Real.log (1 + (s : ℝ) / r) ≤ (logUpS r s : ℝ) :=
  log_le_seriesUp r s _ hr hs

end Schoenfeld.PsiCert
