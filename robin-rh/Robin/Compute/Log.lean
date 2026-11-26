import Mathlib
import RobinCompute.Core

/-!
# Soundness of the fixed-point logarithms and of the bound for Euler's constant

Everything rests on Mathlib's `Real.hasSum_log_one_add_inv`:
`log(1 + 1/a) = Σ_k 2/(2k+1) · (1/(2a+1))^{2k+1}` for `a > 0`. All terms are positive, so
partial sums are lower bounds, and the tail after `J` terms is at most
`2/(2J+1) · z^{2J+1}/(1 − z²)`.
-/

namespace Robin.Compute

open RobinCompute Real Finset

lemma D_pos : (0 : ℝ) < (D : ℝ) := by
  have : 0 < D := by unfold D; positivity
  exact_mod_cast this

lemma XS_pos : (0 : ℝ) < (XS : ℝ) := by
  have : 0 < XS := by unfold XS; positivity
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

/-- `D log(1 + 1/m) ≤ logUpS m 1`. -/
theorem le_logUp1 (m : ℕ) (hm : 0 < m) :
    D * Real.log (1 + 1 / (m : ℝ)) ≤ (logUpS m 1 : ℝ) := by
  have := le_logUpS m 1 hm one_pos; simpa using this

theorem logLo1_le (m : ℕ) (hm : 0 < m) :
    (logLoS m 1 : ℝ) ≤ D * Real.log (1 + 1 / (m : ℝ)) := by
  have := logLoS_le m 1 hm one_pos; simpa using this

theorem log2Lo_le : (log2Lo : ℝ) ≤ D * Real.log 2 := by
  have := logLo1_le 1 one_pos; norm_num at this; unfold log2Lo; norm_num; exact this

theorem le_log2Up : D * Real.log 2 ≤ (log2Up : ℝ) := by
  have := le_logUp1 1 one_pos; norm_num at this; unfold log2Up; norm_num; exact this

lemma log2Floor_go_spec (u v : ℕ) :
    ∀ fuel k, v * 2 ^ k ≤ u → v * 2 ^ (log2Floor.go u v k fuel) ≤ u
  | 0, k, h => by simpa [log2Floor.go] using h
  | fuel + 1, k, h => by
    unfold log2Floor.go
    split_ifs with h1
    · exact log2Floor_go_spec u v fuel (k + 1) h1
    · exact h

lemma log2Floor_spec {u v : ℕ} (h : v ≤ u) : v * 2 ^ (log2Floor u v) ≤ u :=
  log2Floor_go_spec u v 4096 0 (by simpa using h)

/-- The reduction `log(u/v) = k log 2 + log(1 + s/r)`. -/
lemma log_split {u v k : ℕ} (hv : 0 < v) (hk : v * 2 ^ k ≤ u) :
    Real.log ((u : ℝ) / v) =
      k * Real.log 2 + Real.log (1 + ((u - v * 2 ^ k : ℕ) : ℝ) / (v * 2 ^ k : ℕ)) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hr : (0 : ℝ) < (v * 2 ^ k : ℕ) := by push_cast; positivity
  have : (u : ℝ) / v = 2 ^ k * (1 + ((u - v * 2 ^ k : ℕ) : ℝ) / (v * 2 ^ k : ℕ)) := by
    rw [Nat.cast_sub hk]; push_cast; field_simp; ring
  rw [this, Real.log_mul (by positivity) (by
      have : (0 : ℝ) ≤ ((u - v * 2 ^ k : ℕ) : ℝ) / (v * 2 ^ k : ℕ) := by positivity
      linarith), Real.log_pow]

theorem logLoQ_le {u v : ℕ} (hv : 0 < v) (huv : v ≤ u) :
    (logLoQ u v : ℝ) ≤ D * Real.log ((u : ℝ) / v) := by
  have hk := log2Floor_spec huv
  set k := log2Floor u v
  rw [log_split hv hk]
  unfold logLoQ
  simp only [← show k = log2Floor u v from rfl]
  have hl2 := log2Lo_le
  have hkk : (k : ℝ) * log2Lo ≤ k * (D * Real.log 2) :=
    mul_le_mul_of_nonneg_left hl2 (by positivity)
  split_ifs with hs
  · rw [hs]; push_cast; simp; nlinarith
  · have := logLoS_le (v * 2 ^ k) (u - v * 2 ^ k) (by positivity) (by omega)
    push_cast at this ⊢
    nlinarith

theorem le_logUpQ {u v : ℕ} (hv : 0 < v) (huv : v ≤ u) :
    D * Real.log ((u : ℝ) / v) ≤ (logUpQ u v : ℝ) := by
  have hk := log2Floor_spec huv
  set k := log2Floor u v
  rw [log_split hv hk]
  unfold logUpQ
  simp only [← show k = log2Floor u v from rfl]
  have hl2 := le_log2Up
  have hkk : (k : ℝ) * (D * Real.log 2) ≤ k * log2Up :=
    mul_le_mul_of_nonneg_left hl2 (by positivity)
  split_ifs with hs
  · rw [hs]; push_cast; simp; nlinarith
  · have := le_logUpS (v * 2 ^ k) (u - v * 2 ^ k) (by positivity) (by omega)
    push_cast at this ⊢
    nlinarith

theorem logLoNat_le {m : ℕ} (hm : 1 ≤ m) : (logLoNat m : ℝ) ≤ D * Real.log m := by
  unfold logLoNat
  have := logLoQ_le (u := m) (v := 1) one_pos hm; simpa using this

theorem le_logUpNat {m : ℕ} (hm : 1 ≤ m) : D * Real.log m ≤ (logUpNat m : ℝ) := by
  unfold logUpNat
  have := le_logUpQ (u := m) (v := 1) one_pos hm; simpa using this

theorem logLoNatC_le {m : ℕ} (hm : 1 ≤ m) : (logLoNatC m : ℝ) ≤ D * Real.log m := by
  have hk := log2Floor_spec hm
  set k := log2Floor m 1
  have hsplit := log_split (u := m) (v := 1) one_pos hk
  simp only [Nat.cast_one, div_one, one_mul] at hsplit
  rw [hsplit]
  unfold logLoNatC
  simp only [← show k = log2Floor m 1 from rfl]
  have hl2 := log2Lo_le
  have hkk : (k : ℝ) * log2Lo ≤ k * (D * Real.log 2) :=
    mul_le_mul_of_nonneg_left hl2 (by positivity)
  split_ifs with hs
  · have : m - 2 ^ k = 0 := hs
    rw [this]; push_cast; simp; nlinarith
  · have := seriesLo_le_log (2 ^ k) (m - 2 ^ k) 12 (by positivity) (by simp at hk; omega)
    push_cast at this ⊢
    nlinarith

/-- `log log x ≥ logLogLo xn / D` for `x = xn / XS`, when `log x ≥ 1` is certified. -/
theorem logLogLo_le {xn : ℕ} (h1 : XS ≤ xn) (h2 : D ≤ logLoQ xn XS) :
    (logLogLo xn : ℝ) ≤ D * Real.log (Real.log ((xn : ℝ) / XS)) := by
  have hXS : 0 < XS := by unfold XS; positivity
  have hD : 0 < D := by unfold D; positivity
  have hL := logLoQ_le hXS h1
  have hLL := logLoQ_le hD h2
  unfold logLogLo
  refine hLL.trans ?_
  have hD' := D_pos
  have hpos : (0 : ℝ) < (logLoQ xn XS : ℝ) / D := by
    apply div_pos _ hD'
    have : (0 : ℝ) < D := hD'
    have : (D : ℝ) ≤ logLoQ xn XS := by exact_mod_cast h2
    linarith
  apply mul_le_mul_of_nonneg_left _ hD'.le
  apply Real.log_le_log hpos
  rw [div_le_iff₀ hD']
  linarith

/-! ### Euler's constant -/

theorem harmLo_le : ∀ N, (harmLo N : ℝ) ≤ D * (harmonic N : ℝ)
  | 0 => by simp [harmLo]
  | N + 1 => by
    rw [harmLo, harmonic_succ]
    push_cast
    have := harmLo_le N
    have h2 := div_le' D (N + 1)
    push_cast at h2
    have : (D : ℝ) / (N + 1) = D * (N + 1 : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    nlinarith

theorem harmAux_eq : ∀ N acc, harmAux N acc = acc + harmLo N
  | 0, acc => by simp [harmAux, harmLo]
  | N + 1, acc => by rw [harmAux, harmAux_eq N, harmLo]; ring

/-- `a_n = H_n − log n − 1/(2n)` is increasing: the trapezoid rule for `∫ dt/t`. -/
lemma log_one_add_inv_le_trap {n : ℕ} (hn : 0 < n) :
    Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (2 * n) + 1 / (2 * (n + 1)) := by
  have h := log_le_sum_tail n 1 1 hn one_pos
  simp only [Finset.range_one, Finset.sum_singleton, sterm] at h
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h
  set z : ℝ := 1 / (2 * n + 1) with hz
  have hz0 : 0 < z := by positivity
  have hz1 : z < 1 := by rw [hz, div_lt_one (by positivity)]; linarith
  have hz2 : 0 < 1 - z ^ 2 := by nlinarith
  have hid : 1 / (2 * (n : ℝ)) + 1 / (2 * (n + 1)) = 2 * z / (1 - z ^ 2) := by
    have e : 1 - z ^ 2 = 4 * n * (n + 1) / (2 * n + 1) ^ 2 := by
      rw [hz]; field_simp; ring
    rw [e, hz]; field_simp; ring
  rw [hid]
  have key : 2 * z + 2 * (1 / 3) * z ^ 3 / (1 - z ^ 2) ≤ 2 * z / (1 - z ^ 2) := by
    rw [add_div' _ _ _ hz2.ne', div_le_div_iff_of_pos_right hz2]
    nlinarith [pow_pos hz0 3]
  norm_num at h
  norm_num
  linarith

noncomputable def emSeq2 (n : ℕ) : ℝ := (harmonic n : ℝ) - Real.log n - 1 / (2 * n)

lemma emSeq2_mono : ∀ n, 1 ≤ n → emSeq2 n ≤ emSeq2 (n + 1) := by
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := log_one_add_inv_le_trap (n := n) (by omega)
  unfold emSeq2
  rw [harmonic_succ]
  push_cast
  have hlog : Real.log ((n : ℝ) + 1) = Real.log n + Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_mul hn'.ne' (by positivity)]; congr 1; field_simp
  rw [hlog]
  have : ((n : ℝ) + 1)⁻¹ = 1 / (n + 1) := by rw [one_div]
  rw [this]
  have e : 1 / ((n : ℝ) + 1) - 1 / (2 * (n + 1)) = 1 / (2 * (n + 1)) := by field_simp; ring
  linarith

lemma emSeq2_le_gamma {N : ℕ} (hN : 1 ≤ N) : emSeq2 N ≤ Real.eulerMascheroniConstant := by
  have hmono : Monotone (fun k : ℕ => emSeq2 (k + N)) := by
    apply monotone_nat_of_le_succ
    intro k
    have := emSeq2_mono (k + N) (by omega)
    simpa [Nat.add_right_comm] using this
  have hlim : Filter.Tendsto (fun k : ℕ => emSeq2 (k + N)) Filter.atTop
      (nhds Real.eulerMascheroniConstant) := by
    have h1 := Real.tendsto_harmonic_sub_log
    have h2 : Filter.Tendsto (fun k : ℕ => 1 / (2 * (k : ℝ))) Filter.atTop (nhds 0) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
      simp at h
      refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
      field_simp
    have h3 := (h1.sub h2)
    simp only [sub_zero] at h3
    have h4 := h3.comp (Filter.tendsto_add_atTop_nat N)
    refine h4.congr' (Filter.Eventually.of_forall fun k => ?_)
    simp [emSeq2, Function.comp]
  have := hmono.ge_of_tendsto hlim 0
  simpa using this

theorem gammaLoOf_le {N : ℕ} (hN : 1 ≤ N) :
    ((gammaLoOf N : ℤ) : ℝ) ≤ D * Real.eulerMascheroniConstant := by
  have h1 := harmLo_le N
  have h2 := le_logUpNat hN
  have hN' : 0 < 2 * N := by omega
  have h3 := le_cdiv D (2 * N) hN'
  have h4 := emSeq2_le_gamma hN
  unfold emSeq2 at h4
  unfold gammaLoOf
  rw [show harmAux N 0 = harmLo N by rw [harmAux_eq]; simp]
  push_cast
  have hD := D_pos
  have : (D : ℝ) / (2 * N : ℕ) = D * (1 / (2 * N)) := by push_cast; ring
  rw [this] at h3
  nlinarith

end Robin.Compute
