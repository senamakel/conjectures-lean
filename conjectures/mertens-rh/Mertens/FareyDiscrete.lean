import Mertens.FareyCount
import Mertens.FareyIntegral

/-!
# From the Farey discrepancy to `∫₀¹ G²`

With `c_q = M(N/q)` and `G(x) = ∑_{q ≤ N} c_q {q x}`:

* `G_eq`: for `0 ≤ x ≤ 1`, `G(x) = A x − #{f ∈ F_N : f ≤ x}` (counting identity, `A = |F_N|`).
* `fareyFrac_sub_eq`: `f_k − k/A = G(f_k)/A`, since `f_k` has rank `k`.
* `sum_G_sq_le`: `∑_{f ∈ F_N} G(f)² ≤ 3N² ∫₀¹ G² + 3A(A²/N⁴ + 1)`. Just left of a Farey
  fraction `f`, on `[f − 1/N², f)`, there is no other Farey fraction (they are `1/N²` apart), so
  `G` is linear there with slope `A` and `G(f) = G(x) + A(f − x) − 1`.
-/

namespace Mertens

open Finset MeasureTheory intervalIntegral

/-- `c_q = M(N/q)`. -/
noncomputable def fc (N q : ℕ) : ℝ := (mertens (N / q : ℕ) : ℝ)

/-- `G(x) = ∑_{q ≤ N} M(N/q) {q x}`. -/
noncomputable def fareyG (N : ℕ) (x : ℝ) : ℝ := ∑ q ∈ Ioc 0 N, fc N q * Int.fract ((q : ℝ) * x)

/-- `#{f ∈ F_N : f ≤ x}`. -/
noncomputable def fareyCount (N : ℕ) (x : ℝ) : ℕ :=
  ((farey N).filter (fun f : ℚ => (f : ℝ) ≤ x)).card

lemma fareyCount_real (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (fareyCount N x : ℝ) = ∑ q ∈ Ioc 0 N, (⌊(q : ℝ) * x⌋₊ : ℝ) * fc N q := by
  have h := fareyCount_eq (N := N) hx0 hx1
  have h' : ((fareyCount N x : ℤ) : ℝ) = (((∑ q ∈ Ioc 0 N,
      (⌊(q : ℝ) * x⌋₊ : ℤ) * mertens (N / q : ℕ)) : ℤ) : ℝ) := by
    rw [fareyCount, h]
  push_cast at h'
  rw [h']
  rfl

lemma fareyCount_one (N : ℕ) : fareyCount N 1 = (farey N).card := by
  rw [fareyCount]
  congr 1
  refine filter_true_of_mem fun f hf => ?_
  have := (mem_farey.1 hf).2.1
  exact_mod_cast this

/-- `A = ∑_{q ≤ N} q M(N/q)`. -/
lemma card_farey_eq (N : ℕ) : ((farey N).card : ℝ) = ∑ q ∈ Ioc 0 N, (q : ℝ) * fc N q := by
  rw [← fareyCount_one, fareyCount_real N zero_le_one le_rfl]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_one, Nat.floor_natCast]

/-- `G(x) = A x − #{f ≤ x}` on `[0, 1]`. -/
lemma G_eq (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    fareyG N x = (farey N).card * x - fareyCount N x := by
  rw [fareyCount_real N hx0 hx1, card_farey_eq, sum_mul, ← sum_sub_distrib, fareyG]
  refine sum_congr rfl fun q _ => ?_
  have hqx : 0 ≤ (q : ℝ) * x := by positivity
  rw [Int.fract, ← natCast_floor_eq_intCast_floor hqx]
  ring

/-- The `(i+1)`-st Farey fraction has rank `i + 1`. -/
lemma card_filter_le_fareyFrac (N : ℕ) (i : Fin (farey N).card) :
    ((farey N).filter (fun f : ℚ => f ≤ fareyFrac N i)).card = (i : ℕ) + 1 := by
  set e := (farey N).orderEmbOfFin rfl
  have hset : (farey N).filter (fun f : ℚ => f ≤ fareyFrac N i) = (Iic i).map e.toEmbedding := by
    ext f
    rw [mem_filter, mem_map]
    simp only [mem_Iic, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hf, hle⟩
      have : f ∈ Set.range e := by rw [range_orderEmbOfFin]; exact hf
      obtain ⟨j, rfl⟩ := this
      exact ⟨j, e.le_iff_le.1 hle, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ j, e.le_iff_le.2 hj⟩
  rw [hset, card_map, Fin.card_Iic]

lemma fareyCount_fareyFrac (N : ℕ) (i : Fin (farey N).card) :
    fareyCount N (fareyFrac N i : ℝ) = (i : ℕ) + 1 := by
  rw [fareyCount, ← card_filter_le_fareyFrac N i]
  congr 1
  exact filter_congr fun f _ => Rat.cast_le

lemma fareyFrac_mem (N : ℕ) (i : Fin (farey N).card) : fareyFrac N i ∈ farey N :=
  orderEmbOfFin_mem _ _ i

lemma fareyFrac_sub_eq (N : ℕ) (i : Fin (farey N).card) :
    (fareyFrac N i : ℝ) - ((i : ℕ) + 1 : ℝ) / (farey N).card =
      fareyG N (fareyFrac N i) / (farey N).card := by
  have hA : (0 : ℝ) < (farey N).card := by
    have := i.pos; exact_mod_cast this
  obtain ⟨h0, h1, -⟩ := mem_farey.1 (fareyFrac_mem N i)
  rw [G_eq N (by exact_mod_cast h0.le) (by exact_mod_cast h1), fareyCount_fareyFrac]
  field_simp
  push_cast
  ring

/-- Reindexing a sum over `Fin A` as a sum over `F_N`. -/
lemma sum_fin_fareyFrac (N : ℕ) (φ : ℚ → ℝ) :
    ∑ i : Fin (farey N).card, φ (fareyFrac N i) = ∑ f ∈ farey N, φ f := by
  set e := (farey N).orderEmbOfFin rfl
  have : (univ : Finset (Fin (farey N).card)).map e.toEmbedding = farey N := by
    ext f
    simp only [mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨j, rfl⟩; exact orderEmbOfFin_mem _ _ j
    · intro hf
      have : f ∈ Set.range e := by rw [range_orderEmbOfFin]; exact hf
      exact this
  conv_rhs => rw [← this]
  rw [sum_map]
  rfl

lemma franelL2_eq (N : ℕ) :
    franelL2 N = ∑ f ∈ farey N, (fareyG N f / (farey N).card) ^ 2 := by
  rw [franelL2, ← sum_fin_fareyFrac N (fun f => (fareyG N f / (farey N).card) ^ 2)]
  refine sum_congr rfl fun i _ => ?_
  rw [fareyFrac_sub_eq]

lemma franelL1_eq (N : ℕ) :
    franelL1 N = ∑ f ∈ farey N, |fareyG N f / (farey N).card| := by
  rw [franelL1, ← sum_fin_fareyFrac N (fun f => |fareyG N f / (farey N).card|)]
  refine sum_congr rfl fun i _ => ?_
  rw [fareyFrac_sub_eq]

/-! ### `G` is bounded and measurable -/

lemma measurable_fareyG (N : ℕ) : Measurable (fareyG N) := by
  unfold fareyG
  refine Finset.measurable_sum _ fun q _ => ?_
  exact (measurable_fract.comp (measurable_id.const_mul _)).const_mul _

lemma abs_fareyG_le (N : ℕ) (x : ℝ) : |fareyG N x| ≤ ∑ q ∈ Ioc 0 N, |fc N q| := by
  unfold fareyG
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
  rw [abs_mul]
  calc |fc N q| * |Int.fract ((q : ℝ) * x)| ≤ |fc N q| * 1 :=
        mul_le_mul_of_nonneg_left (abs_fract_le_one _) (abs_nonneg _)
    _ = |fc N q| := mul_one _

lemma ii_fareyG_sq (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => fareyG N x ^ 2) volume a b := by
  refine intervalIntegrable_of_bounded ((measurable_fareyG N).pow_const 2)
    (C := (∑ q ∈ Ioc 0 N, |fc N q|) ^ 2) (fun x => ?_) a b
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_fareyG_le N x) 2

/-! ### Discrete sum versus integral -/

lemma one_div_den_le {f : ℚ} (hf : 0 < f) : (1 : ℝ) / f.den ≤ f := by
  have hnum : (1 : ℤ) ≤ f.num := Rat.num_pos.2 hf
  have hden : (0 : ℝ) < f.den := by exact_mod_cast f.den_pos
  rw [Rat.cast_def]
  gcongr
  exact_mod_cast hnum

lemma fareyCount_left {N : ℕ} {f : ℚ} (hf : f ∈ farey N) {x : ℝ}
    (hx1 : (f : ℝ) - 1 / (N : ℝ) ^ 2 ≤ x) (hx2 : x < f) :
    fareyCount N x + 1 = fareyCount N f := by
  have hset : (farey N).filter (fun g : ℚ => (g : ℝ) ≤ x) =
      ((farey N).filter (fun g : ℚ => (g : ℝ) ≤ f)).erase f := by
    ext g
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hg, hgx⟩
      refine ⟨fun h => ?_, hg, hgx.trans hx2.le⟩
      rw [h] at hgx; linarith
    · rintro ⟨hne, hg, hgf⟩
      refine ⟨hg, ?_⟩
      by_contra hcon
      push Not at hcon
      have hsep := farey_sep hf hg (Ne.symm hne)
      have hsep' : (1 : ℝ) / (N : ℝ) ^ 2 ≤ |(f : ℝ) - g| := by
        have := (Rat.cast_le (K := ℝ)).2 hsep; push_cast at this; exact this
      have hlt : (g : ℝ) < f := lt_of_le_of_ne hgf (by exact_mod_cast hne)
      rw [abs_of_pos (by linarith)] at hsep'
      linarith
  have hmem : f ∈ (farey N).filter (fun g : ℚ => (g : ℝ) ≤ f) := mem_filter.2 ⟨hf, le_rfl⟩
  rw [fareyCount, fareyCount, hset, card_erase_of_mem hmem]
  have := card_pos.2 ⟨f, hmem⟩
  omega

/-- Pointwise: `G(f)² ≤ 3 G(x)² + 3 A²/N⁴ + 3` for `f − 1/N² ≤ x ≤ f`. -/
lemma G_sq_le {N : ℕ} {f : ℚ} (hf : f ∈ farey N) {x : ℝ}
    (hx1 : (f : ℝ) - 1 / (N : ℝ) ^ 2 ≤ x) (hx2 : x ≤ f) :
    fareyG N f ^ 2 ≤ 3 * fareyG N x ^ 2 +
      (3 * ((farey N).card : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) ^ 2 + 3) := by
  rcases eq_or_lt_of_le hx2 with h | h
  · rw [h]; nlinarith [sq_nonneg (fareyG N f)]
  obtain ⟨h0, h1, hN⟩ := mem_farey.1 hf
  have hN1 : 1 ≤ N := le_trans f.den_pos hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hf1 : (f : ℝ) ≤ 1 := by exact_mod_cast h1
  have hfN : (1 : ℝ) / N ≤ f := by
    refine le_trans ?_ (one_div_den_le h0)
    gcongr
    try exact_mod_cast hN
  have hNN : (1 : ℝ) / (N : ℝ) ^ 2 ≤ 1 / N := by
    gcongr
    try nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hc := fareyCount_left hf hx1 h
  have hcR : (fareyCount N x : ℝ) + 1 = fareyCount N f := by exact_mod_cast hc
  rw [G_eq N hx0 (by linarith), G_eq N (by linarith) hf1]
  set A : ℝ := ((farey N).card : ℝ)
  set h2 : ℝ := 1 / (N : ℝ) ^ 2
  have hd : (A * f - fareyCount N f) = (A * x - fareyCount N x) + A * (f - x) - 1 := by
    rw [← hcR]; ring
  rw [hd]
  have hfx : 0 ≤ (f : ℝ) - x := by linarith
  have hfx' : (f : ℝ) - x ≤ h2 := by linarith
  have hA : 0 ≤ A := by positivity
  have hAfx : (A * ((f : ℝ) - x)) ^ 2 ≤ A ^ 2 * h2 ^ 2 := by
    rw [mul_pow]; gcongr
  nlinarith [sq_nonneg ((A * x - fareyCount N x) - A * ((f : ℝ) - x)),
    sq_nonneg ((A * x - fareyCount N x) + 1), sq_nonneg (A * ((f : ℝ) - x) + 1)]

/-- **Discrete versus continuous**: `∑_f G(f)² ≤ 3N² ∫₀¹ G² + 3A(A²/N⁴ + 1)`. -/
theorem sum_G_sq_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ f ∈ farey N, fareyG N f ^ 2 ≤
      3 * (N : ℝ) ^ 2 * (∫ x in (0 : ℝ)..1, fareyG N x ^ 2) +
        (farey N).card * (3 * ((farey N).card : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) ^ 2 + 3) := by
  set h2 : ℝ := 1 / (N : ℝ) ^ 2 with hh2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh0 : 0 < h2 := by positivity
  set C : ℝ := 3 * ((farey N).card : ℝ) ^ 2 * h2 ^ 2 + 3
  -- each Farey fraction: `h G(f)² ≤ 3 ∫_{f-h}^f G² + h C`
  have hloc : ∀ f ∈ farey N, h2 * fareyG N f ^ 2 ≤
      3 * (∫ x in ((f : ℝ) - h2)..(f : ℝ), fareyG N x ^ 2) + h2 * C := by
    intro f hf
    have hmono := integral_mono_on (a := (f : ℝ) - h2) (b := f) (by linarith)
      (intervalIntegrable_const (c := fareyG N f ^ 2))
      (((ii_fareyG_sq N _ _).const_mul 3).add intervalIntegrable_const)
      (fun x hx => G_sq_le hf hx.1 hx.2)
    rw [intervalIntegral.integral_const, integral_add ((ii_fareyG_sq N _ _).const_mul 3)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at hmono
    simp only [sub_sub_cancel, smul_eq_mul] at hmono
    have hCdef : h2 * C = h2 * (3 * ((farey N).card : ℝ) ^ 2 * (1 / (N : ℝ) ^ 2) ^ 2 + 3) := rfl
    rw [hCdef]
    linarith
  -- the intervals `(f - h, f]` are disjoint and lie in `(0, 1]`
  set s : ℚ → Set ℝ := fun f => Set.Ioc ((f : ℝ) - h2) f
  have hdisj : Set.Pairwise (↑(farey N)) (Function.onFun Disjoint s) := by
    intro f hf g hg hfg
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    have hsep := farey_sep hf hg hfg
    have hsep' : (1 : ℝ) / (N : ℝ) ^ 2 ≤ |(f : ℝ) - g| := by
      have := (Rat.cast_le (K := ℝ)).2 hsep; push_cast at this; exact this
    rcases le_total (f : ℝ) g with h | h
    · have : |(f : ℝ) - g| < h2 := by rw [abs_lt]; constructor <;> linarith
      linarith [le_abs_self ((f : ℝ) - g), neg_abs_le ((f : ℝ) - g)]
    · have : |(f : ℝ) - g| < h2 := by rw [abs_lt]; constructor <;> linarith
      linarith [le_abs_self ((f : ℝ) - g), neg_abs_le ((f : ℝ) - g)]
  have hsub : (⋃ f ∈ farey N, s f) ⊆ Set.Ioc 0 1 := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨f, hf, hx1, hx2⟩ := hx
    obtain ⟨h0, h1, hfN⟩ := mem_farey.1 hf
    have hfN' : (1 : ℝ) / N ≤ f := by
      refine le_trans ?_ (one_div_den_le h0)
      gcongr
      try exact_mod_cast hfN
    have hNN : h2 ≤ 1 / N := by
      rw [hh2]; gcongr
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    exact ⟨by linarith, hx2.trans (by exact_mod_cast h1)⟩
  have hint : ∑ f ∈ farey N, (∫ x in ((f : ℝ) - h2)..(f : ℝ), fareyG N x ^ 2) ≤
      (∫ x in (0 : ℝ)..1, fareyG N x ^ 2) := by
    have e : ∀ f ∈ farey N, (∫ x in ((f : ℝ) - h2)..(f : ℝ), fareyG N x ^ 2) =
        (∫ x in s f, fareyG N x ^ 2) := fun f _ => integral_of_le (by linarith)
    rw [sum_congr rfl e, ← integral_biUnion_finset (farey N) (fun f _ => measurableSet_Ioc) hdisj
      (fun f _ => (ii_fareyG_sq N ((f : ℝ) - h2) f).1),
      integral_of_le zero_le_one]
    refine setIntegral_mono_set (ii_fareyG_sq N 0 1).1
      (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hsub)
  have htot : h2 * ∑ f ∈ farey N, fareyG N f ^ 2 ≤
      3 * (∫ x in (0 : ℝ)..1, fareyG N x ^ 2) + (farey N).card * (h2 * C) := by
    rw [mul_sum]
    calc ∑ f ∈ farey N, h2 * fareyG N f ^ 2
        ≤ ∑ f ∈ farey N, (3 * (∫ x in ((f : ℝ) - h2)..(f : ℝ), fareyG N x ^ 2) + h2 * C) :=
          sum_le_sum hloc
      _ = 3 * ∑ f ∈ farey N, (∫ x in ((f : ℝ) - h2)..(f : ℝ), fareyG N x ^ 2) +
            (farey N).card * (h2 * C) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr
  have hNh : (N : ℝ) ^ 2 * h2 = 1 := by rw [hh2]; field_simp
  calc ∑ f ∈ farey N, fareyG N f ^ 2 = (N : ℝ) ^ 2 * (h2 * ∑ f ∈ farey N, fareyG N f ^ 2) := by
        rw [← mul_assoc, hNh, one_mul]
    _ ≤ (N : ℝ) ^ 2 * (3 * (∫ x in (0 : ℝ)..1, fareyG N x ^ 2) + (farey N).card * (h2 * C)) := by
        gcongr
    _ = _ := by
        have : (N : ℝ) ^ 2 * ((farey N).card * (h2 * C)) = (farey N).card * C * ((N : ℝ) ^ 2 * h2) := by
          ring
        rw [mul_add, this, hNh]
        ring

end Mertens
