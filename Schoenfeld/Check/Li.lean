import Schoenfeld.Check.Basic
import Schoenfeld.LogIntegral

/-!
# A certified enclosure of `li(2657)`

`li(x) = li(2) + ∫₂ˣ dt/log t` (`Real.logIntegral`). Both pieces are enclosed by a mesh:

* `mFold` sums rational cell bounds over a list of mesh points; `mFold_sound` turns cell
  bounds into bounds for the integral over the whole mesh, by additivity.
* `∫₂^{2657} dt/log t`: on a cell `[t, v]`, `(v − t)/log v ≤ ∫ ≤ (v − t)/log t`
  (`1/log` is decreasing). Mesh: 1024 cells per octave up to 2048, then steps of 2.
* `li(2) = ∫₀¹ g`, `g(u) = 1/log(1 + u) + 1/log(1 − u)` (the vendored definition). On `[0, 2^{-10}]`
  and `[1 − 2^{-11}, 1]` we use `0 ≤ g ≤ 2`; on a cell `[u, v]` in between,
  `A(v) − B(u) ≤ g ≤ A(u) − B(v)` with `A(s) = 1/log(1 + s)` and `B(s) = 1/log(1/(1 − s))`,
  both decreasing. Mesh: 256 cells per octave on `[2^{-10}, 1/2]`, steps of `2^{-11}` after.

The result (`liAnchor_sound`): `li(2657) ∈ [liAnchorLo, liAnchorHi]`, about
`[399.553, 399.640]` (true value 399.597).
-/

namespace Schoenfeld.Check

open Real MeasureTheory intervalIntegral

/-! ### Summing cell bounds over a mesh -/

/-- Mesh-fold state: current point, accumulated bounds, flag. -/
structure MS where
  t : ℚ
  lo : ℚ
  hi : ℚ
  ok : Bool

/-- Fold the cell bounds `cLo`, `cHi` (guarded by `guard`) over the mesh points `pts`. -/
def mFold (cLo cHi : ℚ → ℚ → ℚ) (guard : ℚ → ℚ → Bool) : MS → List ℚ → MS
  | s, [] => s
  | s, v :: rest =>
    mFold cLo cHi guard ⟨v, s.lo + cLo s.t v, s.hi + cHi s.t v, s.ok && guard s.t v⟩ rest

lemma mFold_sound (f : ℝ → ℝ) (P : ℝ) (cLo cHi : ℚ → ℚ → ℚ) (guard : ℚ → ℚ → Bool)
    (hcell : ∀ u v : ℚ, guard u v = true → IntervalIntegrable f volume u v ∧
      (cLo u v : ℝ) ≤ ∫ t in (u : ℝ)..v, f t ∧ ∫ t in (u : ℝ)..v, f t ≤ cHi u v) :
    ∀ (pts : List ℚ) (s : MS), (s.ok = true → IntervalIntegrable f volume P s.t ∧
      (s.lo : ℝ) ≤ ∫ t in P..s.t, f t ∧ ∫ t in P..s.t, f t ≤ s.hi) →
      (mFold cLo cHi guard s pts).ok = true →
      IntervalIntegrable f volume P (mFold cLo cHi guard s pts).t ∧
      ((mFold cLo cHi guard s pts).lo : ℝ) ≤ ∫ t in P..(mFold cLo cHi guard s pts).t, f t ∧
      ∫ t in P..(mFold cLo cHi guard s pts).t, f t ≤ (mFold cLo cHi guard s pts).hi := by
  intro pts
  induction pts with
  | nil => intro s h; simpa [mFold] using h
  | cons v rest ih =>
    intro s h
    simp only [mFold]
    apply ih
    intro hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hI, hlo, hhi⟩ := h hok.1
    obtain ⟨hI', hclo, hchi⟩ := hcell _ _ hok.2
    have hadd := integral_add_adjacent_intervals hI hI'
    refine ⟨hI.trans hI', ?_, ?_⟩ <;> simp only <;> push_cast <;> linarith

/-! ### `∫ dt/log t` -/

lemma continuousOn_inv_log {s : Set ℝ} (hs : ∀ t ∈ s, 1 < t) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t) s := by
  intro t ht
  have h1 := hs t ht
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_const.div (Real.continuousAt_log (by linarith))
    (Real.log_pos h1).ne'

lemma intervalIntegrable_inv_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_inv_log
  intro t ht
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

lemma integral_inv_log_bounds {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ ∫ t in a..b, 1 / Real.log t ∧
      ∫ t in a..b, 1 / Real.log t ≤ (b - a) / Real.log a := by
  have hII := intervalIntegrable_inv_log ha (by linarith)
  have hla := Real.log_pos ha
  constructor
  · have := integral_mono_on hab (intervalIntegrable_const (c := 1 / Real.log b)) hII
      (fun t ht => one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
        (Real.log_le_log (by linarith [ht.1]) ht.2))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [div_eq_mul_one_div]; exact this
  · have := integral_mono_on hab hII (intervalIntegrable_const (c := 1 / Real.log a))
      (fun t ht => one_div_le_one_div_of_le hla (Real.log_le_log (by linarith) ht.1))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [div_eq_mul_one_div]; exact this

lemma logIntegral_eq_add {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Real.logIntegral b = Real.logIntegral a + ∫ t in a..b, 1 / Real.log t := by
  unfold Real.logIntegral
  rw [add_assoc, integral_add_adjacent_intervals
    (intervalIntegrable_inv_log (by norm_num) (by linarith))
    (intervalIntegrable_inv_log (by linarith) (by linarith))]

lemma logIntegral_mono {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.logIntegral a ≤ Real.logIntegral b := by
  rw [logIntegral_eq_add (b := b) ha (by linarith)]
  have := (integral_inv_log_bounds (by linarith) hab).1
  have : 0 ≤ (b - a) / Real.log b :=
    div_nonneg (by linarith) (Real.log_pos (by linarith)).le
  linarith

/-- Cell lower bound for `∫ₜᵛ dt/log t`. -/
def liCellLo (t v : ℚ) : ℚ := (v - t) * invLo (logUp v)

/-- Cell upper bound for `∫ₜᵛ dt/log t`. -/
def liCellHi (t v : ℚ) : ℚ := (v - t) * invUp (logLo t)

/-- Guard for an `li` cell. -/
def liGuard (t v : ℚ) : Bool := decide (1 ≤ t) && decide (t ≤ v) && decide (0 < logLo t)

lemma liCell_bounds {t v : ℚ} (ht : 1 ≤ t) (htv : t ≤ v) (hl : 0 < logLo t) :
    (liCellLo t v : ℝ) ≤ ∫ s in (t : ℝ)..v, 1 / Real.log s ∧
      ∫ s in (t : ℝ)..v, 1 / Real.log s ≤ liCellHi t v := by
  have hlt := logLo_le ht
  have hlt0 : (0 : ℝ) < Real.log t := lt_of_lt_of_le (by exact_mod_cast hl) hlt
  have ht1 : (1 : ℝ) < t := by
    by_contra h; push Not at h
    have := Real.log_nonpos (by exact_mod_cast (by linarith : (0 : ℚ) ≤ t)) h
    linarith
  have htv' : (t : ℝ) ≤ v := by exact_mod_cast htv
  have hv1 : (1 : ℝ) < v := by linarith
  have hvt : (0 : ℝ) ≤ v - t := by linarith
  obtain ⟨b1, b2⟩ := integral_inv_log_bounds ht1 htv'
  have hlv := le_logUp (show (1 : ℚ) ≤ v by linarith)
  have hi1 := invLo_le_one_div (Real.log_pos hv1) hlv
  have hi2 := one_div_le_invUp hl hlt
  constructor
  · unfold liCellLo; push_cast
    calc ((v : ℝ) - t) * (invLo (logUp v) : ℝ) ≤ (v - t) * (1 / Real.log v) :=
          mul_le_mul_of_nonneg_left hi1 hvt
      _ = (v - t) / Real.log v := by ring
      _ ≤ _ := b1
  · unfold liCellHi; push_cast
    calc _ ≤ ((v : ℝ) - t) / Real.log t := b2
      _ = (v - t) * (1 / Real.log t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hi2 hvt

lemma liCell_sound (u v : ℚ) (h : liGuard u v = true) :
    IntervalIntegrable (fun s : ℝ => 1 / Real.log s) volume u v ∧
      (liCellLo u v : ℝ) ≤ ∫ s in (u : ℝ)..v, 1 / Real.log s ∧
      ∫ s in (u : ℝ)..v, 1 / Real.log s ≤ liCellHi u v := by
  simp only [liGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hb := liCell_bounds h1 h2 h3
  have hu1 : (1 : ℝ) < u := by
    have := logLo_le h1
    by_contra hc; push Not at hc
    have := Real.log_nonpos (by exact_mod_cast (by linarith : (0 : ℚ) ≤ u)) hc
    have : (0 : ℝ) < logLo u := by exact_mod_cast h3
    linarith
  exact ⟨intervalIntegrable_inv_log hu1 (by linarith [(show (u : ℝ) ≤ v by exact_mod_cast h2)]),
    hb⟩

/-- Mesh for `∫₂^{2657}`: 1024 cells per octave from 2 to 2048, then steps of 2, then 2657. -/
def ptsLi : List ℚ :=
  (List.range 10).flatMap (fun j => (List.range 1024).map
      (fun i => (2 : ℚ) ^ (j + 1) + (i + 1) * 2 ^ (j + 1) / 1024)) ++
    (List.range 304).map (fun i => (2048 : ℚ) + 2 * (i + 1)) ++ [2657]

/-- The fold for `∫₂^{2657}`. -/
def liInt : MS := mFold liCellLo liCellHi liGuard ⟨2, 0, 0, true⟩ ptsLi

lemma liInt_sound (h : liInt.ok = true) :
    (liInt.lo : ℝ) ≤ ∫ s in (2 : ℝ)..liInt.t, 1 / Real.log s ∧
      ∫ s in (2 : ℝ)..liInt.t, 1 / Real.log s ≤ liInt.hi := by
  have := mFold_sound (fun s : ℝ => 1 / Real.log s) 2 liCellLo liCellHi liGuard liCell_sound
    ptsLi ⟨2, 0, 0, true⟩ (fun _ => ⟨by simp, by simp, by simp⟩) h
  exact ⟨this.2.1, this.2.2⟩

/-! ### `li(2)` -/

/-- The integrand of `li(2)`. -/
noncomputable def gli (u : ℝ) : ℝ := 1 / Real.log (1 + u) + 1 / Real.log (1 - u)

lemma gli_integrableOn : IntegrableOn gli (Set.Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  exact Real.logIntegralTwo_integrand_integrableOn

lemma gli_ii {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable gli volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact gli_integrableOn.mono_set (Set.Ioc_subset_Ioc ha hb)

lemma gli_bounds {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ gli u ∧ gli u ≤ 2 := by
  rcases h0.lt_or_eq with h0 | rfl
  · rcases h1.lt_or_eq with h1 | rfl
    · exact ⟨(Real.logIntegralTwo_integrand_pos h0 h1).le,
        Real.logIntegralTwo_integrand_le_two h0 h1⟩
    · have : (0 : ℝ) < 1 / Real.log 2 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
      have h2 : 1 / Real.log 2 ≤ (2 : ℝ) := by
        have := Real.log_two_gt_d9
        rw [div_le_iff₀ (by linarith)]; linarith
      have e : gli 1 = 1 / Real.log 2 := by simp only [gli]; norm_num
      rw [e]
      exact ⟨this.le, h2⟩
  · simp [gli]

lemma logIntegralTwo_eq : Real.logIntegralTwo = ∫ u in (0 : ℝ)..1, gli u := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

lemma gli_crude {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    0 ≤ ∫ u in a..b, gli u ∧ ∫ u in a..b, gli u ≤ 2 * (b - a) := by
  have hII := gli_ii ha hab hb
  constructor
  · exact intervalIntegral.integral_nonneg hab (fun u hu =>
      (gli_bounds (by linarith [hu.1]) (by linarith [hu.2])).1)
  · have := integral_mono_on hab hII (intervalIntegrable_const (c := (2 : ℝ)))
      (fun u hu => (gli_bounds (by linarith [hu.1]) (by linarith [hu.2])).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith

/-- Upper bound for `A(u) = 1/log(1 + u)`. -/
def AHi (u : ℚ) : ℚ := invUp (logLo (1 + u))
/-- Lower bound for `A(v)`. -/
def ALo (v : ℚ) : ℚ := invLo (logUp (1 + v))
/-- Upper bound for `B(u) = 1/log(1/(1 − u))`. -/
def BHi (u : ℚ) : ℚ := invUp (logLo (1 / (1 - u)))
/-- Lower bound for `B(v)`. -/
def BLo (v : ℚ) : ℚ := invLo (logUp (1 / (1 - v)))

/-- Cell bounds for `∫ᵤᵛ g`. -/
def gCellLo (u v : ℚ) : ℚ := (v - u) * (ALo v - BHi u)
/-- Cell bounds for `∫ᵤᵛ g`. -/
def gCellHi (u v : ℚ) : ℚ := (v - u) * (AHi u - BLo v)
/-- Guard for a `g` cell. -/
def gGuard (u v : ℚ) : Bool :=
  decide (0 < u) && decide (u ≤ v) && decide (v < 1) && decide (0 < logLo (1 + u)) &&
    decide (0 < logLo (1 / (1 - u)))

lemma gCell_sound (u v : ℚ) (h : gGuard u v = true) :
    IntervalIntegrable gli volume u v ∧ (gCellLo u v : ℝ) ≤ ∫ s in (u : ℝ)..v, gli s ∧
      ∫ s in (u : ℝ)..v, gli s ≤ gCellHi u v := by
  simp only [gGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hu0, huv⟩, hv1⟩, hA⟩, hB⟩ := h
  have hu0' : (0 : ℝ) < u := by exact_mod_cast hu0
  have huv' : (u : ℝ) ≤ v := by exact_mod_cast huv
  have hv1' : (v : ℝ) < 1 := by exact_mod_cast hv1
  have hII := gli_ii hu0'.le huv' hv1'.le
  -- the four rational bounds
  have hAu : 1 / Real.log (1 + u) ≤ (AHi u : ℝ) := by
    have := logLo_le (show (1 : ℚ) ≤ 1 + u by linarith)
    push_cast at this
    exact one_div_le_invUp hA this
  have hAv : (ALo v : ℝ) ≤ 1 / Real.log (1 + v) := by
    have := le_logUp (show (1 : ℚ) ≤ 1 + v by linarith)
    push_cast at this
    exact invLo_le_one_div (Real.log_pos (by linarith)) this
  have hq1 : ∀ s : ℚ, 0 ≤ s → s < 1 → (1 : ℚ) ≤ 1 / (1 - s) := fun s h0 h1 => by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hcast : ∀ s : ℚ, ((1 / (1 - s) : ℚ) : ℝ) = 1 / (1 - (s : ℝ)) := fun s => by push_cast; rfl
  have hBu : 1 / Real.log (1 / (1 - u)) ≤ (BHi u : ℝ) := by
    have := logLo_le (hq1 u hu0.le (lt_of_le_of_lt huv hv1))
    rw [hcast] at this
    exact one_div_le_invUp hB this
  have hBv : (BLo v : ℝ) ≤ 1 / Real.log (1 / (1 - v)) := by
    have := le_logUp (hq1 v (by linarith) hv1)
    rw [hcast] at this
    refine invLo_le_one_div (Real.log_pos ?_) this
    rw [lt_div_iff₀ (by linarith)]; linarith
  -- pointwise bounds on the cell
  have hpt : ∀ s ∈ Set.Icc (u : ℝ) v,
      1 / Real.log (1 + v) - 1 / Real.log (1 / (1 - u)) ≤ gli s ∧
        gli s ≤ 1 / Real.log (1 + u) - 1 / Real.log (1 / (1 - v)) := by
    intro s ⟨hs1, hs2⟩
    have hinv : ∀ r : ℝ, r < 1 → 1 / Real.log (1 - r) = -(1 / Real.log (1 / (1 - r))) :=
      fun r _ => by rw [one_div (1 - r), Real.log_inv, div_neg, neg_neg]
    simp only [gli]
    rw [hinv s (by linarith)]
    have l1 : Real.log (1 + u) ≤ Real.log (1 + s) := Real.log_le_log (by linarith) (by linarith)
    have l2 : Real.log (1 + s) ≤ Real.log (1 + v) := Real.log_le_log (by linarith) (by linarith)
    have p1 : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
    have m1 : (1 : ℝ) < 1 / (1 - u) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have m2 : 1 / (1 - u) ≤ 1 / (1 - (s : ℝ)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have m3 : 1 / (1 - (s : ℝ)) ≤ 1 / (1 - v) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have k1 : Real.log (1 / (1 - u)) ≤ Real.log (1 / (1 - s)) := Real.log_le_log (by linarith) m2
    have k2 : Real.log (1 / (1 - s)) ≤ Real.log (1 / (1 - v)) :=
      Real.log_le_log (by linarith) m3
    have q1 : 0 < Real.log (1 / (1 - u)) := Real.log_pos m1
    have e1 := one_div_le_one_div_of_le p1 l1
    have e2 := one_div_le_one_div_of_le (by linarith) l2
    have e3 := one_div_le_one_div_of_le q1 k1
    have e4 := one_div_le_one_div_of_le (by linarith) k2
    constructor <;> linarith
  have hvu : (0 : ℝ) ≤ v - u := by linarith
  refine ⟨hII, ?_, ?_⟩
  · have := integral_mono_on huv' (intervalIntegrable_const
      (c := 1 / Real.log (1 + v) - 1 / Real.log (1 / (1 - u)))) hII (fun s hs => (hpt s hs).1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    unfold gCellLo; push_cast
    calc ((v : ℝ) - u) * ((ALo v : ℝ) - BHi u)
        ≤ (v - u) * (1 / Real.log (1 + v) - 1 / Real.log (1 / (1 - u))) :=
          mul_le_mul_of_nonneg_left (by linarith) hvu
      _ ≤ _ := this
  · have := integral_mono_on huv' hII (intervalIntegrable_const
      (c := 1 / Real.log (1 + u) - 1 / Real.log (1 / (1 - v)))) (fun s hs => (hpt s hs).2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    unfold gCellHi; push_cast
    calc _ ≤ ((v : ℝ) - u) * (1 / Real.log (1 + u) - 1 / Real.log (1 / (1 - v))) := this
      _ ≤ (v - u) * ((AHi u : ℝ) - BLo v) := mul_le_mul_of_nonneg_left (by linarith) hvu

/-- Left end of the `g` mesh. -/
def gStart : ℚ := 1 / 2 ^ 10

/-- Mesh for `∫ g` on `[2^{-10}, 1 − 2^{-11}]`. -/
def ptsG : List ℚ :=
  (List.range 9).flatMap (fun j => (List.range 256).map
      (fun i => (1 : ℚ) / 2 ^ (10 - j) + (i + 1) * (1 / 2 ^ (10 - j)) / 256)) ++
    (List.range 1023).map (fun i => (1 : ℚ) / 2 + (i + 1) / 2 ^ 11)

/-- The fold for `∫ g`. -/
def gInt : MS := mFold gCellLo gCellHi gGuard ⟨gStart, 0, 0, true⟩ ptsG

/-- Lower bound for `li(2657)`. -/
def liAnchorLo : ℚ := gInt.lo + liInt.lo

/-- Upper bound for `li(2657)`. -/
def liAnchorHi : ℚ := gInt.hi + 2 * gStart + 2 * (1 - gInt.t) + liInt.hi

/-- The checks that make the anchor valid. -/
def liAnchorOK : Bool :=
  gInt.ok && decide (gInt.t ≤ 1) && decide (gStart ≤ gInt.t) && liInt.ok && decide (liInt.t = 2657)

lemma liAnchor_sound (h : liAnchorOK = true) :
    (liAnchorLo : ℝ) ≤ Real.logIntegral 2657 ∧ Real.logIntegral 2657 ≤ liAnchorHi := by
  simp only [liAnchorOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hg, hg1⟩, hg2⟩, hl⟩, hlt⟩ := h
  have hst0 : (0 : ℝ) ≤ (gStart : ℝ) := by unfold gStart; positivity
  have hst1 : (gStart : ℝ) ≤ gInt.t := by exact_mod_cast hg2
  have ht1 : (gInt.t : ℝ) ≤ 1 := by exact_mod_cast hg1
  have hG := mFold_sound gli gStart gCellLo gCellHi gGuard gCell_sound ptsG
    ⟨gStart, 0, 0, true⟩ (fun _ => ⟨by simp, by simp, by simp⟩) hg
  have hL := liInt_sound hl
  rw [hlt] at hL
  push_cast at hL
  have e1 := integral_add_adjacent_intervals (gli_ii le_rfl hst0 (by unfold gStart; norm_num))
    hG.1
  have e2 := integral_add_adjacent_intervals (gli_ii le_rfl (hst0.trans hst1) ht1)
    (gli_ii (hst0.trans hst1) ht1 le_rfl)
  have c1 := gli_crude le_rfl hst0 (by unfold gStart; norm_num)
  have c2 := gli_crude (hst0.trans hst1) ht1 le_rfl
  have hli : Real.logIntegral 2657 = (∫ u in (0 : ℝ)..1, gli u) +
      ∫ s in (2 : ℝ)..2657, 1 / Real.log s := by
    rw [Real.logIntegral, logIntegralTwo_eq]
  have hG1 := hG.2.1
  have hG2 := hG.2.2
  simp only [gInt] at hG1 hG2 e1 e2 c2 ⊢
  rw [hli, ← e2, ← e1]
  unfold liAnchorLo liAnchorHi
  simp only [gInt]
  push_cast
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2, hL.1, hL.2]

end Schoenfeld.Check
