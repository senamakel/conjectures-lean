import Cramer.CMS.Taylor
import CramerCompute.CMSCheck

/-!
# A kernel-checkable bound for `(2 − 2cos θ)|Q(cos θ)|/θ²` on cells

`Q(x) = Σ_{i ≤ K} q_i x^i` has integer coefficients. A cell list is a list of entries
`(N, k, cl, cu, j, flag, tag, Gn)`; consecutive entries `e, e'` stand for the cell
`[N/D₀, N'/D₀]` with the claimed bound `Gn/GD`, and each entry certifies
`cl/S ≤ cos(N/D₀) ≤ cu/S`:

* **endpoint check** (`endOK`): with `t = N/D₀ − 2k·π⁺` (`π⁺ = 3.14159265358979323847`) and
  `w = 2k·10⁻²⁰`, `cl/S ≤ cosP 14 (t) − w` and `cosP 13 (t) + w ≤ cu/S`. Since
  `cosP 14 ≤ cos ≤ cosP 13` and `|cos(N/D₀) − cos t| ≤ w`, this encloses `cos(N/D₀)`.
* **cell check** (`cellOK`): `cos` is monotone on `[jπ, (j+1)π]`; a cell inside it (flag `0`)
  has `cos θ` between the endpoint values; a cell inside `[(j−1)π, (j+1)π]` (flag `1`) has
  `cos θ` between the smaller endpoint value and `1` (even `j`) or the larger and `−1` (odd
  `j`). On `[lo, hi]`, `|Q(c)| ≤ U/(2S)^K` with `U = Σ_i |Q'_i| (hi − lo)^i`,
  `Q'_i = Σ_{j ≥ i} q_j C(j,i) (lo + hi)^{j−i} (2S)^{K−j}` (Taylor expansion at the midpoint).
  Tag `0` uses `(2 − 2cos θ)/θ² ≤ 1 − θ_a²/12 + θ_a⁴/360` (`θ_b² ≤ 15`), tag `1` uses
  `(2 − 2cos θ)/θ² ≤ (2 − 2 lo/S)/θ_a²`.

Everything is natural-number and integer arithmetic, evaluated by `decide` in the kernel.
-/

namespace Cramer.CMS

open Real Finset

open CramerCompute (D0 SS PIL PIH TE tNum Ent cLo cHi posOK boundOK chk endOK)

/-! ### Exact evaluation of `cosP n` at `p/q` -/

/-- `num` with `cosP n (p/q) = num / (q^{2(n−1)} (2(n−1))!)`. -/
def cosNumF (n : ℕ) (p : ℤ) (q : ℕ) : ℤ :=
  ∑ i ∈ range n, (-1) ^ i * p ^ (2 * i) * ((q : ℤ) ^ (2 * (n - 1) - 2 * i)) *
    (((2 * (n - 1)).factorial / (2 * i).factorial : ℕ) : ℤ)

/-- The denominator. -/
def cosDenF (n : ℕ) (q : ℕ) : ℕ := q ^ (2 * (n - 1)) * (2 * (n - 1)).factorial

lemma cosP_eq_num_div (n : ℕ) (hn : 1 ≤ n) (p : ℤ) {q : ℕ} (hq : 0 < q) :
    cosP n ((p : ℝ) / q) = (cosNumF n p q : ℝ) / (cosDenF n q : ℝ) := by
  unfold cosP cosNumF cosDenF
  rw [Int.cast_sum, sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n - 1 := by have := mem_range.1 hi; omega
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdvd : (2 * i).factorial ∣ (2 * (n - 1)).factorial := Nat.factorial_dvd_factorial (by omega)
  have hf : (((2 * (n - 1)).factorial / (2 * i).factorial : ℕ) : ℝ) =
      ((2 * (n - 1)).factorial : ℝ) / ((2 * i).factorial : ℝ) := by
    rw [Nat.cast_div hdvd (by positivity)]
  have hpow : (q : ℝ) ^ (2 * (n - 1)) = (q : ℝ) ^ (2 * (n - 1) - 2 * i) * (q : ℝ) ^ (2 * i) := by
    rw [← pow_add]; congr 1; omega
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_mul, Nat.cast_pow]
  rw [hf, hpow, div_pow]
  have h1 : ((2 * i).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * (n - 1)).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-! ### The endpoint check -/

/-! ### The core-only definitions agree with the Mathlib ones -/

lemma lsum_eq (n : ℕ) (f : ℕ → ℤ) : CramerCompute.lsum n f = ∑ i ∈ range n, f i := by
  unfold CramerCompute.lsum
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldr_append, sum_range_succ, ← ih]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, add_zero]
    generalize f n = a
    induction (List.map f (List.range n)) with
    | nil => simp
    | cons b l ihl => simp only [List.foldr_cons]; rw [ihl]; ring

lemma lsumN_eq (n : ℕ) (f : ℕ → ℕ) : CramerCompute.lsumN n f = ∑ i ∈ range n, f i := by
  unfold CramerCompute.lsumN
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldr_append, sum_range_succ, ← ih]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, add_zero]
    generalize f n = a
    induction (List.map f (List.range n)) with
    | nil => simp
    | cons b l ihl => simp only [List.foldr_cons]; rw [ihl]; ring

lemma fact_eq : ∀ n, CramerCompute.fact n = n.factorial
  | 0 => rfl
  | n + 1 => by rw [CramerCompute.fact, fact_eq n, Nat.factorial_succ]

lemma chooseC_eq : ∀ n k, CramerCompute.chooseC n k = n.choose k
  | _, 0 => by simp [CramerCompute.chooseC]
  | 0, _ + 1 => by simp [CramerCompute.chooseC]
  | n + 1, k + 1 => by
    rw [CramerCompute.chooseC, chooseC_eq n k, chooseC_eq n (k + 1), Nat.choose_succ_succ]

lemma cosNum_eq (n : ℕ) (p : ℤ) (q : ℕ) : CramerCompute.cosNum n p q = cosNumF n p q := by
  unfold CramerCompute.cosNum cosNumF
  rw [lsum_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [fact_eq, fact_eq]

lemma cosDen_eq (n q : ℕ) : CramerCompute.cosDen n q = cosDenF n q := by
  unfold CramerCompute.cosDen cosDenF; rw [fact_eq]

/-- The enclosure of `cos(N/D₀)` by the two Taylor polynomials at the reduced point. -/
lemma cos_enclosure (N k : ℕ) :
    cosP 14 ((tNum N k : ℝ) / ((D0 * TE : ℕ) : ℝ)) - 2 * k / TE ≤ Real.cos ((N : ℝ) / D0) ∧
      Real.cos ((N : ℝ) / D0) ≤ cosP 13 ((tNum N k : ℝ) / ((D0 * TE : ℕ) : ℝ)) + 2 * k / TE := by
  set t : ℝ := (tNum N k : ℝ) / ((D0 * TE : ℕ) : ℝ)
  have hD0 : (D0 : ℝ) ≠ 0 := by simp [D0]
  have hTE0 : (TE : ℝ) ≠ 0 := by simp [TE]
  have hTE : (0 : ℝ) < TE := by simp [TE]
  have ht : t = (N : ℝ) / D0 - 2 * k * ((PIH : ℝ) / TE) := by
    simp only [t, tNum]; push_cast; field_simp
  have hpi2 : π < (PIH : ℝ) / TE := by
    have := Real.pi_lt_d20; simp only [PIH, TE]; norm_num at this ⊢; linarith
  have hpi3 : (PIH : ℝ) / TE - π ≤ 1 / TE := by
    have := Real.pi_gt_d20; simp only [PIH, TE]; norm_num at this ⊢; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcos : Real.cos ((N : ℝ) / D0) = Real.cos ((N : ℝ) / D0 - 2 * k * π) := by
    rw [show (N : ℝ) / D0 - 2 * k * π = (N : ℝ) / D0 - (k : ℕ) * (2 * π) by ring,
      Real.cos_sub_nat_mul_two_pi]
  have hw : |Real.cos ((N : ℝ) / D0) - Real.cos t| ≤ 2 * k / TE := by
    rw [hcos]
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [ht, show (N : ℝ) / D0 - 2 * k * π - ((N : ℝ) / D0 - 2 * k * ((PIH : ℝ) / TE)) =
      2 * k * ((PIH : ℝ) / TE - π) by ring]
    have hpos : 0 ≤ (PIH : ℝ) / TE - π := by linarith
    rw [abs_of_nonneg (mul_nonneg (by positivity) hpos)]
    calc 2 * k * ((PIH : ℝ) / TE - π) ≤ 2 * k * (1 / TE) := by gcongr
      _ = 2 * k / TE := by ring
  have hlo := cosP_le_cos_of_even (n := 14) (by norm_num) (by decide) t
  have hhi := cos_le_cosP_of_odd (n := 13) (by decide) t
  have hw' := abs_le.1 hw
  constructor <;> linarith

lemma endOK_sound {N k : ℕ} {cl cu : ℤ} (h : endOK N k cl cu = true) :
    (cl : ℝ) / SS ≤ Real.cos ((N : ℝ) / D0) ∧ Real.cos ((N : ℝ) / D0) ≤ (cu : ℝ) / SS := by
  simp only [endOK, Bool.and_eq_true, decide_eq_true_eq, cosNum_eq, cosDen_eq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := cos_enclosure N k
  generalize hp : tNum N k = p at h1 h2 e1 e2
  generalize hq : D0 * TE = q at h1 h2 e1 e2
  have hq0 : 0 < q := by rw [← hq]; simp [D0, TE]
  rw [cosP_eq_num_div 14 (by norm_num) p hq0] at e1
  rw [cosP_eq_num_div 13 (by norm_num) p hq0] at e2
  generalize cosNumF 14 p q = n14 at h1 e1
  generalize cosNumF 13 p q = n13 at h2 e2
  have hd14 : 0 < cosDenF 14 q := by unfold cosDenF; positivity
  have hd13 : 0 < cosDenF 13 q := by unfold cosDenF; positivity
  generalize cosDenF 14 q = d14 at h1 e1 hd14
  generalize cosDenF 13 q = d13 at h2 e2 hd13
  have hTE : 0 < TE := by simp [TE]
  have hSS : 0 < SS := by simp [SS]
  generalize TE = te at h1 h2 e1 e2 hTE
  generalize SS = ss at h1 h2 hSS ⊢
  have hd14' : (0 : ℝ) < d14 := by exact_mod_cast hd14
  have hd13' : (0 : ℝ) < d13 := by exact_mod_cast hd13
  have hte' : (0 : ℝ) < te := by exact_mod_cast hTE
  have hss' : (0 : ℝ) < ss := by exact_mod_cast hSS
  have h1' : (cl : ℝ) * d14 * te ≤ ((n14 : ℝ) * te - 2 * k * d14) * ss := by exact_mod_cast h1
  have h2' : ((n13 : ℝ) * te + 2 * k * d13) * ss ≤ (cu : ℝ) * d13 * te := by exact_mod_cast h2
  constructor
  · have h3 : (cl : ℝ) / ss ≤ ((n14 : ℝ) * te - 2 * k * d14) / (d14 * te) := by
      rw [div_le_div_iff₀ hss' (by positivity)]; linarith
    have h4 : ((n14 : ℝ) * te - 2 * k * d14) / (d14 * te) = (n14 : ℝ) / d14 - 2 * k / te := by
      field_simp
    linarith
  · have h3 : ((n13 : ℝ) * te + 2 * k * d13) / (d13 * te) ≤ (cu : ℝ) / ss := by
      rw [div_le_div_iff₀ (by positivity) hss']; linarith
    have h4 : ((n13 : ℝ) * te + 2 * k * d13) / (d13 * te) = (n13 : ℝ) / d13 + 2 * k / te := by
      field_simp
    linarith

/-! ### The polynomial bound -/

/-- `Q(x) = Σ_{i<n} q_i x^i` for a coefficient list. -/
noncomputable def Qv (qs : List ℤ) (x : ℝ) : ℝ :=
  ∑ i ∈ range qs.length, (qs.getD i 0 : ℝ) * x ^ i

/-- The Taylor coefficients at the midpoint, scaled: `Q'_i`. -/
def QpF (qs : List ℤ) (A : ℤ) (T : ℕ) (i : ℕ) : ℤ :=
  ∑ j ∈ range qs.length, if i ≤ j then qs.getD j 0 * (j.choose i : ℤ) * A ^ (j - i) *
    ((T : ℤ) ^ (qs.length - 1 - j)) else 0

/-- `U = Σ_i |Q'_i| R^i`. -/
def UbF (qs : List ℤ) (A : ℤ) (T R : ℕ) : ℕ :=
  ∑ i ∈ range qs.length, (QpF qs A T i).natAbs * R ^ i

/-- **Taylor expansion at `c₀ = A/T`**: if `|c − A/T| ≤ R/T`, then
`|Q(c)| ≤ U / T^{n−1}`. -/
lemma Ub_eq (qs : List ℤ) (A : ℤ) (T R : ℕ) : CramerCompute.Ub qs A T R = UbF qs A T R := by
  unfold CramerCompute.Ub UbF CramerCompute.Qp QpF
  rw [lsumN_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [lsum_eq]
  congr 2
  refine sum_congr rfl fun j _ => ?_
  rw [chooseC_eq]

lemma abs_Qv_le (qs : List ℤ) (hqs : qs ≠ []) {A : ℤ} {T R : ℕ} (hT : 0 < T) {c : ℝ}
    (hc : |c - (A : ℝ) / T| ≤ (R : ℝ) / T) :
    |Qv qs c| ≤ (CramerCompute.Ub qs A T R : ℝ) / (T : ℝ) ^ (qs.length - 1) := by
  set n := qs.length
  have hn : 1 ≤ n := by
    rcases qs with _ | ⟨a, l⟩
    · exact absurd rfl hqs
    · simp [n]
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set c0 : ℝ := (A : ℝ) / T
  set δ := c - c0
  -- `c^j = Σ_{i ≤ j} C(j,i) c0^{j−i} δ^i`
  have hexp : Qv qs c = ∑ i ∈ range n, ((QpF qs A T i : ℝ) / (T : ℝ) ^ (n - 1 - i)) * δ ^ i := by
    unfold Qv
    have hc : c = c0 + δ := by simp [δ]
    have e1 : ∀ j ∈ range n, (qs.getD j 0 : ℝ) * c ^ j =
        ∑ i ∈ range n, if i ≤ j then (qs.getD j 0 : ℝ) * (j.choose i : ℝ) * c0 ^ (j - i) * δ ^ i
          else 0 := by
      intro j hj
      rw [hc, add_comm, add_pow, mul_sum]
      have hjn : j + 1 ≤ n := mem_range.1 hj
      rw [← sum_range_add_sum_Ico _ hjn]
      have h0 : ∑ i ∈ Ico (j + 1) n, (if i ≤ j then (qs.getD j 0 : ℝ) * (j.choose i : ℝ) *
          c0 ^ (j - i) * δ ^ i else 0) = 0 :=
        sum_eq_zero fun i hi => by rw [if_neg (by have := (mem_Ico.1 hi).1; omega)]
      rw [h0, add_zero]
      refine sum_congr rfl fun i hi => ?_
      rw [if_pos (by have := mem_range.1 hi; omega)]
      ring
    rw [sum_congr rfl e1, sum_comm]
    refine sum_congr rfl fun i hi => ?_
    unfold QpF
    rw [Int.cast_sum, sum_div, sum_mul]
    refine sum_congr rfl fun j hj => ?_
    split_ifs with hij
    · have hjn : j ≤ n - 1 := by have := mem_range.1 hj; omega
      have hin : i ≤ n - 1 := by omega
      have hpowT : (T : ℝ) ^ (n - 1 - i) = (T : ℝ) ^ (n - 1 - j) * (T : ℝ) ^ (j - i) := by
        rw [← pow_add]; congr 1; omega
      simp only [c0]
      push_cast
      rw [hpowT, div_pow]
      field_simp
      rfl
    · simp
  rw [hexp]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [Ub_eq]
  unfold UbF
  push_cast
  rw [sum_div]
  refine sum_le_sum fun i hi => ?_
  have hin : i ≤ n - 1 := by have := mem_range.1 hi; omega
  rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (T : ℝ) ^ (n - 1 - i)), abs_pow]
  have hδ : |δ| ^ i ≤ ((R : ℝ) / T) ^ i := pow_le_pow_left₀ (abs_nonneg _) hc i
  have hpowT : (T : ℝ) ^ (n - 1) = (T : ℝ) ^ (n - 1 - i) * (T : ℝ) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [hpowT]
  have : |(QpF qs A T i : ℝ)| = ((QpF qs A T i).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]
  rw [div_pow] at hδ
  calc ((QpF qs A T i).natAbs : ℝ) / (T : ℝ) ^ (n - 1 - i) * |δ| ^ i
      ≤ ((QpF qs A T i).natAbs : ℝ) / (T : ℝ) ^ (n - 1 - i) * ((R : ℝ) ^ i / (T : ℝ) ^ i) := by
        gcongr
    _ = _ := by field_simp

/-! ### Monotonicity of `cos` between multiples of `π` -/

lemma cos_eq_neg_one_pow_mul (j : ℕ) (x : ℝ) : Real.cos x = (-1) ^ j * Real.cos (x - j * π) := by
  rw [Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, mul_zero, add_zero]
  have h : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc Real.cos x = ((-1 : ℝ) ^ j * (-1) ^ j) * Real.cos x := by rw [h, one_mul]
    _ = _ := by ring

lemma cos_between {j : ℕ} {a b θ : ℝ} (ha : j * π ≤ a) (hb : b ≤ (j + 1) * π) (h1 : a ≤ θ)
    (h2 : θ ≤ b) :
    min (Real.cos a) (Real.cos b) ≤ Real.cos θ ∧ Real.cos θ ≤ max (Real.cos a) (Real.cos b) := by
  have hpi := Real.pi_pos
  have key : ∀ x y, j * π ≤ x → x ≤ y → y ≤ (j + 1) * π →
      Real.cos (y - j * π) ≤ Real.cos (x - j * π) := fun x y hx hxy hy =>
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have k1 := key a θ ha h1 (by linarith)
  have k2 := key θ b (by linarith) h2 hb
  rw [cos_eq_neg_one_pow_mul j a, cos_eq_neg_one_pow_mul j b, cos_eq_neg_one_pow_mul j θ]
  rcases Nat.even_or_odd j with he | ho
  · rw [he.neg_one_pow]; simp only [one_mul]
    exact ⟨min_le_of_right_le k2, le_max_of_le_left k1⟩
  · rw [ho.neg_one_pow]; simp only [neg_one_mul]
    exact ⟨min_le_of_left_le (neg_le_neg k1), le_max_of_le_right (neg_le_neg k2)⟩

/-! ### The cell check -/

/-- The function bounded on the cells. -/
noncomputable def Fq (qs : List ℤ) (θ : ℝ) : ℝ :=
  (2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| / θ ^ 2

/-- The property certified for a cell. -/
def CellGood (qs : List ℤ) (GD : ℕ) (e e' : Ent) : Prop :=
  ∀ θ : ℝ, (e.N : ℝ) / D0 ≤ θ → θ ≤ (e'.N : ℝ) / D0 → 0 < θ → Fq qs θ ≤ (e.Gn : ℝ) / GD

lemma pi_bounds_scaled : (PIL : ℝ) / TE < π ∧ π < (PIH : ℝ) / TE := by
  constructor
  · have := Real.pi_gt_d20; simp only [PIL, TE]; norm_num at this ⊢; linarith
  · have := Real.pi_lt_d20; simp only [PIH, TE]; norm_num at this ⊢; linarith

lemma int_min_div (a b : ℤ) : ((min a b : ℤ) : ℝ) / SS = min ((a : ℝ) / SS) ((b : ℝ) / SS) := by
  push_cast; exact (min_div_div_right (by simp [SS]) _ _).symm

lemma int_max_div (a b : ℤ) : ((max a b : ℤ) : ℝ) / SS = max ((a : ℝ) / SS) ((b : ℝ) / SS) := by
  push_cast; exact (max_div_div_right (by simp [SS]) _ _).symm

/-- `cos θ ∈ [lo/S, hi/S]` on a checked cell. -/
lemma cos_in_range {e e' : Ent} (he : endOK e.N e.k e.cl e.cu = true)
    (he' : endOK e'.N e'.k e'.cl e'.cu = true) (hp : posOK e e' = true) {θ : ℝ}
    (h1 : (e.N : ℝ) / D0 ≤ θ) (h2 : θ ≤ (e'.N : ℝ) / D0) :
    (cLo e e' : ℝ) / SS ≤ Real.cos θ ∧ Real.cos θ ≤ (cHi e e' : ℝ) / SS := by
  obtain ⟨a1, a2⟩ := endOK_sound he
  obtain ⟨b1, b2⟩ := endOK_sound he'
  obtain ⟨pl, ph⟩ := pi_bounds_scaled
  have hD0 : (0 : ℝ) < D0 := by simp [D0]
  have hTE : (0 : ℝ) < TE := by simp [TE]
  have hSS : (0 : ℝ) < SS := by simp [SS]
  set ca := Real.cos ((e.N : ℝ) / D0)
  set cb := Real.cos ((e'.N : ℝ) / D0)
  have hmin : min ((e.cl : ℝ) / SS) ((e'.cl : ℝ) / SS) ≤ min ca cb := min_le_min a1 b1
  have hmax : max ca cb ≤ max ((e.cu : ℝ) / SS) ((e'.cu : ℝ) / SS) := max_le_max a2 b2
  simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨-, hb⟩, hrest⟩ := hp
  -- scaled position facts
  have up : ∀ (i N : ℕ), N * TE ≤ (i + 1) * PIL * D0 → (N : ℝ) / D0 ≤ (i + 1) * π := by
    intro i N h
    have h' : (N : ℝ) * TE ≤ (i + 1) * PIL * D0 := by exact_mod_cast h
    rw [div_le_iff₀ hD0]
    have : ((i : ℝ) + 1) * ((PIL : ℝ) / TE) ≤ (i + 1) * π := by gcongr
    calc (N : ℝ) = (N : ℝ) * TE / TE := by field_simp
      _ ≤ (i + 1) * PIL * D0 / TE := div_le_div_of_nonneg_right h' hTE.le
      _ = ((i : ℝ) + 1) * ((PIL : ℝ) / TE) * D0 := by field_simp
      _ ≤ (i + 1) * π * D0 := by gcongr
  have down : ∀ (i N : ℕ), i * PIH * D0 ≤ N * TE → (i : ℝ) * π ≤ (N : ℝ) / D0 := by
    intro i N h
    have h' : (i : ℝ) * PIH * D0 ≤ N * TE := by exact_mod_cast h
    rw [le_div_iff₀ hD0]
    have : (i : ℝ) * π ≤ i * ((PIH : ℝ) / TE) := by gcongr
    calc (i : ℝ) * π * D0 ≤ i * ((PIH : ℝ) / TE) * D0 := by gcongr
      _ = i * PIH * D0 / TE := by field_simp
      _ ≤ N * TE / TE := div_le_div_of_nonneg_right h' hTE.le
      _ = N := by field_simp
  have hbR := up e.j e'.N hb
  unfold cLo cHi
  by_cases hfl : e.fl = 0
  · simp only [hfl, if_true, decide_eq_true_eq] at hrest ⊢
    obtain ⟨c1, c2⟩ := cos_between (j := e.j) (down _ _ hrest) hbR h1 h2
    rw [int_min_div, int_max_div]
    exact ⟨hmin.trans c1, c2.trans hmax⟩
  · simp only [hfl, if_false, Bool.and_eq_true, decide_eq_true_eq] at hrest ⊢
    obtain ⟨hj1, hrest⟩ := hrest
    have ha := down _ _ hrest
    have hjc : ((e.j - 1 : ℕ) : ℝ) + 1 = e.j := by rw [Nat.cast_sub hj1]; push_cast; ring
    have hcj : Real.cos (e.j * π) = (-1) ^ e.j := Real.cos_nat_mul_pi e.j
    have hca1 : ca ≤ 1 := Real.cos_le_one _
    have hcb1 : cb ≤ 1 := Real.cos_le_one _
    have hca2 : -1 ≤ ca := Real.neg_one_le_cos _
    have hcb2 : -1 ≤ cb := Real.neg_one_le_cos _
    have left : θ ≤ e.j * π → min ca (Real.cos (e.j * π)) ≤ Real.cos θ ∧
        Real.cos θ ≤ max ca (Real.cos (e.j * π)) := fun hθ =>
      cos_between (j := e.j - 1) ha (by rw [hjc]) h1 hθ
    have right : e.j * π ≤ θ → min (Real.cos (e.j * π)) cb ≤ Real.cos θ ∧
        Real.cos θ ≤ max (Real.cos (e.j * π)) cb := fun hθ =>
      cos_between (j := e.j) le_rfl hbR hθ h2
    rcases Nat.even_or_odd e.j with hev | hod
    · have hj2 : e.j % 2 = 0 := Nat.even_iff.1 hev
      simp only [hj2, if_true]
      rw [hev.neg_one_pow] at hcj
      rw [int_min_div]
      refine ⟨hmin.trans ?_, ?_⟩
      · rcases le_total θ (e.j * π) with hθ | hθ
        · have := (left hθ).1; rw [hcj, min_eq_left hca1] at this
          exact (min_le_left _ _).trans this
        · have := (right hθ).1; rw [hcj, min_eq_right hcb1] at this
          exact (min_le_right _ _).trans this
      · push_cast; rw [div_self hSS.ne']; exact Real.cos_le_one θ
    · have hj2 : e.j % 2 = 1 := Nat.odd_iff.1 hod
      simp only [hj2, show (1 : ℕ) ≠ 0 by norm_num, if_false]
      rw [hod.neg_one_pow] at hcj
      rw [int_max_div]
      refine ⟨?_, le_trans ?_ hmax⟩
      · push_cast; rw [neg_div, div_self hSS.ne']; exact Real.neg_one_le_cos θ
      · rcases le_total θ (e.j * π) with hθ | hθ
        · have := (left hθ).2; rw [hcj, max_eq_left hca2] at this
          exact this.trans (le_max_left _ _)
        · have := (right hθ).2; rw [hcj, max_eq_right hcb2] at this
          exact this.trans (le_max_right _ _)

lemma cosP_four (x : ℝ) : cosP 4 x = 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
  simp [cosP, sum_range_succ, Nat.factorial]; ring

/-- `(2 − 2cos θ)/θ² ≤ 1 − θ²/12 + θ⁴/360`. -/
lemma sinc_sq_le {θ : ℝ} (hθ : 0 < θ) :
    (2 - 2 * Real.cos θ) / θ ^ 2 ≤ 1 - θ ^ 2 / 12 + θ ^ 4 / 360 := by
  have h := cosP_le_cos_of_even (n := 4) (by norm_num) (by decide) θ
  rw [cosP_four] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Soundness of one cell.** -/
theorem cell_sound (qs : List ℤ) (hqs : qs ≠ []) (GD : ℕ) (hGD : 0 < GD) {e e' : Ent}
    (he : endOK e.N e.k e.cl e.cu = true) (he' : endOK e'.N e'.k e'.cl e'.cu = true)
    (hp : posOK e e' = true) (hb : boundOK qs GD e e' = true) : CellGood qs GD e e' := by
  intro θ h1 h2 hθ
  obtain ⟨c1, c2⟩ := cos_in_range he he' hp h1 h2
  set lo := cLo e e'
  set hi := cHi e e'
  have hD0 : (0 : ℝ) < D0 := by simp [D0]
  have hSS : (0 : ℝ) < SS := by simp [SS]
  have hGD' : (0 : ℝ) < GD := by exact_mod_cast hGD
  simp only [boundOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hlohi, hrest⟩ := hb
  set K := qs.length - 1
  set U := CramerCompute.Ub qs (lo + hi) (2 * SS) (hi - lo).toNat
  -- the polynomial bound
  have hR : (((hi - lo).toNat : ℕ) : ℝ) = (hi : ℝ) - lo := by
    rw [show (((hi - lo).toNat : ℕ) : ℝ) = (((hi - lo).toNat : ℤ) : ℝ) by push_cast; rfl,
      Int.toNat_of_nonneg (by linarith)]
    push_cast; ring
  have hcm : |Real.cos θ - ((lo + hi : ℤ) : ℝ) / ((2 * SS : ℕ) : ℝ)| ≤
      (((hi - lo).toNat : ℕ) : ℝ) / ((2 * SS : ℕ) : ℝ) := by
    rw [hR, abs_le]
    push_cast
    constructor
    · rw [show ((lo : ℝ) + hi) / (2 * SS) = (lo / SS + hi / SS) / 2 by field_simp,
        show ((hi : ℝ) - lo) / (2 * SS) = (hi / SS - lo / SS) / 2 by field_simp]
      linarith
    · rw [show ((lo : ℝ) + hi) / (2 * SS) = (lo / SS + hi / SS) / 2 by field_simp,
        show ((hi : ℝ) - lo) / (2 * SS) = (hi / SS - lo / SS) / 2 by field_simp]
      linarith
  have hQ := abs_Qv_le qs hqs (T := 2 * SS) (by simp [SS]) hcm
  have hT0 : (0 : ℝ) < ((2 * SS : ℕ) : ℝ) := by simp [SS]
  have hTK : (0 : ℝ) < ((2 * SS : ℕ) : ℝ) ^ K := pow_pos hT0 K
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hc2 : 0 ≤ 2 - 2 * Real.cos θ := by linarith [Real.cos_le_one θ]
  unfold Fq
  by_cases htg : e.tg = 0
  · simp only [htg, if_true, Bool.and_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨⟨hN15, hmain⟩, hpos⟩ := hrest
    have hθ15 : θ ^ 2 ≤ 15 := by
      have : (e'.N : ℝ) ^ 2 ≤ 15 * D0 ^ 2 := by exact_mod_cast hN15
      have h2' : θ ^ 2 ≤ ((e'.N : ℝ) / D0) ^ 2 := pow_le_pow_left₀ hθ.le h2 2
      rw [div_pow, le_div_iff₀ (by positivity)] at h2'
      have hD2 : (0 : ℝ) < (D0 : ℝ) ^ 2 := by positivity
      exact le_of_mul_le_mul_right (by linarith) hD2
    set a := (e.N : ℝ) / D0
    have ha0 : 0 ≤ a := by positivity
    have hsinc := sinc_sq_le hθ
    have hmono : 1 - θ ^ 2 / 12 + θ ^ 4 / 360 ≤ 1 - a ^ 2 / 12 + a ^ 4 / 360 := by
      have ha2 : a ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ ha0 h1 2
      nlinarith [sq_nonneg a, sq_nonneg θ]
    have hfac : 1 - a ^ 2 / 12 + a ^ 4 / 360 =
        ((360 * D0 ^ 4 + e.N ^ 4 - 30 * e.N ^ 2 * D0 ^ 2 : ℕ) : ℝ) / (360 * (D0 : ℝ) ^ 4) := by
      rw [Nat.cast_sub hpos]; push_cast; simp only [a]; field_simp; ring
    have hmain' : ((360 * D0 ^ 4 + e.N ^ 4 - 30 * e.N ^ 2 * D0 ^ 2 : ℕ) : ℝ) * U * GD ≤
        e.Gn * 360 * D0 ^ 4 * ((2 * SS : ℕ) : ℝ) ^ K := by exact_mod_cast hmain
    have hF0 : 0 ≤ ((360 * D0 ^ 4 + e.N ^ 4 - 30 * e.N ^ 2 * D0 ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| / θ ^ 2
        = (2 - 2 * Real.cos θ) / θ ^ 2 * |Qv qs (Real.cos θ)| := by ring
      _ ≤ (1 - a ^ 2 / 12 + a ^ 4 / 360) * ((U : ℝ) / ((2 * SS : ℕ) : ℝ) ^ K) := by
          apply mul_le_mul (hsinc.trans hmono) hQ (abs_nonneg _)
          nlinarith [div_nonneg hc2 (sq_nonneg θ)]
      _ ≤ (e.Gn : ℝ) / GD := by
          rw [hfac, div_mul_div_comm, div_le_div_iff₀ (by positivity) hGD']
          nlinarith
  · simp only [htg, if_false, Bool.and_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨hN0, hmain⟩ := hrest
    have hN0' : (0 : ℝ) < e.N := by exact_mod_cast hN0
    have hmain' : (2 * (SS : ℝ) - 2 * lo) * U * GD * D0 ^ 2 ≤
        e.Gn * (e.N : ℝ) ^ 2 * SS * ((2 * SS : ℕ) : ℝ) ^ K := by
      have := hmain; exact_mod_cast this
    have hc3 : 2 - 2 * Real.cos θ ≤ (2 * (SS : ℝ) - 2 * lo) / SS := by
      rw [sub_div, mul_div_assoc, div_self hSS.ne', mul_one, mul_div_assoc]; linarith
    have hθa : ((e.N : ℝ) / D0) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have hθ2 : 1 / θ ^ 2 ≤ (D0 : ℝ) ^ 2 / (e.N : ℝ) ^ 2 := by
      rw [div_pow] at hθa
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hθa
      nlinarith
    have hnum : 0 ≤ (2 * (SS : ℝ) - 2 * lo) := by
      have : (lo : ℝ) / SS ≤ 1 := c1.trans (Real.cos_le_one θ)
      rw [div_le_one hSS] at this; linarith
    calc (2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| / θ ^ 2
        = (2 - 2 * Real.cos θ) * |Qv qs (Real.cos θ)| * (1 / θ ^ 2) := by ring
      _ ≤ ((2 * (SS : ℝ) - 2 * lo) / SS) * ((U : ℝ) / ((2 * SS : ℕ) : ℝ) ^ K) *
          ((D0 : ℝ) ^ 2 / (e.N : ℝ) ^ 2) := by
          gcongr
      _ ≤ (e.Gn : ℝ) / GD := by
          rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ (by positivity) hGD']
          nlinarith

/-- **Soundness of the list check**: every consecutive pair of entries is a good cell. -/
theorem chk_sound (qs : List ℤ) (hqs : qs ≠ []) (GD : ℕ) (hGD : 0 < GD) :
    ∀ L : List Ent, chk qs GD L = true → List.IsChain (CellGood qs GD) L := by
  intro L
  induction L with
  | nil => intro _; exact List.IsChain.nil
  | cons e rest ih =>
    intro h
    cases rest with
    | nil => exact List.IsChain.singleton e
    | cons e' rest' =>
      simp only [chk, Bool.and_eq_true] at h
      obtain ⟨⟨⟨he, hp⟩, hb⟩, hrest⟩ := h
      have hrest' := hrest
      cases rest' with
      | nil =>
        simp only [chk] at hrest'
        exact List.IsChain.cons_cons (cell_sound qs hqs GD hGD he hrest' hp hb) (List.IsChain.singleton e')
      | cons e'' rest'' =>
        simp only [chk, Bool.and_eq_true] at hrest'
        exact List.IsChain.cons_cons (cell_sound qs hqs GD hGD he hrest'.1.1.1 hp hb) (ih hrest)

end Cramer.CMS
