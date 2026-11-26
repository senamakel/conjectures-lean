import Shoup.Rosser.Rows

/-!
# The Rosser sieve bounds, by induction over the fuel

For a finite set `Q` of primes `q > 2^E` below `z` and a level `Y > 0`, with `s = log Y/log z`:

* for every cell `(g, β, α)` of `cells` and `s ≥ g/100`: `U(Q, Y) ≤ V(Q) (1 + β/D)`, and if
  `g ≥ 200`, `L(Q, Y) ≥ V(Q) (1 - α/D)`;
* for `s ≥ 12`: `U ≤ V (1 + s^{-6})` and `L ≥ V (1 - s^{-6})`.

Each step is one row of the table (`allOK_cells`), through `step_lower`/`step_upper` and
`row_bound`.
-/

namespace Shoup.Rosser

open Finset Shoup.Fixed Shoup.Sieve

/-- The admissible prime sets below `z`. -/
def Good (Q : Finset ℕ) (z : ℝ) : Prop :=
  (∀ q ∈ Q, q.Prime ∧ 2 ^ E < q ∧ (q : ℝ) < z) ∧ (2 : ℝ) ^ E < z

/-- The four bounds at fuel `n`, for a table `cells`. -/
def ClaimsAt (cells : List Ent) (n : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ z Y : ℝ, Good Q z → 0 < Y →
    (∀ c ∈ cells, (c.1 : ℝ) / 100 * Real.log z ≤ Real.log Y →
      ros n false Q Y recip ≤ V Q * (1 + r c.2.1)) ∧
    (∀ c ∈ cells, 200 ≤ c.1 → (c.1 : ℝ) / 100 * Real.log z ≤ Real.log Y →
      V Q * (1 - r c.2.2) ≤ ros n true Q Y recip) ∧
    (12 * Real.log z ≤ Real.log Y →
      ros n false Q Y recip ≤ V Q * (1 + (Real.log z / Real.log Y) ^ 6)) ∧
    (12 * Real.log z ≤ Real.log Y →
      V Q * (1 - (Real.log z / Real.log Y) ^ 6) ≤ ros n true Q Y recip)

/-! ### Facts extracted from the table check -/

lemma allOK_parts {cells : List Ent} (h : allOK cells = true) :
    (∀ c ∈ cells, (decide (c.1 < 200) || lrowOK cells c) = true ∧ urowOK cells c = true) ∧
    tailCells cells = true ∧
    (∃ c ∈ cells, c.1 = 210 ∧ c.2.2 ≤ Dn) := by
  unfold allOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact ⟨fun c hc => h.1.1.1 c hc, h.1.1.2, h.1.2⟩

lemma rowTail_parts {l : List Ent} {S t : ℕ} (h : rowTail l S t = true) :
    chainOK l = true ∧ boundsOK l 1300 S = true ∧ 0 < S ∧ S ≤ 1300 ∧
      momU l 1300 S + crudeU 1300 S ≤ t := by
  unfold rowTail at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma tailOK_parts {X : ℕ} (h : tailOK X = true) :
    chainOK (entsT X) = true ∧ boundsOK (entsT X) 4 1 = true ∧
      momU (entsT X) 4 1 + tailCrude ≤ Dn := by
  unfold tailOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma r_Dn' : r Dn = 1 := r_Dn

/-! ### Real inequalities used at each prime -/

/-- From `12·2^k lp ≤ lY - lp`: `(lp/(lY - lp))^6 ≤ 12^{-6}/64^k`. -/
lemma pow6_le_of {lp lY : ℝ} (k : ℕ) (hp : 0 < lp) (h : 12 * 2 ^ k * lp ≤ lY - lp) :
    (lp / (lY - lp)) ^ 6 ≤ 1 / 12 ^ 6 / 64 ^ k := by
  have hpos : 0 < lY - lp := lt_of_lt_of_le (by positivity) h
  have h1 : lp / (lY - lp) ≤ 1 / (12 * 2 ^ k) := by
    rw [div_le_div_iff₀ hpos (by positivity)]; linarith
  have h2 := pow_le_pow_left₀ (div_nonneg hp.le hpos.le) h1 6
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, mul_pow, ← pow_mul, show (64 : ℝ) ^ k = 2 ^ (k * 6) by
    rw [pow_mul']; norm_num]
  field_simp

/-- The tail normalisation: `(lp/(lY-lp))^6 ≤ (lz/lY)^6 (lz/lp - 1/12)^{-6}` when `12 lz ≤ lY`. -/
lemma tail_ratio {lp lz lY : ℝ} (hp : 0 < lp) (hpz : lp < lz) (hY : 12 * lz ≤ lY) :
    (lp / (lY - lp)) ^ 6 ≤ (lz / lY) ^ 6 * (1 / (lz / lp - 1 / 12) ^ 6) := by
  have hz : 0 < lz := hp.trans hpz
  have hYp : 0 < lY := by linarith
  have h1 : 0 < lY - lp := by linarith
  have h2 : 0 < lz / lp - 1 / 12 := by
    rw [sub_pos, lt_div_iff₀ hp]; linarith
  rw [← one_div_pow, ← mul_pow, ← div_eq_mul_one_div]
  apply pow_le_pow_left₀ (div_nonneg hp.le h1.le)
  rw [div_le_div_iff₀ h1 h2, div_mul_eq_mul_div, le_div_iff₀ hYp]
  have e : lz / lp - 1 / 12 = (12 * lz - lp) / (12 * lp) := by field_simp
  rw [e, mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hp hz, mul_pos hp hp]

/-- `ψ(u) = (u - 1/12)^{-6}` is antitone. -/
lemma psi_anti {a b : ℝ} (ha : 1 / 12 < a) (hab : a ≤ b) :
    1 / (b - 1 / 12) ^ 6 ≤ 1 / (a - 1 / 12) ^ 6 := by
  apply one_div_le_one_div_of_le (by have : 0 < a - 1 / 12 := by linarith
                                     positivity)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 6

lemma psi_dyadic {u : ℝ} (k : ℕ) (hu : 4 * 2 ^ k < u) :
    1 / (u - 1 / 12) ^ 6 ≤ 1 / ((4 : ℝ) - 1 / 12) ^ 6 / 64 ^ k := by
  have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h1 : 2 ^ k * (4 - 1 / 12) ≤ u - 1 / 12 := by nlinarith
  have hp : 0 < (2 : ℝ) ^ k * (4 - 1 / 12) := by positivity
  calc 1 / (u - 1 / 12) ^ 6 ≤ 1 / (2 ^ k * (4 - 1 / 12)) ^ 6 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le h1 6)
    _ = 1 / ((4 : ℝ) - 1 / 12) ^ 6 / 64 ^ k := by
        rw [mul_pow, ← pow_mul, show (64 : ℝ) ^ k = 2 ^ (k * 6) by rw [pow_mul']; norm_num]
        field_simp

lemma incl_of {p : ℕ} {Y : ℝ} (hp : 0 < (p : ℝ)) (hY : 0 < Y)
    (h : 31 * Real.log p < 10 * Real.log Y) : (p : ℝ) ^ 31 < Y ^ 10 := by
  rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast; linarith

lemma entsT_eq (X : ℕ) : entsT X = (120, 120, tH X (120, 120)) :: (entsT X).tail := rfl

lemma tH_ge_psi (X : ℕ) (x : ℕ × ℕ) : psiU x.1 x.2 ≤ tH X x := by
  unfold tH; split_ifs
  · exact le_max_right _ _
  · exact le_rfl

lemma tH_ge_X (X : ℕ) (x : ℕ × ℕ) (h : 12 * x.1 < 13 * x.2) : X ≤ tH X x := by
  unfold tH; rw [if_pos h]; exact le_max_left _ _

/-- The tail rows, normalised: if each `h_p` is at most `ε ψ(u_p)`, or (for `u_p < 13/12`) at
most `ε X/D`, then `Σ w_p h_p ≤ ε`. -/
lemma tail_core (Q : Finset ℕ) (w u h : ℕ → ℝ) (hw : ∀ p ∈ Q, 0 ≤ w p)
    (hcum : ∀ s, 1 ≤ s → ∑ p ∈ Q.filter (fun p => u p ≤ s), w p ≤ Om s - 1)
    (X : ℕ) (hX : tailOK X = true) (ε : ℝ) (hε : 0 < ε) (hu1 : ∀ p ∈ Q, 1 < u p)
    (hcase : ∀ p ∈ Q, h p ≤ ε * (1 / (u p - 1 / 12) ^ 6) ∨ (u p < 13 / 12 ∧ h p ≤ ε * r X)) :
    ∑ p ∈ Q, w p * h p ≤ ε := by
  obtain ⟨hch, hbd, hfin⟩ := tailOK_parts hX
  set h2 : ℕ → ℝ := fun p => h p / ε with hh2
  have hgood := goodL_of (entsT X) 4 1 (by norm_num) hch hbd
  have hte : (1 : ℝ) ≤ ((4 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
  have hcaseh2 : ∀ p ∈ Q, h2 p ≤ 1 / (u p - 1 / 12) ^ 6 ∨ (u p < 13 / 12 ∧ h2 p ≤ r X) := by
    intro p hp
    rcases hcase p hp with h1 | ⟨h1, h2'⟩
    · left; simp only [hh2]; rw [div_le_iff₀ hε]; linarith
    · right; refine ⟨h1, ?_⟩; simp only [hh2]; rw [div_le_iff₀ hε]; linarith
  have hentall : ∀ p ∈ Q, ∀ e ∈ entsT X, (toR e).1 < u p → h2 p ≤ (toR e).2 := by
    intro p hp e he heu
    obtain ⟨hb0, hba, _⟩ := boundsOK_mem hbd he
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp he
    simp only [toR] at heu ⊢
    have hbR : (0 : ℝ) < x.2 := by exact_mod_cast hb0
    have hab1 : (1 : ℝ) ≤ (x.1 : ℝ) / x.2 := by
      rw [le_div_iff₀ hbR, one_mul]; exact_mod_cast hba
    rcases hcaseh2 p hp with hA | ⟨hB1, hB2⟩
    · refine hA.trans ((psi_anti (by linarith) heu.le).trans ?_)
      refine (psi_sound hb0 (by omega)).trans (r_mono (tH_ge_psi X x))
    · refine hB2.trans (r_mono (tH_ge_X X x ?_))
      have : (x.1 : ℝ) / x.2 < 13 / 12 := heu.trans hB1
      rw [div_lt_div_iff₀ hbR (by norm_num)] at this
      exact_mod_cast (by linarith : (12 : ℝ) * x.1 < 13 * x.2)
  have hrb := row_bound Q w u h2 hw hcum (toR (120, 120, tH X (120, 120)))
    ((entsT X).tail.map toR) (((4 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) (1 / ((4 : ℝ) - 1 / 12) ^ 6) hte
    (by positivity)
    (by have := hgood; rw [entsT_eq, List.map_cons] at this; exact this)
    (fun p hp _ => hentall p hp _ (by rw [entsT_eq]; exact List.mem_cons_self ..)
      (by simp only [toR]; norm_num; exact hu1 p hp))
    (fun p hp _ y hy hyu => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      exact hentall p hp e (by rw [entsT_eq]; exact List.mem_cons_of_mem _ he) hyu)
    (fun p hp hlt k hk => by
      simp only [Nat.cast_ofNat, Nat.cast_one, div_one] at hlt hk
      rcases hcaseh2 p hp with hA | ⟨hB1, _⟩
      · exact hA.trans (psi_dyadic k hk)
      · exfalso; linarith)
  have hmom := momR_le 4 1 (by norm_num) (by norm_num) (entsT X) hch hbd
  have hcr := tailCrude_sound
  have e : toR (120, 120, tH X (120, 120)) :: ((entsT X).tail.map toR) = (entsT X).map toR := by
    conv_rhs => rw [entsT_eq]
    rw [List.map_cons]
  rw [e] at hrb
  simp only [Nat.cast_ofNat, Nat.cast_one, div_one] at hrb hmom
  have hfin' := r_mono hfin
  rw [r_add, r_Dn'] at hfin'
  have hsum : ∑ p ∈ Q, w p * h2 p ≤ 1 := by linarith
  have e2 : ∑ p ∈ Q, w p * h2 p = (∑ p ∈ Q, w p * h p) / ε := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun p _ => by simp only [hh2]; ring
  rw [e2, div_le_iff₀ hε] at hsum
  linarith

lemma tail_case {lp lz lY hh B : ℝ} (hlp : 0 < lp) (hlt : lp < lz) (hs : 12 * lz ≤ lY)
    (hB0 : 0 ≤ B) (hA : 12 * lp ≤ lY - lp → hh ≤ (lp / (lY - lp)) ^ 6)
    (hB : 11 * lp ≤ lY - lp → hh ≤ B) :
    hh ≤ (lz / lY) ^ 6 * (1 / (lz / lp - 1 / 12) ^ 6) ∨
      (lz / lp < 13 / 12 ∧ hh ≤ (lz / lY) ^ 6 * (13 ^ 6 * B)) := by
  by_cases h12 : 12 * lp ≤ lY - lp
  · exact Or.inl ((hA h12).trans (tail_ratio hlp hlt hs))
  · right
    push Not at h12
    have hlY : 0 < lY := by linarith
    have hB' := hB (by linarith)
    refine ⟨?_, ?_⟩
    · rw [div_lt_iff₀ hlp]; linarith
    · have h1 : 1 / 13 ≤ lz / lY := by
        rw [div_le_div_iff₀ (by norm_num) hlY]; linarith
      have h2 := pow_le_pow_left₀ (by norm_num) h1 6
      have hε13 : 1 ≤ 13 ^ 6 * (lz / lY) ^ 6 := by
        have : (1 / 13 : ℝ) ^ 6 * 13 ^ 6 = 1 := by norm_num
        nlinarith
      have : B ≤ (lz / lY) ^ 6 * (13 ^ 6 * B) := by nlinarith
      linarith

/-! ### The induction -/

set_option maxHeartbeats 4000000 in
theorem claims_of (cells : List Ent) (hok : allOK cells = true) :
    ∀ (n : ℕ) (Q : Finset ℕ), Q.card ≤ n → ClaimsAt cells n Q := by
  obtain ⟨hrows, htailc, ⟨c210, hc210, hc210g, hc210a⟩⟩ := allOK_parts hok
  intro n
  induction n with
  | zero =>
    intro Q hQ z Y _ _
    have hQe : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hQe
    simp only [ros, V, Finset.prod_empty, one_mul]
    refine ⟨fun c _ _ => ?_, fun c _ _ _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · have := r_nonneg c.2.1; linarith
    · have := r_nonneg c.2.2; linarith
    · have : 0 ≤ (Real.log z / Real.log Y) ^ 6 := by positivity
      linarith
    · have : 0 ≤ (Real.log z / Real.log Y) ^ 6 := by positivity
      linarith
  | succ n ih =>
    intro Q hQc z Y hG hY
    obtain ⟨hQ, hz⟩ := hG
    have hQ2 : ∀ q ∈ Q, 2 ≤ q := fun q h => (hQ q h).1.two_le
    have hE1 : (1 : ℝ) < 2 ^ E := one_lt_pow₀ (by norm_num) (by have := E_ge; omega)
    have hlz : 0 < Real.log z := Real.log_pos (hE1.trans hz)
    -- facts at each prime
    have hlp : ∀ p ∈ Q, 0 < Real.log p := fun p h =>
      Real.log_pos (by exact_mod_cast (hQ p h).1.one_lt)
    have hp0 : ∀ p ∈ Q, (0 : ℝ) < p := fun p h => by exact_mod_cast (hQ p h).1.pos
    have hlpz : ∀ p ∈ Q, Real.log p < Real.log z := fun p h =>
      Real.log_lt_log (hp0 p h) (hQ p h).2.2
    have hlogYp : ∀ p ∈ Q, Real.log (Y / p) = Real.log Y - Real.log p := fun p h =>
      Real.log_div hY.ne' (hp0 p h).ne'
    have IH : ∀ p ∈ Q, ClaimsAt cells n (Q.filter (· < p)) := fun p h =>
      ih _ (by have := card_filter_lt_lt h; omega)
    have hGp : ∀ p ∈ Q, Good (Q.filter (· < p)) p := by
      intro p hp
      refine ⟨fun q hq => ?_, by exact_mod_cast (hQ p hp).2.1⟩
      obtain ⟨hqQ, hqp⟩ := Finset.mem_filter.mp hq
      exact ⟨(hQ q hqQ).1, (hQ q hqQ).2.1, by exact_mod_cast hqp⟩
    have hYp : ∀ p ∈ Q, 0 < Y / p := fun p h => div_pos hY (hp0 p h)
    have C := fun p (hp : p ∈ Q) => IH p hp p (Y / p) (hGp p hp) (hYp p hp)
    have hVp : ∀ p, 0 < V (Q.filter (· < p)) := fun p =>
      V_pos _ fun q h => hQ2 q (Finset.mem_filter.mp h).1
    -- the weights and the cumulative bound
    set w : ℕ → ℝ := fun p => recip p * Wt Q p with hw
    set u : ℕ → ℝ := fun p => Real.log z / Real.log p with hu
    have hw0 : ∀ p ∈ Q, 0 ≤ w p := fun p _ => mul_nonneg (recip_nonneg p) (Wt_nonneg Q hQ2 p)
    have hcum : ∀ s, 1 ≤ s → ∑ p ∈ Q.filter (fun p => u p ≤ s), w p ≤ Om s - 1 := by
      intro s hs
      have e : Q.filter (fun p => u p ≤ s) = Q.filter (fun p : ℕ => Real.log z ≤ s * Real.log p) := by
        refine Finset.filter_congr fun p hp => ?_
        simp only [hu]
        rw [div_le_iff₀ (hlp p hp)]
      rw [e]
      exact cum_le Q z (fun q h => hQ q h) s hs
    -- `u_p > t` in logarithms
    have hut : ∀ p ∈ Q, ∀ (a b : ℕ), 0 < b → (a : ℝ) / b < u p →
        (a : ℝ) * Real.log p < b * Real.log z := by
      intro p hp a b hb h
      simp only [hu] at h
      rw [div_lt_div_iff₀ (by exact_mod_cast hb) (hlp p hp)] at h
      linarith
    have hU1 : ∀ p ∈ Q, 1 < u p := fun p hp => by
      simp only [hu]; rw [one_lt_div (hlp p hp)]; exact hlpz p hp
    -- the lower step written with `h_p = U_p / V_p - 1`
    set U' : ℕ → ℝ := fun p => ros n false (Q.filter (· < p)) (Y / p) recip with hU'
    set hL : ℕ → ℝ := fun p => U' p / V (Q.filter (· < p)) - 1 with hhL
    have hLeq : ros (n + 1) true Q Y recip = V Q * (1 - ∑ p ∈ Q, w p * hL p) := by
      rw [ros_succ, sel_true]
      simp only [Bool.not_true]
      rw [step_lower Q hQ2]
    have hLle : ∀ p ∈ Q, ∀ B : ℝ, U' p ≤ V (Q.filter (· < p)) * (1 + B) → hL p ≤ B := by
      intro p _ B h
      simp only [hhL]
      have := (div_le_iff₀ (hVp p)).mpr (show U' p ≤ (1 + B) * V (Q.filter (· < p)) by linarith)
      linarith
    -- the upper step
    set Sel := sel false Q Y with hSel
    set L' : ℕ → ℝ := fun p => ros n true (Q.filter (· < p)) (Y / p) recip with hL'
    set hU : ℕ → ℝ := fun p =>
      if p ∈ Sel then 1 - L' p / V (Q.filter (· < p)) else 1 with hhU
    have hUeq : ros (n + 1) false Q Y recip = V Q * (1 + ∑ p ∈ Q, w p * hU p) := by
      rw [ros_succ]
      simp only [Bool.not_false]
      rw [step_upper Q Sel (sel_subset false Q Y) hQ2]
    have hUle : ∀ p ∈ Q, p ∈ Sel → ∀ B : ℝ, V (Q.filter (· < p)) * (1 - B) ≤ L' p → hU p ≤ B := by
      intro p _ hpS B h
      simp only [hhU, if_pos hpS]
      have := (le_div_iff₀ (hVp p)).mpr (show (1 - B) * V (Q.filter (· < p)) ≤ L' p by linarith)
      linarith
    have hSel_of : ∀ p ∈ Q, 31 * Real.log p < 10 * Real.log Y → p ∈ Sel := fun p hp h =>
      mem_sel_false.mpr ⟨hp, incl_of (hp0 p hp) hY h⟩
    have hVQ := V_pos Q hQ2
    -- the four claims
    refine ⟨?_, ?_, ?_, ?_⟩
    · ------------------------------------------------------------------ upper rows
      intro c hc hs
      have hrow := rowTail_parts (hrows c hc).2
      obtain ⟨hch, hbd, hS0, hS13, hfin⟩ := hrow
      set S := c.1 with hSdef
      have hSR : (0 : ℝ) < S := by exact_mod_cast hS0
      set l := entsU cells S with hl
      have hgood := goodL_of l 1300 S hS0 hch hbd
      have hte : (1 : ℝ) ≤ (1300 : ℕ) / (S : ℝ) := by
        rw [le_div_iff₀ hSR, one_mul]; exact_mod_cast hS13
      -- the head
      have hhead : ∀ p ∈ Q, hU p ≤ r (headU cells S) := by
        intro p hp
        unfold headU
        split
        · rename_i hnone
          rw [r_Dn']
          by_cases hpS : p ∈ Sel
          · have h210 : (210 : ℝ) / 100 * Real.log p ≤ Real.log (Y / p) := by
              rw [hlogYp p hp]
              have := (mem_sel_false.mp hpS).2
              have h31 : 31 * Real.log p < 10 * Real.log Y := by
                have := Real.log_lt_log (pow_pos (hp0 p hp) 31) this
                rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
              linarith
            have hcl := (C p hp).2.1 c210 hc210 (by omega) (by rw [hc210g]; exact_mod_cast h210)
            have := hUle p hp hpS _ hcl
            have : r c210.2.2 ≤ 1 := by rw [← r_Dn']; exact r_mono hc210a
            linarith
          · simp only [hhU, if_neg hpS]; exact le_rfl
        · rename_i c0 hc0
          have hmem := List.mem_of_getLast? hc0
          obtain ⟨hc0m, hc0p⟩ := List.mem_filter.mp hmem
          simp only [decide_eq_true_eq] at hc0p
          obtain ⟨h210, hle⟩ := hc0p
          have hle' : ((c0.1 : ℝ) + 100) ≤ S := by exact_mod_cast hle
          have hlt := hlpz p hp
          have hs' : (S : ℝ) / 100 * Real.log z ≤ Real.log Y := hs
          have hkey : ((c0.1 : ℝ) + 100) * Real.log p < 100 * Real.log Y := by
            have := hlp p hp
            nlinarith
          have h210R : (210 : ℝ) ≤ c0.1 := by exact_mod_cast h210
          have hpS : p ∈ Sel := hSel_of p hp (by nlinarith [hlp p hp])
          have hcl := (C p hp).2.1 c0 hc0m (by omega) (by
            rw [hlogYp p hp]; nlinarith)
          exact hUle p hp hpS _ hcl
      -- the entries
      have hent : ∀ p ∈ Q, u p ≤ (1300 : ℕ) / (S : ℝ) → ∀ y ∈ (l.map toR).tail, y.1 < u p →
          hU p ≤ y.2 := by
        intro p hp _ y hy hyu
        rw [hl, entsU, List.map_cons, List.tail_cons] at hy
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        obtain ⟨hdm, hdp⟩ := List.mem_filter.mp hd
        simp only [decide_eq_true_eq] at hdp
        have h1 := hut p hp (d.1 + 100) S hS0 hyu
        have hs' : (S : ℝ) / 100 * Real.log z ≤ Real.log Y := hs
        have h210R : (210 : ℝ) ≤ d.1 := by exact_mod_cast hdp.1
        push_cast at h1
        have hpS : p ∈ Sel := hSel_of p hp (by nlinarith [hlp p hp])
        have hcl := (C p hp).2.1 d hdm (by omega) (by rw [hlogYp p hp]; nlinarith)
        exact hUle p hp hpS _ hcl
      -- the tail
      have htl : ∀ p ∈ Q, (1300 : ℕ) / (S : ℝ) < u p → ∀ k : ℕ,
          (1300 : ℕ) / (S : ℝ) * 2 ^ k < u p → hU p ≤ 1 / 12 ^ 6 / 64 ^ k := by
        intro p hp _ k hk
        have hk' : ((1300 * 2 ^ k : ℕ) : ℝ) / S < u p := by
          push_cast; rwa [mul_div_right_comm]
        have h1 := hut p hp _ S hS0 hk'
        push_cast at h1
        have hs' : (S : ℝ) / 100 * Real.log z ≤ Real.log Y := hs
        have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have hlpp := hlp p hp
        have hmain : 13 * 2 ^ k * Real.log p < Real.log Y := by nlinarith
        have hpS : p ∈ Sel := hSel_of p hp (by nlinarith)
        have h12 : 12 * Real.log p ≤ Real.log (Y / p) := by rw [hlogYp p hp]; nlinarith
        have hcl := (C p hp).2.2.2 h12
        have hb := hUle p hp hpS _ hcl
        refine hb.trans ?_
        rw [hlogYp p hp]
        exact pow6_le_of k hlpp (by nlinarith)
      have hrb := row_bound Q w u hU hw0 hcum (toR (1, 1, headU cells S))
        ((l.map toR).tail) ((1300 : ℕ) / (S : ℝ)) (1 / 12 ^ 6) hte (by positivity)
        (by have := hgood; rw [hl, entsU, List.map_cons] at this ⊢; exact this)
        (fun p hp _ => by simp only [toR]; exact hhead p hp)
        hent htl
      have hmom := momR_le 1300 S hS0 hS13 l hch hbd
      have hcr := crude_sound (a := 1300) (b := S) hS0 hS13
      have hcast : ((1300 : ℕ) : ℝ) = 1300 := by norm_num
      have hsum : ∑ p ∈ Q, w p * hU p ≤ r c.2.1 := by
        have e : toR (1, 1, headU cells S) :: (l.map toR).tail = l.map toR := by
          rw [hl, entsU, List.map_cons, List.tail_cons]
        rw [e] at hrb
        have hfin' := r_mono hfin
        rw [r_add] at hfin'
        rw [hcast] at hrb hmom hcr
        linarith
      rw [hUeq]
      exact mul_le_mul_of_nonneg_left (by linarith) hVQ.le
    · ------------------------------------------------------------------ lower rows
      intro c hc hc200 hs
      have hl0 := (hrows c hc).1
      have hlt200 : ¬ c.1 < 200 := by omega
      simp only [hlt200, decide_false, Bool.false_or] at hl0
      unfold lrowOK at hl0
      split at hl0
      · exact absurd hl0 (by decide)
      rename_i c0 hc0
      obtain ⟨hch, hbd, hS0, hS13, hfin⟩ := rowTail_parts hl0
      set S := c.1 with hSdef
      have hSR : (0 : ℝ) < S := by exact_mod_cast hS0
      have hmem := List.mem_of_getLast? hc0
      obtain ⟨hc0m, hc0p⟩ := List.mem_filter.mp hmem
      simp only [decide_eq_true_eq] at hc0p
      set l := entsL cells S c0.2.1 with hl
      have hgood := goodL_of l 1300 S hS0 hch hbd
      have hte : (1 : ℝ) ≤ (1300 : ℕ) / (S : ℝ) := by
        rw [le_div_iff₀ hSR, one_mul]; exact_mod_cast hS13
      have hs' : (S : ℝ) / 100 * Real.log z ≤ Real.log Y := hs
      have hhead : ∀ p ∈ Q, hL p ≤ r c0.2.1 := by
        intro p hp
        have hle' : ((c0.1 : ℝ) + 100) ≤ S := by exact_mod_cast hc0p
        have hlt := hlpz p hp
        have hlpp := hlp p hp
        have hcl := (C p hp).1 c0 hc0m (by rw [hlogYp p hp]; nlinarith)
        exact hLle p hp _ hcl
      have hent : ∀ p ∈ Q, u p ≤ (1300 : ℕ) / (S : ℝ) → ∀ y ∈ (l.map toR).tail, y.1 < u p →
          hL p ≤ y.2 := by
        intro p hp _ y hy hyu
        rw [hl, entsL, List.map_cons, List.tail_cons] at hy
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        obtain ⟨hdm, _⟩ := List.mem_filter.mp hd
        have h1 := hut p hp (d.1 + 100) S hS0 hyu
        push_cast at h1
        have hcl := (C p hp).1 d hdm (by rw [hlogYp p hp]; nlinarith)
        exact hLle p hp _ hcl
      have htl : ∀ p ∈ Q, (1300 : ℕ) / (S : ℝ) < u p → ∀ k : ℕ,
          (1300 : ℕ) / (S : ℝ) * 2 ^ k < u p → hL p ≤ 1 / 12 ^ 6 / 64 ^ k := by
        intro p hp _ k hk
        have hk' : ((1300 * 2 ^ k : ℕ) : ℝ) / S < u p := by
          push_cast; rwa [mul_div_right_comm]
        have h1 := hut p hp _ S hS0 hk'
        push_cast at h1
        have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have hlpp := hlp p hp
        have h12 : 12 * Real.log p ≤ Real.log (Y / p) := by rw [hlogYp p hp]; nlinarith
        have hcl := (C p hp).2.2.1 h12
        have hb := hLle p hp _ hcl
        refine hb.trans ?_
        rw [hlogYp p hp]
        exact pow6_le_of k hlpp (by nlinarith)
      have hrb := row_bound Q w u hL hw0 hcum (toR (1, 1, c0.2.1))
        ((l.map toR).tail) ((1300 : ℕ) / (S : ℝ)) (1 / 12 ^ 6) hte (by positivity)
        (by have := hgood; rw [hl, entsL, List.map_cons] at this ⊢; exact this)
        (fun p hp _ => by simp only [toR]; exact hhead p hp)
        hent htl
      have hmom := momR_le 1300 S hS0 hS13 l hch hbd
      have hcr := crude_sound (a := 1300) (b := S) hS0 hS13
      have hcast : ((1300 : ℕ) : ℝ) = 1300 := by norm_num
      have hsum : ∑ p ∈ Q, w p * hL p ≤ r c.2.2 := by
        have e : toR (1, 1, c0.2.1) :: (l.map toR).tail = l.map toR := by
          rw [hl, entsL, List.map_cons, List.tail_cons]
        rw [e] at hrb
        have hfin' := r_mono hfin
        rw [r_add] at hfin'
        rw [hcast] at hrb hmom hcr
        linarith
      rw [hLeq]
      exact mul_le_mul_of_nonneg_left (by linarith) hVQ.le
    · ------------------------------------------------------------------ upper tail
      intro hs
      obtain ⟨c11, hc11, hc11g, hX1, hX2⟩ : ∃ c ∈ cells, c.1 = 1100 ∧
          tailOK (13 ^ 6 * c.2.1) = true ∧ tailOK (13 ^ 6 * c.2.2) = true := by
        unfold tailCells at htailc
        split at htailc
        · exact absurd htailc (by decide)
        · rename_i c hc
          simp only [Bool.and_eq_true] at htailc
          have := List.find?_some hc
          simp only [decide_eq_true_eq] at this
          exact ⟨c, List.mem_of_find?_eq_some hc, this, htailc.1, htailc.2⟩
      have hlY : 0 < Real.log Y := by linarith
      set ε := (Real.log z / Real.log Y) ^ 6 with hε
      have hε0 : 0 < ε := by positivity
      have hcase : ∀ p ∈ Q, ∀ (hh : ℕ → ℝ) (B : ℝ), 0 ≤ B →
          (12 * Real.log p ≤ Real.log (Y / p) → hh p ≤ (Real.log p / Real.log (Y / p)) ^ 6) →
          ((1100 : ℝ) / 100 * Real.log p ≤ Real.log (Y / p) → hh p ≤ B) →
          hh p ≤ ε * (1 / (u p - 1 / 12) ^ 6) ∨ (u p < 13 / 12 ∧ hh p ≤ ε * (13 ^ 6 * B)) := by
        intro p hp hh B hB0 hA hB
        rw [hlogYp p hp] at hA hB
        exact tail_case (hlp p hp) (hlpz p hp) hs hB0 hA (fun h => hB (by linarith))
      have hsum := tail_core Q w u hU hw0 hcum (13 ^ 6 * c11.2.2) hX2 ε hε0 hU1 (fun p hp => by
        have hpS : p ∈ Sel := hSel_of p hp (by
          have := hlpz p hp; have := hlp p hp; linarith)
        have := hcase p hp hU (r c11.2.2) (r_nonneg _)
          (fun h12 => hUle p hp hpS _ ((C p hp).2.2.2 h12))
          (fun h11 => hUle p hp hpS _ ((C p hp).2.1 c11 hc11 (by omega) (by rw [hc11g]; exact_mod_cast h11)))
        rwa [show r (13 ^ 6 * c11.2.2) = 13 ^ 6 * r c11.2.2 by unfold r; push_cast; ring])
      rw [hUeq]
      exact mul_le_mul_of_nonneg_left (by linarith) hVQ.le
    · ------------------------------------------------------------------ lower tail
      intro hs
      obtain ⟨c11, hc11, hc11g, hX1, hX2⟩ : ∃ c ∈ cells, c.1 = 1100 ∧
          tailOK (13 ^ 6 * c.2.1) = true ∧ tailOK (13 ^ 6 * c.2.2) = true := by
        unfold tailCells at htailc
        split at htailc
        · exact absurd htailc (by decide)
        · rename_i c hc
          simp only [Bool.and_eq_true] at htailc
          have := List.find?_some hc
          simp only [decide_eq_true_eq] at this
          exact ⟨c, List.mem_of_find?_eq_some hc, this, htailc.1, htailc.2⟩
      have hlY : 0 < Real.log Y := by linarith
      set ε := (Real.log z / Real.log Y) ^ 6 with hε
      have hε0 : 0 < ε := by positivity
      have hcase : ∀ p ∈ Q, ∀ (hh : ℕ → ℝ) (B : ℝ), 0 ≤ B →
          (12 * Real.log p ≤ Real.log (Y / p) → hh p ≤ (Real.log p / Real.log (Y / p)) ^ 6) →
          ((1100 : ℝ) / 100 * Real.log p ≤ Real.log (Y / p) → hh p ≤ B) →
          hh p ≤ ε * (1 / (u p - 1 / 12) ^ 6) ∨ (u p < 13 / 12 ∧ hh p ≤ ε * (13 ^ 6 * B)) := by
        intro p hp hh B hB0 hA hB
        rw [hlogYp p hp] at hA hB
        exact tail_case (hlp p hp) (hlpz p hp) hs hB0 hA (fun h => hB (by linarith))
      have hsum := tail_core Q w u hL hw0 hcum (13 ^ 6 * c11.2.1) hX1 ε hε0 hU1 (fun p hp => by
        have := hcase p hp hL (r c11.2.1) (r_nonneg _)
          (fun h12 => hLle p hp _ ((C p hp).2.2.1 h12))
          (fun h11 => hLle p hp _ ((C p hp).1 c11 hc11 (by rw [hc11g]; exact_mod_cast h11)))
        rwa [show r (13 ^ 6 * c11.2.1) = 13 ^ 6 * r c11.2.1 by unfold r; push_cast; ring])
      rw [hLeq]
      exact mul_le_mul_of_nonneg_left (by linarith) hVQ.le

end Shoup.Rosser
