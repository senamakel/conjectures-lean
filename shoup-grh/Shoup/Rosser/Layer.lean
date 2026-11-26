import Shoup.Rosser.Mertens

/-!
# Sums over the primes of a Rosser step

With `g_q = 1/q`, `V(Q) = ∏_{q ∈ Q} (1 - g_q)` and `W_Q(p) = ∏_{q ∈ Q, q ≥ p} (1 - g_q)⁻¹`,

* `step_lower`, `step_upper`: one step of the recursion, written as
  `L = V(Q) (1 - Σ_p g_p W_Q(p) h_p)` and `U = V(Q) (1 + Σ_p g_p W_Q(p) h'_p)`;
* `sum_upper_eq`: over an upward closed part `A` of `Q`, `Σ_{p ∈ A} g_p W_Q(p) = ∏_A (1-g)⁻¹ - 1`,
  which Mertens bounds by `Ω(t) - 1` (`cum_le`);
* `row_bound`: a layer-cake (Abel summation) bound for `Σ_p g_p W_Q(p) h_p` when `h_p` is
  bounded by a decreasing step function of `u_p = log z / log p`, plus a dyadic tail.
-/

namespace Shoup.Rosser

open Finset Shoup.Sieve

noncomputable def V (Q : Finset ℕ) : ℝ := ∏ q ∈ Q, (1 - recip q)

noncomputable def Wt (Q : Finset ℕ) (p : ℕ) : ℝ := ∏ q ∈ Q.filter (p ≤ ·), (1 - recip q)⁻¹

lemma recip_le_half {q : ℕ} (hq : 2 ≤ q) : recip q ≤ 1 / 2 := by
  unfold recip
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq)

lemma recip_nonneg (q : ℕ) : 0 ≤ recip q := by unfold recip; positivity

lemma one_sub_recip_pos {q : ℕ} (hq : 2 ≤ q) : 0 < 1 - recip q := by
  have := recip_le_half hq; linarith

lemma V_pos (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 2 ≤ q) : 0 < V Q :=
  Finset.prod_pos fun q h => one_sub_recip_pos (hQ q h)

lemma Wt_nonneg (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 2 ≤ q) (p : ℕ) : 0 ≤ Wt Q p :=
  Finset.prod_nonneg fun q h =>
    (inv_pos.mpr (one_sub_recip_pos (hQ q (Finset.mem_filter.mp h).1))).le

lemma Wt_pos (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 2 ≤ q) (p : ℕ) : 0 < Wt Q p :=
  Finset.prod_pos fun q h => inv_pos.mpr (one_sub_recip_pos (hQ q (Finset.mem_filter.mp h).1))

lemma V_lt_eq (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 2 ≤ q) (p : ℕ) :
    V (Q.filter (· < p)) = V Q * Wt Q p := by
  unfold V Wt
  rw [← Finset.prod_filter_mul_prod_filter_not Q (· < p)]
  have hf : Q.filter (fun q => ¬ q < p) = Q.filter (p ≤ ·) := by
    ext x; simp [not_lt]
  rw [hf, mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one (s := Q.filter (p ≤ ·)) (fun q h => ?_)]
  · ring
  · exact mul_inv_cancel₀ (one_sub_recip_pos (hQ q (Finset.mem_filter.mp h).1)).ne'

/-- `Σ_{p ∈ Q} g_p V(Q_{<p}) = 1 - V(Q)`. -/
lemma sum_gV (Q : Finset ℕ) : ∑ p ∈ Q, recip p * V (Q.filter (· < p)) = 1 - V Q :=
  telescope Q recip

/-- One lower step: `1 - Σ g_p U_p = V(Q) (1 - Σ g_p W(p) (U_p / V(Q_{<p}) - 1))`. -/
lemma step_lower (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 2 ≤ q) (U : ℕ → ℝ) :
    1 - ∑ p ∈ Q, recip p * U p =
      V Q * (1 - ∑ p ∈ Q, recip p * Wt Q p * (U p / V (Q.filter (· < p)) - 1)) := by
  have hpos : ∀ p, 0 < V (Q.filter (· < p)) := fun p =>
    V_pos _ fun q h => hQ q (Finset.mem_filter.mp h).1
  have h1 : ∀ p ∈ Q, recip p * U p = recip p * V (Q.filter (· < p)) +
      V Q * (recip p * Wt Q p * (U p / V (Q.filter (· < p)) - 1)) := by
    intro p _
    have := V_lt_eq Q hQ p
    have hW := (Wt_pos Q hQ p).ne'
    have hV := (V_pos Q hQ).ne'
    rw [this]
    field_simp
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, sum_gV, ← Finset.mul_sum]
  ring

/-- One upper step, over `S ⊆ Q`: `1 - Σ_{p ∈ S} g_p L_p = V(Q) (1 + Σ_{p ∈ Q} g_p W(p) h'_p)`
with `h'_p = 1 - L_p / V(Q_{<p})` on `S` and `1` off `S`. -/
lemma step_upper (Q S : Finset ℕ) (hS : S ⊆ Q) (hQ : ∀ q ∈ Q, 2 ≤ q) (L : ℕ → ℝ) :
    1 - ∑ p ∈ S, recip p * L p =
      V Q * (1 + ∑ p ∈ Q, recip p * Wt Q p *
        (if p ∈ S then 1 - L p / V (Q.filter (· < p)) else 1)) := by
  classical
  have hpos : ∀ p, 0 < V (Q.filter (· < p)) := fun p =>
    V_pos _ fun q h => hQ q (Finset.mem_filter.mp h).1
  have h1 : ∀ p ∈ Q, V Q * (recip p * Wt Q p *
      (if p ∈ S then 1 - L p / V (Q.filter (· < p)) else 1)) =
      recip p * V (Q.filter (· < p)) - (if p ∈ S then recip p * L p else 0) := by
    intro p _
    have := V_lt_eq Q hQ p
    have hW := (Wt_pos Q hQ p).ne'
    have hV := (V_pos Q hQ).ne'
    rw [this]
    split_ifs
    · field_simp
    · ring
  rw [mul_add, mul_one, Finset.mul_sum, Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_gV, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : Q.filter (· ∈ S) = S := by
    ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  rw [this]
  ring

/-- Over an upward closed part `A ⊆ Q`, `Σ_{p ∈ A} g_p W_Q(p) = ∏_A (1 - g)⁻¹ - 1`. -/
lemma sum_upper_eq (Q A : Finset ℕ) (hQ : ∀ q ∈ Q, 2 ≤ q) (hA : A ⊆ Q)
    (hup : ∀ p ∈ A, ∀ q ∈ Q, p ≤ q → q ∈ A) :
    ∑ p ∈ A, recip p * Wt Q p = ∏ q ∈ A, (1 - recip q)⁻¹ - 1 := by
  have hQA : ∀ q ∈ A, 2 ≤ q := fun q h => hQ q (hA h)
  have hW : ∀ p ∈ A, Wt Q p = Wt A p := by
    intro p hp
    unfold Wt
    congr 1
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hq, hpq⟩ => ⟨hup p hp q hq hpq, hpq⟩, fun ⟨hq, hpq⟩ => ⟨hA hq, hpq⟩⟩
  rw [Finset.sum_congr rfl fun p hp => by rw [hW p hp]]
  have hVA := V_pos A hQA
  have h := sum_gV A
  have h2 : ∀ p ∈ A, recip p * V (A.filter (· < p)) = V A * (recip p * Wt A p) := by
    intro p _; rw [V_lt_eq A hQA p]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum] at h
  have hinv : ∏ q ∈ A, (1 - recip q)⁻¹ = (V A)⁻¹ := by unfold V; rw [Finset.prod_inv_distrib]
  rw [hinv]
  field_simp
  linarith

/-- The Mertens bound for the cumulative weight: `Σ_{p ∈ Q, log z ≤ t log p} g_p W(p) ≤ Ω(t) - 1`. -/
lemma cum_le (Q : Finset ℕ) (z : ℝ) (hQ : ∀ q ∈ Q, q.Prime ∧ 2 ^ E < q ∧ (q : ℝ) < z)
    (t : ℝ) (ht : 1 ≤ t) :
    ∑ p ∈ Q.filter (fun p : ℕ => Real.log z ≤ t * Real.log p), recip p * Wt Q p ≤ Om t - 1 := by
  have hQ2 : ∀ q ∈ Q, 2 ≤ q := fun q h => (hQ q h).1.two_le
  rw [sum_upper_eq Q _ hQ2 (Finset.filter_subset _ _)]
  · have := prod_inv_le_Om (Q.filter fun p => Real.log z ≤ t * Real.log p) z t ht
      fun q h => by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
        exact ⟨(hQ q h1).1, (hQ q h1).2.1, (hQ q h1).2.2, h2⟩
    linarith
  · intro p hp q hq hpq
    obtain ⟨_, h2⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hq, h2.trans ?_⟩
    have hp2 := hQ2 p (Finset.mem_filter.mp hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hp0 (by exact_mod_cast hpq)) (by linarith)

/-! ### Layer cakes -/

/-- The step majorant: entries `(t_k, H_k)`, end `t_e`; value `H_k` on `(t_k, t_{k+1}]`. -/
noncomputable def maj : List (ℝ × ℝ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | [x], te, u => if u ≤ te then x.2 else 0
  | x :: y :: rest, te, u => (if u ≤ y.1 then x.2 - y.2 else 0) + maj (y :: rest) te u

/-- Its integral against the Mertens bound. -/
noncomputable def momR : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | [x], te => x.2 * (Om te - 1)
  | x :: y :: rest, te => (x.2 - y.2) * (Om y.1 - 1) + momR (y :: rest) te

/-- Entries with increasing thresholds `≥ 1` (all `≤ te`) and decreasing nonnegative heights. -/
def GoodL (l : List (ℝ × ℝ)) (te : ℝ) : Prop :=
  l.Pairwise (fun a b => a.1 ≤ b.1 ∧ b.2 ≤ a.2) ∧ (∀ x ∈ l, 1 ≤ x.1 ∧ x.1 ≤ te ∧ 0 ≤ x.2)

lemma GoodL.tail {x : ℝ × ℝ} {l : List (ℝ × ℝ)} {te : ℝ} (h : GoodL (x :: l) te) :
    GoodL l te :=
  ⟨(List.pairwise_cons.mp h.1).2, fun y hy => h.2 y (List.mem_cons_of_mem _ hy)⟩

lemma maj_eq_head (te u : ℝ) (hu : u ≤ te) : ∀ (l : List (ℝ × ℝ)) (x : ℝ × ℝ),
    (∀ y ∈ l, u ≤ y.1) → maj (x :: l) te u = x.2 := by
  intro l
  induction l with
  | nil => intro x _; simp [maj, hu]
  | cons y rest ih =>
    intro x hl
    simp only [maj]
    rw [if_pos (hl y (List.mem_cons_self ..)), ih y fun w hw => hl w (List.mem_cons_of_mem _ hw)]
    ring

lemma maj_nonneg (te u : ℝ) : ∀ (l : List (ℝ × ℝ)), GoodL l te → 0 ≤ maj l te u := by
  intro l
  induction l with
  | nil => intro _; simp [maj]
  | cons x rest ih =>
    intro hg
    cases rest with
    | nil => simp only [maj]; split_ifs <;> simp [hg.2 x (by simp)]
    | cons y r =>
      simp only [maj]
      have hxy := (List.pairwise_cons.mp hg.1).1 y (List.mem_cons_self ..)
      have := ih hg.tail
      split_ifs <;> linarith [hxy.2]

lemma maj_ge (te u h : ℝ) (hu : u ≤ te) : ∀ (l : List (ℝ × ℝ)) (x : ℝ × ℝ), GoodL (x :: l) te →
    h ≤ x.2 → (∀ y ∈ l, y.1 < u → h ≤ y.2) → h ≤ maj (x :: l) te u := by
  intro l
  induction l with
  | nil => intro x _ hx _; simp [maj, hu, hx]
  | cons y rest ih =>
    intro x hg hx hl
    simp only [maj]
    by_cases hy : u ≤ y.1
    · rw [if_pos hy]
      have hrest : ∀ w ∈ rest, u ≤ w.1 := fun w hw =>
        hy.trans ((List.pairwise_cons.mp (hg.tail).1).1 w hw).1
      rw [maj_eq_head te u hu rest y hrest]
      linarith
    · rw [if_neg hy, zero_add]
      push Not at hy
      exact ih y hg.tail (hl y (List.mem_cons_self ..) hy)
        fun w hw hw' => hl w (List.mem_cons_of_mem _ hw) hw'

/-- `Σ_p w_p maj(u_p) ≤ momR` given the cumulative bound `Σ_{u_p ≤ s} w_p ≤ Ω(s) - 1`. -/
lemma sum_maj_le (Q : Finset ℕ) (w u : ℕ → ℝ) (hw : ∀ p ∈ Q, 0 ≤ w p) (te : ℝ) (hte : 1 ≤ te)
    (hcum : ∀ s, 1 ≤ s → ∑ p ∈ Q.filter (fun p => u p ≤ s), w p ≤ Om s - 1) :
    ∀ l : List (ℝ × ℝ), GoodL l te → ∑ p ∈ Q, w p * maj l te (u p) ≤ momR l te := by
  intro l
  induction l with
  | nil => intro _; simp [maj, momR]
  | cons x rest ih =>
    intro hg
    cases rest with
    | nil =>
      simp only [maj, momR]
      have : ∑ p ∈ Q, w p * (if u p ≤ te then x.2 else 0) =
          x.2 * ∑ p ∈ Q.filter (fun p => u p ≤ te), w p := by
        rw [Finset.mul_sum, Finset.sum_filter]
        exact Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (hcum te hte) (hg.2 x (by simp)).2.2
    | cons y r =>
      simp only [maj, momR]
      have hxy := (List.pairwise_cons.mp hg.1).1 y (List.mem_cons_self ..)
      have hy1 := (hg.2 y (by simp)).1
      have e : ∑ p ∈ Q, w p * ((if u p ≤ y.1 then x.2 - y.2 else 0) + maj (y :: r) te (u p)) =
          (x.2 - y.2) * ∑ p ∈ Q.filter (fun p => u p ≤ y.1), w p +
            ∑ p ∈ Q, w p * maj (y :: r) te (u p) := by
        rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      rw [e]
      have := mul_le_mul_of_nonneg_left (hcum y.1 hy1) (by linarith [hxy.2] : 0 ≤ x.2 - y.2)
      linarith [ih hg.tail]

/-- The dyadic tail: if `h_p ≤ C/64^k` whenever `te 2^k < u_p`, then
`Σ_{u_p > te} w_p h_p ≤ C (Ω(2 te) - 1 + κ 4 te²/15)`. -/
lemma sum_tail_le (Q : Finset ℕ) (w u h : ℕ → ℝ) (hw : ∀ p ∈ Q, 0 ≤ w p) (te C : ℝ)
    (hte : 1 ≤ te) (hC : 0 ≤ C)
    (hcum : ∀ s, 1 ≤ s → ∑ p ∈ Q.filter (fun p => u p ≤ s), w p ≤ Om s - 1)
    (hh : ∀ p ∈ Q, te < u p → ∀ k : ℕ, te * 2 ^ k < u p → h p ≤ C / 64 ^ k) :
    ∑ p ∈ Q.filter (fun p => te < u p), w p * h p ≤
      C * (Om (2 * te) - 1 + (1001 / 1000) ^ 2 * 4 * te ^ 2 / 15) := by
  classical
  -- a uniform number of layers
  set N := ⌈∑ p ∈ Q, |u p|⌉₊ + 1 with hN
  have hbig : ∀ p ∈ Q, u p ≤ te * 2 ^ N := by
    intro p hp
    have h1 : u p ≤ ∑ p ∈ Q, |u p| :=
      (le_abs_self _).trans (Finset.single_le_sum (fun q _ => abs_nonneg (u q)) hp)
    have h2 : ∑ p ∈ Q, |u p| ≤ (N : ℝ) := by
      rw [hN]; push_cast; linarith [Nat.le_ceil (∑ p ∈ Q, |u p|)]
    have h3 : (N : ℝ) ≤ 2 ^ N := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h4 : (2 : ℝ) ^ N ≤ te * 2 ^ N := le_mul_of_one_le_left (by positivity) hte
    linarith
  -- pointwise layer bound
  have hpt : ∀ p ∈ Q.filter (fun p => te < u p),
      h p ≤ ∑ k ∈ Finset.range N, C / 64 ^ k * (if u p ≤ te * 2 ^ (k + 1) then 1 else 0) := by
    intro p hp
    obtain ⟨hpQ, hpu⟩ := Finset.mem_filter.mp hp
    have hex : ∃ k, u p ≤ te * 2 ^ (k + 1) := ⟨N, by
      have := hbig p hpQ
      have : te * 2 ^ N ≤ te * 2 ^ (N + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by linarith)
      linarith⟩
    set k := Nat.find hex with hk
    have hk1 : u p ≤ te * 2 ^ (k + 1) := Nat.find_spec hex
    have hk2 : te * 2 ^ k < u p := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero, mul_one]; exact hpu
      · have := Nat.find_min hex (show k - 1 < k by omega)
        push Not at this
        rwa [show k - 1 + 1 = k by omega] at this
    have hkN : k < N := by
      by_contra hc; push Not at hc
      have h1 := hbig p hpQ
      have : te * 2 ^ N ≤ te * 2 ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hc) (by linarith)
      linarith
    have hterm : ∀ j ∈ Finset.range N,
        0 ≤ C / 64 ^ j * (if u p ≤ te * 2 ^ (j + 1) then 1 else 0) := fun j _ => by
      split_ifs <;> positivity
    have := Finset.single_le_sum hterm (Finset.mem_range.mpr hkN)
    simp only [if_pos hk1, mul_one] at this
    exact (hh p hpQ hpu k hk2).trans this
  have hsum : ∑ p ∈ Q.filter (fun p => te < u p), w p * h p ≤
      ∑ k ∈ Finset.range N, C / 64 ^ k * ∑ p ∈ Q.filter (fun p => u p ≤ te * 2 ^ (k + 1)), w p := by
    calc ∑ p ∈ Q.filter (fun p => te < u p), w p * h p
        ≤ ∑ p ∈ Q.filter (fun p => te < u p), w p *
            ∑ k ∈ Finset.range N, C / 64 ^ k * (if u p ≤ te * 2 ^ (k + 1) then 1 else 0) :=
          Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (hpt p hp) (hw p (Finset.mem_filter.mp hp).1)
      _ ≤ ∑ p ∈ Q, w p *
            ∑ k ∈ Finset.range N, C / 64 ^ k * (if u p ≤ te * 2 ^ (k + 1) then 1 else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro p hp _
          refine mul_nonneg (hw p hp) (Finset.sum_nonneg fun j _ => ?_)
          split_ifs <;> positivity
      _ = ∑ k ∈ Finset.range N, C / 64 ^ k *
            ∑ p ∈ Q.filter (fun p => u p ≤ te * 2 ^ (k + 1)), w p := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
  refine hsum.trans ?_
  -- bound each layer
  have hlay : ∀ k ∈ Finset.range N, C / 64 ^ k *
      ∑ p ∈ Q.filter (fun p => u p ≤ te * 2 ^ (k + 1)), w p ≤
      C * (if k = 0 then Om (2 * te) - 1 else (1001 / 1000) ^ 2 * 4 * te ^ 2 * (1 / 16) ^ k) := by
    intro k _
    have hs1 : 1 ≤ te * 2 ^ (k + 1) := by
      have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hc := hcum _ hs1
    have hc0 : 0 ≤ C / 64 ^ k := by positivity
    have h1 := mul_le_mul_of_nonneg_left hc hc0
    split_ifs with hk0
    · subst hk0; simp only [pow_zero, div_one, zero_add, pow_one] at h1 ⊢
      simp only [mul_comm te 2] at h1 ⊢; exact h1
    · have hOm := Om_le_sq hs1
      have : C / 64 ^ k * (Om (te * 2 ^ (k + 1)) - 1) ≤
          C * ((1001 / 1000) ^ 2 * 4 * te ^ 2 * (1 / 16) ^ k) := by
        have e : C * ((1001 / 1000) ^ 2 * 4 * te ^ 2 * (1 / 16) ^ k) =
            C / 64 ^ k * ((1001 / 1000) ^ 2 * (te * 2 ^ (k + 1)) ^ 2) := by
          rw [mul_pow, ← pow_mul, show (2 : ℝ) ^ ((k + 1) * 2) = 4 * 4 ^ k by
            rw [show (k + 1) * 2 = 2 * k + 2 by ring, pow_add, pow_mul]; norm_num; ring]
          rw [one_div_pow, show (64 : ℝ) ^ k = 16 ^ k * 4 ^ k by
            rw [← mul_pow]; norm_num]
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left (by linarith) hc0
      linarith
  refine (Finset.sum_le_sum hlay).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · rw [hN0]; simp
    have : 1 ≤ Om (2 * te) := one_le_Om (by linarith)
    positivity
  rw [← Finset.sum_range_add_sum_Ico _ (show 1 ≤ N by omega), Finset.sum_range_one, if_pos rfl]
  have hgeom : ∑ k ∈ Finset.Ico 1 N, (if k = 0 then Om (2 * te) - 1 else
      (1001 / 1000) ^ 2 * 4 * te ^ 2 * (1 / 16) ^ k) ≤ (1001 / 1000) ^ 2 * 4 * te ^ 2 / 15 := by
    rw [Finset.sum_congr rfl fun k hk => by
      rw [if_neg (by have := (Finset.mem_Ico.mp hk).1; omega)]]
    rw [← Finset.mul_sum]
    have hg : ∑ k ∈ Finset.Ico 1 N, (1 / 16 : ℝ) ^ k ≤ 1 / 15 := by
      have h := geom_sum_Ico_le_of_lt_one (x := (1 / 16 : ℝ)) (m := 1) (n := N) (by norm_num)
        (by norm_num)
      norm_num at h ⊢; linarith
    have : 0 ≤ (1001 / 1000 : ℝ) ^ 2 * 4 * te ^ 2 := by positivity
    calc (1001 / 1000 : ℝ) ^ 2 * 4 * te ^ 2 * ∑ k ∈ Finset.Ico 1 N, (1 / 16 : ℝ) ^ k
        ≤ (1001 / 1000) ^ 2 * 4 * te ^ 2 * (1 / 15) := mul_le_mul_of_nonneg_left hg this
      _ = _ := by ring
  linarith

/-- **Row bound.** -/
theorem row_bound (Q : Finset ℕ) (w u h : ℕ → ℝ) (hw : ∀ p ∈ Q, 0 ≤ w p)
    (hcum : ∀ s, 1 ≤ s → ∑ p ∈ Q.filter (fun p => u p ≤ s), w p ≤ Om s - 1)
    (x : ℝ × ℝ) (l : List (ℝ × ℝ)) (te C : ℝ) (hte : 1 ≤ te) (hC : 0 ≤ C)
    (hg : GoodL (x :: l) te)
    (hhead : ∀ p ∈ Q, u p ≤ te → h p ≤ x.2)
    (hent : ∀ p ∈ Q, u p ≤ te → ∀ y ∈ l, y.1 < u p → h p ≤ y.2)
    (htail : ∀ p ∈ Q, te < u p → ∀ k : ℕ, te * 2 ^ k < u p → h p ≤ C / 64 ^ k) :
    ∑ p ∈ Q, w p * h p ≤
      momR (x :: l) te + C * (Om (2 * te) - 1 + (1001 / 1000) ^ 2 * 4 * te ^ 2 / 15) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p => u p ≤ te)]
  have h1 : ∑ p ∈ Q.filter (fun p => u p ≤ te), w p * h p ≤ momR (x :: l) te := by
    calc ∑ p ∈ Q.filter (fun p => u p ≤ te), w p * h p
        ≤ ∑ p ∈ Q.filter (fun p => u p ≤ te), w p * maj (x :: l) te (u p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          obtain ⟨hpQ, hpu⟩ := Finset.mem_filter.mp hp
          exact mul_le_mul_of_nonneg_left
            (maj_ge te (u p) (h p) hpu l x hg (hhead p hpQ hpu) (hent p hpQ hpu)) (hw p hpQ)
      _ ≤ ∑ p ∈ Q, w p * maj (x :: l) te (u p) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ =>
            mul_nonneg (hw p hp) (maj_nonneg te (u p) _ hg)
      _ ≤ momR (x :: l) te := sum_maj_le Q w u hw te hte hcum _ hg
  have h2 := sum_tail_le Q w u h hw te C hte hC hcum htail
  have e : Q.filter (fun p => ¬ u p ≤ te) = Q.filter (fun p => te < u p) := by
    ext p; simp [not_le]
  rw [e]
  linarith

end Shoup.Rosser
