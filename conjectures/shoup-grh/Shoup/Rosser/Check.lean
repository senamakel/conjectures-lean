import Shoup.Rosser.Layer
import Shoup.Sieve.Fixed

/-!
# Fixed-point checker for the Rosser tables

Numbers are fixed point with scale `D = 2^48` (`Shoup.Fixed`), rounded up. An entry
`(a, b, H) : ℕ × ℕ × ℕ` stands for the threshold `a/b` and the height `H/D`.

* `omU a b ≥ Ω(a/b) - 1`, `crudeU`, `psiU`, `tailCrude`: the constants of `row_bound`;
* `momU` is `momR` in fixed point (`momR_le`); `chainOK`, `boundsOK` give `GoodL` (`goodL_of`).
-/

namespace Shoup.Rosser

open Shoup.Fixed Shoup.Sieve

abbrev Ent := ℕ × ℕ × ℕ

/-- `Ω(a/b) - 1`, rounded up. -/
def omU (a b : ℕ) : ℕ :=
  cdiv (Dn * (1001 * a * (1000 * b + a - b) - 1000000 * b * b)) (1000000 * b * b)

lemma r_cdiv_ge (m n : ℕ) (hn : 0 < n) : (m : ℝ) / n ≤ r (cdiv (Dn * m) n) := by
  have h := real_le_cdiv (Dn * m) n hn
  have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
  unfold r
  rw [le_div_iff₀ hD]
  push_cast at h
  calc (m : ℝ) / n * Dn = Dn * m / n := by ring
    _ ≤ _ := h

lemma omU_sound {a b : ℕ} (hb : 0 < b) (hab : b ≤ a) : Om ((a : ℝ) / b) - 1 ≤ r (omU a b) := by
  have hle : 1000000 * b * b ≤ 1001 * a * (1000 * b + a - b) := by
    have h1 : 1000 * b ≤ 1000 * b + a - b := by omega
    have h2 : 1000000 * b * b ≤ 1001 * b * (1000 * b) := by nlinarith
    calc 1000000 * b * b ≤ 1001 * b * (1000 * b) := h2
      _ ≤ 1001 * a * (1000 * b + a - b) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hab) h1
  have hden : 0 < 1000000 * b * b := by positivity
  refine le_trans (le_of_eq ?_) (r_cdiv_ge _ _ hden)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Nat.cast_sub hle]
  have hsub : ((1000 * b + a - b : ℕ) : ℝ) = 1000 * b + a - b := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  push_cast
  rw [hsub]
  unfold Om
  field_simp
  ring

/-- `momR` in fixed point. -/
def momU : List Ent → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | [x], ea, eb => mulU x.2.2 (omU ea eb)
  | x :: y :: rest, ea, eb => mulU (x.2.2 - y.2.2) (omU y.1 y.2.1) + momU (y :: rest) ea eb

/-- Adjacent entries: thresholds increase, heights decrease. -/
def chainOK : List Ent → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest =>
      decide (x.1 * y.2.1 ≤ y.1 * x.2.1) && decide (y.2.2 ≤ x.2.2) && chainOK (y :: rest)

/-- Every threshold lies in `[1, ea/eb]`. -/
def boundsOK (l : List Ent) (ea eb : ℕ) : Bool :=
  l.all fun x => decide (0 < x.2.1) && decide (x.2.1 ≤ x.1) && decide (x.1 * eb ≤ ea * x.2.1)

noncomputable def toR (x : Ent) : ℝ × ℝ := ((x.1 : ℝ) / x.2.1, r x.2.2)

lemma boundsOK_mem {l : List Ent} {ea eb : ℕ} (h : boundsOK l ea eb = true) {x : Ent}
    (hx : x ∈ l) : 0 < x.2.1 ∧ x.2.1 ≤ x.1 ∧ x.1 * eb ≤ ea * x.2.1 := by
  have := List.all_eq_true.mp h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

lemma boundsOK_tail {x : Ent} {l : List Ent} {ea eb : ℕ} (h : boundsOK (x :: l) ea eb = true) :
    boundsOK l ea eb = true := by
  unfold boundsOK at *
  rw [List.all_cons, Bool.and_eq_true] at h
  exact h.2

lemma div_le_div_of_cross {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    (a : ℝ) / b ≤ c / d := by
  rw [div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hd)]
  exact_mod_cast h

lemma pairwise_of_chain (ea eb : ℕ) : ∀ l : List Ent, chainOK l = true → boundsOK l ea eb = true →
    (l.map toR).Pairwise (fun a b => a.1 ≤ b.1 ∧ b.2 ≤ a.2) := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x rest ih =>
    intro hc hb
    cases rest with
    | nil => simp
    | cons y r =>
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hxy1, hxy2⟩, hc'⟩ := hc
      have hb' := boundsOK_tail hb
      have IH := ih hc' hb'
      have hxpos := (boundsOK_mem hb (List.mem_cons_self ..)).1
      have hypos := (boundsOK_mem hb' (List.mem_cons_self ..)).1
      have hR : (toR x).1 ≤ (toR y).1 ∧ (toR y).2 ≤ (toR x).2 :=
        ⟨div_le_div_of_cross hxpos hypos hxy1, r_mono hxy2⟩
      rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, IH⟩
      intro w hw
      rw [List.map_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hR
      · rw [List.map_cons, List.pairwise_cons] at IH
        have := IH.1 w hw
        exact ⟨hR.1.trans this.1, this.2.trans hR.2⟩

lemma goodL_of (l : List Ent) (ea eb : ℕ) (heb : 0 < eb) (hc : chainOK l = true)
    (hb : boundsOK l ea eb = true) : GoodL (l.map toR) ((ea : ℝ) / eb) := by
  refine ⟨pairwise_of_chain ea eb l hc hb, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h1, h2, h3⟩ := boundsOK_mem hb hy
  refine ⟨?_, div_le_div_of_cross h1 heb h3, r_nonneg _⟩
  show (1 : ℝ) ≤ (y.1 : ℝ) / y.2.1
  rw [le_div_iff₀ (by exact_mod_cast h1), one_mul]; exact_mod_cast h2

lemma Om_sub_one_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ Om t - 1 := by
  have := one_le_Om ht; linarith

theorem momR_le (ea eb : ℕ) (heb : 0 < eb) (hab : eb ≤ ea) : ∀ l : List Ent,
    chainOK l = true → boundsOK l ea eb = true →
    momR (l.map toR) ((ea : ℝ) / eb) ≤ r (momU l ea eb) := by
  intro l
  induction l with
  | nil => intro _ _; simp [momR, momU, r]
  | cons x rest ih =>
    intro hc hb
    have hte : (1 : ℝ) ≤ (ea : ℝ) / eb := by
      rw [le_div_iff₀ (by exact_mod_cast heb), one_mul]; exact_mod_cast hab
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil, momR, momU, toR]
      exact mulU_ge_of (r_nonneg _) (Om_sub_one_nonneg hte) le_rfl (omU_sound heb hab)
    | cons y r' =>
      have hc' := hc
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc'
      obtain ⟨⟨_, hxy2⟩, hc''⟩ := hc'
      have hb' := boundsOK_tail hb
      obtain ⟨hy1, hy2, _⟩ := boundsOK_mem hb' (List.mem_cons_self ..)
      have IH := ih hc'' hb'
      simp only [List.map_cons] at IH ⊢
      simp only [momR, momU] at IH ⊢
      rw [r_add]
      have hyt : (1 : ℝ) ≤ (y.1 : ℝ) / y.2.1 := by
        rw [le_div_iff₀ (by exact_mod_cast hy1), one_mul]; exact_mod_cast hy2
      have h1 : ((toR x).2 - (toR y).2) * (Om (toR y).1 - 1) ≤
          r (mulU (x.2.2 - y.2.2) (omU y.1 y.2.1)) := by
        simp only [toR]
        rw [← r_sub hxy2]
        exact mulU_ge_of (r_nonneg _) (Om_sub_one_nonneg hyt) le_rfl (omU_sound hy1 hy2)
      linarith

/-- The tail constant of a table row with end `a/b`, `C = 12^{-6}`. -/
def crudeU (a b : ℕ) : ℕ :=
  cdiv (omU (2 * a) b + cdiv (Dn * (1001 * 1001 * 4 * a * a)) (1000000 * 15 * b * b)) (12 ^ 6)

lemma crude_sound {a b : ℕ} (hb : 0 < b) (hab : b ≤ a) :
    1 / 12 ^ 6 * (Om (2 * ((a : ℝ) / b)) - 1 + (1001 / 1000) ^ 2 * 4 * ((a : ℝ) / b) ^ 2 / 15)
      ≤ r (crudeU a b) := by
  unfold crudeU
  refine le_trans ?_ (cdiv_ge _ _ (by norm_num))
  rw [r_add]
  have h1 := omU_sound (a := 2 * a) hb (by omega)
  have h2 := r_cdiv_ge (1001 * 1001 * 4 * a * a) (1000000 * 15 * b * b) (by positivity)
  have e1 : ((2 * a : ℕ) : ℝ) / b = 2 * ((a : ℝ) / b) := by push_cast; ring
  rw [e1] at h1
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have e2 : (((1001 * 1001 * 4 * a * a : ℕ) : ℝ) / ((1000000 * 15 * b * b : ℕ) : ℝ)) =
      (1001 / 1000) ^ 2 * 4 * ((a : ℝ) / b) ^ 2 / 15 := by
    push_cast; field_simp; ring
  rw [e2] at h2
  rw [Nat.cast_pow, Nat.cast_ofNat]
  calc 1 / 12 ^ 6 * (Om (2 * ((a : ℝ) / b)) - 1 + (1001 / 1000) ^ 2 * 4 * ((a : ℝ) / b) ^ 2 / 15)
      = (Om (2 * ((a : ℝ) / b)) - 1 + (1001 / 1000) ^ 2 * 4 * ((a : ℝ) / b) ^ 2 / 15) / 12 ^ 6 := by
        ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by norm_num)

/-- `(a/b - 1/12)^{-6}`, rounded up. -/
def psiU (a b : ℕ) : ℕ := cdiv (Dn * (12 * b) ^ 6) ((12 * a - b) ^ 6)

lemma psi_sound {a b : ℕ} (hb : 0 < b) (h : b < 12 * a) :
    1 / ((a : ℝ) / b - 1 / 12) ^ 6 ≤ r (psiU a b) := by
  have h0 : 0 < 12 * a - b := by omega
  refine le_trans (le_of_eq ?_) (r_cdiv_ge _ _ (pow_pos h0 6))
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsub : ((12 * a - b : ℕ) : ℝ) = 12 * a - b := by rw [Nat.cast_sub h.le]; push_cast; ring
  have hpos : (0 : ℝ) < 12 * a - b := by rw [← hsub]; exact_mod_cast h0
  rw [Nat.cast_pow, Nat.cast_pow, hsub]
  have e : (a : ℝ) / b - 1 / 12 = (12 * a - b) / (12 * b) := by field_simp
  rw [e, div_pow, one_div_div]
  push_cast; ring

/-- The tail constant of the tail rows: `ψ(4) (Ω(8) - 1 + κ·64/15)`. -/
def tailCrude : ℕ := mulU (psiU 4 1) (omU 8 1 + cdiv (Dn * (1001 * 1001 * 64)) (1000000 * 15))

lemma tailCrude_sound :
    1 / ((4 : ℝ) - 1 / 12) ^ 6 * (Om (2 * 4) - 1 + (1001 / 1000) ^ 2 * 4 * 4 ^ 2 / 15)
      ≤ r tailCrude := by
  unfold tailCrude
  have hψ := psi_sound (a := 4) (b := 1) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_one, div_one] at hψ
  have h1 := omU_sound (a := 8) (b := 1) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_one, div_one] at h1
  have h2 := r_cdiv_ge (1001 * 1001 * 64) (1000000 * 15) (by norm_num)
  have hOm : 0 ≤ Om (2 * 4) - 1 + (1001 / 1000) ^ 2 * 4 * 4 ^ 2 / 15 := by
    have := Om_sub_one_nonneg (t := 2 * 4) (by norm_num); positivity
  refine mulU_ge_of (by positivity) hOm hψ ?_
  rw [r_add]
  norm_num at h2 ⊢
  norm_num at h1
  linarith

end Shoup.Rosser
