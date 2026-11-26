import Shoup.Rosser.Claims
import Shoup.Rosser.Table
import Shoup.Statement2
import Shoup.Poly7

/-!
# `PolyOmegaRealStatement (21/5)`: `g(p) ≤ C ω(p-1)^{4.2} (log p)²` under GRH

Write `P` for the prime factors of `p - 1`, `r = |P|`, `A = 2^E` (`E = 2^36`),
`Z = A^{32} r^{1.01}` and `Y = Z^{2.05}`. The sieve function is

`F(y) = ∏_{q ∈ P, q ≤ A} (1 - y_q) · L(P ∩ (A, Z), Y)(y) - Σ_{q ∈ P, q > A, q ≥ Z} y_q`,

with `L` Rosser's lower sieve (`Shoup.Rosser`). On `0/1` points it is `≤ 0` unless all `y_q = 0`;
its mass is at most `2^{2^E} Y + r`; and at `y_q = 1/q`, by the table bound `L ≥ V (1 - α_{2.05})`
with `α_{2.05} ≤ 0.98`, it is at least `θ = 1/(200 (A + 1) t²)`, `t = log Z / log A`. The sieve
inequality `x ≤ 1089 (M log p / θ)²` then gives `x ≪ Y (log Z)² ≪ r^{2.0755}` squared.
-/

namespace Shoup.Rosser

open Finset Shoup.Fixed Shoup.Sieve ArithmeticFunction Erdos985
open scoped ArithmeticFunction.omega

lemma cell205 : ∃ c ∈ cells, c.1 = 205 ∧ 100 * c.2.2 ≤ 98 * Dn := by
  have h := allOK_cells
  unfold allOK at h
  simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact h.2

/-! ### The exact factor -/

lemma isRep_prod_one_sub (B : Finset ℕ) :
    IsRep (fun y => ∏ q ∈ B, (1 - y q)) B (2 ^ B.card) := by
  induction B using Finset.induction_on with
  | empty =>
    simpa using (IsRep.one.congr fun y => by simp)
  | insert a s ha ih =>
    have h1 : IsRep (fun y => 1 - y a) {a} 2 := by
      have := (IsRep.one.mono (Finset.empty_subset {a}) le_rfl).sub (isRep_monomial a)
      exact this.mono le_rfl (by norm_num)
    have hd : Disjoint ({a} : Finset ℕ) s := Finset.disjoint_singleton_left.mpr ha
    refine ((h1.mul ih hd).congr fun y => ?_).mono ?_ ?_
    · rw [Finset.prod_insert ha]
    · intro x hx; rcases Finset.mem_union.mp hx with h | h
      · rw [Finset.mem_singleton.mp h]; exact Finset.mem_insert_self a s
      · exact Finset.mem_insert_of_mem h
    · rw [Finset.card_insert_of_notMem ha, pow_succ]; linarith

lemma prod_one_sub_01 (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ q ∈ B, y q = 0 ∨ y q = 1) :
    (∏ q ∈ B, (1 - y q) = 1 ∧ ∀ q ∈ B, y q = 0) ∨ (∏ q ∈ B, (1 - y q) = 0) := by
  by_cases h : ∃ q ∈ B, y q = 1
  · right
    obtain ⟨q, hq, h1⟩ := h
    exact Finset.prod_eq_zero hq (by rw [h1]; ring)
  · left
    push Not at h
    have h0 : ∀ q ∈ B, y q = 0 := fun q hq => (hy q hq).resolve_right (h q hq)
    exact ⟨Finset.prod_eq_one fun q hq => by rw [h0 q hq]; ring, h0⟩

lemma rmass_ge_one : ∀ (n : ℕ) (lo : Bool) (Q : Finset ℕ) (Y : ℝ), 1 ≤ rmass n lo Q Y := by
  intro n
  induction n with
  | zero => intro _ _ _; simp [rmass]
  | succ n ih =>
    intro lo Q Y
    show 1 ≤ 1 + ∑ p ∈ sel lo Q Y, rmass n (!lo) (Q.filter (· < p)) (Y / p)
    have : 0 ≤ ∑ p ∈ sel lo Q Y, rmass n (!lo) (Q.filter (· < p)) (Y / p) :=
      Finset.sum_nonneg fun p _ => le_trans zero_le_one (ih _ _ _)
    linarith

/-! ### Constants -/

noncomputable def AA : ℝ := (2 : ℝ) ^ E

noncomputable def Ks : ℝ := (2 : ℝ) ^ (2 ^ E)

lemma E_le_AA : (E : ℝ) < AA := by
  unfold AA; exact_mod_cast Nat.lt_two_pow_self

lemma AA_big : (2 : ℝ) ^ 36 ≤ AA := by
  unfold AA; exact pow_le_pow_right₀ (by norm_num) E_ge

lemma E_big : (36 : ℝ) ≤ E := by exact_mod_cast E_ge

lemma log_AA : Real.log AA = E * Real.log 2 := by unfold AA; rw [Real.log_pow]

/-- `200 (A + 1) (33 A)² ≤ A^{32}`. -/
lemma const_ok : 200 * (AA + 1) * (33 * AA) ^ 2 ≤ AA ^ 32 := by
  have hA := AA_big
  have hA1 : (435600 : ℝ) ≤ AA := le_trans (by norm_num) hA
  have hA0 : 0 < AA := by linarith
  have h1 : 200 * (AA + 1) * (33 * AA) ^ 2 ≤ 435600 * AA ^ 3 := by nlinarith
  have h2 : 435600 * AA ^ 3 ≤ AA ^ 4 := by
    rw [show AA ^ 4 = AA * AA ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right hA1 (by positivity)
  have h3 : AA ^ 4 ≤ AA ^ 32 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

/-! ### The real-variable bookkeeping -/

lemma log_le_rpow400 {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 400 * x ^ (1 / 400 : ℝ) := by
  have := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 400 by norm_num)
  rw [div_div_eq_mul_div, div_one] at this
  linarith

/-- With `Z = A^{32} ρ^{1.01}`: `log Z ≤ 33 A ρ^{1/400}`, and `log Z ≥ log A`. -/
lemma logZ_bounds {ρ : ℝ} (hρ : 1 ≤ ρ) :
    Real.log (AA ^ 32 * ρ ^ (101 / 100 : ℝ)) ≤ 33 * AA * ρ ^ (1 / 400 : ℝ) ∧
      Real.log AA ≤ Real.log (AA ^ 32 * ρ ^ (101 / 100 : ℝ)) := by
  have hA0 : 0 < AA := lt_of_lt_of_le (by positivity) AA_big
  have hρ0 : 0 < ρ := by linarith
  have hr1 : 1 ≤ ρ ^ (1 / 400 : ℝ) := Real.one_le_rpow hρ (by norm_num)
  have e : Real.log (AA ^ 32 * ρ ^ (101 / 100 : ℝ)) =
      32 * (E * Real.log 2) + 101 / 100 * Real.log ρ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, log_AA,
      Real.log_rpow hρ0]
    push_cast; ring
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hlr := log_le_rpow400 hρ0.le
  have hlr0 : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hE := E_le_AA
  have hEb := E_big
  rw [e]
  have hAb := AA_big
  have hEl : (E : ℝ) * Real.log 2 ≤ 7 / 10 * AA := by nlinarith
  have hAr : AA ≤ AA * ρ ^ (1 / 400 : ℝ) := le_mul_of_one_le_right hA0.le hr1
  have hAr2 : 41 * ρ ^ (1 / 400 : ℝ) ≤ AA * ρ ^ (1 / 400 : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  constructor
  · nlinarith
  · rw [log_AA]; nlinarith

theorem key_bounds {ρ : ℝ} (hρ : 1 ≤ ρ) :
    let Z := AA ^ 32 * ρ ^ (101 / 100 : ℝ)
    let t := Real.log Z / Real.log AA
    1 ≤ t ∧ 200 * (AA + 1) * t ^ 2 * ρ ≤ Z ∧ AA < Z ∧ ρ ≤ Z ∧
      Z ^ (41 / 20 : ℝ) * t ^ 2 ≤ (AA ^ 32) ^ (41 / 20 : ℝ) * (33 * AA) ^ 2 * ρ ^ (21 / 10 : ℝ) := by
  intro Z t
  have hA0 : 0 < AA := lt_of_lt_of_le (by positivity) AA_big
  have hA1 : 1 < AA := lt_of_lt_of_le (by norm_num) AA_big
  have hρ0 : 0 < ρ := by linarith
  have hlA : 0 < Real.log AA := Real.log_pos hA1
  have hlA1 : 1 ≤ Real.log AA := by
    rw [log_AA]; have := Real.log_two_gt_d9; have := E_big; nlinarith
  obtain ⟨hup, hlo⟩ := logZ_bounds hρ
  have ht1 : 1 ≤ t := by
    show 1 ≤ Real.log Z / Real.log AA
    rw [le_div_iff₀ hlA, one_mul]; exact hlo
  have hlZ0 : 0 ≤ Real.log Z := le_trans hlA.le hlo
  have ht_le : t ≤ 33 * AA * ρ ^ (1 / 400 : ℝ) := by
    show Real.log Z / Real.log AA ≤ _
    rw [div_le_iff₀ hlA]
    have : 0 ≤ 33 * AA * ρ ^ (1 / 400 : ℝ) := by positivity
    nlinarith
  have ht0 : 0 ≤ t := by linarith
  have ht2 : t ^ 2 ≤ (33 * AA) ^ 2 * ρ ^ (1 / 200 : ℝ) := by
    have := pow_le_pow_left₀ ht0 ht_le 2
    rw [mul_pow, ← Real.rpow_natCast (ρ ^ (1 / 400 : ℝ)), ← Real.rpow_mul hρ0.le] at this
    norm_num at this ⊢
    exact this
  have hρ101 : ρ ≤ ρ ^ (101 / 100 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one ρ]
    exact Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  have hA32 : 1 ≤ AA ^ 32 := one_le_pow₀ hA1.le
  have hZρ : ρ ≤ Z := by
    show ρ ≤ AA ^ 32 * ρ ^ (101 / 100 : ℝ)
    have : 0 ≤ ρ ^ (101 / 100 : ℝ) := by positivity
    nlinarith
  have hZA : AA < Z := by
    show AA < AA ^ 32 * ρ ^ (101 / 100 : ℝ)
    have h1 : 1 ≤ ρ ^ (101 / 100 : ℝ) := Real.one_le_rpow hρ (by norm_num)
    have h2 : AA < AA ^ 32 := by
      calc AA = AA ^ 1 := (pow_one _).symm
        _ < AA ^ 32 := pow_lt_pow_right₀ hA1 (by norm_num)
    nlinarith
  refine ⟨ht1, ?_, hZA, hZρ, ?_⟩
  · -- `200 (A+1) t² ρ ≤ A^{32} ρ^{1.01}`
    have hc := const_ok
    have hpow : ρ ^ (1 / 200 : ℝ) * ρ ≤ ρ ^ (101 / 100 : ℝ) := by
      rw [← Real.rpow_add_one hρ0.ne']
      exact Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
    have h0 : 0 ≤ 200 * (AA + 1) := by positivity
    calc 200 * (AA + 1) * t ^ 2 * ρ ≤ 200 * (AA + 1) * ((33 * AA) ^ 2 * ρ ^ (1 / 200 : ℝ)) * ρ := by
          gcongr
      _ = 200 * (AA + 1) * (33 * AA) ^ 2 * (ρ ^ (1 / 200 : ℝ) * ρ) := by ring
      _ ≤ AA ^ 32 * ρ ^ (101 / 100 : ℝ) := by
          apply mul_le_mul hc hpow (by positivity) (by positivity)
  · -- `Z^{2.05} t² ≤ (A^{32})^{2.05} (33A)² ρ^{2.1}`
    have hZpow : Z ^ (41 / 20 : ℝ) = (AA ^ 32) ^ (41 / 20 : ℝ) * ρ ^ (4141 / 2000 : ℝ) := by
      show (AA ^ 32 * ρ ^ (101 / 100 : ℝ)) ^ (41 / 20 : ℝ) = _
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hρ0.le]
      norm_num
    have hpow : ρ ^ (4141 / 2000 : ℝ) * ρ ^ (1 / 200 : ℝ) ≤ ρ ^ (21 / 10 : ℝ) := by
      rw [← Real.rpow_add hρ0]
      exact Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
    rw [hZpow]
    have hK : 0 ≤ (AA ^ 32) ^ (41 / 20 : ℝ) := by positivity
    calc (AA ^ 32) ^ (41 / 20 : ℝ) * ρ ^ (4141 / 2000 : ℝ) * t ^ 2
        ≤ (AA ^ 32) ^ (41 / 20 : ℝ) * ρ ^ (4141 / 2000 : ℝ) *
            ((33 * AA) ^ 2 * ρ ^ (1 / 200 : ℝ)) := by gcongr
      _ = (AA ^ 32) ^ (41 / 20 : ℝ) * (33 * AA) ^ 2 *
            (ρ ^ (4141 / 2000 : ℝ) * ρ ^ (1 / 200 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ### The sieve inequality -/

/-- The constant of the main bound. -/
noncomputable def Kfin : ℝ := (Ks + 1) * 200 * (AA + 1) * ((AA ^ 32) ^ (41 / 20 : ℝ) * (33 * AA) ^ 2)

lemma AA_pos : 0 < AA := lt_of_lt_of_le (by positivity) AA_big

lemma Ks_pos : 0 < Ks := by unfold Ks; positivity

lemma Kfin_pos : 0 < Kfin := by
  unfold Kfin; have := AA_pos; have := Ks_pos; positivity

set_option maxHeartbeats 4000000 in
theorem le_of_no_primitive_root_lt_real (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1) :
    (x : ℝ) ≤ 1089 * Kfin ^ 2 * ((p - 1).primeFactors.card : ℝ) ^ (21 / 5 : ℝ) *
      Real.log p ^ 2 := by
  classical
  set P := (p - 1).primeFactors with hPdef
  have hP : ∀ ℓ ∈ P, ℓ.Prime := fun ℓ h => (Nat.mem_primeFactors.mp h).1
  set ρ : ℝ := (P.card : ℝ) with hρdef
  have hρ : 1 ≤ ρ := by
    rw [hρdef]; exact_mod_cast one_le_card_primeFactors p hp hp2
  obtain ⟨ht1, hZt, hZA, hZρ, hYt⟩ := key_bounds hρ
  set Z := AA ^ 32 * ρ ^ (101 / 100 : ℝ) with hZdef
  set t := Real.log Z / Real.log AA with htdef
  set Y := Z ^ (41 / 20 : ℝ) with hYdef
  have hA0 := AA_pos
  have hA1 : 1 < AA := lt_of_lt_of_le (by norm_num) AA_big
  have hZ1 : 1 < Z := hA1.trans hZA
  have hZ0 : 0 < Z := by linarith
  have hY0 : 0 < Y := by positivity
  have hZY : Z ≤ Y := by
    conv_lhs => rw [← Real.rpow_one Z]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)
  have hlA : 0 < Real.log AA := Real.log_pos hA1
  have hlZ : Real.log Y = 41 / 20 * Real.log Z := Real.log_rpow hZ0 _
  -- the three parts
  set small := P.filter (fun q : ℕ => q ≤ 2 ^ E) with hsmall
  set mid := P.filter (fun q : ℕ => 2 ^ E < q ∧ (q : ℝ) < Z) with hmid
  set large := P.filter (fun q : ℕ => 2 ^ E < q ∧ Z ≤ (q : ℝ)) with hlarge
  have hcastE : ∀ q : ℕ, 2 ^ E < q → AA < (q : ℝ) := fun q h => by
    unfold AA; exact_mod_cast h
  set F : (ℕ → ℝ) → ℝ := fun y =>
    (∏ q ∈ small, (1 - y q)) * ros mid.card true mid Y y - ∑ q ∈ large, y q with hF
  set M : ℝ := 2 ^ small.card * rmass mid.card true mid Y + large.card with hM
  -- representation
  have hrep : IsRep F P M := by
    have hd : Disjoint small mid := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2.1
      omega
    have h1 := ((isRep_prod_one_sub small).mul (isRep_ros mid.card true mid Y) hd).mono
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) le_rfl
    have h2 := IsRep.sum large (fun q y => y q) P (fun _ => 1) fun q hq =>
      (isRep_monomial q).mono (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hq).1) le_rfl
    refine ((h1.sub h2).congr fun y => rfl).mono le_rfl (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the sieve property
  have hpt : ∀ y : ℕ → ℝ, (∀ ℓ ∈ P, y ℓ = 0 ∨ y ℓ = 1) → (∃ ℓ ∈ P, y ℓ = 1) → F y ≤ 0 := by
    intro y hy ⟨q, hq, hq1⟩
    have hys : ∀ ℓ ∈ small, y ℓ = 0 ∨ y ℓ = 1 := fun ℓ h => hy ℓ (Finset.mem_filter.mp h).1
    have hym : ∀ ℓ ∈ mid, y ℓ = 0 ∨ y ℓ = 1 := fun ℓ h => hy ℓ (Finset.mem_filter.mp h).1
    have hyl : ∀ ℓ ∈ large, y ℓ = 0 ∨ y ℓ = 1 := fun ℓ h => hy ℓ (Finset.mem_filter.mp h).1
    obtain ⟨hall, hact, _⟩ := ros_sieve y mid.card mid le_rfl hym Y
    set Lv := ros mid.card true mid Y y with hLvdef
    have hL1 : Lv ≤ 1 := by
      by_cases h : ∃ ℓ ∈ mid, y ℓ = 1
      · linarith [hact h]
      · push Not at h
        rw [hLvdef, hall (fun ℓ hℓ => (hym ℓ hℓ).resolve_right (h ℓ hℓ)) true]
    have hl0 : 0 ≤ ∑ ℓ ∈ large, y ℓ := Finset.sum_nonneg fun ℓ h => by
      rcases hyl ℓ h with h' | h' <;> simp [h']
    show (∏ q ∈ small, (1 - y q)) * Lv - ∑ q ∈ large, y q ≤ 0
    rcases prod_one_sub_01 small y hys with ⟨hE1, hs0⟩ | hE0
    · rw [hE1, one_mul]
      by_cases hql : q ∈ large
      · have := Finset.single_le_sum (fun ℓ h => by rcases hyl ℓ h with h' | h' <;> simp [h'] :
          ∀ ℓ ∈ large, (0 : ℝ) ≤ y ℓ) hql
        rw [hq1] at this; linarith
      · have hqs : q ∉ small := fun h => by rw [hs0 q h] at hq1; norm_num at hq1
        have hqm : q ∈ mid := by
          rw [hsmall, Finset.mem_filter] at hqs
          rw [hlarge, Finset.mem_filter] at hql
          push Not at hqs hql
          have h1 := hqs hq
          exact Finset.mem_filter.mpr ⟨hq, h1, hql hq h1⟩
        linarith [hact ⟨q, hqm, hq1⟩]
    · rw [hE0, zero_mul]; linarith
  -- the mass
  have hM1 : 1 ≤ M := by
    have := rmass_ge_one mid.card true mid Y
    have h2 : (1 : ℝ) ≤ 2 ^ small.card := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) ≤ large.card := Nat.cast_nonneg _
    rw [hM]; nlinarith
  have hMle : M ≤ (Ks + 1) * Y := by
    have hm1 := rmass_le_cnt mid.card true mid Y
      (fun q h => (hP q (Finset.mem_filter.mp h).1).one_lt.le) (by linarith)
      (fun _ q h => by
        obtain ⟨_, _, hqZ⟩ := Finset.mem_filter.mp h
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
        have h2 : (q : ℝ) ^ 2 < Z ^ 2 := by nlinarith
        have h3 : Z ^ 2 ≤ Y := by
          rw [hYdef, ← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)
        linarith)
    have hm2 := cnt_le mid (fun q h => hP q (Finset.mem_filter.mp h).1) Y hY0.le
    have hks : (2 : ℝ) ^ small.card ≤ Ks := by
      unfold Ks
      exact pow_le_pow_right₀ (by norm_num)
        (card_filter_le_pow P hP E _ fun ℓ h => h)
    have hlc : (large.card : ℝ) ≤ ρ := by
      rw [hρdef]; exact_mod_cast Finset.card_filter_le _ _
    have hr0 : 0 ≤ rmass mid.card true mid Y := le_trans zero_le_one (rmass_ge_one _ _ _ _)
    rw [hM]
    calc (2 : ℝ) ^ small.card * rmass mid.card true mid Y + large.card ≤ Ks * Y + ρ := by
          have := mul_le_mul hks (hm1.trans hm2) hr0 Ks_pos.le
          linarith
      _ ≤ (Ks + 1) * Y := by nlinarith
  -- the main term
  set θ : ℝ := 1 / (200 * (AA + 1) * t ^ 2) with hθdef
  have ht0 : 0 < t := by linarith
  have hθpos : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht1
    nlinarith
  have hθF : θ ≤ F recip := by
    obtain ⟨c205, hc205, hcg, hca⟩ := cell205
    have hgood : Good mid Z := by
      refine ⟨fun q h => ?_, ?_⟩
      · obtain ⟨hqP, h1, h2⟩ := Finset.mem_filter.mp h
        exact ⟨hP q hqP, h1, h2⟩
      · have : (2 : ℝ) ^ E = AA := rfl
        rw [this]; exact hZA
    have hcl := (claims_of cells allOK_cells mid.card mid le_rfl Z Y hgood hY0).2.1 c205 hc205
      (by omega) (by rw [hcg, hlZ]; norm_num)
    have hra : r c205.2.2 ≤ 98 / 100 := by
      unfold r
      have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
      rw [div_le_iff₀ hD]
      have : ((100 * c205.2.2 : ℕ) : ℝ) ≤ ((98 * Dn : ℕ) : ℝ) := by exact_mod_cast hca
      push_cast at this; linarith
    -- `V(mid) ≥ 1/(2t²)`
    have hVm : 1 / (2 * t ^ 2) ≤ V mid := by
      have hW := prod_inv_le_Om mid Z t ht1 fun q h => by
        obtain ⟨hqP, h1, h2⟩ := Finset.mem_filter.mp h
        refine ⟨hP q hqP, h1, h2, ?_⟩
        have hq := hcastE q h1
        have hlq : Real.log AA < Real.log q := Real.log_lt_log hA0 hq
        rw [htdef, div_mul_eq_mul_div, le_div_iff₀ hlA]
        have : 0 ≤ Real.log Z := by linarith [Real.log_pos hZ1]
        nlinarith
      have hOm := Om_le_sq ht1
      have hinv : ∏ q ∈ mid, (1 - recip q)⁻¹ = (V mid)⁻¹ := by
        unfold V; rw [Finset.prod_inv_distrib]
      have hVpos := V_pos mid fun q h => (hP q (Finset.mem_filter.mp h).1).two_le
      rw [hinv] at hW
      have h2 : (V mid)⁻¹ ≤ 2 * t ^ 2 := by nlinarith
      rw [one_div]
      exact (inv_le_comm₀ (by positivity) hVpos).mpr h2
    -- `V(small) ≥ 1/(A+1)`
    have hVs : 1 / (AA + 1) ≤ ∏ q ∈ small, (1 - recip q) := by
      have h := prod_one_sub_inv_ge small fun q h => (hP q (Finset.mem_filter.mp h).1).two_le
      have hc : (small.card : ℝ) ≤ AA := by
        unfold AA; exact_mod_cast card_filter_le_pow P hP E _ fun ℓ h => h
      have h' : 1 / ((small.card : ℝ) + 1) ≤ ∏ q ∈ small, (1 - recip q) := by
        simpa [recip] using h
      exact le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) h'
    -- the large primes
    have hlg : ∑ q ∈ large, recip q ≤ ρ / Z := by
      calc ∑ q ∈ large, recip q ≤ ∑ _q ∈ large, 1 / Z := Finset.sum_le_sum fun q h => by
            unfold recip
            exact one_div_le_one_div_of_le hZ0 (Finset.mem_filter.mp h).2.2
        _ = large.card / Z := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ρ / Z := by
            apply div_le_div_of_nonneg_right _ hZ0.le
            rw [hρdef]; exact_mod_cast Finset.card_filter_le _ _
    have hρZ : ρ / Z ≤ θ := by
      rw [hθdef, div_le_div_iff₀ hZ0 (by positivity)]; linarith
    have hLlow : 1 / (2 * t ^ 2) * (1 / 50) ≤ ros mid.card true mid Y recip := by
      refine le_trans ?_ hcl
      exact mul_le_mul hVm (by linarith) (by norm_num) (V_pos mid fun q h =>
        (hP q (Finset.mem_filter.mp h).1).two_le).le
    have hVs0 : 0 ≤ ∏ q ∈ small, (1 - recip q) := by
      have := hVs; have : 0 < 1 / (AA + 1) := by positivity
      linarith
    show θ ≤ (∏ q ∈ small, (1 - recip q)) * ros mid.card true mid Y recip - ∑ q ∈ large, recip q
    have hprod : 1 / (AA + 1) * (1 / (2 * t ^ 2) * (1 / 50)) ≤
        (∏ q ∈ small, (1 - recip q)) * ros mid.card true mid Y recip :=
      mul_le_mul hVs hLlow (by positivity) hVs0
    have e : 1 / (AA + 1) * (1 / (2 * t ^ 2) * (1 / 50)) = 2 * θ := by
      rw [hθdef]; field_simp; ring
    linarith
  have hsieve := le_of_no_primitive_root_lt_rep hGRH p hp hp2 x hx1 hxp hno F M θ hrep hpt hM1
    hθpos hθ1 hθF
  -- bookkeeping
  have hL0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hMθ : M / θ ≤ Kfin * ρ ^ (21 / 10 : ℝ) := by
    rw [div_le_iff₀ hθpos]
    have hK : M ≤ (Ks + 1) * Y := hMle
    have : (Ks + 1) * Y = (Ks + 1) * 200 * (AA + 1) * (Y * t ^ 2) * θ := by
      rw [hθdef]; field_simp
    rw [this] at hK
    refine hK.trans ?_
    unfold Kfin
    have h0 : 0 ≤ (Ks + 1) * 200 * (AA + 1) := by have := Ks_pos; positivity
    have := mul_le_mul_of_nonneg_left hYt h0
    nlinarith [hθpos]
  have hMθ0 : 0 ≤ M / θ := by positivity
  calc (x : ℝ) ≤ 1089 * (M * Real.log p / θ) ^ 2 := hsieve
    _ = 1089 * (M / θ) ^ 2 * Real.log p ^ 2 := by ring
    _ ≤ 1089 * (Kfin * ρ ^ (21 / 10 : ℝ)) ^ 2 * Real.log p ^ 2 := by gcongr
    _ = 1089 * Kfin ^ 2 * ρ ^ (21 / 5 : ℝ) * Real.log p ^ 2 := by
        have e : (ρ ^ (21 / 10 : ℝ)) ^ 2 = ρ ^ (21 / 5 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
        rw [mul_pow, e]; ring

end Shoup.Rosser

namespace Shoup

open Rosser ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- The constant of `PolyOmegaRealStatement (21/5)`. -/
noncomputable def Creal : ℝ := 1089 * Kfin ^ 2

/-- **Main theorem (exponent `21/5`).** Under GRH, every odd prime `p` has a primitive root
`0 < g ≤ C ω(p-1)^{21/5} (log p)²`. -/
theorem leastPrimitiveRoot_le_real_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (Creal * (ω (p - 1) : ℝ) ^ (21 / 5 : ℝ) * Real.log p ^ 2) := by
  have h := hasPrimitiveRootLE_of_bound p hp
    (1089 * Kfin ^ 2 * ((p - 1).primeFactors.card : ℝ) ^ (21 / 5 : ℝ) * Real.log p ^ 2)
    (by positivity) fun x hx1 hxp hno =>
      le_of_no_primitive_root_lt_real hGRH p hp hp2 x hx1 hxp hno
  rw [← cardDistinctFactors_eq_card_primeFactors] at h
  exact h

/-- `PolyOmegaRealStatement (21/5)` holds under GRH. -/
theorem polyOmegaReal_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    PolyOmegaRealStatement (21 / 5) :=
  ⟨Creal, fun p hp hp2 => leastPrimitiveRoot_le_real_of_GRH hGRH p hp hp2⟩

/-- Consequently `PolyOmegaStatement 5`. -/
theorem polyOmega5_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    PolyOmegaStatement 5 := by
  refine ⟨Creal, fun p hp hp2 => (leastPrimitiveRoot_le_real_of_GRH hGRH p hp hp2).mono ?_⟩
  have hm : (1 : ℝ) ≤ ω (p - 1) := by
    rw [cardDistinctFactors_eq_card_primeFactors]
    exact_mod_cast one_le_card_primeFactors p hp hp2
  have h5 : (ω (p - 1) : ℝ) ^ (21 / 5 : ℝ) ≤ (ω (p - 1) : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have hC : 0 ≤ Creal := by unfold Creal; positivity
  have := mul_le_mul_of_nonneg_left h5 hC
  have hL : 0 ≤ Real.log p ^ 2 := by positivity
  nlinarith

end Shoup
