import Shoup.Sieve.Main

/-!
# Sharper bookkeeping for the Brun–Hooley sieve

* `phi_eq_prodU_mul`: `Φ = (∏_j U_j)(1 - Σ_j e_j/U_j)` exactly (when every `U_j ≠ 0`), so
  `Φ ≥ (∏_j A_j)(1 - Σ_j e_j/U_j)` (`phi_ge_U`). For a level-1 block `U = 1` and `e/U = Σ y`.
* `isRep_phi2`: `Φ` has mass at most `(1 + Σ_j |B_j|) ∏_j (|B_j| + 1)^{2k_j}`, instead of
  `(J + 1) ∏_j (|B_j| + 1)^{2k_j+1}`.
* `E_le_pow_div_factorial`: Maclaurin's `e_m(y) ≤ (Σ y)^m / m!`.
* `exp_le_prod'`: `∏ (1 - y) ≥ exp(-(1 + η) Σ y)` when every `y ≤ η ≤ 1/3`.
* `le_of_no_primitive_root_lt'`: the sieve inequality with a general mass `M` and a general
  lower bound `θ ≤ Φ(1/ℓ)`: `x ≤ 1089 (M log p / θ)²`.
-/

namespace Shoup.Sieve

open Finset ArithmeticFunction Erdos985 Erdos985.Indicator

/-! ### The exact Brun–Hooley identity -/

/-- `Σ_j e_j / U_j`. -/
noncomputable def ratioSumU : List Block → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | b :: bs, y => Eb b y / Ub b y + ratioSumU bs y

lemma phi_eq_prodU_mul (y : ℕ → ℝ) (bs : List Block) (hU : ∀ b ∈ bs, Ub b y ≠ 0) :
    phi bs y = prodU bs y * (1 - ratioSumU bs y) := by
  induction bs with
  | nil => simp [phi, prodU, ratioSumU]
  | cons b bs ih =>
    have hb := hU b List.mem_cons_self
    have ih' := ih fun c h => hU c (List.mem_cons_of_mem _ h)
    simp only [phi, prodU, ratioSumU, ih']
    field_simp
    ring

lemma Ub_pos (y : ℕ → ℝ) (b : Block) (hy : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) : 0 < Ub b y := by
  have hyb : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => ⟨(hy ℓ h).1, by linarith [(hy ℓ h).2]⟩
  exact (Ab_pos y b hy).trans_le (block_bounds y b hyb).2.1

/-- Main-term lower bound with the ratios `e_j/U_j`. -/
theorem phi_ge_U (y : ℕ → ℝ) (bs : List Block) (hy : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2)
    (hR : ratioSumU bs y ≤ 1) : prodA bs y * (1 - ratioSumU bs y) ≤ phi bs y := by
  have hU : ∀ b ∈ bs, 0 < Ub b y := fun b hb =>
    Ub_pos y b fun ℓ h => hy ℓ (subset_supp hb h)
  rw [phi_eq_prodU_mul y bs fun b hb => (hU b hb).ne']
  have hy' : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 :=
    fun ℓ h => ⟨(hy ℓ h).1, by linarith [(hy ℓ h).2]⟩
  obtain ⟨_, hAU, _⟩ := phi_le_prodA y bs hy'
  exact mul_le_mul_of_nonneg_right hAU (by linarith)

lemma Eb_div_Ub_le (y : ℕ → ℝ) (b : Block) (hy : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) :
    Eb b y / Ub b y ≤ Eb b y / Ab b y := by
  have hyb : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => ⟨(hy ℓ h).1, by linarith [(hy ℓ h).2]⟩
  exact div_le_div_of_nonneg_left (E_nonneg _ _ _ fun ℓ h => (hy ℓ h).1) (Ab_pos y b hy)
    (block_bounds y b hyb).2.1

lemma Eb_div_Ub_level_one (y : ℕ → ℝ) (B : Finset ℕ) :
    Eb (B, 0) y / Ub (B, 0) y = ∑ ℓ ∈ B, y ℓ := by
  simp [Eb, Ub, E_one, G_one]

lemma ratioSumU_append (L₁ L₂ : List Block) (y : ℕ → ℝ) :
    ratioSumU (L₁ ++ L₂) y = ratioSumU L₁ y + ratioSumU L₂ y := by
  induction L₁ with
  | nil => simp [ratioSumU]
  | cons b L ih => simp only [List.cons_append, ratioSumU, ih]; ring

lemma ratioSumU_map_range (g : ℕ → Block) (t : ℕ) (y : ℕ → ℝ) :
    ratioSumU ((List.range t).map g) y = ∑ i ∈ range t, Eb (g i) y / Ub (g i) y := by
  induction t with
  | zero => simp [ratioSumU]
  | succ t ih =>
    rw [List.range_succ, List.map_append, ratioSumU_append, ih, Finset.sum_range_succ]
    simp [ratioSumU]

/-! ### Maclaurin and the product bound -/

lemma E_zero (B : Finset ℕ) (y : ℕ → ℝ) : E 0 B y = 1 := by simp [E]

lemma E_insert {x : ℕ} {B : Finset ℕ} (hx : x ∉ B) (k : ℕ) (y : ℕ → ℝ) :
    E (k + 1) (insert x B) y = E (k + 1) B y + y x * E k B y := by
  have a := G_succ (k + 1) (insert x B) y
  have b := G_insert hx (k + 1) y
  have c := G_insert hx k y
  have d := G_succ (k + 1) B y
  have e := G_succ k B y
  have hs : (-1 : ℝ) ^ (k + 1) * E (k + 1) (insert x B) y =
      (-1 : ℝ) ^ (k + 1) * E (k + 1) B y - y x * ((-1 : ℝ) ^ k * E k B y) := by
    linear_combination -a + b - c + d - (y x) * e
  have hsign : (-1 : ℝ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have : (-1 : ℝ) ^ (k + 1) * E (k + 1) (insert x B) y =
      (-1 : ℝ) ^ (k + 1) * (E (k + 1) B y + y x * E k B y) := by
    rw [hs, pow_succ]; ring
  exact mul_left_cancel₀ hsign this

lemma bin_lower (σ t : ℝ) (hσ : 0 ≤ σ) (ht : 0 ≤ t) (k : ℕ) :
    σ ^ (k + 1) + (k + 1) * t * σ ^ k ≤ (σ + t) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ σ + t := by linarith
    have h2 := mul_le_mul_of_nonneg_left ih h1
    have h3 : 0 ≤ (k + 1) * t ^ 2 * σ ^ k := by positivity
    push_cast
    calc σ ^ (k + 1 + 1) + (k + 1 + 1) * t * σ ^ (k + 1)
        ≤ (σ + t) * (σ ^ (k + 1) + (k + 1) * t * σ ^ k) := by
          rw [pow_succ σ (k + 1), pow_succ σ k]; nlinarith
      _ ≤ (σ + t) * (σ + t) ^ (k + 1) := h2
      _ = (σ + t) ^ (k + 1 + 1) := by rw [pow_succ]; ring

/-- **Maclaurin's inequality** `e_m ≤ (Σ y)^m / m!`. -/
theorem E_le_pow_div_factorial (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ) (m : ℕ) :
    E m B y ≤ (∑ ℓ ∈ B, y ℓ) ^ m / m.factorial := by
  induction B using Finset.induction_on generalizing m with
  | empty =>
    rcases m with _ | m
    · simp [E_zero]
    · rw [E, Finset.powersetCard_eq_empty.mpr (by simp)]; simp
  | insert x B hx ih =>
    have hyB : ∀ ℓ ∈ B, 0 ≤ y ℓ := fun ℓ h => hy ℓ (Finset.mem_insert_of_mem h)
    have hyx : 0 ≤ y x := hy x (Finset.mem_insert_self x B)
    rcases m with _ | k
    · simp [E_zero]
    · rw [E_insert hx k y, Finset.sum_insert hx]
      set σ := ∑ ℓ ∈ B, y ℓ with hσ
      have hσ0 : 0 ≤ σ := Finset.sum_nonneg hyB
      have h1 := ih hyB (k + 1)
      have h2 := ih hyB k
      have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
      have hf1 : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial := by
        push_cast [Nat.factorial_succ]; ring
      have hbin : σ ^ (k + 1) + (k + 1) * y x * σ ^ k ≤ (y x + σ) ^ (k + 1) := by
        rw [add_comm (y x) σ]; exact bin_lower σ (y x) hσ0 hyx k
      calc E (k + 1) B y + y x * E k B y
          ≤ σ ^ (k + 1) / ((k + 1).factorial) + y x * (σ ^ k / k.factorial) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 hyx)
        _ = (σ ^ (k + 1) + (k + 1) * y x * σ ^ k) / ((k + 1).factorial) := by
            rw [hf1]; field_simp
        _ ≤ (y x + σ) ^ (k + 1) / ((k + 1).factorial) := by
            apply div_le_div_of_nonneg_right hbin; positivity

lemma one_sub_ge_exp {y η : ℝ} (h0 : 0 ≤ y) (hη : y ≤ η) (hη3 : η ≤ 1 / 3) :
    Real.exp (-((1 + η) * y)) ≤ 1 - y := by
  have ht : 0 ≤ y + y ^ 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg ht
  have hpos := Real.exp_pos (y + y ^ 2)
  have hmul : Real.exp (-(y + y ^ 2)) * Real.exp (y + y ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 : Real.exp (-(y + y ^ 2)) ≤ 1 - y := by
    -- `(1 - y) exp(y + y²) ≥ (1 - y)(1 + y + 3y²/2) ≥ 1`
    have hy3 : y ≤ 1 / 3 := hη.trans hη3
    have hkey : 1 ≤ (1 - y) * Real.exp (y + y ^ 2) := by
      have : 1 ≤ (1 - y) * (1 + (y + y ^ 2) + (y + y ^ 2) ^ 2 / 2) := by nlinarith
      exact this.trans (mul_le_mul_of_nonneg_left hq (by linarith))
    nlinarith
  refine le_trans ?_ h1
  apply Real.exp_le_exp.mpr
  nlinarith

/-- `∏ (1 - y) ≥ exp(-(1 + η) Σ y)` for `0 ≤ y ≤ η ≤ 1/3`. -/
lemma exp_le_prod' (B : Finset ℕ) (y : ℕ → ℝ) {η : ℝ} (hη3 : η ≤ 1 / 3)
    (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ η) :
    Real.exp (-((1 + η) * ∑ ℓ ∈ B, y ℓ)) ≤ ∏ ℓ ∈ B, (1 - y ℓ) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun ℓ _ => (Real.exp_pos _).le)
    fun ℓ h => one_sub_ge_exp (hy ℓ h).1 (hy ℓ h).2 hη3

/-- `e_m / ∏(1 - y) ≤ σ^m/m! · exp((1 + η) σ)`. -/
theorem E_div_prod_le' (m : ℕ) (B : Finset ℕ) (y : ℕ → ℝ) {η : ℝ} (hη3 : η ≤ 1 / 3)
    (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ η) :
    E m B y / ∏ ℓ ∈ B, (1 - y ℓ) ≤
      (∑ ℓ ∈ B, y ℓ) ^ m / m.factorial * Real.exp ((1 + η) * ∑ ℓ ∈ B, y ℓ) := by
  have hP := exp_le_prod' B y hη3 hy
  have hPpos : 0 < ∏ ℓ ∈ B, (1 - y ℓ) := (Real.exp_pos _).trans_le hP
  have hE := E_le_pow_div_factorial B y (fun ℓ h => (hy ℓ h).1) m
  rw [div_le_iff₀ hPpos]
  have hinv : Real.exp ((1 + η) * ∑ ℓ ∈ B, y ℓ) * Real.exp (-((1 + η) * ∑ ℓ ∈ B, y ℓ)) = 1 := by
    rw [← Real.exp_add]; simp
  have h0 : 0 ≤ (∑ ℓ ∈ B, y ℓ) ^ m / m.factorial := by
    have := Finset.sum_nonneg fun ℓ h => (hy ℓ h).1
    positivity
  have hX := mul_le_mul_of_nonneg_left hP
    (mul_nonneg h0 (Real.exp_pos ((1 + η) * ∑ ℓ ∈ B, y ℓ)).le)
  nlinarith

/-! ### The sharper mass bound -/

lemma isRep_G' (k : ℕ) (B : Finset ℕ) :
    IsRep (G (2 * k + 1) B) B ((B.card + 1 : ℝ) ^ (2 * k)) := by
  have h := IsRep.finsetSum (B.powerset.filter fun T => T.card < 2 * k + 1)
    (fun T => (-1 : ℝ) ^ T.card) B
    (fun T hT => Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
  refine (h.congr fun y => ?_).mono le_rfl ?_
  · unfold G; rw [Finset.sum_filter]
  · simp only [abs_pow, abs_neg, abs_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    set m := 2 * k with hm
    have hcard : (B.powerset.filter fun T => T.card < m + 1).card ≤ (B.card + 1) ^ m := by
      calc (B.powerset.filter fun T => T.card < m + 1).card
          = ∑ i ∈ Finset.range (m + 1), (B.powersetCard i).card := by
            rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (m + 1))
              (fun T hT => Finset.mem_range.mpr (Finset.mem_filter.mp hT).2)]
            refine Finset.sum_congr rfl fun i hi => ?_
            congr 1
            ext T
            simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
            constructor
            · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ Finset.mem_range.mp hi⟩, h2⟩
        _ ≤ ∑ i ∈ Finset.range (m + 1), B.card ^ i * 1 ^ (m - i) * m.choose i := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [Finset.card_powersetCard, one_pow, mul_one]
            have h1 := Nat.choose_le_pow B.card i
            have h2 : 1 ≤ m.choose i := Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
            nlinarith
        _ = (B.card + 1) ^ m := (add_pow _ _ _).symm
    exact_mod_cast hcard

lemma isRep_E' (k : ℕ) (B : Finset ℕ) :
    IsRep (E (2 * k + 1) B) B ((B.card : ℝ) * (B.card + 1 : ℝ) ^ (2 * k)) := by
  have h := IsRep.finsetSum (B.powersetCard (2 * k + 1)) (fun _ => 1) B
    (fun T hT => (Finset.mem_powersetCard.mp hT).1)
  refine (h.congr fun y => ?_).mono le_rfl ?_
  · simp [E]
  · simp only [abs_one, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard]
    have h1 := Nat.choose_le_pow B.card (2 * k + 1)
    have h2 : B.card ^ (2 * k + 1) ≤ B.card * (B.card + 1) ^ (2 * k) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _)
    exact_mod_cast h1.trans h2

/-- `∏_j (|B_j| + 1)^{2k_j}`. -/
noncomputable def massU : List Block → ℝ
  | [] => 1
  | b :: bs => ((b.1.card + 1 : ℝ) ^ (2 * b.2)) * massU bs

/-- `Σ_j |B_j|`. -/
def cardSum : List Block → ℕ
  | [] => 0
  | b :: bs => b.1.card + cardSum bs

lemma massU_nonneg (bs : List Block) : 0 ≤ massU bs := by
  induction bs with
  | nil => simp [massU]
  | cons b bs ih => simp only [massU]; positivity

theorem isRep_phi2 (bs : List Block) (hd : Disj bs) :
    IsRep (prodU bs) (supp bs) (massU bs) ∧
    IsRep (phi bs) (supp bs) ((1 + cardSum bs : ℝ) * massU bs) := by
  induction bs with
  | nil =>
    simp only [prodU, phi, supp, massU, cardSum, Nat.cast_zero, add_zero, one_mul]
    exact ⟨IsRep.one, IsRep.one⟩
  | cons b bs ih =>
    obtain ⟨hdb, hds⟩ := hd
    obtain ⟨hU, hΦ⟩ := ih hds
    have hUb := isRep_G' b.2 b.1
    have hEb := isRep_E' b.2 b.1
    have hM0 := massU_nonneg bs
    refine ⟨?_, ?_⟩
    · exact (hUb.mul hU hdb).congr fun y => rfl
    · have h1 := hUb.mul hΦ hdb
      have h2 := hEb.mul hU hdb
      refine ((h1.sub h2).congr fun y => rfl).mono le_rfl ?_
      simp only [massU, cardSum]
      push_cast
      have : 0 ≤ ((b.1.card + 1 : ℝ) ^ (2 * b.2)) := by positivity
      nlinarith

/-! ### The sieve inequality, general form -/

theorem le_of_no_primitive_root_lt' (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1)
    (bs : List Block) (hsupp : supp bs = (p - 1).primeFactors)
    (M θ : ℝ) (hrep : IsRep (phi bs) (supp bs) M) (hM1 : 1 ≤ M) (hθpos : 0 < θ)
    (hθ : θ ≤ phi bs recip) :
    (x : ℝ) ≤ 1089 * (M * Real.log p / θ) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hN : p - 1 ≠ 0 := by omega
  obtain ⟨ψ', hψ'⟩ : ∃ ψ : MulChar (ZMod p) ℂ, orderOf ψ = p - 1 :=
    MulChar.exists_mulChar_orderOf (ZMod p) (by rw [ZMod.card])
      (Complex.isPrimitiveRoot_exp (p - 1) hN)
  set ψ : DirichletCharacter ℂ p := ψ'
  have hψ : orderOf ψ = p - 1 := hψ'
  set L := Real.log p with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ p := by exact_mod_cast h3
    linarith
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  set s := √(x : ℝ) with hsdef
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr hxR
  have hss : s * s = x := Real.mul_self_sqrt (by linarith)
  set B : ℝ := 13 * s * L with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B := by
    intro χ hχ
    refine (Analytic.bach_nonprincipal_of_GRH hGRH p χ hχ x hx1).trans ?_
    have := bachC_le_thirteen p x h3 hx1
    have : 0 ≤ s * L := by positivity
    calc bachC p x * s * L = bachC p x * (s * L) := by ring
      _ ≤ 13 * (s * L) := mul_le_mul_of_nonneg_right (by assumption) this
      _ = B := by ring
  have hrep' := hrep
  rw [hsupp] at hrep'
  have htr := transfer ψ hψ x hxp B hB0 hB hrep'
  set S := ∑ n ∈ range x, wt x n with hSdef
  have hpt : ∑ n ∈ range x, wt x n * phi bs (ind ψ n) ≤ 0 := by
    refine Finset.sum_nonpos fun n hn => ?_
    by_cases hΛ : Λ n = 0
    · simp [wt, hΛ]
    have hwt : 0 ≤ wt x n := by
      unfold wt
      have : (n : ℝ) / x ≤ 1 := by
        rw [div_le_one (by linarith)]; exact_mod_cast (mem_range.mp hn).le
      exact mul_nonneg vonMangoldt_nonneg (by linarith)
    have hn0 := natCast_ne_zero_of_vonMangoldt hxp (mem_range.mp hn) hΛ
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hn0
      · exact h
    obtain ⟨ℓ, hℓ, hpow⟩ :=
      exists_primeFactor_pow_eq_one p hn0 (hno n hnpos (mem_range.mp hn))
    have hind : ind ψ n ℓ = 1 := by
      unfold ind; rw [ite_eq_left_iff.mpr (fun h => absurd (by rw [← map_pow, hpow, map_one]) h)]
    have hmem : ∀ ℓ ∈ supp bs, 0 ≤ ind ψ n ℓ ∧ ind ψ n ℓ ≤ 1 := fun ℓ _ => ind_mem ψ n ℓ
    have hΦ := (phi_le_prodA (ind ψ n) bs hmem).1
    rw [prodA_eq_zero (ind ψ n) bs (hsupp ▸ hℓ) hind] at hΦ
    exact mul_nonpos_of_nonneg_of_nonpos hwt hΦ
  have hrec1 : ∀ ℓ ∈ supp bs, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 := fun ℓ h =>
    have := recip_mem (Nat.mem_primeFactors.mp (hsupp ▸ h)).1
    ⟨this.1, by linarith [this.2]⟩
  have hθ1 : θ ≤ 1 :=
    hθ.trans ((phi_le_prodA recip bs hrec1).1.trans (prodA_le_one bs recip hrec1))
  have hSΦ : S * phi bs recip ≤ M * B := by
    have := (abs_le.mp htr).1
    linarith
  have hprin := (abs_le.mp (Analytic.bach_principal_of_GRH hGRH x hx1)).1
  have hSlow : (x : ℝ) / 2 - s / 20 - 3 ≤ S := by
    have : S = ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) := rfl
    rw [this]; linarith
  set K := M * L / θ with hK
  have hK1 : 1 ≤ K := by
    rw [hK, le_div_iff₀ hθpos]; nlinarith
  have hgoal : (x : ℝ) ≤ 1089 * K ^ 2 := by
    by_cases hs0 : (x : ℝ) / 2 - s / 20 - 3 ≤ 0
    · nlinarith
    rw [not_le] at hs0
    have hSpos : 0 < S := by linarith
    have h1 : ((x : ℝ) / 2 - s / 20 - 3) * θ ≤ M * B := by
      calc ((x : ℝ) / 2 - s / 20 - 3) * θ ≤ S * θ :=
            mul_le_mul_of_nonneg_right hSlow hθpos.le
        _ ≤ S * phi bs recip := mul_le_mul_of_nonneg_left hθ hSpos.le
        _ ≤ M * B := hSΦ
    have hKθ : K * θ = M * L := by rw [hK]; field_simp
    have h2 : (x : ℝ) / 2 - s / 20 - 3 ≤ 13 * K * s := by
      have : ((x : ℝ) / 2 - s / 20 - 3) * θ ≤ (13 * K * s) * θ := by
        have : M * B = 13 * s * (M * L) := by rw [hBdef]; ring
        nlinarith
      exact le_of_mul_le_mul_right this hθpos
    have h3 : s ≤ 33 * K := by nlinarith
    nlinarith
  exact hgoal

end Shoup.Sieve
