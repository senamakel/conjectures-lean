import Shoup.Sieve.DesignBound

/-!
# The error of the Buchstab sieve, from a checked table

A table is a list of classes `C` with thresholds `hi > lo` (the primes `2^{lo n} < ℓ ≤ 2^{hi n}`
of a class), a log bound `cl ≥ D log(hi/lo)` and the rows of the class's design. The prime
`ℓ` gets the design of its class (`pick`), and the primes `ℓ ≤ 2^n` get the tail design.

`errSum` computes, in fixed point, `Σ_C σ_C · W_C · (F_C - 1)` where `σ_C` bounds `Σ 1/ℓ` over
the class, `W_C = exp((1+10^{-6}) Σ_{ℓ > 2^{lo n}} 1/ℓ)` bounds `W_ℓ`, and `F_C` bounds the
factor product of the design. `err_table_le` proves that the real error is at most
`errSum / D + 10^{-5}` when `tableOK` holds.
-/

namespace Shoup.Sieve

open Finset Fixed

structure Cls where
  hi : ℕ
  lo : ℕ
  cl : ℕ
  des : List Row

def TAILF : ℕ := Dn + cdiv Dn (10 ^ 9)

def clsF (first : Bool) (up : ℕ) (C : Cls) : ℕ :=
  mulU (mulU (if first then expU (xq up) else Dn) (facProd C.des)) TAILF

def errSum : Bool → ℕ → List Cls → ℕ
  | _, _, [] => 0
  | first, up, C :: rest =>
    mulU (sigq C.hi C.lo C.cl + (if first then up else 0))
        (mulU (expU (xq (up + sigq C.hi C.lo C.cl))) (clsF first up C - Dn)) +
      errSum false (up + sigq C.hi C.lo C.cl) rest

def massE : List Row → ℕ
  | [] => 0
  | x :: rs => 2 * x.2.2.1 * x.1 + massE rs

def kSum : List Row → ℕ
  | [] => 0
  | x :: rs => 2 * x.2.2.1 + kSum rs

def tableOK (S : ℕ) : Bool → ℕ → ℕ → List Cls → Bool
  | first, up, t, [] => !first && t == 1 && xq up ≤ 16 * Dn && expU (xq up) ≤ 30000 * Dn
  | first, up, t, C :: rest =>
      C.hi == t && rowOK C.hi C.lo 0 C.cl && chainOK C.hi C.des && xq up ≤ 16 * Dn &&
        xq (up + sigq C.hi C.lo C.cl) ≤ 16 * Dn && C.hi + 30 + massE C.des ≤ S &&
        kSum C.des ≤ 600 && tableOK S false (up + sigq C.hi C.lo C.cl) C.lo rest

def custList (P : Finset ℕ) (n : ℕ) : List Cls → List (ℕ × List Block)
  | [] => []
  | C :: rest => (C.lo * n, desC P n C.hi C.des) :: custList P n rest

/-- The design of `ℓ`. -/
def desOf (P : Finset ℕ) (n : ℕ) (tab : List Cls) (ℓ : ℕ) : List Block :=
  restr ℓ (pick (desC P n 1 []) ℓ (custList P n tab))

/-! ### Auxiliary bounds -/

lemma sigma_le_sigq (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) {a b n : ℕ} (k c : ℕ)
    (hB : ∀ ℓ ∈ S, 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n)) (hn : 2 ^ 36 ≤ n)
    (hok : rowOK a b k c = true) : ∑ ℓ ∈ S, recip ℓ ≤ r (sigq a b c) := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hb, hab⟩, ha4⟩, hlog⟩, _⟩ := hok
  have hlo : 2 ^ 36 ≤ b * n := le_trans hn (Nat.le_mul_of_pos_left n hb)
  have hσ := sigma_block_le S hS (b * n) (a * n) hlo
    (Nat.mul_le_mul_right n hab.le) (by nlinarith) hB
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) < 2 ^ 36 := by positivity
    exact this.trans_le (by exact_mod_cast hn)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have e1 : Real.log (((a * n : ℕ) : ℝ) / ((b * n : ℕ) : ℝ)) = Real.log ((a : ℝ) / b) := by
    push_cast; congr 1; field_simp
  have e2 : (((a * n : ℕ) : ℝ) - ((b * n : ℕ) : ℝ)) / (4096 * ((b * n : ℕ) : ℝ)) =
      ((a : ℝ) - b) / (4096 * b) := by push_cast; field_simp
  rw [e1, e2] at hσ
  have hl := log_le_of_lowSum (by omega) hb hlog
  have hsq := sigq_ge a b c hb hab.le
  linarith

lemma sum_recip_mono {A B : Finset ℕ} (h : A ⊆ B) : ∑ ℓ ∈ A, recip ℓ ≤ ∑ ℓ ∈ B, recip ℓ :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ℓ _ _ => by unfold recip; positivity

/-- `W_ℓ ≤ exp((1 + 2^{-L}) σ)` for `ℓ > 2^L`, `σ ≥ Σ_{ℓ' ∈ P, ℓ' > 2^L} 1/ℓ'`. -/
lemma Wt_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (L : ℕ) (hL : 2 ≤ L) (ℓ : ℕ) (hℓ : 2 ^ L < ℓ)
    (σ₀ : ℝ) (hσ : ∑ x ∈ P.filter (fun x => 2 ^ L < x), recip x ≤ σ₀) :
    Wt P recip ℓ ≤ Real.exp ((1 + 1 / 2 ^ L) * σ₀) := by
  set Big := P.filter (fun x => 2 ^ L < x)
  set Small := P.filter (fun x => ℓ ≤ x)
  have hsub : Small ⊆ Big := by
    intro x hx
    simp only [Small, Big, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by omega⟩
  have hη3 : (1 : ℝ) / 2 ^ L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (4 : ℝ) ≤ 2 ^ L := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL
    linarith
  have hy : ∀ x ∈ Big, 0 ≤ recip x ∧ recip x ≤ 1 / 2 ^ L := by
    intro x hx
    have : (2 : ℝ) ^ L < x := by exact_mod_cast (Finset.mem_filter.mp hx).2
    exact ⟨by unfold recip; positivity, one_div_le_one_div_of_le (by positivity) this.le⟩
  have hfac : ∀ x ∈ Big, 0 < 1 - recip x ∧ 1 - recip x ≤ 1 := by
    intro x hx
    have := hy x hx
    constructor <;> linarith
  have hBig := exp_le_prod' Big recip hη3 hy
  have hsplit : ∏ x ∈ Big, (1 - recip x) =
      (∏ x ∈ Small, (1 - recip x)) * ∏ x ∈ Big \ Small, (1 - recip x) := by
    rw [mul_comm, Finset.prod_sdiff hsub]
  have hrest : ∏ x ∈ Big \ Small, (1 - recip x) ≤ 1 :=
    Finset.prod_le_one₀ (fun x hx => (hfac x (Finset.sdiff_subset hx)).1.le)
      fun x hx => (hfac x (Finset.sdiff_subset hx)).2
  have hrest0 : 0 ≤ ∏ x ∈ Big \ Small, (1 - recip x) :=
    Finset.prod_nonneg fun x hx => (hfac x (Finset.sdiff_subset hx)).1.le
  have hS0 : 0 < ∏ x ∈ Small, (1 - recip x) :=
    Finset.prod_pos fun x hx => (hfac x (hsub hx)).1
  have hBS : ∏ x ∈ Big, (1 - recip x) ≤ ∏ x ∈ Small, (1 - recip x) := by
    rw [hsplit]; nlinarith
  have hσ' : (1 + 1 / 2 ^ L) * ∑ x ∈ Big, recip x ≤ (1 + 1 / 2 ^ L) * σ₀ :=
    mul_le_mul_of_nonneg_left hσ (by positivity)
  unfold Wt
  rw [div_le_iff₀ hS0]
  have h1 : Real.exp (-((1 + 1 / 2 ^ L) * σ₀)) ≤ ∏ x ∈ Small, (1 - recip x) :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) (hBig.trans hBS)
  have hinv : Real.exp ((1 + 1 / 2 ^ L) * σ₀) * Real.exp (-((1 + 1 / 2 ^ L) * σ₀)) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 : ℝ) = Real.exp ((1 + 1 / 2 ^ L) * σ₀) * Real.exp (-((1 + 1 / 2 ^ L) * σ₀)) := hinv.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

lemma Wt_nonneg (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (ℓ : ℕ) : 0 ≤ Wt P recip ℓ := by
  unfold Wt
  apply div_nonneg zero_le_one
  exact Finset.prod_nonneg fun x hx => by
    have := recip_mem (hP x (Finset.mem_filter.mp hx).1); linarith [this.2]

lemma sigma_split (P : Finset ℕ) (L H : ℕ) (hLH : L ≤ H) :
    ∑ x ∈ P.filter (fun x => 2 ^ L < x), recip x =
      ∑ x ∈ P.filter (fun x => 2 ^ H < x), recip x +
        ∑ x ∈ P.filter (fun x => 2 ^ L < x ∧ x ≤ 2 ^ H), recip x := by
  have hp : 2 ^ L ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hLH
  rw [← Finset.sum_filter_add_sum_filter_not (P.filter fun x => 2 ^ L < x) (fun x => 2 ^ H < x)]
  congr 1
  · congr 1; ext x; simp only [Finset.mem_filter]; constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  · congr 1; ext x; simp only [Finset.mem_filter, not_lt, and_assoc]

/-- `Σ g W (R - 1)` over one class. -/
lemma class_err_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (C : Finset ℕ) (hC : C ⊆ P)
    (d : List Block) (sB WB : ℝ) (φ : ℝ) (hφ : 0 ≤ φ) (hWB : 0 ≤ WB) (hs : ∑ ℓ ∈ C, recip ℓ ≤ sB)
    (hW : ∀ ℓ ∈ C, Wt P recip ℓ ≤ WB) (hR : ∀ ℓ ∈ C, ratProd (restr ℓ d) recip - 1 ≤ φ) :
    ∑ ℓ ∈ C, recip ℓ * Wt P recip ℓ * (ratProd (restr ℓ d) recip - 1) ≤ sB * WB * φ := by
  have hg : ∀ ℓ ∈ C, 0 ≤ recip ℓ := fun ℓ h => (recip_mem (hP ℓ (hC h))).1
  calc ∑ ℓ ∈ C, recip ℓ * Wt P recip ℓ * (ratProd (restr ℓ d) recip - 1)
      ≤ ∑ ℓ ∈ C, recip ℓ * (WB * φ) := Finset.sum_le_sum fun ℓ h => by
        have hw0 := Wt_nonneg P hP ℓ
        calc recip ℓ * Wt P recip ℓ * (ratProd (restr ℓ d) recip - 1)
            = recip ℓ * (Wt P recip ℓ * (ratProd (restr ℓ d) recip - 1)) := by ring
          _ ≤ recip ℓ * (WB * φ) := by
              apply mul_le_mul_of_nonneg_left _ (hg ℓ h)
              by_cases hneg : ratProd (restr ℓ d) recip - 1 ≤ 0
              · have : Wt P recip ℓ * (ratProd (restr ℓ d) recip - 1) ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos hw0 hneg
                have : 0 ≤ WB * φ := mul_nonneg (hw0.trans (hW ℓ h)) hφ
                linarith
              · push Not at hneg
                exact mul_le_mul (hW ℓ h) (hR ℓ h) hneg.le (hw0.trans (hW ℓ h))
    _ = (∑ ℓ ∈ C, recip ℓ) * (WB * φ) := by rw [Finset.sum_mul]
    _ ≤ sB * (WB * φ) := by
        apply mul_le_mul_of_nonneg_right hs
        exact mul_nonneg hWB hφ
    _ = _ := by ring

end Shoup.Sieve
