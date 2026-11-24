import Shoup.Sieve.Rep

/-!
# The Brun–Hooley lower-bound sieve

The prime set is split into disjoint blocks `B_j`, each with a truncation level `k_j`. Write
`A_j = ∏_{ℓ∈B_j}(1 - y ℓ)`, `U_j = G (2k_j+1) B_j` (an upper bound for `A_j`) and
`e_j = E (2k_j+1) B_j`, so `U_j - e_j = G (2k_j+2) B_j` is a lower bound. The sieve function
is defined recursively by `Φ [] = 1`, `Φ (b :: bs) = U_b Φ bs - e_b ∏_{bs} U`, i.e.
`Φ = ∏ U_j - Σ_i e_i ∏_{j≠i} U_j`.

* `phi_le_prodA`: for `0 ≤ y ≤ 1`, `Φ y ≤ ∏_j A_j y` (Brun–Hooley inequality);
* `phi_ge`: for `0 ≤ y ≤ 1/2`, `Φ y ≥ (∏_j A_j y) (1 - Σ_j e_j y / A_j y)` when the sum is `≤ 1`;
* `isRep_phi`: `Φ` is a combination of monomials over the union of the blocks, of mass at most
  `(J + 1) ∏_j (|B_j| + 1)^{2k_j+1}`.
-/

namespace Shoup.Sieve

open Finset

/-- A block: a finite set of primes and a truncation parameter `k` (level `2k+1`). -/
abbrev Block := Finset ℕ × ℕ

noncomputable def Ub (b : Block) (y : ℕ → ℝ) : ℝ := G (2 * b.2 + 1) b.1 y
noncomputable def Eb (b : Block) (y : ℕ → ℝ) : ℝ := E (2 * b.2 + 1) b.1 y
noncomputable def Ab (b : Block) (y : ℕ → ℝ) : ℝ := ∏ ℓ ∈ b.1, (1 - y ℓ)

noncomputable def prodU : List Block → (ℕ → ℝ) → ℝ
  | [], _ => 1
  | b :: bs, y => Ub b y * prodU bs y

noncomputable def prodA : List Block → (ℕ → ℝ) → ℝ
  | [], _ => 1
  | b :: bs, y => Ab b y * prodA bs y

noncomputable def phi : List Block → (ℕ → ℝ) → ℝ
  | [], _ => 1
  | b :: bs, y => Ub b y * phi bs y - Eb b y * prodU bs y

/-- `Σ_j e_j / A_j`. -/
noncomputable def ratioSum : List Block → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | b :: bs, y => Eb b y / Ab b y + ratioSum bs y

/-- Union of the blocks. -/
def supp : List Block → Finset ℕ
  | [] => ∅
  | b :: bs => b.1 ∪ supp bs

/-- The blocks are pairwise disjoint. -/
def Disj : List Block → Prop
  | [] => True
  | b :: bs => Disjoint b.1 (supp bs) ∧ Disj bs

/-- `∏_j (|B_j| + 1)^{2k_j+1}`. -/
noncomputable def massBound : List Block → ℝ
  | [] => 1
  | b :: bs => ((b.1.card + 1 : ℝ) ^ (2 * b.2 + 1)) * massBound bs

lemma subset_supp {b : Block} {bs : List Block} (h : b ∈ bs) : b.1 ⊆ supp bs := by
  induction bs with
  | nil => simp at h
  | cons c cs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

section Pointwise

variable (y : ℕ → ℝ)

lemma block_bounds (b : Block) (hy : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1) :
    0 ≤ Ab b y ∧ Ab b y ≤ Ub b y ∧ Ub b y - Eb b y ≤ Ab b y := by
  refine ⟨Finset.prod_nonneg fun ℓ h => by linarith [(hy ℓ h).2], prod_le_G_odd _ _ hy _, ?_⟩
  have h1 := G_even_le_prod b.1 y hy b.2
  have h2 := G_succ (2 * b.2 + 1) b.1 y
  rw [show 2 * b.2 + 1 + 1 = 2 * b.2 + 2 by ring, pow_succ, pow_mul] at h2
  norm_num at h2
  unfold Ub Eb Ab
  linarith

/-- **Brun–Hooley inequality.** -/
theorem phi_le_prodA (bs : List Block) (hy : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1) :
    phi bs y ≤ prodA bs y ∧ prodA bs y ≤ prodU bs y ∧ 0 ≤ prodA bs y := by
  induction bs with
  | nil => simp [phi, prodA, prodU]
  | cons b bs ih =>
    have hyb : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => hy ℓ (by simp [supp, h])
    have hys : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => hy ℓ (by simp [supp, h])
    obtain ⟨h1, h2, h3⟩ := ih hys
    obtain ⟨a0, aU, aL⟩ := block_bounds y b hyb
    simp only [phi, prodA, prodU]
    refine ⟨?_, mul_le_mul aU h2 h3 (a0.trans aU), mul_nonneg a0 h3⟩
    -- `U Φ - e ΠU = L ΠU - U (ΠU - Φ) ≤ L ΠU - A (ΠU - Φ) ≤ A Φ ≤ A ΠA`
    have hD : 0 ≤ prodU bs y - phi bs y := by linarith
    have hPU : 0 ≤ prodU bs y := h3.trans h2
    nlinarith [mul_le_mul_of_nonneg_right aU hD, mul_le_mul_of_nonneg_right aL hPU,
      mul_le_mul_of_nonneg_left h1 a0]

lemma prodA_eq_zero (bs : List Block) {ℓ : ℕ} (hℓ : ℓ ∈ supp bs) (h1 : y ℓ = 1) :
    prodA bs y = 0 := by
  induction bs with
  | nil => simp [supp] at hℓ
  | cons b bs ih =>
    simp only [prodA]
    rcases Finset.mem_union.mp hℓ with h | h
    · rw [show Ab b y = 0 from Finset.prod_eq_zero h (by rw [h1]; ring), zero_mul]
    · rw [ih h, mul_zero]

end Pointwise

section Main

variable (y : ℕ → ℝ)

lemma Ab_pos (b : Block) (hy : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) : 0 < Ab b y :=
  Finset.prod_pos fun ℓ h => by linarith [(hy ℓ h).2]

lemma phi_ge_aux (bs : List Block) (hy : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) :
    prodU bs y * (1 - ratioSum bs y) ≤ phi bs y ∧ 0 ≤ ratioSum bs y := by
  induction bs with
  | nil => simp [phi, prodU, ratioSum]
  | cons b bs ih =>
    have hyb : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2 := fun ℓ h => hy ℓ (by simp [supp, h])
    have hys : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2 := fun ℓ h => hy ℓ (by simp [supp, h])
    obtain ⟨h1, hR⟩ := ih hys
    have hyb' : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => ⟨(hyb ℓ h).1, by linarith [(hyb ℓ h).2]⟩
    have hys' : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 :=
      fun ℓ h => ⟨(hys ℓ h).1, by linarith [(hys ℓ h).2]⟩
    obtain ⟨_, aU, _⟩ := block_bounds y b hyb'
    obtain ⟨_, hAU, hA0⟩ := phi_le_prodA y bs hys'
    have hApos := Ab_pos y b hyb
    have hUpos : 0 < Ub b y := hApos.trans_le aU
    have hE0 : 0 ≤ Eb b y := E_nonneg _ _ _ fun ℓ h => (hyb ℓ h).1
    have hPU : 0 ≤ prodU bs y := hA0.trans hAU
    have hEU : Eb b y / Ab b y * Ub b y ≥ Eb b y := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hApos]
      exact mul_le_mul_of_nonneg_left aU hE0
    simp only [phi, prodU, ratioSum]
    refine ⟨?_, add_nonneg (div_nonneg hE0 hApos.le) hR⟩
    -- `U Φ - e ΠU ≥ U ΠU (1 - R) - (e/A) U ΠU`
    have := mul_le_mul_of_nonneg_left h1 hUpos.le
    nlinarith [mul_le_mul_of_nonneg_right hEU hPU]

/-- Main-term lower bound for the Brun–Hooley sieve. -/
theorem phi_ge (bs : List Block) (hy : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2)
    (hR : ratioSum bs y ≤ 1) : prodA bs y * (1 - ratioSum bs y) ≤ phi bs y := by
  obtain ⟨h1, _⟩ := phi_ge_aux y bs hy
  have hys' : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 :=
    fun ℓ h => ⟨(hy ℓ h).1, by linarith [(hy ℓ h).2]⟩
  obtain ⟨_, hAU, _⟩ := phi_le_prodA y bs hys'
  exact (mul_le_mul_of_nonneg_right hAU (by linarith)).trans h1

end Main

section Rep

lemma massBound_nonneg (bs : List Block) : 0 ≤ massBound bs := by
  induction bs with
  | nil => simp [massBound]
  | cons b bs ih => simp only [massBound]; positivity

theorem isRep_prodU_phi (bs : List Block) (hd : Disj bs) :
    IsRep (prodU bs) (supp bs) (massBound bs) ∧
    IsRep (phi bs) (supp bs) ((bs.length + 1 : ℝ) * massBound bs) := by
  induction bs with
  | nil =>
    simp only [prodU, phi, supp, massBound, List.length_nil]
    exact ⟨IsRep.one, IsRep.one.mono le_rfl (by norm_num)⟩
  | cons b bs ih =>
    obtain ⟨hdb, hds⟩ := hd
    obtain ⟨hU, hΦ⟩ := ih hds
    have hUb := isRep_G (2 * b.2 + 1) b.1
    have hEb := isRep_E (2 * b.2 + 1) b.1
    have hM0 := massBound_nonneg bs
    refine ⟨?_, ?_⟩
    · exact (hUb.mul hU hdb).congr fun y => rfl
    · have h1 := hUb.mul hΦ hdb
      have h2 := hEb.mul hU hdb
      refine ((h1.sub h2).congr fun y => rfl).mono le_rfl ?_
      simp only [massBound, List.length_cons]
      push_cast
      have : 0 ≤ ((b.1.card + 1 : ℝ) ^ (2 * b.2 + 1)) := by positivity
      nlinarith

end Rep

end Shoup.Sieve
