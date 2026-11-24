import Shoup.Poly7

/-!
# A Buchstab-type lower-bound sieve built from upper Brun–Hooley sieves

For a finite set `P` of primes and, for each `ℓ ∈ P`, a Brun–Hooley block design `D ℓ`
whose blocks partition `{ℓ' ∈ P : ℓ' < ℓ}`, put

`Φ(y) = 1 - Σ_{ℓ ∈ P} y_ℓ · ∏_{b ∈ D ℓ} U_b(y)`.

Each `∏_b U_b` is an upper-bound sieve for the primes below `ℓ`, so this is Buchstab's identity
`S(A, z) = |A| - Σ_ℓ S(A_ℓ, ℓ)` with every `S(A_ℓ, ℓ)` replaced by an upper bound.

* `buch_nonpos`: if `y ∈ {0,1}^P` and some `y_ℓ = 1`, then `Φ(y) ≤ 0` (look at the least such
  `ℓ`: its term is `≥ 1`, and all terms are `≥ 0`);
* `isRep_buch`: `Φ` has mass at most `1 + Σ_ℓ ∏_{b ∈ D ℓ} (|B_b| + 1)^{2k_b}`;
* `buch_ge`: with `V_{<ℓ} = ∏_{ℓ' < ℓ}(1 - g_ℓ')` and `∏_b U_b(g) ≤ V_{<ℓ}(1 + e_ℓ)`,
  `Φ(g) ≥ ∏_P (1 - g) - Σ_ℓ g_ℓ V_{<ℓ} e_ℓ` (from `Σ_ℓ g_ℓ V_{<ℓ} = 1 - ∏_P (1 - g)`);
* `le_of_no_primitive_root_lt_rep`: the sieve inequality `x ≤ 1089 (M log p / θ)²` for any
  function with these two properties.
-/

namespace Shoup.Sieve

open Finset ArithmeticFunction Erdos985 Erdos985.Indicator

/-! ### Restricting a design to the primes below `ℓ` -/

/-- Keep only the primes below `ℓ` in every block. -/
def restr (ℓ : ℕ) (bs : List Block) : List Block := bs.map fun b => (b.1.filter (· < ℓ), b.2)

lemma supp_restr (ℓ : ℕ) (bs : List Block) : supp (restr ℓ bs) = (supp bs).filter (· < ℓ) := by
  induction bs with
  | nil => simp [restr, supp]
  | cons b bs ih =>
    show (b.1.filter (· < ℓ)) ∪ supp (restr ℓ bs) = (b.1 ∪ supp bs).filter (· < ℓ)
    rw [ih, Finset.filter_union]

lemma disj_restr (ℓ : ℕ) {bs : List Block} (hd : Disj bs) : Disj (restr ℓ bs) := by
  induction bs with
  | nil => trivial
  | cons b bs ih =>
    obtain ⟨h1, h2⟩ := hd
    refine ⟨?_, ih h2⟩
    show Disjoint (b.1.filter (· < ℓ)) (supp (restr ℓ bs))
    rw [supp_restr]
    exact Finset.disjoint_filter_filter h1

/-! ### Representations -/

lemma isRep_monomial (ℓ : ℕ) : IsRep (fun y => y ℓ) {ℓ} 1 :=
  ⟨[({ℓ}, 1)], by simp, by simp [mass], fun y => by simp [ev]⟩

lemma isRep_zero (S : Finset ℕ) : IsRep (fun _ => 0) S 0 :=
  ⟨[], by simp, by simp [mass], fun y => by simp [ev]⟩

lemma IsRep.add {F G : (ℕ → ℝ) → ℝ} {S : Finset ℕ} {M N : ℝ} (hF : IsRep F S M)
    (hG : IsRep G S N) : IsRep (fun y => F y + G y) S (M + N) := by
  obtain ⟨L, h1, h2, h3⟩ := hF
  obtain ⟨L', h1', h2', h3'⟩ := hG
  refine ⟨L ++ L', fun q hq => ?_, ?_, fun y => ?_⟩
  · rcases List.mem_append.mp hq with h | h
    · exact h1 q h
    · exact h1' q h
  · rw [mass_append]; linarith
  · dsimp only; rw [ev_append, h3, h3']

lemma IsRep.sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → (ℕ → ℝ) → ℝ)
    (S : Finset ℕ) (M : ι → ℝ) (h : ∀ i ∈ s, IsRep (F i) S (M i)) :
    IsRep (fun y => ∑ i ∈ s, F i y) S (∑ i ∈ s, M i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isRep_zero S
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ((h1.add h2).congr fun y => ?_).mono le_rfl (le_of_eq ?_)
    · rw [Finset.sum_insert ha]
    · rw [Finset.sum_insert ha]

/-! ### The Buchstab sieve function -/

/-- `Φ(y) = 1 - Σ_{ℓ ∈ P} y_ℓ ∏_{b ∈ D ℓ} U_b(y)`. -/
noncomputable def buch (P : Finset ℕ) (D : ℕ → List Block) (y : ℕ → ℝ) : ℝ :=
  1 - ∑ ℓ ∈ P, y ℓ * prodU (D ℓ) y

/-- The designs are admissible: disjoint blocks covering exactly the primes below `ℓ`. -/
def Admissible (P : Finset ℕ) (D : ℕ → List Block) : Prop :=
  ∀ ℓ ∈ P, Disj (D ℓ) ∧ supp (D ℓ) = P.filter (· < ℓ)

section Buch

variable {P : Finset ℕ} {D : ℕ → List Block}

theorem buch_nonpos (hD : Admissible P D) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ P, y ℓ = 0 ∨ y ℓ = 1)
    (h1 : ∃ ℓ ∈ P, y ℓ = 1) : buch P D y ≤ 0 := by
  classical
  set Q := P.filter fun ℓ => y ℓ = 1 with hQdef
  have hQ : Q.Nonempty := by
    obtain ⟨ℓ, hℓ, h⟩ := h1
    exact ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, h⟩⟩
  set ℓ0 := Q.min' hQ
  have hℓ0 : ℓ0 ∈ P ∧ y ℓ0 = 1 := Finset.mem_filter.mp (Finset.min'_mem Q hQ)
  have hbelow : ∀ ℓ ∈ P, ℓ < ℓ0 → y ℓ = 0 := by
    intro ℓ hℓ hlt
    rcases hy ℓ hℓ with h | h
    · exact h
    · exfalso
      have := Q.min'_le ℓ (Finset.mem_filter.mpr ⟨hℓ, h⟩)
      omega
  have hy01 : ∀ ℓ ∈ P, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := by
    intro ℓ h
    rcases hy ℓ h with h | h <;> simp [h]
  have hs : ∀ ℓ ∈ P, ∀ ℓ' ∈ supp (D ℓ), 0 ≤ y ℓ' ∧ y ℓ' ≤ 1 := by
    intro ℓ hℓ ℓ' h
    rw [(hD ℓ hℓ).2] at h
    exact hy01 ℓ' (Finset.mem_filter.mp h).1
  have hterm : ∀ ℓ ∈ P, 0 ≤ y ℓ * prodU (D ℓ) y := by
    intro ℓ hℓ
    obtain ⟨_, h2, h3⟩ := phi_le_prodA y (D ℓ) (hs ℓ hℓ)
    exact mul_nonneg (hy01 ℓ hℓ).1 (h3.trans h2)
  have hmain : 1 ≤ y ℓ0 * prodU (D ℓ0) y := by
    rw [hℓ0.2, one_mul]
    obtain ⟨_, h2, _⟩ := phi_le_prodA y (D ℓ0) (hs ℓ0 hℓ0.1)
    refine le_trans (le_of_eq ?_) h2
    rw [prodA_eq_prod (hD ℓ0 hℓ0.1).1, (hD ℓ0 hℓ0.1).2]
    symm
    refine Finset.prod_eq_one fun ℓ h => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    rw [hbelow ℓ h1 h2]; ring
  have := Finset.single_le_sum hterm hℓ0.1
  unfold buch
  linarith

theorem isRep_buch (hD : Admissible P D) :
    IsRep (buch P D) P (1 + ∑ ℓ ∈ P, massU (D ℓ)) := by
  classical
  have hterm : ∀ ℓ ∈ P, IsRep (fun y => y ℓ * prodU (D ℓ) y) P (massU (D ℓ)) := by
    intro ℓ hℓ
    have hU := (isRep_phi2 (D ℓ) (hD ℓ hℓ).1).1
    have hdisj : Disjoint ({ℓ} : Finset ℕ) (supp (D ℓ)) := by
      rw [(hD ℓ hℓ).2, Finset.disjoint_singleton_left]
      simp
    refine ((isRep_monomial ℓ).mul hU hdisj).mono ?_ (by rw [one_mul])
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · rw [Finset.mem_singleton.mp h]; exact hℓ
    · rw [(hD ℓ hℓ).2] at h; exact (Finset.mem_filter.mp h).1
  have hsum := IsRep.sum P (fun ℓ y => y ℓ * prodU (D ℓ) y) P (fun ℓ => massU (D ℓ)) hterm
  have h1 : IsRep (fun _ => (1 : ℝ)) P 1 := IsRep.one.mono (Finset.empty_subset _) le_rfl
  exact (h1.sub hsum).congr fun y => rfl

/-- `Σ_{ℓ∈P} g_ℓ ∏_{ℓ' ∈ P, ℓ' < ℓ} (1 - g_ℓ') = 1 - ∏_{ℓ ∈ P} (1 - g_ℓ)`. -/
lemma telescope (P : Finset ℕ) (g : ℕ → ℝ) :
    ∑ ℓ ∈ P, g ℓ * ∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ') = 1 - ∏ ℓ ∈ P, (1 - g ℓ) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert x s hlt ih =>
    have hxs : x ∉ s := fun h => lt_irrefl x (hlt x h)
    rw [Finset.sum_insert hxs, Finset.prod_insert hxs]
    have hfx : (insert x s).filter (· < x) = s := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | h, h'⟩
        · exact absurd h' (lt_irrefl _)
        · exact h
      · intro h; exact ⟨Or.inr h, hlt ℓ h⟩
    have hfl : ∀ ℓ ∈ s, (insert x s).filter (· < ℓ) = s.filter (· < ℓ) := by
      intro ℓ hℓ
      rw [Finset.filter_insert, if_neg (not_lt.mpr (hlt ℓ hℓ).le)]
    rw [hfx, Finset.sum_congr rfl fun ℓ hℓ => by rw [hfl ℓ hℓ], ih]
    ring

/-- `∏_b U_b / A_b`. -/
noncomputable def ratProd : List Block → (ℕ → ℝ) → ℝ
  | [], _ => 1
  | b :: bs, y => (Ub b y / Ab b y) * ratProd bs y

lemma prodU_eq_ratProd (y : ℕ → ℝ) (bs : List Block)
    (hy : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) :
    prodU bs y = prodA bs y * ratProd bs y := by
  induction bs with
  | nil => simp [prodU, prodA, ratProd]
  | cons b bs ih =>
    have hyb : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2 := fun ℓ h => hy ℓ (by simp [supp, h])
    have hys : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2 := fun ℓ h => hy ℓ (by simp [supp, h])
    have hA := Ab_pos y b hyb
    simp only [prodU, prodA, ratProd, ih hys]
    field_simp

lemma ratProd_append (L₁ L₂ : List Block) (y : ℕ → ℝ) :
    ratProd (L₁ ++ L₂) y = ratProd L₁ y * ratProd L₂ y := by
  induction L₁ with
  | nil => simp [ratProd]
  | cons b L ih => simp only [List.cons_append, ratProd, ih]; ring

lemma ratProd_nonneg (y : ℕ → ℝ) (bs : List Block)
    (hy : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) : 0 ≤ ratProd bs y := by
  induction bs with
  | nil => simp [ratProd]
  | cons b bs ih =>
    have hyb : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2 := fun ℓ h => hy ℓ (by simp [supp, h])
    have hys : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2 := fun ℓ h => hy ℓ (by simp [supp, h])
    have hyb' : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 :=
      fun ℓ h => ⟨(hyb ℓ h).1, by linarith [(hyb ℓ h).2]⟩
    obtain ⟨a0, aU, _⟩ := block_bounds y b hyb'
    have hA := Ab_pos y b hyb
    simp only [ratProd]
    exact mul_nonneg (div_nonneg (a0.trans aU) hA.le) (ih hys)

theorem buch_ge (hD : Admissible P D) (g : ℕ → ℝ) (hg : ∀ ℓ ∈ P, 0 ≤ g ℓ) (e : ℕ → ℝ)
    (he : ∀ ℓ ∈ P, prodU (D ℓ) g ≤ (∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) * (1 + e ℓ)) :
    (∏ ℓ ∈ P, (1 - g ℓ)) - ∑ ℓ ∈ P, g ℓ * (∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) * e ℓ
      ≤ buch P D g := by
  have h1 : ∑ ℓ ∈ P, g ℓ * prodU (D ℓ) g ≤
      ∑ ℓ ∈ P, g ℓ * ((∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) * (1 + e ℓ)) :=
    Finset.sum_le_sum fun ℓ hℓ => mul_le_mul_of_nonneg_left (he ℓ hℓ) (hg ℓ hℓ)
  have h2 : ∑ ℓ ∈ P, g ℓ * ((∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) * (1 + e ℓ)) =
      (1 - ∏ ℓ ∈ P, (1 - g ℓ)) +
        ∑ ℓ ∈ P, g ℓ * (∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) * e ℓ := by
    rw [← telescope P g, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  unfold buch
  linarith

/-- `W_ℓ = 1 / ∏_{ℓ' ∈ P, ℓ' ≥ ℓ} (1 - g_ℓ')`, so that `V_{<ℓ} = V_P W_ℓ`. -/
noncomputable def Wt (P : Finset ℕ) (g : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  1 / ∏ ℓ' ∈ P.filter (fun ℓ' => ℓ ≤ ℓ'), (1 - g ℓ')

theorem buch_ge_W (hD : Admissible P D) (g : ℕ → ℝ) (hg : ∀ ℓ ∈ P, 0 ≤ g ℓ ∧ g ℓ ≤ 1 / 2) :
    (∏ ℓ ∈ P, (1 - g ℓ)) * (1 - ∑ ℓ ∈ P, g ℓ * Wt P g ℓ * (ratProd (D ℓ) g - 1))
      ≤ buch P D g := by
  have he : ∀ ℓ ∈ P, prodU (D ℓ) g ≤
      (∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) * (1 + (ratProd (D ℓ) g - 1)) := by
    intro ℓ hℓ
    have hs : ∀ ℓ' ∈ supp (D ℓ), 0 ≤ g ℓ' ∧ g ℓ' ≤ 1 / 2 := by
      intro ℓ' h; rw [(hD ℓ hℓ).2] at h; exact hg ℓ' (Finset.mem_filter.mp h).1
    rw [prodU_eq_ratProd g (D ℓ) hs, prodA_eq_prod (hD ℓ hℓ).1, (hD ℓ hℓ).2]
    ring_nf; exact le_rfl
  have h := buch_ge hD g (fun ℓ h => (hg ℓ h).1) _ he
  have hsplit : ∀ ℓ ∈ P, (∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) =
      (∏ ℓ ∈ P, (1 - g ℓ)) * Wt P g ℓ := by
    intro ℓ _
    have hpos : 0 < ∏ ℓ' ∈ P.filter (fun ℓ' => ℓ ≤ ℓ'), (1 - g ℓ') :=
      Finset.prod_pos fun ℓ' h' => by linarith [(hg ℓ' (Finset.mem_filter.mp h').1).2]
    rw [← Finset.prod_filter_mul_prod_filter_not P (· < ℓ)]
    have : P.filter (fun ℓ' => ¬ ℓ' < ℓ) = P.filter (fun ℓ' => ℓ ≤ ℓ') := by
      ext x; simp [not_lt]
    rw [this, Wt]
    field_simp
  have hsum : ∑ ℓ ∈ P, g ℓ * (∏ ℓ' ∈ P.filter (· < ℓ), (1 - g ℓ')) * (ratProd (D ℓ) g - 1) =
      (∏ ℓ ∈ P, (1 - g ℓ)) * ∑ ℓ ∈ P, g ℓ * Wt P g ℓ * (ratProd (D ℓ) g - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ hℓ => by rw [hsplit ℓ hℓ]; ring
  rw [hsum] at h
  linarith

end Buch

/-! ### The sieve inequality for a general sieve function -/

lemma ind_zero_or_one {p : ℕ} [Fact p.Prime] (ψ : DirichletCharacter ℂ p) (n ℓ : ℕ) :
    ind ψ n ℓ = 0 ∨ ind ψ n ℓ = 1 := by
  unfold ind; split_ifs <;> simp

theorem le_of_no_primitive_root_lt_rep (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1)
    (F : (ℕ → ℝ) → ℝ) (M θ : ℝ) (hrep : IsRep F (p - 1).primeFactors M)
    (hpt : ∀ y : ℕ → ℝ, (∀ ℓ ∈ (p - 1).primeFactors, y ℓ = 0 ∨ y ℓ = 1) →
      (∃ ℓ ∈ (p - 1).primeFactors, y ℓ = 1) → F y ≤ 0)
    (hM1 : 1 ≤ M) (hθpos : 0 < θ) (hθ1 : θ ≤ 1) (hθ : θ ≤ F recip) :
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
  have htr := transfer ψ hψ x hxp B hB0 hB hrep
  set S := ∑ n ∈ range x, wt x n with hSdef
  have hpt' : ∑ n ∈ range x, wt x n * F (ind ψ n) ≤ 0 := by
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
    have hF := hpt (ind ψ n) (fun ℓ _ => ind_zero_or_one ψ n ℓ) ⟨ℓ, hℓ, hind⟩
    exact mul_nonpos_of_nonneg_of_nonpos hwt hF
  have hSΦ : S * F recip ≤ M * B := by
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
        _ ≤ S * F recip := mul_le_mul_of_nonneg_left hθ hSpos.le
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
