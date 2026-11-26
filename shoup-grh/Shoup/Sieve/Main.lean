import Shoup.Sieve.BrunHooley
import Shoup.Sieve.Transfer
import Shoup.Ankeny

/-!
# The sieve inequality for primitive roots under GRH

For any Brun–Hooley block decomposition `bs` of the prime factors of `p - 1` with
`Σ_j e_j(1/ℓ)/A_j(1/ℓ) ≤ 1/2`: if no `0 < g < x ≤ p` is a primitive root, then
`x ≤ 1089 (2 (J+1) ∏_j (|B_j|+1)^{2k_j+1} log p / ∏_{ℓ | p-1} (1 - 1/ℓ))²`.

Proof: with `wt n = Λ(n)(1 - n/x) ≥ 0` and `Φ` the sieve function, every `n < x` with
`Λ(n) ≠ 0` is an `ℓ`-th power residue for some `ℓ ∣ p - 1`, so `Φ(ind n) ≤ 0`
(`phi_le_prodA`). The transfer lemma and Bach's bounds give
`S(x) Φ(1/ℓ) ≤ M · 13 √x log p` with `S(x) ≥ x/2 - √x/20 - 3`, and `Φ(1/ℓ) ≥ ∏(1 - 1/ℓ)/2`.
-/

namespace Shoup.Sieve

open ArithmeticFunction Finset Erdos985 Erdos985.Indicator

lemma prodA_le_one (bs : List Block) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1) :
    prodA bs y ≤ 1 := by
  induction bs with
  | nil => simp [prodA]
  | cons b bs ih =>
    have hyb : ∀ ℓ ∈ b.1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => hy ℓ (by simp [supp, h])
    have hys : ∀ ℓ ∈ supp bs, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => hy ℓ (by simp [supp, h])
    have h1 : Ab b y ≤ 1 := Finset.prod_le_one₀ (fun ℓ h => by linarith [(hyb ℓ h).2])
      fun ℓ h => by linarith [(hyb ℓ h).1]
    have h0 : 0 ≤ Ab b y := Finset.prod_nonneg fun ℓ h => by linarith [(hyb ℓ h).2]
    have h2 := (phi_le_prodA y bs hys).2.2
    simp only [prodA]
    nlinarith [ih hys]

lemma one_le_massBound (bs : List Block) : 1 ≤ massBound bs := by
  induction bs with
  | nil => simp [massBound]
  | cons b bs ih =>
    simp only [massBound]
    have : (1 : ℝ) ≤ ((b.1.card + 1 : ℝ) ^ (2 * b.2 + 1)) :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) b.1.card])
    nlinarith

lemma recip_mem {ℓ : ℕ} (hℓ : ℓ.Prime) : 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := by
  have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
  unfold recip
  exact ⟨by positivity, by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith⟩

lemma ind_mem {p : ℕ} [Fact p.Prime] (ψ : DirichletCharacter ℂ p) (n ℓ : ℕ) :
    0 ≤ ind ψ n ℓ ∧ ind ψ n ℓ ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- **The sieve inequality.** -/
theorem le_of_no_primitive_root_lt (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1)
    (bs : List Block) (hd : Disj bs) (hsupp : supp bs = (p - 1).primeFactors)
    (hR : ratioSum bs recip ≤ 1 / 2) :
    (x : ℝ) ≤ 1089 * (2 * ((bs.length + 1 : ℝ) * massBound bs) * Real.log p
      / prodA bs recip) ^ 2 := by
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
  -- the non-principal bound
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
  -- the sieve function and its representation
  set M : ℝ := (bs.length + 1 : ℝ) * massBound bs with hMdef
  have hrep := (isRep_prodU_phi bs hd).2
  rw [hsupp] at hrep
  have htr := transfer ψ hψ x hxp B hB0 hB hrep
  set S := ∑ n ∈ range x, wt x n with hSdef
  -- pointwise: `Σ wt Φ(ind) ≤ 0`
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
      unfold ind; rw [if_pos]; rw [← map_pow, hpow, map_one]
    have hmem : ∀ ℓ ∈ supp bs, 0 ≤ ind ψ n ℓ ∧ ind ψ n ℓ ≤ 1 := fun ℓ _ => ind_mem ψ n ℓ
    have hΦ := (phi_le_prodA (ind ψ n) bs hmem).1
    rw [prodA_eq_zero (ind ψ n) bs (hsupp ▸ hℓ) hind] at hΦ
    exact mul_nonpos_of_nonneg_of_nonpos hwt hΦ
  -- main term
  have hrec : ∀ ℓ ∈ supp bs, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := fun ℓ h =>
    recip_mem (Nat.mem_primeFactors.mp (hsupp ▸ h)).1
  have hrec1 : ∀ ℓ ∈ supp bs, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 :=
    fun ℓ h => ⟨(hrec ℓ h).1, by linarith [(hrec ℓ h).2]⟩
  have hΦa := phi_ge recip bs hrec (by linarith)
  set θ := prodA bs recip with hθ
  have hθpos : 0 < θ := by
    have hA := (phi_le_prodA recip bs hrec1).2.2
    -- `θ > 0`: every factor is positive
    have : ∀ cs : List Block, (∀ ℓ ∈ supp cs, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2) →
        0 < prodA cs recip := by
      intro cs hcs
      induction cs with
      | nil => simp [prodA]
      | cons c cs ih =>
        simp only [prodA]
        exact mul_pos (Ab_pos recip c fun ℓ h => hcs ℓ (by simp [supp, h]))
          (ih fun ℓ h => hcs ℓ (by simp [supp, h]))
    exact this bs hrec
  have hθ1 : θ ≤ 1 := prodA_le_one bs recip hrec1
  have hΦθ : θ / 2 ≤ phi bs recip := by
    have hR0 : 0 ≤ ratioSum bs recip := (phi_ge_aux recip bs hrec).2
    nlinarith
  have hM1 : 1 ≤ M := by
    have := one_le_massBound bs
    have : (1 : ℝ) ≤ bs.length + 1 := by linarith [Nat.cast_nonneg (α := ℝ) bs.length]
    nlinarith
  -- `S Φ ≤ M B`
  have hSΦ : S * phi bs recip ≤ M * B := by
    have := (abs_le.mp htr).1
    linarith
  have hprin := (abs_le.mp (Analytic.bach_principal_of_GRH hGRH x hx1)).1
  have hSlow : (x : ℝ) / 2 - s / 20 - 3 ≤ S := by
    have : S = ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) := rfl
    rw [this]; linarith
  set K := 2 * M * L / θ with hK
  have hK1 : 1 ≤ K := by
    rw [hK, le_div_iff₀ hθpos]; nlinarith
  have hgoal : (x : ℝ) ≤ 1089 * K ^ 2 := by
    by_cases hs0 : (x : ℝ) / 2 - s / 20 - 3 ≤ 0
    · nlinarith
    rw [not_le] at hs0
    have hSpos : 0 < S := by linarith
    -- `(x/2 - s/20 - 3) θ/2 ≤ S Φ ≤ 13 M s L`
    have h1 : ((x : ℝ) / 2 - s / 20 - 3) * (θ / 2) ≤ M * B := by
      calc ((x : ℝ) / 2 - s / 20 - 3) * (θ / 2) ≤ S * (θ / 2) :=
            mul_le_mul_of_nonneg_right hSlow (by linarith)
        _ ≤ S * phi bs recip := mul_le_mul_of_nonneg_left hΦθ hSpos.le
        _ ≤ M * B := hSΦ
    have hKθ : K * θ = 2 * M * L := by rw [hK]; field_simp
    -- divide by `θ/2`: `s²/2 - s/20 - 3 ≤ 13 K s`
    have h2 : (x : ℝ) / 2 - s / 20 - 3 ≤ 13 * K * s := by
      have : ((x : ℝ) / 2 - s / 20 - 3) * θ ≤ (13 * K * s) * θ := by
        have : M * B = 13 * s * (M * L) := by rw [hBdef]; ring
        nlinarith
      exact le_of_mul_le_mul_right this hθpos
    have h3 : s ≤ 33 * K := by nlinarith
    nlinarith
  calc (x : ℝ) ≤ 1089 * K ^ 2 := hgoal
    _ = _ := by rw [hK, hMdef]

end Shoup.Sieve
