import Shoup.Sieve.TableErr2
import Shoup.Sieve.Mass6
import Shoup.Sieve.Table6

/-!
# `PolyOmegaStatement 6` (Wang's exponent): `g(p) ≤ C ω(p-1)^6 (log p)²` under GRH

Write `m = ω(p - 1)`, `P` for the prime factors of `p - 1`, and choose `n` least with
`10^5 m ≤ 2^{8000 n}`. The sieve function is Buchstab's lower bound

`Φ(y) = 1 - Σ_{ℓ ∈ P} y_ℓ ∏_{b ∈ D_ℓ} U_b(y)`,

where `D_ℓ` is an upper Brun–Hooley design for the primes below `ℓ`, taken from the checked
table `tab6` (137 classes of `ℓ`, 1446 blocks) according to the size of `ℓ`, with the tail
design for `ℓ ≤ 2^n` (`Shoup.Sieve.Buchstab`, `Design`, `Table`, `TableErr`).

* the table is checked by `decide +kernel` (`tab6_ok`, `tab6_err`): every block's log bound,
  every class's mass exponent `hi + 30 + Σ 2k a ≤ 23984`, and the total error
  `Σ_C σ_C W_C (F_C - 1) ≤ 0.94`;
* so `Φ(1/ℓ) ≥ ∏_{ℓ∈P} (1 - 1/ℓ) (1 - 0.94 - 10^{-5}) ≥ c 2^{-n}` and the mass is
  `≤ 138 K 2^{23983 n}`;
* the sieve inequality gives `x ≤ C 2^{47968 n} (log p)² ≤ C' m^6 (log p)²`, since
  `2^{8000 n} ≤ 2^{8000} · 10^5 m`.

Small `m` are covered by `polyOmega_of_GRH : PolyOmegaStatement 136`.
-/

namespace Shoup.Sieve

open Finset Fixed ArithmeticFunction Erdos985
open scoped ArithmeticFunction.omega

/-! ### The table checks -/

def up0 : ℕ := cdiv Dn (10 ^ 5)

set_option maxRecDepth 100000 in
theorem tab6_ok : tableOK 23984 true up0 8000 tab6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem tab6_err : 100 * errSum true up0 tab6 ≤ 94 * Dn := by decide +kernel

theorem tab6_len : tab6.length = 137 := by rfl


/-! ### The product `∏ (1 - 1/ℓ)` -/

lemma prod_P_ge6 (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 23 ≤ n)
    (hcard : 100000 * P.card ≤ 2 ^ (8000 * n)) :
    1 ≤ (∏ ℓ ∈ P, (1 - recip ℓ)) * (9 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun ℓ => ℓ ≤ 2 ^ Ubot)]
  set Ps := P.filter fun ℓ => ℓ ≤ 2 ^ Ubot
  set Pb := P.filter fun ℓ => ¬ ℓ ≤ 2 ^ Ubot
  -- small primes
  have hs : 1 / ((2 : ℝ) ^ Ubot + 1) ≤ ∏ ℓ ∈ Ps, (1 - recip ℓ) := by
    have h := prod_one_sub_inv_ge Ps fun ℓ h => (hP ℓ (Finset.mem_filter.mp h).1).two_le
    have hc : Ps.card ≤ 2 ^ Ubot := card_filter_le_pow P hP Ubot _ fun ℓ h => h
    have hcR : (Ps.card : ℝ) ≤ 2 ^ Ubot := by exact_mod_cast hc
    have h' : 1 / ((Ps.card : ℝ) + 1) ≤ ∏ ℓ ∈ Ps, (1 - recip ℓ) := by simpa [recip] using h
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans h'
  -- large primes
  set σ := ∑ ℓ ∈ Pb, recip ℓ with hσ
  have hU3 : (1 : ℝ) / 3 ≤ 1 / 3 := le_rfl
  have hyb : ∀ ℓ ∈ Pb, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 3 := by
    intro ℓ h
    have h2 := (Finset.mem_filter.mp h).2
    push Not at h2
    have : (2 : ℝ) ^ Ubot < ℓ := by exact_mod_cast h2
    have h4 : (4 : ℝ) ≤ 2 ^ Ubot := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ Ubot := pow_le_pow_right₀ (by norm_num) (by rw [Ubot_def]; norm_num)
    refine ⟨by unfold recip; positivity, ?_⟩
    unfold recip
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hb := exp_le_prod' Pb recip (η := 1 / 3) le_rfl hyb
  rw [← hσ] at hb
  -- `σ ≤ 8000 n / 2^20 + 1`
  have hσle : σ ≤ 8000 * n / 2 ^ 20 + 1 := by
    rw [hσ, ← Finset.sum_filter_add_sum_filter_not Pb (fun ℓ => ℓ ≤ 2 ^ (8000 * n))]
    have hU : 1 ≤ Ubot := by rw [Ubot_def]; norm_num
    have hUn : Ubot ≤ 8000 * n := by rw [Ubot_def]; omega
    have h1 := sum_inv_shell_le'' (Pb.filter fun ℓ => ℓ ≤ 2 ^ (8000 * n))
      (fun ℓ h => hP ℓ (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1) Ubot (8000 * n) hU hUn
      (fun ℓ h => by
        have h' := Finset.mem_filter.mp h
        have h'' := (Finset.mem_filter.mp h'.1).2
        push Not at h''
        exact ⟨h'', h'.2⟩)
    have h2 : ∑ ℓ ∈ Pb.filter (fun ℓ => ¬ ℓ ≤ 2 ^ (8000 * n)), recip ℓ ≤ 1 / 1000 := by
      set S := Pb.filter (fun ℓ => ¬ ℓ ≤ 2 ^ (8000 * n))
      have hpow : (0 : ℝ) < 2 ^ (8000 * n) := by positivity
      calc ∑ ℓ ∈ S, recip ℓ ≤ ∑ _ℓ ∈ S, (1 : ℝ) / 2 ^ (8000 * n) := by
            refine Finset.sum_le_sum fun ℓ h => ?_
            have h' := (Finset.mem_filter.mp h).2
            push Not at h'
            have : (2 : ℝ) ^ (8000 * n) < ℓ := by exact_mod_cast h'
            exact one_div_le_one_div_of_le hpow this.le
        _ = S.card / 2 ^ (8000 * n) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ P.card / 2 ^ (8000 * n) := by
            gcongr
            exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
        _ ≤ 1 / 1000 := by
            rw [div_le_div_iff₀ hpow (by norm_num)]
            have : ((100000 * P.card : ℕ) : ℝ) ≤ ((2 ^ (8000 * n) : ℕ) : ℝ) := by exact_mod_cast hcard
            push_cast at this
            linarith
    simp only [recip] at h2 ⊢
    have hc := c₁_le
    rw [Ubot_def] at h1
    push_cast at h1
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have : ((8000 * n : ℝ) - 2 ^ 20) / 2 ^ 20 + c₁ / 2 ^ 20 ≤ 8000 * n / 2 ^ 20 + 1 / 2 := by
      rw [← add_div, div_le_iff₀ (by positivity)]
      have : (8000 * n / 2 ^ 20 + 1 / 2 : ℝ) * 2 ^ 20 = 8000 * n + 2 ^ 19 := by ring
      rw [this]; linarith
    linarith
  -- `exp((4/3) σ) ≤ 9 · 2^n`
  have hexp : Real.exp ((1 + 1 / 3) * σ) ≤ 9 * 2 ^ n := by
    have h1 : (1 + 1 / 3) * σ ≤ n * Real.log 2 + 4 / 3 := by
      have hl2 := Real.log_two_gt_d9
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    calc Real.exp ((1 + 1 / 3) * σ) ≤ Real.exp (n * Real.log 2 + 4 / 3) := Real.exp_le_exp.mpr h1
      _ = 2 ^ n * Real.exp (4 / 3) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ 2 ^ n * 9 := mul_le_mul_of_nonneg_left exp_four_thirds_le (by positivity)
      _ = 9 * 2 ^ n := by ring
  have hinv : Real.exp ((1 + 1 / 3) * σ) * Real.exp (-((1 + 1 / 3) * σ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos1 : (0 : ℝ) < 2 ^ Ubot + 1 := by positivity
  have hs' : 1 ≤ (∏ ℓ ∈ Ps, (1 - recip ℓ)) * ((2 : ℝ) ^ Ubot + 1) := by
    rw [div_le_iff₀ hpos1] at hs; linarith
  have hb' : 1 ≤ (∏ ℓ ∈ Pb, (1 - recip ℓ)) * (9 * 2 ^ n) := by
    have := mul_le_mul_of_nonneg_left hb (Real.exp_pos ((1 + 1 / 3) * σ)).le
    have h0 : 0 ≤ ∏ ℓ ∈ Pb, (1 - recip ℓ) := (Real.exp_pos _).le.trans hb
    nlinarith
  have hPs0 : 0 ≤ ∏ ℓ ∈ Ps, (1 - recip ℓ) := by
    have : (0 : ℝ) < 1 / ((2 : ℝ) ^ Ubot + 1) := by positivity
    linarith
  calc (1 : ℝ) ≤ ((∏ ℓ ∈ Ps, (1 - recip ℓ)) * ((2 : ℝ) ^ Ubot + 1)) *
        ((∏ ℓ ∈ Pb, (1 - recip ℓ)) * (9 * 2 ^ n)) := by nlinarith
    _ = _ := by ring




/-! ### Admissibility -/

lemma tableOK_designs (P : Finset ℕ) (n S : ℕ) : ∀ (tab : List Cls) (first : Bool) (up t : ℕ),
    tableOK S first up t tab = true →
      ∀ x ∈ custList P n tab, Disj x.2 ∧ supp x.2 = P := by
  intro tab
  induction tab with
  | nil => intro _ _ _ _ x hx; simp [custList] at hx
  | cons C rest ih =>
    intro first up t hok x hx
    simp only [tableOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨_, hrow⟩, hch⟩, _⟩, _⟩, _⟩, _⟩, hrest⟩ := hok
    simp only [custList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow
      exact desC_spec P n C.hi C.des hch (by omega)
    · exact ih false _ _ hrest x hx

/-! ### The bound for large `ω(p - 1)` -/

irreducible_def E36 : ℕ := 8000 * 2 ^ 36

/-- The threshold `2^{8000 · 2^{36}}` on `ω(p - 1)`. -/
irreducible_def M6 : ℕ := 2 ^ E36

lemma one_le_M6 : 1 ≤ M6 := by rw [M6_def]; exact Nat.one_le_two_pow

/-- `2^{8000}`, kept opaque. -/
irreducible_def T8000 : ℕ := 2 ^ 8000

lemma T8000_pos : 0 < T8000 := by rw [T8000_def]; positivity

/-- `K₆ = 139 Kmass · 25 · 9 (2^U + 1)`. -/
noncomputable def K₆ : ℝ := 139 * Kmass * (25 * 9 * ((2 : ℝ) ^ Ubot + 1))

/-- The constant for large `ω`. -/
noncomputable def C6 : ℝ := 1089 * K₆ ^ 2 * ((T8000 : ℝ) * 100000) ^ 6

lemma one_le_Kmass : 1 ≤ Kmass := by
  unfold Kmass Cbot
  have h1 : (1 : ℝ) ≤ ((2 : ℝ) ^ (2 * Ubot) + 1) ^ (2 * kbot) :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ 2 ^ (2 * Ubot) := by positivity
                    linarith)
  have h2 : (1 : ℝ) ≤ 2 ^ 600 := one_le_pow₀ (by norm_num)
  exact one_le_mul_of_one_le_of_one_le h1 h2

lemma K₆_pos : 0 < K₆ := by
  unfold K₆; have := one_le_Kmass; positivity

theorem le_of_no_primitive_root_lt_six (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1)
    (hm : M6 ≤ (p - 1).primeFactors.card) :
    (x : ℝ) ≤ C6 * ((p - 1).primeFactors.card : ℝ) ^ 6 * Real.log p ^ 2 := by
  classical
  set P := (p - 1).primeFactors with hPdef
  set m := P.card with hmdef
  have hP : ∀ ℓ ∈ P, ℓ.Prime := fun ℓ h => (Nat.mem_primeFactors.mp h).1
  have hm1 : 1 ≤ m := le_trans one_le_M6 hm
  -- choose `n`
  have hex : ∃ n, 100000 * m ≤ 2 ^ (8000 * n) := ⟨m + 1, by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ (m + 17) ≤ 2 ^ (8000 * (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (m + 17) = 131072 * 2 ^ m := by rw [pow_add]; ring
    omega⟩
  set n := Nat.find hex with hndef
  have hcard : 100000 * m ≤ 2 ^ (8000 * n) := Nat.find_spec hex
  have hn : 2 ^ 36 ≤ n := by
    by_contra h
    push Not at h
    have h3 : 2 ^ (8000 * n) ≤ M6 := by
      rw [M6_def]; exact Nat.pow_le_pow_right (by norm_num) (by rw [E36_def]; omega)
    omega
  have hlt : 2 ^ (8000 * n) < T8000 * (100000 * m) := by
    have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this
    have e : 2 ^ (8000 * n) = T8000 * 2 ^ (8000 * (n - 1)) := by
      rw [T8000_def, ← pow_add]; congr 1; omega
    rw [e]
    exact Nat.mul_lt_mul_of_pos_left this T8000_pos
  -- the sieve
  set D : ℕ → List Block := fun ℓ => restr ℓ (pick (desC P n 1 []) ℓ (custList P n tab6))
  have hadm : Admissible P D :=
    admissible_pick P _ _ (desC_spec P n 1 [] rfl le_rfl)
      (tableOK_designs P n 23984 tab6 true up0 8000 tab6_ok)
  have hrep := isRep_buch hadm
  set M := 1 + ∑ ℓ ∈ P, massU (D ℓ) with hM
  have hmass := mass_table_le P hP n hn 23984 (by norm_num) tab6 true up0 8000 P tab6_ok
    subset_rfl (by have : m ≤ 2 ^ (8000 * n) := by omega
                   simpa using this) (fun h => absurd h (by decide))
  rw [tab6_len] at hmass
  have hM0 : 0 ≤ ∑ ℓ ∈ P, massU (D ℓ) := Finset.sum_nonneg fun ℓ _ => massU_nonneg _
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  -- the main term
  have hσtop : ∑ x ∈ P.filter (fun x => 2 ^ (8000 * n) < x), recip x ≤ r up0 := by
    have hpow : (0 : ℝ) < 2 ^ (8000 * n) := by positivity
    have h1 : ∑ x ∈ P.filter (fun x => 2 ^ (8000 * n) < x), recip x ≤ 1 / 10 ^ 5 := by
      calc ∑ x ∈ P.filter (fun x => 2 ^ (8000 * n) < x), recip x
          ≤ ∑ _x ∈ P.filter (fun x => 2 ^ (8000 * n) < x), (1 : ℝ) / 2 ^ (8000 * n) := by
            refine Finset.sum_le_sum fun ℓ h => ?_
            have : (2 : ℝ) ^ (8000 * n) < ℓ := by exact_mod_cast (Finset.mem_filter.mp h).2
            exact one_div_le_one_div_of_le hpow this.le
        _ = (P.filter (fun x => 2 ^ (8000 * n) < x)).card / 2 ^ (8000 * n) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ m / 2 ^ (8000 * n) := by gcongr; exact Finset.card_filter_le _ _
        _ ≤ 1 / 10 ^ 5 := by
            rw [div_le_div_iff₀ hpow (by norm_num)]
            have : ((100000 * m : ℕ) : ℝ) ≤ ((2 ^ (8000 * n) : ℕ) : ℝ) := by exact_mod_cast hcard
            push_cast at this
            linarith
    have h2 : (1 : ℝ) / 10 ^ 5 ≤ r up0 := by
      unfold up0
      refine le_trans (le_of_eq ?_) (cdiv_ge Dn (10 ^ 5) (by norm_num))
      rw [r_Dn]; norm_num
    linarith
  have herr := err_table_le P hP n hn 23984 tab6 true up0 8000 P tab6_ok subset_rfl
    (by norm_num) (fun h => absurd h (by decide)) (by simpa using hσtop)
  have hE : r (errSum true up0 tab6) ≤ 94 / 100 := by
    have h := r_mono tab6_err
    have e1 : r (100 * errSum true up0 tab6) = 100 * r (errSum true up0 tab6) := by
      unfold r; push_cast; ring
    have e2 : r (94 * Dn) = 94 := by
      have hD : (Dn : ℝ) ≠ 0 := by exact_mod_cast Dn_pos.ne'
      unfold r; push_cast; field_simp
    rw [e1, e2] at h
    linarith
  have hg : ∀ ℓ ∈ P, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := fun ℓ h => recip_mem (hP ℓ h)
  have hΦ := buch_ge_W hadm recip hg
  set V := ∏ ℓ ∈ P, (1 - recip ℓ) with hV
  have hpg := prod_P_ge6 P hP n (by omega) hcard
  rw [← hV] at hpg
  have hV0 : 0 < V := by
    by_contra h; push Not at h
    have h0 : (0 : ℝ) ≤ 9 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n := by positivity
    have := mul_nonpos_of_nonpos_of_nonneg h h0
    linarith
  have hV1 : V ≤ 1 := Finset.prod_le_one₀ (fun ℓ h => by linarith [(hg ℓ h).2])
    fun ℓ h => by linarith [(hg ℓ h).1]
  set θ := V / 25 with hθ
  have hθΦ : θ ≤ buch P D recip := by
    refine le_trans ?_ hΦ
    rw [hθ]
    have : (1 : ℝ) / 25 ≤ 1 - ∑ ℓ ∈ P, recip ℓ * Wt P recip ℓ * (ratProd (D ℓ) recip - 1) := by
      have : ∑ ℓ ∈ P, recip ℓ * Wt P recip ℓ * (ratProd (D ℓ) recip - 1) ≤
          94 / 100 + 1 / 10 ^ 5 := by linarith
      linarith
    calc V / 25 = V * (1 / 25) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hV0.le
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have key := le_of_no_primitive_root_lt_rep hGRH p hp hp2 x hx1 hxp hno (buch P D) M θ hrep
    (fun y hy h1 => buch_nonpos hadm y hy h1) hM1 hθpos hθ1 hθΦ
  -- bound `M / θ`
  set L := Real.log p with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hK := one_le_Kmass
  have h1 : M ≤ 139 * Kmass * 2 ^ (n * 23983) := by
    have : (1 : ℝ) ≤ Kmass * 2 ^ (n * 23983) :=
      one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ (by norm_num))
    rw [hM]
    have e : (n * (23984 - 1)) = n * 23983 := rfl
    rw [e] at hmass
    push_cast at hmass
    linarith
  have hinvθ : 1 / θ ≤ 25 * 9 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n := by
    rw [hθ, one_div_div, div_le_iff₀ hV0]
    calc (25 : ℝ) ≤ 25 * (V * (9 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n)) := by linarith
      _ = _ := by ring
  have hMθ : M / θ ≤ K₆ * 2 ^ (23984 * n) := by
    rw [div_eq_mul_one_div]
    calc M * (1 / θ) ≤ (139 * Kmass * 2 ^ (n * 23983)) * (25 * 9 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n) :=
          mul_le_mul h1 hinvθ (by positivity) (by positivity)
      _ = K₆ * 2 ^ (23984 * n) := by
          rw [K₆, show 23984 * n = n * 23983 + n by ring, pow_add]; ring
  have hMLθ : M * L / θ ≤ K₆ * 2 ^ (23984 * n) * L := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hMθ hL0
  have h0 : 0 ≤ M * L / θ := by
    have : (0 : ℝ) ≤ M := by linarith
    positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hpow6 : (2 : ℝ) ^ (47968 * n) ≤ ((T8000 : ℝ) * 100000) ^ 6 * (m : ℝ) ^ 6 := by
    have h2 : ((2 ^ (8000 * n) : ℕ) : ℝ) ≤ ((T8000 * (100000 * m) : ℕ) : ℝ) := by
      exact_mod_cast hlt.le
    push_cast at h2
    calc (2 : ℝ) ^ (47968 * n) ≤ 2 ^ (48000 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((2 : ℝ) ^ (8000 * n)) ^ 6 := by rw [← pow_mul]; ring_nf
      _ ≤ ((T8000 : ℝ) * (100000 * m)) ^ 6 := pow_le_pow_left₀ (by positivity) h2 6
      _ = ((T8000 : ℝ) * 100000) ^ 6 * (m : ℝ) ^ 6 := by ring
  calc (x : ℝ) ≤ 1089 * (M * L / θ) ^ 2 := key
    _ ≤ 1089 * (K₆ * 2 ^ (23984 * n) * L) ^ 2 := by gcongr
    _ = 1089 * K₆ ^ 2 * (2 : ℝ) ^ (47968 * n) * L ^ 2 := by
        rw [show 47968 * n = 23984 * n * 2 by ring, pow_mul]; ring
    _ ≤ 1089 * K₆ ^ 2 * (((T8000 : ℝ) * 100000) ^ 6 * (m : ℝ) ^ 6) * L ^ 2 := by gcongr
    _ = C6 * (m : ℝ) ^ 6 * L ^ 2 := by rw [C6]; ring

end Shoup.Sieve

namespace Shoup

open Sieve ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- The constant of `PolyOmegaStatement 6`. -/
noncomputable def C6total : ℝ := C6 + polyC * (M6 : ℝ) ^ 130

/-- **Main theorem (exponent 6).** Under GRH, every odd prime `p` has a primitive root
`0 < g ≤ C ω(p-1)^6 (log p)²`. -/
theorem leastPrimitiveRoot_le_six_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (C6total * (ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2) := by
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hC6 : 0 ≤ C6 := by unfold C6; have := T8000_pos; positivity
  have hpC : 0 ≤ polyC := by rw [polyC_def]; have := c16_pos; positivity
  have hm : 1 ≤ ω (p - 1) := by
    rw [cardDistinctFactors_eq_card_primeFactors]; exact one_le_card_primeFactors p hp hp2
  have hmR : (1 : ℝ) ≤ ω (p - 1) := by exact_mod_cast hm
  by_cases hbig : M6 ≤ (p - 1).primeFactors.card
  · have h := hasPrimitiveRootLE_of_bound p hp (C6 * ((p - 1).primeFactors.card : ℝ) ^ 6 *
      Real.log p ^ 2) (by positivity) fun x hx1 hxp hno =>
        le_of_no_primitive_root_lt_six hGRH p hp hp2 x hx1 hxp hno hbig
    rw [← cardDistinctFactors_eq_card_primeFactors] at h
    refine h.mono ?_
    have h0 : 0 ≤ polyC * (M6 : ℝ) ^ 130 := by positivity
    have h6 : 0 ≤ (ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2 := by positivity
    have hle : C6 ≤ C6total := by unfold C6total; linarith
    calc C6 * (ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2 = C6 * ((ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2) := by ring
      _ ≤ C6total * ((ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2) := mul_le_mul_of_nonneg_right hle h6
      _ = _ := by ring
  · push Not at hbig
    have h := leastPrimitiveRoot_le_poly_of_GRH hGRH p hp hp2
    refine h.mono ?_
    rw [← cardDistinctFactors_eq_card_primeFactors] at hbig
    have hmM : (ω (p - 1) : ℝ) ≤ M6 := by exact_mod_cast hbig.le
    have h130 : (ω (p - 1) : ℝ) ^ 130 ≤ (M6 : ℝ) ^ 130 :=
      pow_le_pow_left₀ (by positivity) hmM 130
    have hsplit : (ω (p - 1) : ℝ) ^ 136 = (ω (p - 1) : ℝ) ^ 130 * (ω (p - 1) : ℝ) ^ 6 := by
      rw [← pow_add]
    have h6 : 0 ≤ (ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2 := by positivity
    rw [hsplit]
    have hle : polyC * (M6 : ℝ) ^ 130 ≤ C6total := by unfold C6total; linarith
    calc polyC * ((ω (p - 1) : ℝ) ^ 130 * (ω (p - 1) : ℝ) ^ 6) * Real.log p ^ 2
        = polyC * (ω (p - 1) : ℝ) ^ 130 * ((ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2) := by ring
      _ ≤ polyC * (M6 : ℝ) ^ 130 * ((ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ h6
          exact mul_le_mul_of_nonneg_left h130 hpC
      _ ≤ C6total * ((ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2) := mul_le_mul_of_nonneg_right hle h6
      _ = _ := by ring

/-- `PolyOmegaStatement 6` holds under GRH. -/
theorem polyOmega6_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    PolyOmegaStatement 6 :=
  ⟨C6total, fun p hp hp2 => leastPrimitiveRoot_le_six_of_GRH hGRH p hp hp2⟩

/-- `WangStatement` is `PolyOmegaStatement 6`. -/
theorem wangStatement_iff : WangStatement ↔ PolyOmegaStatement 6 := Iff.rfl

/-- **Wang Yuan (1959), as quoted by Shoup**: under GRH, `g(p) = O(ω(p-1)^6 (log p)²)`. -/
theorem wang_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) : WangStatement :=
  wangStatement_iff.mpr (polyOmega6_of_GRH hGRH)

end Shoup
