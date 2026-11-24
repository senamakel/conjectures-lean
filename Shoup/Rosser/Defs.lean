import Shoup.Sieve.Buchstab

/-!
# Rosser's sieve weights (`β = 2`, upper cut at `3.1`) as polynomials

For a finite set `Q` of primes, a level `Y > 0` and a fuel `n ≥ |Q|`, put

* `L(Q, Y) = 1 - Σ_{p ∈ Q} y_p · U(Q_{<p}, Y/p)` (the lower sieve),
* `U(Q, Y) = 1 - Σ_{p ∈ Q, p^{3.1} < Y} y_p · L(Q_{<p}, Y/p)` (the upper sieve),

where `Q_{<p} = {q ∈ Q : q < p}`. This is Rosser's construction with `β = 2` for the lower
weights; the upper weights keep only the primes with `p^{31} < Y^{10}`, so that the lower
bounds they use are taken at `s > 2.1`, away from the sieve limit `s = 2`.

* `ros_sieve`: on `0/1` points `L ≤ 0` unless all `y_q = 0` (then `L = U = 1`), and `U ≥ 0`;
* `isRep_ros`: `L`, `U` are combinations of squarefree monomials in `Q` of mass `rmass`;
* `rmass_le_cnt`, `cnt_le`: the mass of `L(Q, Y)` is at most `Y` when every `q ∈ Q` has
  `q² < Y` (every monomial is a distinct squarefree number `≤ Y`).
-/

namespace Shoup.Rosser

open Finset Shoup.Sieve

/-- The primes kept at a step: all of `Q` for the lower sieve, those with `p^{31} < Y^{10}` for
the upper sieve. -/
noncomputable def sel (lo : Bool) (Q : Finset ℕ) (Y : ℝ) : Finset ℕ := by
  classical exact if lo then Q else Q.filter fun p => (p : ℝ) ^ 31 < Y ^ 10

lemma sel_true (Q : Finset ℕ) (Y : ℝ) : sel true Q Y = Q := by
  classical simp [sel]

lemma mem_sel_false {Q : Finset ℕ} {Y : ℝ} {p : ℕ} :
    p ∈ sel false Q Y ↔ p ∈ Q ∧ (p : ℝ) ^ 31 < Y ^ 10 := by
  classical simp [sel]

lemma sel_subset (lo : Bool) (Q : Finset ℕ) (Y : ℝ) : sel lo Q Y ⊆ Q := by
  cases lo
  · intro p h; exact (mem_sel_false.mp h).1
  · rw [sel_true]

/-- Rosser's sieve polynomials, with fuel `n`: `ros n true` is the lower sieve, `ros n false`
the upper sieve. -/
noncomputable def ros : ℕ → Bool → Finset ℕ → ℝ → (ℕ → ℝ) → ℝ
  | 0, _, _, _, _ => 1
  | n + 1, lo, Q, Y, y =>
      1 - ∑ p ∈ sel lo Q Y, y p * ros n (!lo) (Q.filter (· < p)) (Y / p) y

lemma ros_succ (n : ℕ) (lo : Bool) (Q : Finset ℕ) (Y : ℝ) (y : ℕ → ℝ) :
    ros (n + 1) lo Q Y y =
      1 - ∑ p ∈ sel lo Q Y, y p * ros n (!lo) (Q.filter (· < p)) (Y / p) y := rfl

lemma card_filter_lt_lt {Q : Finset ℕ} {p : ℕ} (hp : p ∈ Q) :
    (Q.filter (· < p)).card < Q.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨p, hp, lt_irrefl p⟩)

/-! ### The sieve property on `0/1` points -/

theorem ros_sieve (y : ℕ → ℝ) : ∀ (n : ℕ) (Q : Finset ℕ), Q.card ≤ n →
    (∀ q ∈ Q, y q = 0 ∨ y q = 1) → ∀ Y : ℝ,
      ((∀ q ∈ Q, y q = 0) → ∀ b, ros n b Q Y y = 1) ∧
      ((∃ q ∈ Q, y q = 1) → ros n true Q Y y ≤ 0) ∧
      (0 ≤ ros n false Q Y y) := by
  intro n
  induction n with
  | zero =>
    intro Q hQ _ Y
    have hQe : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hQe
    refine ⟨fun _ b => rfl, fun ⟨q, hq, _⟩ => absurd hq (Finset.notMem_empty q), ?_⟩
    show (0 : ℝ) ≤ 1; norm_num
  | succ n ih =>
    intro Q hQ hy Y
    have hsub : ∀ p ∈ Q, (Q.filter (· < p)).card ≤ n := fun p hp => by
      have := card_filter_lt_lt hp; omega
    have hysub : ∀ p, ∀ q ∈ Q.filter (· < p), y q = 0 ∨ y q = 1 :=
      fun p q hq => hy q (Finset.mem_filter.mp hq).1
    have IH := fun p (hp : p ∈ Q) (Y' : ℝ) => ih (Q.filter (· < p)) (hsub p hp) (hysub p) Y'
    -- all zero
    have hzero : (∀ q ∈ Q, y q = 0) → ∀ b, ros (n + 1) b Q Y y = 1 := by
      intro h0 b
      rw [ros_succ]
      have : ∑ p ∈ sel b Q Y, y p * ros n (!b) (Q.filter (· < p)) (Y / p) y = 0 :=
        Finset.sum_eq_zero fun p hp => by rw [h0 p (sel_subset b Q Y hp), zero_mul]
      rw [this, sub_zero]
    refine ⟨hzero, ?_, ?_⟩
    · -- lower sieve: the least active prime contributes `1`
      rintro ⟨q, hq, hq1⟩
      set A := Q.filter fun ℓ => y ℓ = 1
      have hA : A.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hq, hq1⟩⟩
      set q0 := A.min' hA
      have hq0 : q0 ∈ Q ∧ y q0 = 1 := Finset.mem_filter.mp (Finset.min'_mem A hA)
      have hbelow : ∀ ℓ ∈ Q.filter (· < q0), y ℓ = 0 := by
        intro ℓ hℓ
        obtain ⟨hℓQ, hlt⟩ := Finset.mem_filter.mp hℓ
        rcases hy ℓ hℓQ with h | h
        · exact h
        · exfalso
          have := A.min'_le ℓ (Finset.mem_filter.mpr ⟨hℓQ, h⟩)
          omega
      have hterm : ∀ p ∈ Q, 0 ≤ y p * ros n false (Q.filter (· < p)) (Y / p) y := by
        intro p hp
        have h1 : 0 ≤ y p := by rcases hy p hp with h | h <;> simp [h]
        exact mul_nonneg h1 (IH p hp (Y / p)).2.2
      have hmain : 1 ≤ y q0 * ros n false (Q.filter (· < q0)) (Y / q0) y := by
        rw [hq0.2, one_mul, (IH q0 hq0.1 (Y / q0)).1 hbelow false]
      rw [ros_succ, sel_true]
      have := Finset.single_le_sum hterm hq0.1
      simp only [Bool.not_true]
      linarith
    · -- upper sieve: at most the least active prime contributes, and it contributes `1`
      by_cases hact : ∃ q ∈ Q, y q = 1
      · obtain ⟨q, hq, hq1⟩ := hact
        set A := Q.filter fun ℓ => y ℓ = 1
        have hA : A.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hq, hq1⟩⟩
        set q0 := A.min' hA
        have hq0 : q0 ∈ Q ∧ y q0 = 1 := Finset.mem_filter.mp (Finset.min'_mem A hA)
        have hbelow : ∀ ℓ ∈ Q.filter (· < q0), y ℓ = 0 := by
          intro ℓ hℓ
          obtain ⟨hℓQ, hlt⟩ := Finset.mem_filter.mp hℓ
          rcases hy ℓ hℓQ with h | h
          · exact h
          · exfalso
            have := A.min'_le ℓ (Finset.mem_filter.mpr ⟨hℓQ, h⟩)
            omega
        have hpt : ∀ p ∈ sel false Q Y, y p * ros n true (Q.filter (· < p)) (Y / p) y ≤
            if p = q0 then 1 else 0 := by
          intro p hp
          have hpQ := sel_subset false Q Y hp
          rcases hy p hpQ with h | h
          · rw [h, zero_mul]; split_ifs <;> norm_num
          · by_cases hpq : p = q0
            · subst hpq
              rw [if_pos rfl, h, one_mul, (IH _ hpQ (Y / _)).1 hbelow true]
            · rw [if_neg hpq, h, one_mul]
              have hlt : q0 < p := by
                have := A.min'_le p (Finset.mem_filter.mpr ⟨hpQ, h⟩)
                exact lt_of_le_of_ne this (Ne.symm hpq)
              exact (IH p hpQ (Y / p)).2.1 ⟨q0, Finset.mem_filter.mpr ⟨hq0.1, hlt⟩, hq0.2⟩
        have hsum := Finset.sum_le_sum hpt
        rw [Finset.sum_ite_eq'] at hsum
        rw [ros_succ]
        simp only [Bool.not_false]
        split_ifs at hsum <;> linarith
      · push Not at hact
        have h0 : ∀ q ∈ Q, y q = 0 := fun q hq => by
          rcases hy q hq with h | h
          · exact h
          · exact absurd h (hact q hq)
        rw [hzero h0 false]; norm_num

/-! ### Monomial expansion and mass -/

/-- The mass bound of `ros`. -/
noncomputable def rmass : ℕ → Bool → Finset ℕ → ℝ → ℝ
  | 0, _, _, _ => 1
  | n + 1, lo, Q, Y => 1 + ∑ p ∈ sel lo Q Y, rmass n (!lo) (Q.filter (· < p)) (Y / p)

theorem isRep_ros : ∀ (n : ℕ) (lo : Bool) (Q : Finset ℕ) (Y : ℝ),
    IsRep (ros n lo Q Y) Q (rmass n lo Q Y) := by
  intro n
  induction n with
  | zero =>
    intro lo Q Y
    exact (IsRep.one.mono (Finset.empty_subset Q) le_rfl).congr fun y => rfl
  | succ n ih =>
    intro lo Q Y
    have hterm : ∀ p ∈ sel lo Q Y,
        IsRep (fun y => y p * ros n (!lo) (Q.filter (· < p)) (Y / p) y) Q
          (rmass n (!lo) (Q.filter (· < p)) (Y / p)) := by
      intro p hp
      have hpQ := sel_subset lo Q Y hp
      have hdisj : Disjoint ({p} : Finset ℕ) (Q.filter (· < p)) := by
        rw [Finset.disjoint_singleton_left]; simp
      refine ((isRep_monomial p).mul (ih (!lo) (Q.filter (· < p)) (Y / p)) hdisj).mono ?_
        (by rw [one_mul])
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · rw [Finset.mem_singleton.mp h]; exact hpQ
      · exact (Finset.mem_filter.mp h).1
    have hsum := IsRep.sum (sel lo Q Y) _ Q _ hterm
    have h1 : IsRep (fun _ => (1 : ℝ)) Q 1 := IsRep.one.mono (Finset.empty_subset _) le_rfl
    exact (h1.sub hsum).congr fun y => rfl

/-- Subsets of `Q` with product at most `Y`. -/
noncomputable def cnt (Q : Finset ℕ) (Y : ℝ) : ℕ := by
  classical exact (Q.powerset.filter fun T => ((∏ q ∈ T, q : ℕ) : ℝ) ≤ Y).card

lemma cnt_split (Q S : Finset ℕ) (hS : S ⊆ Q) (hQ : ∀ p ∈ Q, 0 < p) (Y : ℝ) (hY : 1 ≤ Y) :
    1 + ∑ p ∈ S, (cnt (Q.filter (· < p)) (Y / p) : ℝ) ≤ cnt Q Y := by
  classical
  set F := Q.powerset.filter fun T => ((∏ q ∈ T, q : ℕ) : ℝ) ≤ Y with hF
  set G : ℕ → Finset (Finset ℕ) := fun p =>
    ((Q.filter (· < p)).powerset.filter fun T => ((∏ q ∈ T, q : ℕ) : ℝ) ≤ Y / p).image
      (insert p) with hG
  have hcntQ : cnt Q Y = F.card := by simp only [cnt, hF]
  have hcntG : ∀ p ∈ S, (G p).card = cnt (Q.filter (· < p)) (Y / p) := by
    intro p _
    simp only [hG, cnt]
    rw [Finset.card_image_of_injOn]
    · intro A hA B hB hAB
      have hpA : p ∉ A := by
        intro h
        have := (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1) h
        simp at this
      have hpB : p ∉ B := by
        intro h
        have := (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1) h
        simp at this
      have := congrArg (fun T => T.erase p) hAB
      simpa [Finset.erase_insert hpA, Finset.erase_insert hpB] using this
  have hdisj : (S : Set ℕ).PairwiseDisjoint G := by
    intro p hp p' hp' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨B, hB, hAB⟩ := Finset.mem_image.mp hT'
    have hAsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
    have hBsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have h1 : p ∈ insert p' B := by rw [hAB]; exact Finset.mem_insert_self p A
    have h2 : p' ∈ insert p A := by rw [← hAB]; exact Finset.mem_insert_self p' B
    rcases Finset.mem_insert.mp h1 with h | h
    · exact hne h
    rcases Finset.mem_insert.mp h2 with h' | h'
    · exact hne h'.symm
    have := (Finset.mem_filter.mp (hBsub h)).2
    have := (Finset.mem_filter.mp (hAsub h')).2
    omega
  have hemp : ∅ ∉ S.biUnion G := by
    intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h
    obtain ⟨A, _, hA⟩ := Finset.mem_image.mp hp
    exact Finset.insert_ne_empty p A hA
  have hsubF : insert ∅ (S.biUnion G) ⊆ F := by
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · simp [hF, hY]
    obtain ⟨p, hpS, hp⟩ := Finset.mem_biUnion.mp hT
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hA1, hA2⟩ := Finset.mem_filter.mp hA
    have hAsub := Finset.mem_powerset.mp hA1
    have hpA : p ∉ A := fun h => by have := hAsub h; simp at this
    have hpQ := hS hpS
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hQ p hpQ
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hpQ (hAsub.trans (Finset.filter_subset _ _)), ?_⟩
    rw [Finset.prod_insert hpA]
    push_cast
    push_cast at hA2
    calc (p : ℝ) * ∏ q ∈ A, (q : ℝ) ≤ p * (Y / p) := mul_le_mul_of_nonneg_left hA2 hp0.le
      _ = Y := by field_simp
  have hcard := Finset.card_le_card hsubF
  rw [Finset.card_insert_of_notMem hemp, Finset.card_biUnion hdisj] at hcard
  rw [hcntQ]
  have : (1 : ℝ) + ∑ p ∈ S, (cnt (Q.filter (· < p)) (Y / p) : ℝ) =
      ((∑ p ∈ S, (G p).card + 1 : ℕ) : ℝ) := by
    push_cast
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun p hp => by rw [hcntG p hp]
  rw [this]
  exact_mod_cast hcard

lemma cnt_le (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (Y : ℝ) (hY : 0 ≤ Y) :
    (cnt Q Y : ℝ) ≤ Y := by
  classical
  set F := Q.powerset.filter fun T => ((∏ q ∈ T, q : ℕ) : ℝ) ≤ Y with hF
  have hcntQ : cnt Q Y = F.card := by simp only [cnt, hF]
  have hmaps : ∀ T ∈ F, (∏ q ∈ T, q) ∈ Finset.Icc 1 ⌊Y⌋₊ := by
    intro T hT
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hT
    have hTsub := Finset.mem_powerset.mp h1
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q hq =>
      (hQ q (hTsub hq)).ne_zero), Nat.le_floor h2⟩
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ q ∈ T, q) F := by
    intro A hA B hB hAB
    have hA' : ∀ q ∈ A, q.Prime := fun q hq =>
      hQ q (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1 hq)
    have hB' : ∀ q ∈ B, q.Prime := fun q hq =>
      hQ q (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1 hq)
    have := congrArg Nat.primeFactors hAB
    simp only at this
    rwa [Nat.primeFactors_prod hA', Nat.primeFactors_prod hB'] at this
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
  rw [hcntQ]
  calc (F.card : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hc
    _ ≤ Y := Nat.floor_le hY

/-- `p^{31} < Y^{10}` gives `p³ < Y`. -/
lemma cube_lt_of_incl {p : ℕ} {Y : ℝ} (hp : 1 ≤ p) (hY : 0 < Y) (h : (p : ℝ) ^ 31 < Y ^ 10) :
    (p : ℝ) ^ 3 < Y := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h30 : ((p : ℝ) ^ 3) ^ 10 ≤ (p : ℝ) ^ 31 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hp1 (by norm_num)
  exact (pow_lt_pow_iff_left₀ (by positivity) hY.le (by norm_num)).mp (h30.trans_lt h)

theorem rmass_le_cnt : ∀ (n : ℕ) (lo : Bool) (Q : Finset ℕ) (Y : ℝ), (∀ q ∈ Q, 1 ≤ q) →
    1 ≤ Y → (lo = true → ∀ q ∈ Q, (q : ℝ) ^ 2 < Y) → rmass n lo Q Y ≤ cnt Q Y := by
  intro n
  induction n with
  | zero =>
    intro lo Q Y _ hY _
    show (1 : ℝ) ≤ cnt Q Y
    classical
    have : (∅ : Finset ℕ) ∈ Q.powerset.filter fun T => ((∏ q ∈ T, q : ℕ) : ℝ) ≤ Y := by
      simp [hY]
    have h := Finset.card_pos.mpr ⟨_, this⟩
    have : 1 ≤ cnt Q Y := by simp only [cnt]; exact h
    exact_mod_cast this
  | succ n ih =>
    intro lo Q Y hQ hY hsq
    show 1 + ∑ p ∈ sel lo Q Y, rmass n (!lo) (Q.filter (· < p)) (Y / p) ≤ cnt Q Y
    have hY0 : 0 < Y := by linarith
    have hterm : ∀ p ∈ sel lo Q Y, rmass n (!lo) (Q.filter (· < p)) (Y / p) ≤
        cnt (Q.filter (· < p)) (Y / p) := by
      intro p hp
      have hpQ := sel_subset lo Q Y hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hQ p hpQ
      have hp0 : (0 : ℝ) < p := by linarith
      -- `p^2 < Y` (lower) or `p^3 < Y` (upper)
      have hkey : (p : ℝ) ≤ Y / p ∧ (lo = false → ∀ q ∈ Q.filter (· < p), (q : ℝ) ^ 2 < Y / p) := by
        cases lo
        · have h3 := cube_lt_of_incl (hQ p hpQ) hY0 (mem_sel_false.mp hp).2
          refine ⟨?_, fun _ q hq => ?_⟩
          · rw [le_div_iff₀ hp0]; nlinarith
          · obtain ⟨hqQ, hqp⟩ := Finset.mem_filter.mp hq
            have hq0 : (0 : ℝ) ≤ q := by positivity
            have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
            rw [lt_div_iff₀ hp0]
            have : (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by nlinarith
            nlinarith
        · have h2 := hsq rfl p hpQ
          refine ⟨?_, fun h => absurd h (by decide)⟩
          rw [le_div_iff₀ hp0]; nlinarith
      refine ih (!lo) _ (Y / p) (fun q hq => hQ q (Finset.mem_filter.mp hq).1) ?_ ?_
      · exact le_trans hp1 hkey.1
      · intro hlo
        exact hkey.2 (by cases lo <;> simp_all)
    have hsplit := cnt_split Q (sel lo Q Y) (sel_subset lo Q Y)
      (fun p hp => hQ p hp) Y hY
    linarith [Finset.sum_le_sum hterm]

end Shoup.Rosser
