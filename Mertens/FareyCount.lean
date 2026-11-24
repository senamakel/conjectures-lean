import Mertens.Statement2
import Mertens.Uniform

/-!
# Farey fractions: membership, separation and the counting identity

* `mem_farey`: `f ∈ F_N ↔ 0 < f ≤ 1 ∧ den f ≤ N`.
* `farey_sep`: two distinct Farey fractions of order `N` are at least `1/N²` apart.
* `fareyCount_eq`: for `0 ≤ x ≤ 1`, `#{f ∈ F_N : f ≤ x} = ∑_{q ≤ N} M(N/q) ⌊q x⌋`
  (Möbius inversion over the denominators).
-/

namespace Mertens

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

lemma mem_farey {N : ℕ} {f : ℚ} : f ∈ farey N ↔ 0 < f ∧ f ≤ 1 ∧ f.den ≤ N := by
  constructor
  · intro hf
    simp only [farey, mem_image, mem_filter, mem_product, mem_Icc] at hf
    obtain ⟨⟨p, q⟩, ⟨⟨⟨hp1, hpN⟩, hq1, hqN⟩, hpq⟩, rfl⟩ := hf
    simp only at *
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hq1
    refine ⟨by positivity, (div_le_one hq0).2 (by exact_mod_cast hpq), ?_⟩
    calc ((p : ℚ) / q).den ≤ q := by
          have := Rat.den_dvd p q
          rw [Rat.divInt_eq_div] at this
          push_cast at this
          exact Nat.le_of_dvd (by omega) (by exact_mod_cast this)
      _ ≤ N := hqN
  · rintro ⟨h0, h1, hN⟩
    simp only [farey, mem_image, mem_filter, mem_product, mem_Icc]
    have hnum : 0 < f.num := Rat.num_pos.2 h0
    have hden : (0 : ℚ) < f.den := by exact_mod_cast f.den_pos
    have hle : f.num ≤ f.den := by
      have h := f.num_div_den
      rw [← h, div_le_one hden] at h1
      exact_mod_cast h1
    refine ⟨(f.num.toNat, f.den), ⟨⟨⟨?_, ?_⟩, f.den_pos, hN⟩, ?_⟩, ?_⟩
    · omega
    · omega
    · simp only; omega
    · simp only
      rw [show ((f.num.toNat : ℕ) : ℚ) = (f.num : ℚ) by
        rw [show (f.num.toNat : ℚ) = ((f.num.toNat : ℤ) : ℚ) by norm_cast, Int.toNat_of_nonneg hnum.le]]
      exact f.num_div_den

/-- Distinct Farey fractions of order `N` are at least `1/N²` apart. -/
lemma farey_sep {N : ℕ} {f g : ℚ} (hf : f ∈ farey N) (hg : g ∈ farey N) (hfg : f ≠ g) :
    (1 : ℚ) / (N : ℚ) ^ 2 ≤ |f - g| := by
  obtain ⟨-, -, hfN⟩ := mem_farey.1 hf
  obtain ⟨-, -, hgN⟩ := mem_farey.1 hg
  have hb : (0 : ℚ) < f.den := by exact_mod_cast f.den_pos
  have hd : (0 : ℚ) < g.den := by exact_mod_cast g.den_pos
  have key : (f - g) * ((f.den : ℚ) * g.den) = ((f.num * g.den - g.num * f.den : ℤ) : ℚ) := by
    push_cast
    have h1 := Rat.mul_den_eq_num f
    have h2 := Rat.mul_den_eq_num g
    linear_combination (g.den : ℚ) * h1 - (f.den : ℚ) * h2
  have hne : (f.num * g.den - g.num * f.den : ℤ) ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at key
    exact hfg (sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right (by positivity)))
  have h1 : (1 : ℚ) ≤ |f - g| * ((f.den : ℚ) * g.den) := by
    rw [← abs_of_pos (show (0 : ℚ) < (f.den : ℚ) * g.den by positivity), ← abs_mul, key]
    exact_mod_cast Int.one_le_abs hne
  have hN0 : (0 : ℚ) < N := by
    have := f.den_pos; exact_mod_cast (lt_of_lt_of_le this hfN)
  have h2 : (f.den : ℚ) * g.den ≤ (N : ℚ) ^ 2 := by
    rw [sq]; gcongr
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℚ) ≤ |f - g| * ((f.den : ℚ) * g.den) := h1
    _ ≤ |f - g| * (N : ℚ) ^ 2 := by gcongr

lemma sum_divisors_moebius (n : ℕ) : ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- `#{1 ≤ p ≤ m : gcd(p, q) = 1} = ∑_{d ∣ q} μ(d) ⌊m/d⌋` for `q ≠ 0`. -/
lemma card_coprime_Ioc (m : ℕ) {q : ℕ} (hq : q ≠ 0) :
    ((#{p ∈ Ioc 0 m | p.Coprime q} : ℕ) : ℤ) = ∑ d ∈ q.divisors, μ d * ((m / d : ℕ) : ℤ) := by
  have h1 : ((#{p ∈ Ioc 0 m | p.Coprime q} : ℕ) : ℤ) =
      ∑ p ∈ Ioc 0 m, ∑ d ∈ q.divisors, if d ∣ p then μ d else 0 := by
    rw [card_filter]
    push_cast
    refine sum_congr rfl fun p _ => ?_
    rw [← sum_filter]
    have hset : {d ∈ q.divisors | d ∣ p} = (Nat.gcd p q).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, Nat.gcd_ne_zero_right h2⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hq⟩, h1⟩
    rw [hset, sum_divisors_moebius]
  rw [h1, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]

/-- `h_x(e) = ⌊e x⌋`, as an arithmetic function. -/
noncomputable def floorFn (x : ℝ) : ArithmeticFunction ℤ :=
  ⟨fun e => (⌊(e : ℝ) * x⌋₊ : ℤ), by simp⟩

lemma floorFn_apply (x : ℝ) (e : ℕ) : floorFn x e = (⌊(e : ℝ) * x⌋₊ : ℤ) := rfl

/-- The pairs `(p, q)` with `1 ≤ p, q ≤ N`, `gcd(p, q) = 1` and `p ≤ q x`. -/
noncomputable def coprimePairs (N : ℕ) (x : ℝ) : Finset (ℕ × ℕ) :=
  {pq ∈ Ioc 0 N ×ˢ Ioc 0 N | pq.1.Coprime pq.2 ∧ (pq.1 : ℝ) ≤ pq.2 * x}

lemma fareyFilter_eq_image {N : ℕ} {x : ℝ} (hx1 : x ≤ 1) :
    (farey N).filter (fun f : ℚ => (f : ℝ) ≤ x) = (coprimePairs N x).image fun pq => (pq.1 : ℚ) / pq.2 := by
  ext f
  simp only [mem_filter, mem_image, coprimePairs, mem_product, mem_Ioc, mem_farey]
  constructor
  · rintro ⟨⟨h0, h1, hN⟩, hx⟩
    have hnum : 0 < f.num := Rat.num_pos.2 h0
    have hden : (0 : ℚ) < f.den := by exact_mod_cast f.den_pos
    have hfe : ((f.num.toNat : ℕ) : ℚ) / f.den = f := by
      rw [show ((f.num.toNat : ℕ) : ℚ) = (f.num : ℚ) by
        rw [show (f.num.toNat : ℚ) = ((f.num.toNat : ℤ) : ℚ) by norm_cast,
          Int.toNat_of_nonneg hnum.le]]
      exact f.num_div_den
    have hle : f.num ≤ f.den := by
      have h := f.num_div_den
      rw [← h, div_le_one hden] at h1
      exact_mod_cast h1
    refine ⟨(f.num.toNat, f.den), ⟨⟨⟨by omega, by omega⟩, f.den_pos, hN⟩, ?_, ?_⟩, hfe⟩
    · have := f.reduced
      simp only
      rwa [show f.num.natAbs = f.num.toNat by omega] at this
    · simp only
      have hd : (0 : ℝ) < f.den := by exact_mod_cast f.den_pos
      have : ((f.num.toNat : ℕ) : ℝ) / f.den ≤ x := by
        have := congrArg (fun r : ℚ => (r : ℝ)) hfe
        push_cast at this
        rw [this]; exact hx
      rwa [div_le_iff₀ hd, mul_comm] at this
  · rintro ⟨⟨p, q⟩, ⟨⟨⟨hp0, hpN⟩, hq0, hqN⟩, hcop, hpx⟩, rfl⟩
    simp only at *
    have hq : (0 : ℚ) < q := by exact_mod_cast hq0
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
    have hpq : (p : ℝ) ≤ q := hpx.trans (by nlinarith)
    refine ⟨⟨by positivity, (div_le_one hq).2 (by exact_mod_cast hpq), ?_⟩, ?_⟩
    · have := Rat.den_dvd p q
      rw [Rat.divInt_eq_div] at this
      push_cast at this
      exact le_trans (Nat.le_of_dvd (by omega) (by exact_mod_cast this)) hqN
    · push_cast
      rw [div_le_iff₀ hqR, mul_comm]; exact hpx

lemma coprimePairs_injOn (N : ℕ) (x : ℝ) :
    Set.InjOn (fun pq : ℕ × ℕ => (pq.1 : ℚ) / pq.2) (coprimePairs N x) := by
  rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' heq
  simp only [coprimePairs, coe_filter, mem_product, mem_Ioc, Set.mem_ofPred_eq] at hpq hpq'
  simp only at heq
  have h := Rat.div_int_inj (a := p) (b := q) (c := p') (d := q')
    (by exact_mod_cast hpq.1.2.1) (by exact_mod_cast hpq'.1.2.1)
    (by simpa using hpq.2.1) (by simpa using hpq'.2.1) (by simpa only [Int.cast_natCast] using heq)
  simp only [Nat.cast_inj] at h
  rw [h.1, h.2]

lemma card_coprimePairs {N : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    #(coprimePairs N x) = ∑ q ∈ Ioc 0 N, #{p ∈ Ioc 0 ⌊(q : ℝ) * x⌋₊ | p.Coprime q} := by
  rw [coprimePairs, card_filter, sum_product_right]
  refine sum_congr rfl fun q hq => ?_
  rw [card_filter, ← sum_filter, ← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc] at hq ⊢
  have hqx : 0 ≤ (q : ℝ) * x := by positivity
  have hfl : ⌊(q : ℝ) * x⌋₊ ≤ N := by
    refine Nat.floor_le_of_le ?_
    calc (q : ℝ) * x ≤ q * 1 := by gcongr
      _ = q := mul_one _
      _ ≤ N := by exact_mod_cast hq.2
  rw [Nat.le_floor_iff hqx]
  constructor
  · rintro ⟨⟨h0, -⟩, h1, h2⟩; exact ⟨⟨h0, h2⟩, h1⟩
  · rintro ⟨⟨h0, h2⟩, h1⟩
    refine ⟨⟨h0, ?_⟩, h1, h2⟩
    exact le_trans (Nat.le_floor h2) hfl

/-- **The counting identity**: for `0 ≤ x ≤ 1`, `#{f ∈ F_N : f ≤ x} = ∑_{q ≤ N} ⌊q x⌋ M(N/q)`. -/
theorem fareyCount_eq {N : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((((farey N).filter (fun f : ℚ => (f : ℝ) ≤ x)).card : ℕ) : ℤ) =
      ∑ q ∈ Ioc 0 N, (⌊(q : ℝ) * x⌋₊ : ℤ) * mertens (N / q : ℕ) := by
  rw [fareyFilter_eq_image hx1, card_image_of_injOn (coprimePairs_injOn N x),
    card_coprimePairs hx0 hx1]
  push_cast
  have hstep : ∀ q ∈ Ioc 0 N, ((#{p ∈ Ioc 0 ⌊(q : ℝ) * x⌋₊ | p.Coprime q} : ℕ) : ℤ) =
      ((μ : ArithmeticFunction ℤ) * floorFn x) q := by
    intro q hq
    have hq0 : q ≠ 0 := by simp at hq; omega
    rw [card_coprime_Ioc _ hq0, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b => (μ : ArithmeticFunction ℤ) a * floorFn x b)]
    refine sum_congr rfl fun d hd => ?_
    rw [floorFn_apply]
    congr 2
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd; positivity
    rw [Nat.cast_div hdq hd0, div_mul_eq_mul_div, Nat.floor_div_natCast]
  rw [sum_congr rfl hstep]
  have hmert : ∀ k : ℕ, ∑ m ∈ Ioc 0 k, μ m = mertens k := fun k => by
    rw [mertens, Nat.floor_natCast,
      show Icc 1 k = Ioc 0 k from by ext n; simp only [mem_Ioc, mem_Icc]; omega]
  calc ∑ q ∈ Ioc 0 N, ((μ : ArithmeticFunction ℤ) * floorFn x) q
      = ∑ q ∈ Ioc 0 N, (floorFn x * (μ : ArithmeticFunction ℤ)) q := by rw [mul_comm]
    _ = ∑ q ∈ Ioc 0 N, floorFn x q * ∑ m ∈ Ioc 0 (N / q), (μ : ArithmeticFunction ℤ) m :=
        sum_Ioc_mul_eq_sum_sum _ _ N
    _ = _ := by
        refine sum_congr rfl fun q _ => ?_
        rw [floorFn_apply, ← hmert]

/-- `∑_{q ≤ N} M(N/q) = 1` for `N ≥ 1`. -/
theorem sum_mertens_div {N : ℕ} (hN : 1 ≤ N) : ∑ q ∈ Ioc 0 N, mertens (N / q : ℕ) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum (ζ : ArithmeticFunction ℤ) (μ : ArithmeticFunction ℤ) N
  rw [coe_zeta_mul_moebius] at h
  have hl : ∑ n ∈ Ioc 0 N, (1 : ArithmeticFunction ℤ) n = 1 := by
    simp only [ArithmeticFunction.one_apply]
    rw [sum_ite_eq']
    simp; omega
  rw [hl] at h
  rw [h]
  refine sum_congr rfl fun q hq => ?_
  have hq0 : q ≠ 0 := by simp at hq; omega
  rw [natCoe_apply, zeta_apply_ne hq0, Nat.cast_one, one_mul, mertens, Nat.floor_natCast,
    show Icc 1 (N / q) = Ioc 0 (N / q) from by ext n; simp only [mem_Ioc, mem_Icc]; omega]

end Mertens
