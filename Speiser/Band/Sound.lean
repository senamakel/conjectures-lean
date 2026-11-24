import Mathlib
import SpeiserCompute.Core

/-!
# Soundness of the disc arithmetic in `SpeiserCompute.Core`

An integer `a` stands for `a / δ`, `δ = 2^64`; a `Disc` `⟨re, im, rad⟩` for the closed disc of
radius `rad/δ` about `(re + i·im)/δ`. `Mem z a` says that `z` lies in it. Each operation of the
checker maps members to members.
-/

open Complex SpeiserCompute

namespace Speiser.Band

/-- `δ = 2^64`. -/
noncomputable def δ : ℝ := ((D : ℤ) : ℝ)

lemma D_pos : (0 : ℤ) < D := by unfold D; positivity

lemma δ_pos : 0 < δ := by unfold δ; exact_mod_cast D_pos

lemma δ_eq : δ = 2 ^ 64 := by unfold δ D; push_cast; ring

/-! ### Integer rounding -/

lemma ediv_le_real (a : ℤ) {b : ℤ} (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

lemma lt_ediv_real (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℤ) : ℝ) + 1 := by
  rw [div_lt_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.lt_ediv_add_one_mul_self a hb

lemma le_cdiv_real (a : ℤ) {b : ℤ} (hb : 0 < b) : (a : ℝ) / b ≤ ((cdiv a b : ℤ) : ℝ) := by
  unfold cdiv
  have h := Int.lt_ediv_add_one_mul_self (a + b - 1) hb
  have h' : a ≤ (a + b - 1) / b * b := by nlinarith
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast h'

lemma fmul_le (a b : ℤ) : ((fmul a b : ℤ) : ℝ) / δ ≤ (a / δ) * (b / δ) := by
  have h : ((a * b / D : ℤ) : ℝ) ≤ ((a * b : ℤ) : ℝ) / δ := ediv_le_real _ D_pos
  calc ((fmul a b : ℤ) : ℝ) / δ ≤ ((a * b : ℤ) : ℝ) / δ / δ :=
        div_le_div_of_nonneg_right h δ_pos.le
    _ = (a / δ) * (b / δ) := by push_cast; ring

lemma lt_fmul (a b : ℤ) : (a / δ) * (b / δ) < ((fmul a b : ℤ) : ℝ) / δ + 1 / δ := by
  have h : ((a * b : ℤ) : ℝ) / δ < ((a * b / D : ℤ) : ℝ) + 1 := lt_ediv_real _ D_pos
  calc (a / δ) * (b / δ) = ((a * b : ℤ) : ℝ) / δ / δ := by push_cast; ring
    _ < (((a * b / D : ℤ) : ℝ) + 1) / δ := div_lt_div_of_pos_right h δ_pos
    _ = _ := by unfold fmul; rw [add_div]

lemma le_fmulUp (a b : ℤ) : (a / δ) * (b / δ) ≤ ((fmulUp a b : ℤ) : ℝ) / δ := by
  have h : ((a * b : ℤ) : ℝ) / δ ≤ ((cdiv (a * b) D : ℤ) : ℝ) := le_cdiv_real _ D_pos
  calc (a / δ) * (b / δ) = ((a * b : ℤ) : ℝ) / δ / δ := by push_cast; ring
    _ ≤ _ := div_le_div_of_nonneg_right h δ_pos.le

lemma iabs_eq (a : ℤ) : ((iabs a : ℤ) : ℝ) = |(a : ℝ)| := by
  unfold iabs
  split_ifs with h
  · rw [abs_of_neg (by exact_mod_cast h)]; push_cast; ring
  · rw [abs_of_nonneg (by exact_mod_cast not_lt.mp h)]

lemma iabs_nonneg (a : ℤ) : 0 ≤ iabs a := by
  unfold iabs; split_ifs with h <;> omega

/-! ### Discs -/

/-- The centre. -/
noncomputable def _root_.SpeiserCompute.Disc.c (a : Disc) : ℂ := ⟨a.re / δ, a.im / δ⟩

/-- Membership. -/
def Mem (z : ℂ) (a : Disc) : Prop := ‖z - a.c‖ ≤ a.rad / δ

lemma norm_c_le (a : Disc) : ‖a.c‖ ≤ (a.l1 : ℝ) / δ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp only [Disc.c, Disc.l1]
  push_cast
  rw [iabs_eq, iabs_eq, abs_div, abs_div, abs_of_pos δ_pos, add_div]

lemma l1_nonneg (a : Disc) : 0 ≤ a.l1 := by
  unfold Disc.l1; have := iabs_nonneg a.re; have := iabs_nonneg a.im; omega

lemma Mem.rad_nonneg {z : ℂ} {a : Disc} (h : Mem z a) : 0 ≤ (a.rad : ℝ) := by
  have := (norm_nonneg _).trans h
  have hδ := δ_pos
  rwa [le_div_iff₀ hδ, zero_mul] at this

lemma norm_le_of_mem {z : ℂ} {a : Disc} (h : Mem z a) : ‖z‖ ≤ ((a.l1 + a.rad : ℤ) : ℝ) / δ := by
  calc ‖z‖ = ‖a.c + (z - a.c)‖ := by ring_nf
    _ ≤ ‖a.c‖ + ‖z - a.c‖ := norm_add_le _ _
    _ ≤ (a.l1 : ℝ) / δ + a.rad / δ := add_le_add (norm_c_le a) h
    _ = _ := by push_cast; ring

lemma mem_pt (x y : ℤ) : Mem (Disc.pt x y).c (Disc.pt x y) := by
  simp [Mem, Disc.pt]

lemma mem_add {z w : ℂ} {a b : Disc} (hz : Mem z a) (hw : Mem w b) : Mem (z + w) (a.add b) := by
  unfold Mem at *
  have hc : (a.add b).c = a.c + b.c := by
    simp only [Disc.c, Disc.add]; apply Complex.ext <;> simp <;> ring
  rw [hc, show z + w - (a.c + b.c) = (z - a.c) + (w - b.c) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [Disc.add]; push_cast; rw [add_div]; exact add_le_add hz hw

lemma mem_neg {z : ℂ} {a : Disc} (hz : Mem z a) : Mem (-z) a.neg := by
  unfold Mem at *
  have hc : a.neg.c = -a.c := by
    simp only [Disc.c, Disc.neg]; apply Complex.ext <;> simp <;> ring
  rw [hc, show -z - -a.c = -(z - a.c) by ring, norm_neg]
  exact hz

lemma mem_sub {z w : ℂ} {a b : Disc} (hz : Mem z a) (hw : Mem w b) : Mem (z - w) (a.sub b) := by
  rw [sub_eq_add_neg]; exact mem_add hz (mem_neg hw)

/-- The rounding error of a product of centres. -/
lemma norm_mul_center_sub (a b : Disc) :
    ‖a.c * b.c - (a.mul b).c‖ ≤ 4 / δ := by
  have hδ := δ_pos
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 := fmul_le a.re b.re
  have e2 := lt_fmul a.re b.re
  have e3 := fmul_le a.im b.im
  have e4 := lt_fmul a.im b.im
  have e5 := fmul_le a.re b.im
  have e6 := lt_fmul a.re b.im
  have e7 := fmul_le a.im b.re
  have e8 := lt_fmul a.im b.re
  simp only [Disc.c, Disc.mul, mul_re, mul_im, sub_re, sub_im]
  push_cast
  rw [sub_div, add_div]
  have h2 : (2 : ℝ) / δ = 1 / δ + 1 / δ := by ring
  have h4 : (4 : ℝ) / δ = 2 / δ + 2 / δ := by ring
  have hr : |a.re / δ * (b.re / δ) - a.im / δ * (b.im / δ) -
      ((fmul a.re b.re : ℝ) / δ - (fmul a.im b.im : ℝ) / δ)| ≤ 2 / δ := by
    rw [abs_le]; constructor <;> nlinarith
  have hi : |a.re / δ * (b.im / δ) + a.im / δ * (b.re / δ) -
      ((fmul a.re b.im : ℝ) / δ + (fmul a.im b.re : ℝ) / δ)| ≤ 2 / δ := by
    rw [abs_le]; constructor <;> nlinarith
  linarith

lemma mem_mul {z w : ℂ} {a b : Disc} (hz : Mem z a) (hw : Mem w b) : Mem (z * w) (a.mul b) := by
  have hδ := δ_pos
  have hra := hz.rad_nonneg
  have hrb := hw.rad_nonneg
  unfold Mem at *
  have key : z * w - (a.mul b).c = (a.c * b.c - (a.mul b).c) + a.c * (w - b.c) +
      b.c * (z - a.c) + (z - a.c) * (w - b.c) := by ring
  rw [key]
  have h1 := norm_mul_center_sub a b
  have h2 : ‖a.c * (w - b.c)‖ ≤ (fmulUp a.l1 b.rad : ℝ) / δ := by
    rw [norm_mul]
    calc ‖a.c‖ * ‖w - b.c‖ ≤ ((a.l1 : ℝ) / δ) * (b.rad / δ) :=
          mul_le_mul (norm_c_le a) hw (norm_nonneg _) (by have := l1_nonneg a; positivity)
      _ ≤ _ := le_fmulUp _ _
  have h3 : ‖b.c * (z - a.c)‖ ≤ (fmulUp b.l1 a.rad : ℝ) / δ := by
    rw [norm_mul]
    calc ‖b.c‖ * ‖z - a.c‖ ≤ ((b.l1 : ℝ) / δ) * (a.rad / δ) :=
          mul_le_mul (norm_c_le b) hz (norm_nonneg _) (by have := l1_nonneg b; positivity)
      _ ≤ _ := le_fmulUp _ _
  have h4 : ‖(z - a.c) * (w - b.c)‖ ≤ (fmulUp a.rad b.rad : ℝ) / δ := by
    rw [norm_mul]
    calc ‖z - a.c‖ * ‖w - b.c‖ ≤ ((a.rad : ℝ) / δ) * (b.rad / δ) :=
          mul_le_mul hz hw (norm_nonneg _) (by positivity)
      _ ≤ _ := le_fmulUp _ _
  calc _ ≤ ‖a.c * b.c - (a.mul b).c‖ + ‖a.c * (w - b.c)‖ + ‖b.c * (z - a.c)‖ +
        ‖(z - a.c) * (w - b.c)‖ := norm_add₄_le
    _ ≤ 4 / δ + (fmulUp a.l1 b.rad : ℝ) / δ + (fmulUp b.l1 a.rad : ℝ) / δ +
        (fmulUp a.rad b.rad : ℝ) / δ := by linarith
    _ = _ := by simp only [Disc.mul]; push_cast; ring

lemma mem_smulInt {z : ℂ} {a : Disc} (k : ℤ) (hz : Mem z a) : Mem ((k : ℂ) * z) (a.smulInt k) := by
  unfold Mem at *
  have hc : (a.smulInt k).c = (k : ℂ) * a.c := by
    simp only [Disc.c, Disc.smulInt]; apply Complex.ext <;> simp <;> ring
  rw [hc, ← mul_sub, norm_mul, Complex.norm_intCast]
  simp only [Disc.smulInt]
  push_cast
  rw [iabs_eq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

lemma mem_divInt {z : ℂ} {a : Disc} {k : ℤ} (hk : 0 < k) (hz : Mem z a) :
    Mem (z / (k : ℂ)) (a.divInt k) := by
  have hδ := δ_pos
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold Mem at *
  have e : ‖z / (k : ℂ) - (a.divInt k).c‖
      ≤ ‖z / (k : ℂ) - a.c / (k : ℂ)‖ + ‖a.c / (k : ℂ) - (a.divInt k).c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  refine e.trans ?_
  have h1 : ‖z / (k : ℂ) - a.c / (k : ℂ)‖ ≤ (a.rad : ℝ) / δ / k := by
    rw [← sub_div, norm_div, Complex.norm_intCast, abs_of_pos hk']
    exact div_le_div_of_nonneg_right hz hk'.le
  have h2 : ‖a.c / (k : ℂ) - (a.divInt k).c‖ ≤ 2 / δ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have r1 := ediv_le_real a.re hk
    have r2 := lt_ediv_real a.re hk
    have i1 := ediv_le_real a.im hk
    have i2 := lt_ediv_real a.im hk
    simp only [Disc.c, Disc.divInt, sub_re, sub_im, div_re, div_im, intCast_re, intCast_im,
      normSq_intCast]
    have hre : |a.re / δ * k / (k * k) - ((a.re / k : ℤ) : ℝ) / δ| ≤ 1 / δ := by
      rw [show a.re / δ * k / (k * k) = (a.re : ℝ) / k / δ by field_simp, ← sub_div, abs_div,
        abs_of_pos hδ]
      exact div_le_div_of_nonneg_right (by rw [abs_le]; constructor <;> linarith) hδ.le
    have him : |a.im / δ * k / (k * k) - ((a.im / k : ℤ) : ℝ) / δ| ≤ 1 / δ := by
      rw [show a.im / δ * k / (k * k) = (a.im : ℝ) / k / δ by field_simp, ← sub_div, abs_div,
        abs_of_pos hδ]
      exact div_le_div_of_nonneg_right (by rw [abs_le]; constructor <;> linarith) hδ.le
    simp only [mul_zero, sub_zero, zero_div, add_zero] at hre him ⊢
    have h2 : (2 : ℝ) / δ = 1 / δ + 1 / δ := by ring
    linarith
  have h3 := le_cdiv_real a.rad hk
  have h4 : (a.rad : ℝ) / δ / k = (a.rad : ℝ) / k / δ := by ring
  simp only [Disc.divInt]
  push_cast
  rw [add_div]
  calc _ ≤ (a.rad : ℝ) / δ / k + 2 / δ := add_le_add h1 h2
    _ ≤ _ := by rw [h4]; gcongr

lemma mem_invPt {x y : ℤ} (h : x * x + y * y ≠ 0) :
    Mem (1 / (Disc.pt x y).c) (Disc.invPt x y) := by
  have hδ := δ_pos
  have hq : (0 : ℤ) < x * x + y * y := lt_of_le_of_ne (by nlinarith) (Ne.symm h)
  have hq' : (0 : ℝ) < (x : ℝ) * x + y * y := by exact_mod_cast hq
  unfold Mem
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have r1 := ediv_le_real (D * D * x) hq
  have r2 := lt_ediv_real (D * D * x) hq
  have i1 := ediv_le_real (D * D * -y) hq
  have i2 := lt_ediv_real (D * D * -y) hq
  simp only [Disc.c, Disc.pt, Disc.invPt, one_div, sub_re, sub_im, inv_re, inv_im, normSq_mk]
  push_cast at r1 r2 i1 i2 ⊢
  have hn : x / δ * (x / δ) + y / δ * (y / δ) = ((x : ℝ) * x + y * y) / δ ^ 2 := by ring
  rw [hn]
  have hre : x / δ / (((x : ℝ) * x + y * y) / δ ^ 2) =
      (D : ℝ) * D * x / ((x : ℝ) * x + y * y) / δ := by
    unfold δ; field_simp
  have him : -(y / δ) / (((x : ℝ) * x + y * y) / δ ^ 2) =
      (D : ℝ) * D * -y / ((x : ℝ) * x + y * y) / δ := by
    unfold δ; field_simp
  rw [hre, him, ← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos hδ]
  have a1 : |(D : ℝ) * D * x / ((x : ℝ) * x + y * y) - ((D * D * x / (x * x + y * y) : ℤ) : ℝ)| ≤ 1 := by
    push_cast; rw [abs_le]; constructor <;> linarith
  have a2 : |(D : ℝ) * D * -y / ((x : ℝ) * x + y * y) - ((D * D * -y / (x * x + y * y) : ℤ) : ℝ)| ≤ 1 := by
    push_cast; rw [abs_le]; constructor <;> linarith
  push_cast at a1 a2
  rw [show (2 : ℝ) / δ = 1 / δ + 1 / δ by ring]
  exact add_le_add (div_le_div_of_nonneg_right a1 hδ.le) (div_le_div_of_nonneg_right a2 hδ.le)

/-! ### `exp` -/

lemma c_pt (x y : ℤ) : (Disc.pt x y).c = ⟨x / δ, y / δ⟩ := rfl

lemma c_pt_D : (Disc.pt D 0).c = 1 := by
  apply Complex.ext <;> simp [c_pt, δ, ne_of_gt D_pos]

lemma mem_of_eq {z : ℂ} {a : Disc} (h : z = a.c) (h0 : 0 ≤ (a.rad : ℝ)) : Mem z a := by
  unfold Mem; rw [h, sub_self, norm_zero]; exact div_nonneg h0 δ_pos.le

lemma fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, ih, Nat.factorial_succ]

lemma mem_taylorStep (wx wy : ℤ) (n : ℕ) :
    Mem ((Disc.pt wx wy).c ^ n / (n.factorial : ℂ)) (taylorStep (Disc.pt wx wy) n).1 ∧
    Mem (∑ i ∈ Finset.range n, (Disc.pt wx wy).c ^ i / (i.factorial : ℂ))
      (taylorStep (Disc.pt wx wy) n).2 := by
  induction n with
  | zero =>
    refine ⟨mem_of_eq (by simp [taylorStep, c_pt_D]) (by simp [taylorStep, Disc.pt]),
      mem_of_eq ?_ (by simp [taylorStep, Disc.pt])⟩
    apply Complex.ext <;> simp [taylorStep, c_pt]
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · have h := mem_divInt (k := ((n + 1 : ℕ) : ℤ)) (by omega) (mem_mul ih.1 (mem_pt wx wy))
      have e : (Disc.pt wx wy).c ^ (n + 1) / ((n + 1).factorial : ℂ) =
          (Disc.pt wx wy).c ^ n / (n.factorial : ℂ) * (Disc.pt wx wy).c /
            ((((n + 1 : ℕ) : ℤ)) : ℂ) := by
        rw [Nat.factorial_succ]; push_cast
        have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        field_simp
        ring
      rw [e]; exact h
    · rw [Finset.sum_range_succ]
      exact mem_add ih.2 ih.1

lemma exp_taylor_rem {wx wy : ℤ} (h : iabs wx + iabs wy ≤ D) :
    ‖Complex.exp (Disc.pt wx wy).c - ∑ m ∈ Finset.range nT,
      (Disc.pt wx wy).c ^ m / (m.factorial : ℂ)‖ ≤ (taylorRem (iabs wx + iabs wy) : ℝ) / δ := by
  have hδ := δ_pos
  have hw : ‖(Disc.pt wx wy).c‖ ≤ ((iabs wx + iabs wy : ℤ) : ℝ) / δ := norm_c_le _
  have hw1 : ‖(Disc.pt wx wy).c‖ ≤ 1 := by
    refine hw.trans ?_
    rw [div_le_one hδ]; unfold δ; exact_mod_cast h
  have hb := Complex.exp_bound hw1 (n := nT) (by decide)
  have hpow : ‖(Disc.pt wx wy).c‖ ^ nT ≤ ‖(Disc.pt wx wy).c‖ :=
    pow_le_of_le_one (norm_nonneg _) hw1 (by decide)
  have hfpos : (0 : ℤ) < ((fact nT * nT : ℕ) : ℤ) := by
    rw [fact_eq]; exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (by decide)
  have hc := le_cdiv_real ((iabs wx + iabs wy) * ((nT + 1 : ℕ) : ℤ)) hfpos
  have hl : (0 : ℝ) ≤ ((iabs wx + iabs wy : ℤ) : ℝ) := by
    have := iabs_nonneg wx; have := iabs_nonneg wy; exact_mod_cast (by omega)
  refine hb.trans ?_
  calc ‖(Disc.pt wx wy).c‖ ^ nT * ((nT.succ : ℝ) * (nT.factorial * nT : ℝ)⁻¹)
      ≤ ((iabs wx + iabs wy : ℤ) : ℝ) / δ * ((nT.succ : ℝ) * (nT.factorial * nT : ℝ)⁻¹) := by
        gcongr; exact hpow.trans hw
    _ = (((iabs wx + iabs wy) * ((nT + 1 : ℕ) : ℤ) : ℤ) : ℝ) /
        (((fact nT * nT : ℕ) : ℤ) : ℝ) / δ := by rw [fact_eq]; push_cast; ring
    _ ≤ ((cdiv ((iabs wx + iabs wy) * ((nT + 1 : ℕ) : ℤ)) ((fact nT * nT : ℕ) : ℤ) : ℤ) : ℝ)
        / δ := div_le_div_of_nonneg_right hc hδ.le
    _ ≤ (taylorRem (iabs wx + iabs wy) : ℝ) / δ := by
        unfold taylorRem; gcongr; push_cast; linarith

lemma mem_expSmall {wx wy : ℤ} (h : iabs wx + iabs wy ≤ D) (S : Disc)
    (hS : Mem (∑ m ∈ Finset.range nT, (Disc.pt wx wy).c ^ m / (m.factorial : ℂ)) S) :
    Mem (Complex.exp (Disc.pt wx wy).c) ⟨S.re, S.im, S.rad + taylorRem (iabs wx + iabs wy)⟩ := by
  have hb := exp_taylor_rem h
  unfold Mem at hS ⊢
  have hc : (⟨S.re, S.im, S.rad + taylorRem (iabs wx + iabs wy)⟩ : Disc).c = S.c := rfl
  rw [hc]
  calc _ ≤ ‖Complex.exp (Disc.pt wx wy).c - ∑ m ∈ Finset.range nT,
          (Disc.pt wx wy).c ^ m / (m.factorial : ℂ)‖ +
        ‖∑ m ∈ Finset.range nT, (Disc.pt wx wy).c ^ m / (m.factorial : ℂ) - S.c‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (taylorRem (iabs wx + iabs wy) : ℝ) / δ + S.rad / δ := add_le_add hb hS
    _ = _ := by push_cast; ring

lemma mem_sq {z : ℂ} {a : Disc} (h : Mem z a) (k : ℕ) :
    Mem (z ^ (2 ^ k)) (SpeiserCompute.sq a k) := by
  induction k with
  | zero => simpa [SpeiserCompute.sq] using h
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) = z ^ (2 ^ k) * z ^ (2 ^ k) := by
      rw [pow_succ, pow_mul, _root_.sq]
    rw [e]
    exact mem_mul ih ih

lemma ediv_bounds (a : ℤ) {p : ℤ} (hp : 0 < p) :
    (0 : ℝ) ≤ a - p * (a / p : ℤ) ∧ (a : ℝ) - p * (a / p : ℤ) ≤ p := by
  have h1 := Int.ediv_mul_le a hp.ne'
  have h2 := Int.lt_ediv_add_one_mul_self a hp
  constructor
  · have : p * (a / p) ≤ a := by linarith [mul_comm p (a / p)]
    have : ((p * (a / p) : ℤ) : ℝ) ≤ a := by exact_mod_cast this
    push_cast at this; linarith
  · have : a - p * (a / p) ≤ p := by nlinarith [mul_comm p (a / p)]
    have : ((a - p * (a / p) : ℤ) : ℝ) ≤ p := by exact_mod_cast this
    push_cast at this; linarith

lemma mem_expDisc {z : ℂ} {a : Disc} (hz : Mem z a) (hok : expOK a = true) :
    Mem (Complex.exp z) (expDisc a) := by
  have hδ := δ_pos
  unfold expOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h1, h2⟩ := hok
  have hp : (0 : ℤ) < 2 ^ nSq := by positivity
  have hpr : (0 : ℝ) < ((2 ^ nSq : ℤ) : ℝ) := by exact_mod_cast hp
  have hE := mem_expSmall h1 _ (mem_taylorStep (a.re / (2 ^ nSq : ℤ)) (a.im / (2 ^ nSq : ℤ)) nT).2
  have hsq := mem_sq hE nSq
  set w := (Disc.pt (a.re / (2 ^ nSq : ℤ)) (a.im / (2 ^ nSq : ℤ))).c with hw
  have hexp : Complex.exp w ^ (2 ^ nSq) = Complex.exp (((2 ^ nSq : ℕ) : ℂ) * w) :=
    (Complex.exp_nat_mul w _).symm
  obtain ⟨r1, r2⟩ := ediv_bounds a.re hp
  obtain ⟨i1, i2⟩ := ediv_bounds a.im hp
  have hc : ‖a.c - ((2 ^ nSq : ℕ) : ℂ) * w‖ ≤ ((2 * 2 ^ nSq : ℤ) : ℝ) / δ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have ere : (a.c - ((2 ^ nSq : ℕ) : ℂ) * w).re =
        ((a.re : ℝ) - ((2 ^ nSq : ℤ) : ℝ) * ((a.re / (2 ^ nSq : ℤ) : ℤ) : ℝ)) / δ := by
      simp only [hw, Disc.c, Disc.pt, sub_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
      push_cast; ring
    have eim : (a.c - ((2 ^ nSq : ℕ) : ℂ) * w).im =
        ((a.im : ℝ) - ((2 ^ nSq : ℤ) : ℝ) * ((a.im / (2 ^ nSq : ℤ) : ℤ) : ℝ)) / δ := by
      simp only [hw, Disc.c, Disc.pt, sub_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero]
      push_cast; ring
    rw [ere, eim, abs_div, abs_div, abs_of_pos hδ, abs_of_nonneg r1, abs_of_nonneg i1,
      ← add_div]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    push_cast at r2 i2 ⊢
    linarith
  have hdist : ‖z - ((2 ^ nSq : ℕ) : ℂ) * w‖ ≤ ((a.rad + 2 * 2 ^ nSq : ℤ) : ℝ) / δ := by
    unfold Mem at hz
    calc ‖z - ((2 ^ nSq : ℕ) : ℂ) * w‖ ≤ ‖z - a.c‖ + ‖a.c - ((2 ^ nSq : ℕ) : ℂ) * w‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ a.rad / δ + ((2 * 2 ^ nSq : ℤ) : ℝ) / δ := add_le_add hz hc
      _ = _ := by push_cast; ring
  have hu1 : ‖z - ((2 ^ nSq : ℕ) : ℂ) * w‖ ≤ 1 := by
    refine hdist.trans ?_
    rw [div_le_one hδ]; unfold δ; exact_mod_cast h2
  have hrem : Mem (Complex.exp (z - ((2 ^ nSq : ℕ) : ℂ) * w))
      ⟨D, 0, 2 * (a.rad + 2 * 2 ^ nSq)⟩ := by
    unfold Mem
    have hc1 : (⟨D, 0, 2 * (a.rad + 2 * 2 ^ nSq)⟩ : Disc).c = 1 := c_pt_D
    rw [hc1]
    refine (Complex.norm_exp_sub_one_le hu1).trans ?_
    have := mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * ‖z - ((2 ^ nSq : ℕ) : ℂ) * w‖ ≤ 2 * (((a.rad + 2 * 2 ^ nSq : ℤ) : ℝ) / δ) := this
      _ = _ := by push_cast; ring
  have hsplit : Complex.exp z = Complex.exp w ^ (2 ^ nSq) *
      Complex.exp (z - ((2 ^ nSq : ℕ) : ℂ) * w) := by
    rw [hexp, ← Complex.exp_add]; ring_nf
  rw [hsplit]
  exact mem_mul hsq hrem

end Speiser.Band
