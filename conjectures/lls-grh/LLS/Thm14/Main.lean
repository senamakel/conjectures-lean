import LLS.Thm14.Elim
import LLS.Statement

/-!
# LLS Theorem 1.4 under GRH, with the paper's bound

For `q ≥ 20000`, a subgroup `H` of index `h > 1` and a coset `aH`, let
`B = (h − 1) log q + 3(h + 1) + (5/2)(log log q)²`, `s = max(31622, ⌊B⌋)` and `X = s²`. If no
prime `p ≤ X` lay in `aH`, `LLS.Thm14.main_ineq` (orthogonality over the characters trivial on
`H`, the explicit formulas for each of them, and the square-prime-power bound) and
`LLS.Thm14.reduce` with `LLS.Thm14.star_small` / `LLS.Thm14.star_large` contradict each other.
Since `X ≤ 31622² < 10⁹` or `X ≤ B²`, the least prime in `aH` is `≤ 10⁹` or `≤ B²`. No finite
computation over `q` or `h` is needed.
-/

namespace LLS.Thm14

open Real Finset

/-- `ω(q) ≤ 10 + log q / log 30`: at most ten prime factors below `30`, the rest are `≥ 30`. -/
lemma omega_le (q : ℕ) (hq : q ≠ 0) :
    (q.primeFactors.card : ℝ) ≤ 10 + Real.log q / Real.log 30 := by
  classical
  set S1 := q.primeFactors.filter (· < 30)
  set S2 := q.primeFactors.filter (fun p => ¬ p < 30)
  have hsplit : q.primeFactors.card = S1.card + S2.card :=
    (card_filter_add_card_filter_not _).symm
  have h1 : S1.card ≤ 10 := by
    have : S1 ⊆ (range 30).filter Nat.Prime := fun p hp => by
      simp only [S1, mem_filter, Nat.mem_primeFactors] at hp
      simp only [mem_filter, mem_range]
      exact ⟨hp.2, hp.1.1⟩
    exact (card_le_card this).trans (by decide)
  have h2 : 30 ^ S2.card ≤ q := by
    have hp : 30 ^ S2.card ≤ ∏ p ∈ S2, p :=
      Finset.pow_card_le_prod _ _ _ fun p hp => not_lt.1 (mem_filter.1 hp).2
    have hd : ∏ p ∈ S2, p ∣ q :=
      (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd q)
    exact hp.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hd)
  have hlog30 : 0 < Real.log 30 := Real.log_pos (by norm_num)
  have h2' : (S2.card : ℝ) * Real.log 30 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h2)
  have : (S2.card : ℝ) ≤ Real.log q / Real.log 30 := by rw [le_div_iff₀ hlog30]; exact h2'
  rw [hsplit]; push_cast
  have : (S1.card : ℝ) ≤ 10 := by exact_mod_cast h1
  linarith

lemma llp_le_two (s : ℕ) (hs : 31622 ≤ s) (p : ℕ) (hp : p.Prime) :
    llp (s ^ 2) p ≤ (Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 2 / 2) ^ 2 / 2 := by
  have hl := logX_ge hs
  have hX : 1 ≤ s ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
  rcases lt_or_ge (s ^ 2) p with h | h
  · rw [llp_eq_zero hp h]; positivity
  · refine (llp_le _ p hp hX).trans ?_
    have h2p : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    have hpX : Real.log p ≤ Real.log ((s ^ 2 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h)
    have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log p / 2 := by linarith
    have : Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log p / 2
        ≤ Real.log ((s ^ 2 : ℕ) : ℝ) - Real.log 2 / 2 := by linarith
    have := pow_le_pow_left₀ (by linarith) this 2
    linarith

lemma psiU_nonneg {y : ℝ} (hy : 1 ≤ y) : 0 ≤ psiU y := by
  unfold psiU
  have := Real.log_nonneg hy
  positivity

lemma Pc_nonneg {L S l : ℝ} (hS : 31622 ≤ S) (hL : 9.9 ≤ L) (hl : 0 ≤ l) : 0 ≤ Pc L S l := by
  unfold Pc
  obtain ⟨hA1, -⟩ := Acoef_bounds hS
  have hsq : 1 / S ^ 2 ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsq0 : 0 ≤ 1 / S ^ 2 := by positivity
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hin : 0 ≤ (1 - 1 / S ^ 2) * L - 1.72 + Real.log 2 * (1 + 1 / S ^ 2)
      + Real.log 3 / S ^ 2 := by
    have : 9.8 ≤ (1 - 1 / S ^ 2) * L := by nlinarith
    have : 0 ≤ Real.log 2 * (1 + 1 / S ^ 2) := by positivity
    have : 0 ≤ Real.log 3 / S ^ 2 := by positivity
    linarith
  have hmax : 0 ≤ max (L - 3) (l + 2) := le_max_of_le_right (by linarith)
  have := mul_nonneg (show 0 ≤ Acoef S by linarith) hin
  have := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) hl) hmax
  have : 0 ≤ (0.627 * L + 5.93) * l := mul_nonneg (by linarith) hl
  positivity

/-- **LLS Theorem 1.4 under GRH.** -/
theorem leastPrimeInCoset_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    LeastPrimeInCoset := by
  intro q hq H hH a
  have : NeZero q := ⟨by omega⟩
  have hq0 : q ≠ 0 := by omega
  set L := Real.log q with hLdef
  have hL : 9.9 ≤ L := by
    have := log_ge_nat (y := (q : ℝ)) (X := 20000) (k := 14630) (by exact_mod_cast hq)
      (by decide +kernel) (by norm_num)
    linarith
  set u := H.index - 1 with hudef
  have hu : 1 ≤ u := by omega
  have hucast : (u : ℝ) = (H.index : ℝ) - 1 := by
    rw [hudef, Nat.cast_sub (by omega)]; simp
  set B := Bf u L with hBdef
  have hBeq : B = ((H.index - 1 : ℝ) * Real.log q + 3 * (H.index + 1 : ℝ)
      + 5 / 2 * Real.log (Real.log q) ^ 2) := by
    rw [hBdef]; unfold Bf; rw [hucast]; ring
  have hB0 : 0 ≤ B := by
    unfold B Bf; have := sq_nonneg (Real.log L)
    have : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    nlinarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = max 31622 ⌊B⌋₊ := ⟨_, rfl⟩
  have hs : 31622 ≤ s := hsdef ▸ le_max_left _ _
  have hsR : (31622 : ℝ) ≤ s := by exact_mod_cast hs
  obtain ⟨N, hNdef⟩ : ∃ N, N = s * 7072 / 10000 + 1 := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hNdef]; exact Nat.le_add_left 1 _
  obtain ⟨d, hd⟩ : ∃ d, d = s * 7072 / 10000 := ⟨_, rfl⟩
  have hd1 : d * 10000 ≤ s * 7072 := hd ▸ Nat.div_mul_le_self (s * 7072) 10000
  have hd2 : s * 7072 < (d + 1) * 10000 := by
    rw [hd, Nat.add_mul, one_mul]
    exact Nat.lt_div_mul_add (by norm_num)
  have hNd : N = d + 1 := by rw [hNdef, hd]
  have hN' : 10000 * N ≤ 7072 * s + 10000 := by rw [hNd]; linarith
  have hN : s ^ 2 ≤ 2 * N ^ 2 := by
    rw [hNd]
    have h7 : 7072 * s ≤ 10000 * (d + 1) := by linarith
    have : (7072 * s) ^ 2 ≤ (10000 * (d + 1)) ^ 2 := Nat.pow_le_pow_left h7 2
    nlinarith
  by_contra hcon
  have hno : ∀ p ≤ s ^ 2, p.Prime → ∀ hp : p.Coprime q, a⁻¹ * ZMod.unitOfCoprime p hp ∉ H := by
    intro p hps hpr hc hmem
    apply hcon
    refine ⟨p, hpr, hc, hmem, ?_⟩
    rcases le_total ⌊B⌋₊ 31622 with h | h
    · left
      have : s = 31622 := by rw [hsdef]; exact max_eq_left h
      have : p ≤ 10 ^ 9 := by rw [this] at hps; omega
      exact_mod_cast this
    · right
      have hse : s = ⌊B⌋₊ := by rw [hsdef]; exact max_eq_right h
      have hsB : (s : ℝ) ≤ B := by rw [hse]; exact Nat.floor_le hB0
      have : (p : ℝ) ≤ (s : ℝ) ^ 2 := by exact_mod_cast hps
      rw [← hBeq]
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      have : (s : ℝ) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hs0 hsB 2
      linarith
  have hmain := main_ineq hGRH H a s N hs hN hno
  -- the pieces
  set l := Real.log ((s ^ 2 : ℕ) : ℝ)
  have hl := logX_ge hs
  have hllp : ∑ p ∈ q.primeFactors, llp (s ^ 2) p
      ≤ (q.primeFactors.card : ℝ) * ((l - Real.log 2 / 2) ^ 2 / 2) := by
    rw [← nsmul_eq_mul]
    refine (sum_le_sum fun p hp => llp_le_two s hs p (Nat.prime_of_mem_primeFactors hp)).trans ?_
    rw [sum_const]
  have hω := omega_le q hq0
  rw [← hLdef] at hω
  have hP2 := LLS.Sharp.P2sum_le_sharp (LLS.psi1NatBound_of_GRH hGRH) (s ^ 2) (by nlinarith)
  have hm : ((Htil H).card : ℝ) ≤ u + 1 := by
    have := card_Htil_le H
    rw [hucast]; push_cast
    have : ((Htil H).card : ℝ) ≤ H.index := by exact_mod_cast this
    linarith
  have hm1 : (1 : ℝ) ≤ (Htil H).card := by exact_mod_cast card_pos.2 ⟨1, one_mem_Htil H⟩
  have hT0 : 0 ≤ 2 * psiU s + 2 * psiU N := by
    have := psiU_nonneg (y := (s : ℝ)) (by linarith)
    have := psiU_nonneg (y := (N : ℝ)) (by exact_mod_cast hN1)
    linarith
  have hPc0 : 0 ≤ Pc L s l := Pc_nonneg hsR hL (by linarith)
  have hk1 := mul_le_mul_of_nonneg_right hm hT0
  have hk2 := mul_le_mul_of_nonneg_right (show ((Htil H).card : ℝ) - 1 ≤ u by linarith) hPc0
  obtain ⟨hA1, -⟩ := Acoef_bounds hsR
  have hk3 := mul_le_mul_of_nonneg_left hP2 (show 0 ≤ 2 * Acoef s by linarith)
  -- `uL ≤ s` and `(★)`
  have hBu : (u : ℝ) * L + 6 ≤ B := by
    unfold B Bf; have := sq_nonneg (Real.log L)
    have : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    nlinarith
  have hfl := Nat.lt_floor_add_one B
  rcases lt_or_ge B 31622 with hBs | hBs
  · have hfB : ⌊B⌋₊ ≤ 31622 := by
      have : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB0
      have : (⌊B⌋₊ : ℝ) < 31622 := by linarith
      exact_mod_cast this.le
    have hs31 : s = 31622 := by rw [hsdef]; exact max_eq_left hfB
    have huL : (u : ℝ) * L ≤ s := by rw [hs31]; push_cast; linarith
    have hstar := star_small u L (by exact_mod_cast hu) hL hBs
    rw [← hs31] at hstar
    have hred := reduce s N u hs hN' hN1 hu L hL huL _ hω hstar
    linarith
  · have hfB : 31622 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hBs)
    have hse : s = ⌊B⌋₊ := by rw [hsdef]; exact max_eq_right hfB
    have hsB : (s : ℝ) ≤ B := by rw [hse]; exact Nat.floor_le hB0
    have hsB1 : B - 1 < s := by rw [hse]; linarith
    have huL : (u : ℝ) * L ≤ s := by linarith
    have hstar := star_large u L s (by exact_mod_cast hu) hL hBs hsB1 hsB
    have hred := reduce s N u hs hN' hN1 hu L hL huL _ hω hstar
    linarith

end LLS.Thm14
