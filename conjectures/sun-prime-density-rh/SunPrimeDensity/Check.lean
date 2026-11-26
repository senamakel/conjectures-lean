import SunPrimeDensity.Analytic
import Schoenfeld.Check.Pi

/-!
# The finite range `n^k < 10¹⁰`: a proved-sound checker

Every pair `(k, n)` with `k ≥ 4`, `n ≥ 2`, `n^k < 10¹⁰` (there are 565) is checked by `allOK`,
evaluated once with `native_decide`:

* if `(n+1)^k ≤ 41⁴ = 2825761` (83 pairs), exactly: `π(n^k)` and `π((n+1)^k)` are read from
  `piTable` (79 values), and `π((n+1)^k) · n^k < π(n^k) · (n+1)^k` is checked in `ℕ`. The table
  itself is verified by `chainOK`, which recounts the primes up to `2825761` with schoenfeld-rh's
  `cntLoop` (trial division by `Nat.minFac`; `cntLoop_eq` is its soundness lemma);
* otherwise (482 pairs, all with `n^k ≥ 2657`) analytically, by the criterion of
  `ratio_lt_of_bounds`, with rational upper bounds for the error terms and a rational lower
  bound for `li(x) − x/log x`. The error term at `t` is `piErrMid t` (PsiCert) on
  `[4·10⁵, 10¹⁰]` and Schoenfeld's `√t log t/(8π)` elsewhere. Logarithms and square roots
  come with schoenfeld-rh's enclosures `logLo`, `logUp`, `sqrtLo` and their soundness lemmas;
  `sqrtUp` is added here.

`allOK_sound` turns `allOK = true` into the inequality for every such pair.
-/

namespace SunPrimeDensity.Check

open Real Schoenfeld Schoenfeld.Check

/-! ### Exact prime counts -/

/-- `chainOK a c L`: starting from `c = π(a)`, every entry `(b, d)` of `L` has `d = π(b)`,
checked by counting the primes in `(a, b]` with `cntLoop`. -/
def chainOK : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, _, [] => true
  | a, c, (b, d) :: rest => decide (a ≤ b) && cntLoop (b - a) (a + 1) c == d && chainOK b d rest

theorem chainOK_sound : ∀ (L : List (ℕ × ℕ)) (a c : ℕ), c = Nat.primeCounting a →
    chainOK a c L = true → ∀ p ∈ L, Nat.primeCounting p.1 = p.2 := by
  intro L
  induction L with
  | nil => intro a c _ _ p hp; simp at hp
  | cons q L ih =>
    obtain ⟨b, d⟩ := q
    intro a c hc h p hp
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hab, hcnt⟩, hrest⟩ := h
    have hd : d = Nat.primeCounting b := by
      rw [← hcnt, cntLoop_eq (b - a) a c hc, Nat.add_sub_cancel' hab]
    rcases List.mem_cons.mp hp with h1 | h1
    · rw [h1]; exact hd.symm
    · exact ih b d hd hrest p h1

/-- `π` at the 79 points `n^k`, `(n+1)^k` of the exactly checked pairs. -/
def piTable : List (ℕ × ℕ) := [
  (16, 6), (32, 11), (64, 18), (81, 22), (128, 31), (243, 53),
  (256, 54), (512, 97), (625, 114), (729, 129), (1024, 172), (1296, 210),
  (2048, 309), (2187, 327), (2401, 357), (3125, 445), (4096, 564), (6561, 847),
  (7776, 985), (8192, 1028), (10000, 1229), (14641, 1715), (15625, 1821), (16384, 1900),
  (16807, 1939), (19683, 2227), (20736, 2334), (28561, 3107), (32768, 3512), (38416, 4052),
  (46656, 4821), (50625, 5191), (59049, 5968), (65536, 6542), (78125, 7671), (83521, 8152),
  (100000, 9592), (104976, 10022), (117649, 11098), (130321, 12187), (160000, 14683), (161051, 14773),
  (177147, 16097), (194481, 17531), (234256, 20768), (248832, 21950), (262144, 23000), (279841, 24421),
  (279936, 24427), (331776, 28546), (371293, 31616), (390625, 33118), (456976, 38236), (531441, 43934),
  (537824, 44413), (614656, 50203), (707281, 57097), (759375, 60927), (810000, 64683), (823543, 65685),
  (923521, 72992), (1000000, 78498), (1048576, 82025), (1185921, 91932), (1336336, 102588), (1419857, 108479),
  (1500625, 114204), (1594323, 120739), (1679616, 126726), (1771561, 133083), (1874161, 140235), (1889568, 141315),
  (1953125, 145713), (2085136, 154787), (2097152, 155611), (2313441, 170426), (2476099, 181449), (2560000, 187134),
  (2825761, 205143)]

theorem chainOK_piTable : chainOK 0 0 piTable = true := by native_decide

theorem piTable_sound {a b : ℕ} (h : (a, b) ∈ piTable) : Nat.primeCounting a = b :=
  chainOK_sound piTable 0 0 (by simp) chainOK_piTable (a, b) h

theorem mem_of_lookup_eq_some : ∀ (L : List (ℕ × ℕ)) (a b : ℕ), L.lookup a = some b → (a, b) ∈ L
  | [], a, b, h => by simp [List.lookup] at h
  | (k, v) :: L, a, b, h => by
    by_cases hak : a = k
    · subst hak
      simp [List.lookup] at h
      subst h; exact List.mem_cons_self
    · have : (a == k) = false := by simpa using hak
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some L a b h)

/-- The exact comparison `π(y) · x < π(x) · y`, from the table. -/
def exactOK (x y : ℕ) : Bool :=
  match piTable.lookup x, piTable.lookup y with
  | some px, some py => decide (py * x < px * y)
  | _, _ => false

theorem exactOK_sound {x y : ℕ} (h : exactOK x y = true) :
    Nat.primeCounting y * x < Nat.primeCounting x * y := by
  unfold exactOK at h
  split at h
  · rename_i px py hx hy
    rw [piTable_sound (mem_of_lookup_eq_some _ _ _ hx),
      piTable_sound (mem_of_lookup_eq_some _ _ _ hy)]
    exact of_decide_eq_true h
  · exact absurd h (by simp)

/-! ### Rational error terms -/

/-- Upper bound for `√q`. -/
def sqrtUp (q : ℚ) : ℚ := ((Nat.sqrt ⌊q * 4 ^ 32⌋₊ : ℚ) + 1) / 2 ^ 32

lemma le_sqrtUp {q : ℚ} (_hq : 0 ≤ q) : √(q : ℝ) ≤ (sqrtUp q : ℝ) := by
  set m := ⌊q * 4 ^ 32⌋₊
  set s := Nat.sqrt m
  have hm : q * 4 ^ 32 < m + 1 := Nat.lt_floor_add_one _
  have hs : m < (s + 1) * (s + 1) := Nat.lt_succ_sqrt m
  have hs' : ((m : ℕ) : ℚ) + 1 ≤ ((s : ℚ) + 1) ^ 2 := by
    have : m + 1 ≤ (s + 1) * (s + 1) := hs
    have : ((m + 1 : ℕ) : ℚ) ≤ (((s + 1) * (s + 1) : ℕ) : ℚ) := by exact_mod_cast this
    push_cast at this; nlinarith
  have hq' : q ≤ (((s : ℚ) + 1) / 2 ^ 32) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have : ((2 : ℚ) ^ 32) ^ 2 = 4 ^ 32 := by norm_num
    rw [this]; linarith
  have hqR : (q : ℝ) ≤ (((s : ℝ) + 1) / 2 ^ 32) ^ 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hq'
    push_cast at this; exact this
  unfold sqrtUp
  push_cast
  rw [← Real.sqrt_sq (show (0 : ℝ) ≤ ((s : ℝ) + 1) / 2 ^ 32 by positivity)]
  exact Real.sqrt_le_sqrt hqR

/-- `π > 3.141592` (`Real.pi_gt_d6`). -/
def piLo : ℚ := 3141592 / 10 ^ 6

/-- Schoenfeld's `√t log t/(8π)`, rounded up. -/
def EschQ (t : ℚ) : ℚ := sqrtUp t * logUp t / (8 * piLo)

/-- `piErrMid t`, rounded up. -/
def EmidQ (t : ℚ) : ℚ :=
  3.9252 * (sqrtUp t * invUp (logLo t)) + 49.886
    + 3.9252 * (10.15 / (10.15 - 4) * (2 * sqrtUp t * invUp (logLo t) ^ 2))

/-- The error term used at `t`. -/
def EQ (t : ℚ) : ℚ := if 400000 ≤ t ∧ t ≤ 10 ^ 10 ∧ 0 < logLo t then EmidQ t else EschQ t

/-- Lower bound for `li(x) − x/log x`. -/
def DlQ (x : ℚ) : ℚ := (x - 2) * invLo (logUp x) ^ 2 - 2.886

lemma abs_sub_le_EQ (hS : SchoenfeldPi) {t : ℕ} (ht : 2657 ≤ t) :
    |(Nat.primeCounting t : ℝ) - logIntegral t| ≤ ((EQ (t : ℚ) : ℚ) : ℝ) := by
  have htR : (2657 : ℝ) ≤ t := by exact_mod_cast ht
  have htQ : (1 : ℚ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hfl : ⌊(t : ℝ)⌋₊ = t := Nat.floor_natCast _
  have hlog0 : 0 < Real.log t := Real.log_pos (by linarith)
  have hsq := le_sqrtUp (show (0 : ℚ) ≤ t by positivity)
  have hlu := le_logUp htQ
  have hll := logLo_le htQ
  push_cast at hsq hlu hll
  unfold EQ
  split_ifs with hmid
  · -- `4·10⁵ ≤ t ≤ 10¹⁰`: the PsiCert bound
    obtain ⟨h1, h2, hlo_pos⟩ := hmid
    have h1R : (400000 : ℝ) ≤ t := by exact_mod_cast h1
    have h2R : (t : ℝ) ≤ 10 ^ 10 := by exact_mod_cast h2
    have hm := pi_mid_explicit psiCert thetaSmallRange h1R h2R
    rw [hfl] at hm
    refine hm.trans ?_
    have hinv : 1 / Real.log t ≤ (invUp (logLo (t : ℚ)) : ℝ) := one_div_le_invUp hlo_pos hll
    have hsq0 : 0 ≤ √(t : ℝ) := Real.sqrt_nonneg _
    have hi0 : 0 ≤ 1 / Real.log t := by positivity
    have hA : √(t : ℝ) / Real.log t ≤ (sqrtUp (t : ℚ) : ℝ) * (invUp (logLo (t : ℚ)) : ℝ) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul hsq hinv hi0 (hsq0.trans hsq)
    have hB : 2 * √(t : ℝ) / Real.log t ^ 2
        ≤ 2 * (sqrtUp (t : ℚ) : ℝ) * (invUp (logLo (t : ℚ)) : ℝ) ^ 2 := by
      have e : 2 * √(t : ℝ) / Real.log t ^ 2 = 2 * √(t : ℝ) * (1 / Real.log t) ^ 2 := by
        field_simp
      rw [e]
      have : (1 / Real.log t) ^ 2 ≤ (invUp (logLo (t : ℚ)) : ℝ) ^ 2 :=
        pow_le_pow_left₀ hi0 hinv 2
      exact mul_le_mul (by linarith) this (by positivity) (by linarith)
    unfold piErrMid EmidQ
    push_cast
    nlinarith
  · have h := hS t htR
    rw [hfl] at h
    refine h.le.trans ?_
    unfold EschQ piLo
    push_cast
    have hpi := Real.pi_gt_d6
    have hsq0 : 0 ≤ √(t : ℝ) := Real.sqrt_nonneg _
    have hA : √(t : ℝ) * Real.log t ≤ (sqrtUp (t : ℚ) : ℝ) * (logUp (t : ℚ) : ℝ) :=
      mul_le_mul hsq hlu hlog0.le (hsq0.trans hsq)
    have hB : 1 / (8 * π) ≤ 1 / (8 * (3141592 / 10 ^ 6 : ℝ)) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    calc 1 / (8 * π) * (√(t : ℝ) * Real.log t)
        ≤ 1 / (8 * (3141592 / 10 ^ 6 : ℝ)) * ((sqrtUp (t : ℚ) : ℝ) * (logUp (t : ℚ) : ℝ)) :=
          mul_le_mul hB hA (by positivity) (by positivity)
      _ = _ := by ring

/-! ### The pairs -/

/-- The analytic check of the pair `(k, n)`: `x = n^k ≥ 2657` and
`EQ(x)/x + EQ(y)/y < (1 − x/y) · DlQ(x)/x` with `y = (n+1)^k`. -/
def pairOK (k n : ℕ) : Bool :=
  let x : ℚ := (n : ℚ) ^ k
  let y : ℚ := ((n : ℚ) + 1) ^ k
  decide (2657 ≤ x) && decide (0 ≤ invLo (logUp x)) &&
    decide (EQ x / x + EQ y / y < (1 - x / y) * DlQ x / x)

theorem pairOK_sound (hS : SchoenfeldPi) {k n : ℕ} (hk : 1 ≤ k) (h : pairOK k n = true) :
    (Nat.primeCounting ((n + 1) ^ k) : ℝ) / (((n : ℝ) + 1) ^ k) <
      (Nat.primeCounting (n ^ k) : ℝ) / ((n : ℝ) ^ k) := by
  simp only [pairOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hxN : 2657 ≤ n ^ k := by exact_mod_cast h1
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; rw [zero_pow (by omega)] at hxN; omega
    · exact h0
  have hyN : 2657 ≤ (n + 1) ^ k := hxN.trans (Nat.pow_le_pow_left (by omega) k)
  have hEx := abs_sub_le_EQ hS hxN
  have hEy := abs_sub_le_EQ hS hyN
  push_cast at hEx hEy
  set x : ℝ := (n : ℝ) ^ k with hxdef
  set y : ℝ := ((n : ℝ) + 1) ^ k with hydef
  have hx2657 : (2657 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hxN
  have hxy : x < y := by
    rw [hxdef, hydef]
    exact pow_lt_pow_left₀ (by linarith) (by positivity) (by omega)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hxQ : (1 : ℚ) ≤ (n : ℚ) ^ k := by linarith
  have hlu := le_logUp hxQ
  push_cast at hlu
  have hinv : (invLo (logUp ((n : ℚ) ^ k)) : ℝ) ≤ 1 / Real.log x := invLo_le_one_div hlx hlu
  have hinv0 : (0 : ℝ) ≤ (invLo (logUp ((n : ℚ) ^ k)) : ℝ) := by exact_mod_cast h2
  have hD : ((DlQ ((n : ℚ) ^ k) : ℚ) : ℝ) ≤ logIntegral x - x / Real.log x := by
    refine le_trans ?_ (logIntegral_sub_ge (by linarith))
    unfold DlQ
    push_cast
    have : (invLo (logUp ((n : ℚ) ^ k)) : ℝ) ^ 2 ≤ (1 / Real.log x) ^ 2 :=
      pow_le_pow_left₀ hinv0 hinv 2
    have e : (x - 2) / Real.log x ^ 2 = (x - 2) * (1 / Real.log x) ^ 2 := by field_simp
    rw [e]
    have hx2 : 0 ≤ x - 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hx2]
  have hkey := (Rat.cast_lt (K := ℝ)).mpr h3
  push_cast at hkey
  exact ratio_lt_of_bounds (by linarith) hxy hEx hEy hD hkey

/-- Every pair `(k, n)` with `4 ≤ k ≤ 33`, `2 ≤ n ≤ 316` and `n^k < 10¹⁰`: exactly when
`(n+1)^k ≤ 41⁴`, analytically otherwise. -/
def allOK : Bool :=
  (List.range 30).all fun i => (List.range 315).all fun j =>
    !(decide ((j + 2) ^ (i + 4) < 10 ^ 10)) ||
      (if (j + 3) ^ (i + 4) ≤ 2825761 then exactOK ((j + 2) ^ (i + 4)) ((j + 3) ^ (i + 4))
       else pairOK (i + 4) (j + 2))

theorem allOK_eq_true : allOK = true := by native_decide

/-- **The finite range.** For `k ≥ 4`, `n ≥ 2` and `n^k < 10¹⁰`,
`π((n+1)^k)/(n+1)^k < π(n^k)/n^k`, given Schoenfeld's bound (used only above `2657`). -/
theorem finite_range (hS : SchoenfeldPi) {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ≤ n)
    (hx : n ^ k < 10 ^ 10) :
    (Nat.primeCounting ((n + 1) ^ k) : ℝ) / (((n : ℝ) + 1) ^ k) <
      (Nat.primeCounting (n ^ k) : ℝ) / ((n : ℝ) ^ k) := by
  have hk33 : k ≤ 33 := by
    by_contra hc; push Not at hc
    have : 2 ^ 34 ≤ n ^ k :=
      (Nat.pow_le_pow_right (by norm_num) hc).trans (Nat.pow_le_pow_left hn k)
    omega
  have hn316 : n ≤ 316 := by
    by_contra hc; push Not at hc
    have : 317 ^ 4 ≤ n ^ k :=
      (Nat.pow_le_pow_left hc 4).trans (Nat.pow_le_pow_right (by omega) hk)
    omega
  have h := allOK_eq_true
  simp only [allOK, List.all_eq_true, List.mem_range] at h
  have hij := h (k - 4) (by omega) (n - 2) (by omega)
  rw [show k - 4 + 4 = k by omega, show n - 2 + 2 = n by omega,
    show n - 2 + 3 = n + 1 by omega] at hij
  simp only [hx, decide_true, Bool.not_true, Bool.false_or] at hij
  split_ifs at hij with hy
  · have hlt := exactOK_sound hij
    have hx0 : (0 : ℝ) < (n : ℝ) ^ k := by positivity
    have hy0 : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
    rw [div_lt_div_iff₀ hy0 hx0]
    have := (Nat.cast_lt (α := ℝ)).mpr hlt
    push_cast at this
    linarith
  · exact pairOK_sound hS (by omega) hij

end SunPrimeDensity.Check
