import Schoenfeld.Check.Basic

/-!
# A proved-sound checker for `|S(⌊x⌋) − x| < √x log² x/(8π)` on a compact range

`S : ℕ → ℝ` is a step function with `S(n) = S(n−1) + log(minFac n)` when `jump n` and
`S(n) = S(n−1)` otherwise: `ψ` (jumps at prime powers) and `θ` (jumps at primes).

`checkA Flo jump lo N` walks the integers `⌊lo⌋ + 1, …, N`. Between two consecutive jumps `a < b`
the function `x ↦ S(⌊x⌋)` is constant, equal to `c = S(a)`, and since `F` is increasing it
suffices that `c − a < F(a)` (checked when the cell opens) and `b − c < F(a)` (checked when
it closes): then `|c − x| < F(a) ≤ F(x)` for every `x ∈ [a, b)`. `S(a)` is carried as a
rational enclosure; `F(a)` as a rational lower bound. The last cell is closed at `N + 1`.

`checkA_sound` proves that `checkA Flo jump lo N = true` implies the bound for every real
`x ∈ [lo, N]`.
-/

namespace Schoenfeld.Check

open Real

/-- The checker state: start of the current cell, enclosure of `S` on it, lower bound for
`F` at the start, and the flag. -/
structure StA where
  a : ℚ
  cLo : ℚ
  cHi : ℚ
  fa : ℚ
  ok : Bool

/-- Process the integer `n`. -/
def stepA (Flo : ℚ → ℚ) (jump : ℕ → Bool) (st : StA) (n : ℕ) : StA :=
  if jump n then
    let cLo' := st.cLo + logLo n.minFac
    let cHi' := st.cHi + logUp n.minFac
    let fa' := Flo n
    ⟨n, cLo', cHi', fa', st.ok && decide ((n : ℚ) - st.cLo < st.fa) && decide (cHi' - n < fa')⟩
  else st

/-- `loopA Flo jump k n st` processes `n, …, n + k − 1`. -/
def loopA (Flo : ℚ → ℚ) (jump : ℕ → Bool) : ℕ → ℕ → StA → StA
  | 0, _, st => st
  | k + 1, n, st => loopA Flo jump k (n + 1) (stepA Flo jump st n)

/-- The state at `⌊lo⌋`, with the cell opened at `lo`. -/
def startA (Flo : ℚ → ℚ) (jump : ℕ → Bool) (lo : ℚ) : StA :=
  let st := loopA Flo jump ⌊lo⌋₊ 1 ⟨1, 0, 0, 0, true⟩
  ⟨lo, st.cLo, st.cHi, Flo lo, decide (st.cHi - lo < Flo lo)⟩

/-- The check of the range `[lo, N]`. -/
def checkA (Flo : ℚ → ℚ) (jump : ℕ → Bool) (lo : ℚ) (N : ℕ) : Bool :=
  let st := loopA Flo jump (N - ⌊lo⌋₊) (⌊lo⌋₊ + 1) (startA Flo jump lo)
  st.ok && decide ((N + 1 : ℚ) - st.cLo < st.fa) && decide (1 ≤ lo) && decide (⌊lo⌋₊ ≤ N)

section Sound

variable (Flo : ℚ → ℚ) (F : ℝ → ℝ) (hFlo : ∀ a : ℚ, 1 ≤ a → (Flo a : ℝ) ≤ F a)
  (hF : ∀ a x : ℝ, 1 ≤ a → a ≤ x → F a ≤ F x)
  (jump : ℕ → Bool) (S : ℕ → ℝ)
  (hS : ∀ n, S (n + 1) = S n + if jump (n + 1) then Real.log ((n + 1).minFac : ℝ) else 0)

include hS hFlo hF

omit hS hFlo hF in
lemma log_minFac_bounds (n : ℕ) :
    (logLo ((n.minFac : ℕ) : ℚ) : ℝ) ≤ Real.log (n.minFac : ℝ) ∧
      Real.log (n.minFac : ℝ) ≤ (logUp ((n.minFac : ℕ) : ℚ) : ℝ) := by
  have h1 : (1 : ℚ) ≤ ((n.minFac : ℕ) : ℚ) := by exact_mod_cast n.minFac_pos
  have a := logLo_le h1
  have b := le_logUp h1
  push_cast at a b
  exact ⟨a, b⟩

omit hS hFlo hF in
/-- Enclosure of `S n`. -/
def EncA (n : ℕ) (st : StA) : Prop := (st.cLo : ℝ) ≤ S n ∧ S n ≤ st.cHi

lemma encA_step {n : ℕ} {st : StA} (h : EncA S n st) : EncA S (n + 1) (stepA Flo jump st (n + 1)) := by
  have e := hS n
  unfold stepA
  split_ifs with hj
  · rw [if_pos hj] at e
    obtain ⟨l, u⟩ := log_minFac_bounds (n + 1)
    simp only [EncA] at h ⊢
    rw [e]
    push_cast
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · rw [if_neg hj, add_zero] at e
    simp only [EncA] at h ⊢
    rw [e]
    exact h

lemma encA_loop (k : ℕ) : ∀ (n : ℕ) (st : StA), EncA S n st →
    EncA S (n + k) (loopA Flo jump k (n + 1) st) := by
  induction k with
  | zero => intro n st h; simpa [loopA] using h
  | succ k ih =>
    intro n st h
    simp only [loopA]
    have := ih (n + 1) _ (encA_step Flo F hFlo hF jump S hS h)
    rwa [show n + 1 + k = n + (k + 1) by omega] at this

omit hS hFlo hF in
/-- The invariant after processing `n`. -/
def InvA (lo : ℚ) (n : ℕ) (st : StA) : Prop :=
  (lo : ℝ) ≤ st.a ∧ (st.a : ℝ) < n + 1 ∧ EncA S n st ∧
    (∀ x : ℝ, (st.a : ℝ) ≤ x → x < n + 1 → S ⌊x⌋₊ = S n) ∧ (st.fa : ℝ) ≤ F st.a ∧
    (st.ok = true → S n - st.a < st.fa ∧
      ∀ x : ℝ, (lo : ℝ) ≤ x → x < st.a → |S ⌊x⌋₊ - x| < F x)

omit hS hFlo hF in
lemma floor_eq_succ {x : ℝ} {n : ℕ} (h1 : (n : ℝ) + 1 ≤ x) (h2 : x < n + 1 + 1) :
    ⌊x⌋₊ = n + 1 := by
  rw [Nat.floor_eq_iff (by linarith)]
  push_cast
  exact ⟨h1, h2⟩

omit hS hFlo in
lemma cell_bound {lo : ℚ} (hlo : 1 ≤ lo) {a b c cLo fa : ℝ} (hla : (lo : ℝ) ≤ a)
    (hfa : fa ≤ F a) (hc : cLo ≤ c) (hopen : c - a < fa) (hclose : b - cLo < fa) {x : ℝ}
    (hx1 : a ≤ x) (hx2 : x ≤ b) : |c - x| < F x := by
  have h1 : (1 : ℝ) ≤ a := le_trans (by exact_mod_cast hlo) hla
  have hF := hF _ _ h1 hx1
  rw [abs_lt]
  constructor <;> linarith

lemma invA_step {lo : ℚ} (hlo : 1 ≤ lo) {n : ℕ} {st : StA} (h : InvA F S lo n st) :
    InvA F S lo (n + 1) (stepA Flo jump st (n + 1)) := by
  obtain ⟨hla, han, henc, hconst, hfa, hok⟩ := h
  have henc' := encA_step Flo F hFlo hF jump S hS henc
  unfold stepA at henc' ⊢
  have hSn := hS n
  split_ifs with hj
  · rw [if_pos hj] at hSn henc'
    refine ⟨?_, ?_, henc', ?_, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
    · intro x hx1 hx2
      push_cast at hx1
      rw [floor_eq_succ hx1 (by push_cast at hx2; linarith)]
    · have := hFlo _ (show (1 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) by exact_mod_cast Nat.succ_pos n)
      simpa using this
    · intro hok'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
      obtain ⟨⟨hok0, hclose⟩, hopen⟩ := hok'
      obtain ⟨hopen0, hprev⟩ := hok hok0
      refine ⟨?_, ?_⟩
      · have : (((st.cHi + logUp ((n + 1).minFac : ℚ)) - ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) <
            (Flo ((n + 1 : ℕ) : ℚ) : ℝ) := by exact_mod_cast hopen
        push_cast at this
        have := henc'.2
        simp only at this
        push_cast at this ⊢
        linarith
      · intro x hx1 hx2
        rcases lt_or_ge x st.a with hxa | hxa
        · exact hprev x hx1 hxa
        · have hx2' : x < n + 1 := by push_cast at hx2; exact hx2
          rw [hconst x hxa (by linarith)]
          have hclose' : (((n + 1 : ℕ) : ℚ) - st.cLo : ℝ) < st.fa := by exact_mod_cast hclose
          push_cast at hclose'
          exact cell_bound F hF hlo hla hfa henc.1 hopen0 hclose' hxa hx2'.le
  · rw [if_neg hj, add_zero] at hSn
    rw [if_neg hj] at henc'
    refine ⟨hla, by push_cast; linarith, henc', ?_, hfa, ?_⟩
    · intro x hx1 hx2
      rcases lt_or_ge x (n + 1) with h' | h'
      · rw [hconst x hx1 h', hSn]
      · rw [floor_eq_succ h' (by push_cast at hx2; linarith)]
    · intro hok'
      obtain ⟨h1, h2⟩ := hok hok'
      exact ⟨by rw [hSn]; exact h1, h2⟩

lemma invA_loop {lo : ℚ} (hlo : 1 ≤ lo) (k : ℕ) : ∀ (n : ℕ) (st : StA), InvA F S lo n st →
    InvA F S lo (n + k) (loopA Flo jump k (n + 1) st) := by
  induction k with
  | zero => intro n st h; simpa [loopA] using h
  | succ k ih =>
    intro n st h
    simp only [loopA]
    have := ih (n + 1) _ (invA_step Flo F hFlo hF jump S hS hlo h)
    rwa [show n + 1 + k = n + (k + 1) by omega] at this

lemma invA_start (hS0 : S 0 = 0) {lo : ℚ} (hlo : 1 ≤ lo) :
    InvA F S lo ⌊lo⌋₊ (startA Flo jump lo) := by
  have hlo0 : (0 : ℚ) ≤ lo := by linarith
  have henc : EncA S (0 + ⌊lo⌋₊) (loopA Flo jump ⌊lo⌋₊ (0 + 1) ⟨1, 0, 0, 0, true⟩) :=
    encA_loop Flo F hFlo hF jump S hS _ 0 _ (by simp [EncA, hS0])
  simp only [zero_add] at henc
  have hfl : (⌊lo⌋₊ : ℚ) ≤ lo := Nat.floor_le hlo0
  have hfl' : lo < ⌊lo⌋₊ + 1 := Nat.lt_floor_add_one lo
  refine ⟨le_rfl, ?_, henc, ?_, hFlo _ hlo, ?_⟩
  · simp only [startA]; exact_mod_cast hfl'
  · intro x hx1 hx2
    simp only [startA] at hx1
    congr 1
    rw [Nat.floor_eq_iff (by linarith [(show (0 : ℝ) ≤ lo by exact_mod_cast hlo0)])]
    refine ⟨le_trans (by exact_mod_cast hfl) hx1, hx2⟩
  · intro hok
    simp only [startA, decide_eq_true_eq] at hok
    refine ⟨?_, fun x hx1 hx2 => absurd hx2 (not_lt.mpr (by simpa [startA] using hx1))⟩
    have : (((loopA Flo jump ⌊lo⌋₊ 1 ⟨1, 0, 0, 0, true⟩).cHi - lo : ℚ) : ℝ) < (Flo lo : ℝ) := by
      exact_mod_cast hok
    push_cast at this
    simp only [startA]
    linarith [henc.2]

/-- **Soundness of `checkA`.** -/
theorem checkA_sound (hS0 : S 0 = 0) {lo : ℚ} {N : ℕ} (h : checkA Flo jump lo N = true) :
    ∀ x : ℝ, (lo : ℝ) ≤ x → x ≤ N → |S ⌊x⌋₊ - x| < F x := by
  simp only [checkA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hfin⟩, hlo⟩, hN⟩ := h
  have hinv := invA_loop Flo F hFlo hF jump S hS hlo (N - ⌊lo⌋₊) _ _ (invA_start Flo F hFlo hF jump S hS hS0 hlo)
  rw [show ⌊lo⌋₊ + (N - ⌊lo⌋₊) = N by omega] at hinv
  set st := loopA Flo jump (N - ⌊lo⌋₊) (⌊lo⌋₊ + 1) (startA Flo jump lo)
  obtain ⟨hla, han, henc, hconst, hfa, hok'⟩ := hinv
  obtain ⟨hopen, hprev⟩ := hok' hok
  intro x hx1 hx2
  rcases lt_or_ge x st.a with hxa | hxa
  · exact hprev x hx1 hxa
  · rw [hconst x hxa (by linarith)]
    have hfin' : ((N + 1 : ℚ) - st.cLo : ℝ) < st.fa := by exact_mod_cast hfin
    push_cast at hfin'
    exact cell_bound F hF hlo hla hfa henc.1 hopen (b := N + 1) hfin' hxa (by linarith)

end Sound

end Schoenfeld.Check
