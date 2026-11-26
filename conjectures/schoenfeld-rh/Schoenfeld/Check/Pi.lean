import Schoenfeld.Check.Li
import Schoenfeld.Check.PsiTheta

/-!
# `PiSmallRange`: `|π(x) − li(x)| < √x log x/(8π)` on `[2657, 4·10⁵]`

`checkB N` walks the integers `2658, …, N`. Between consecutive primes `a < b` (from
`a = 2657`), `π(⌊x⌋) = k` is constant and `li` is increasing, so it suffices that
`k − li(a) < F1(a)` (checked when the cell opens) and `li(b) − k < F1(a)` (checked when it
closes), with `F1(a) ≤ F1(x)`. `li(a)` is carried as an enclosure, started from
`liAnchor_sound` at `2657` and advanced by `li(b) = li(a) + ∫ₐᵇ dt/log t` with the cell bounds
`liCellLo`, `liCellHi`. The last cell is closed at `N + 1`. `π(2657)` is counted by `cntLoop`.

`checkB_sound` proves the bound from `checkB N = true`; `checkB 400000` is one `native_decide`.
-/

namespace Schoenfeld.Check

open Real

/-- `cntLoop k n c` counts the primes among `n, …, n + k − 1`, added to `c`. -/
def cntLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | k + 1, n, c => cntLoop k (n + 1) (if isPrime n then c + 1 else c)

lemma primeCounting_succ' (n : ℕ) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n + if (n + 1).Prime then 1 else 0 := by
  simp only [Nat.primeCounting, Nat.primeCounting']
  rw [Nat.count_succ]

lemma cntLoop_eq (k : ℕ) : ∀ n c, c = Nat.primeCounting n →
    cntLoop k (n + 1) c = Nat.primeCounting (n + k) := by
  induction k with
  | zero => intro n c h; simpa [cntLoop] using h
  | succ k ih =>
    intro n c h
    simp only [cntLoop]
    rw [ih (n + 1), show n + 1 + k = n + (k + 1) by omega]
    rw [primeCounting_succ', h]
    by_cases hp : (n + 1).Prime
    · rw [if_pos ((isPrime_iff _).mpr hp), if_pos hp]
    · rw [if_neg (fun h' => hp ((isPrime_iff _).mp h')), if_neg hp, add_zero]

/-- Checker state: cell start, `π` on the cell, enclosure of `li` at the start, lower bound
for `F1` at the start, flag. -/
structure StB where
  a : ℚ
  k : ℕ
  laLo : ℚ
  laHi : ℚ
  fa : ℚ
  ok : Bool

/-- Process the integer `n`. -/
def stepB (st : StB) (n : ℕ) : StB :=
  if isPrime n then
    let lbLo := st.laLo + liCellLo st.a n
    let lbHi := st.laHi + liCellHi st.a n
    let fa' := F1lo n
    ⟨n, st.k + 1, lbLo, lbHi, fa', st.ok && liGuard st.a n && decide (lbHi - st.k < st.fa) &&
      decide (((st.k + 1 : ℕ) : ℚ) - lbLo < fa')⟩
  else st

/-- `loopB k n st` processes `n, …, n + k − 1`. -/
def loopB : ℕ → ℕ → StB → StB
  | 0, _, st => st
  | k + 1, n, st => loopB k (n + 1) (stepB st n)

/-- `π(2657)`, counted. -/
@[irreducible] def k2657 : ℕ := cntLoop 2657 1 0

/-- The state at `2657`. -/
def startB : StB :=
  ⟨2657, k2657, liAnchorLo, liAnchorHi, F1lo 2657,
    liAnchorOK && decide ((k2657 : ℚ) - liAnchorLo < F1lo 2657)⟩

/-- The check of `[2657, N]`. -/
def checkB (N : ℕ) : Bool :=
  let st := loopB (N - 2657) 2658 startB
  st.ok && liGuard st.a (N + 1) && decide (st.laHi + liCellHi st.a (N + 1) - st.k < st.fa) &&
    decide (2657 ≤ N)

/-- The invariant after processing `n`. -/
def InvB (n : ℕ) (st : StB) : Prop :=
  (2657 : ℝ) ≤ st.a ∧ (st.a : ℝ) < n + 1 ∧ st.k = Nat.primeCounting n ∧
    (∀ x : ℝ, (st.a : ℝ) ≤ x → x < n + 1 → Nat.primeCounting ⌊x⌋₊ = Nat.primeCounting n) ∧
    (st.fa : ℝ) ≤ F1 st.a ∧
    (st.ok = true → (st.laLo : ℝ) ≤ Real.logIntegral st.a ∧ Real.logIntegral st.a ≤ st.laHi ∧
      (st.k : ℝ) - st.laLo < st.fa ∧
      ∀ x : ℝ, (2657 : ℝ) ≤ x → x < st.a →
        |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < F1 x)

lemma li_cell {a b : ℚ} (h : liGuard a b = true) (ha : (2 : ℝ) ≤ a) {lo hi : ℚ}
    (hlo : (lo : ℝ) ≤ Real.logIntegral a) (hhi : Real.logIntegral a ≤ hi) :
    ((lo + liCellLo a b : ℚ) : ℝ) ≤ Real.logIntegral b ∧
      Real.logIntegral b ≤ ((hi + liCellHi a b : ℚ) : ℝ) ∧ (a : ℝ) ≤ b := by
  obtain ⟨_, h1, h2⟩ := liCell_sound a b h
  simp only [liGuard, Bool.and_eq_true, decide_eq_true_eq] at h
  have hab : (a : ℝ) ≤ b := by exact_mod_cast h.1.2
  rw [logIntegral_eq_add ha (by linarith)]
  push_cast
  exact ⟨by linarith, by linarith, hab⟩

lemma cellB_bound {a b : ℝ} {k : ℕ} {laLo lbHi fa : ℝ} (ha : (2657 : ℝ) ≤ a)
    (hfa : fa ≤ F1 a) (hla : laLo ≤ Real.logIntegral a) (hlb : Real.logIntegral b ≤ lbHi)
    (hopen : (k : ℝ) - laLo < fa) (hclose : lbHi - k < fa) {x : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) :
    |(k : ℝ) - Real.logIntegral x| < F1 x := by
  have hF := F1_mono (by linarith) hx1
  have m1 := logIntegral_mono (by linarith) hx1
  have m2 := logIntegral_mono (by linarith) hx2
  rw [abs_lt]
  constructor <;> linarith

lemma invB_step {n : ℕ} {st : StB} (h : InvB n st) : InvB (n + 1) (stepB st (n + 1)) := by
  obtain ⟨ha, han, hk, hconst, hfa, hok⟩ := h
  have hpc := primeCounting_succ' n
  unfold stepB
  split_ifs with hp
  · have hp' := (isPrime_iff _).mp hp
    rw [if_pos hp'] at hpc
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
    · simp only; rw [hk, hpc]
    · intro x hx1 hx2
      push_cast at hx1
      rw [floor_eq_succ hx1 (by push_cast at hx2; linarith)]
    · have := F1lo_le (show (1 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) by exact_mod_cast Nat.succ_pos n)
      simpa using this
    · intro hok'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
      obtain ⟨⟨⟨hok0, hg⟩, hclose⟩, hopen⟩ := hok'
      obtain ⟨hlaLo, hlaHi, hopen0, hprev⟩ := hok hok0
      obtain ⟨c1, c2, hab⟩ := li_cell hg (by linarith) hlaLo hlaHi
      have hclose' : ((st.laHi + liCellHi st.a ((n + 1 : ℕ) : ℚ) - st.k : ℚ) : ℝ) < st.fa := by
        exact_mod_cast hclose
      have hopen' : ((((st.k + 1 : ℕ) : ℚ) - (st.laLo + liCellLo st.a ((n + 1 : ℕ) : ℚ)) : ℚ) :
          ℝ) < F1lo ((n + 1 : ℕ) : ℚ) := by exact_mod_cast hopen
      push_cast at hclose' hopen' c1 c2 ⊢
      refine ⟨c1, c2, by linarith, ?_⟩
      intro x hx1 hx2
      rcases lt_or_ge x st.a with hxa | hxa
      · exact hprev x hx1 hxa
      · rw [hconst x hxa (by linarith), ← hk]
        exact cellB_bound ha hfa hlaLo c2 hopen0 (by push_cast; linarith) hxa hx2.le
  · have hp' : ¬ (n + 1).Prime := fun h' => hp ((isPrime_iff _).mpr h')
    rw [if_neg hp', add_zero] at hpc
    refine ⟨ha, by push_cast; linarith, by rw [hk, hpc], ?_, hfa, hok⟩
    intro x hx1 hx2
    rcases lt_or_ge x (n + 1) with h' | h'
    · rw [hconst x hx1 h', hpc]
    · rw [floor_eq_succ h' (by push_cast at hx2; linarith)]

lemma invB_loop (k : ℕ) : ∀ (n : ℕ) (st : StB), InvB n st → InvB (n + k) (loopB k (n + 1) st) := by
  induction k with
  | zero => intro n st h; simpa [loopB] using h
  | succ k ih =>
    intro n st h
    simp only [loopB]
    have := ih (n + 1) _ (invB_step h)
    rwa [show n + 1 + k = n + (k + 1) by omega] at this

attribute [local irreducible] liAnchorOK liAnchorLo liAnchorHi F1lo in
lemma invB_start : InvB 2657 startB := by
  have hk : k2657 = Nat.primeCounting 2657 := by
    have := cntLoop_eq 2657 0 0 (by simp)
    unfold k2657
    simpa using this
  have ea : startB.a = 2657 := rfl
  have ek : startB.k = k2657 := rfl
  have efa : startB.fa = F1lo 2657 := rfl
  have elo : startB.laLo = liAnchorLo := rfl
  have ehi : startB.laHi = liAnchorHi := rfl
  have eok : startB.ok = (liAnchorOK && decide ((k2657 : ℚ) - liAnchorLo < F1lo 2657)) := rfl
  refine ⟨by rw [ea]; norm_num, by rw [ea]; norm_num, by rw [ek, hk], ?_, ?_, ?_⟩
  · intro x hx1 hx2
    rw [ea] at hx1
    push_cast at hx1
    congr 1
    rw [Nat.floor_eq_iff (by linarith)]
    push_cast
    exact ⟨hx1, hx2⟩
  · rw [efa, ea]; exact F1lo_le (by norm_num)
  · intro hok
    rw [eok] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hA, hopen⟩ := hok
    obtain ⟨h1, h2⟩ := liAnchor_sound hA
    have hopen' : (((k2657 : ℕ) : ℚ) - liAnchorLo : ℝ) < F1lo 2657 := by
      exact_mod_cast hopen
    push_cast at hopen'
    rw [ea, ek, efa, elo, ehi]
    push_cast
    refine ⟨h1, h2, hopen', fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1)⟩

/-- **Soundness of `checkB`.** -/
theorem checkB_sound {N : ℕ} (h : checkB N = true) :
    ∀ x : ℝ, (2657 : ℝ) ≤ x → x ≤ N →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < F1 x := by
  simp only [checkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hg⟩, hfin⟩, hN⟩ := h
  have hinv := invB_loop (N - 2657) 2657 _ invB_start
  rw [show 2657 + (N - 2657) = N by omega] at hinv
  set st := loopB (N - 2657) 2658 startB
  obtain ⟨ha, han, hk, hconst, hfa, hok'⟩ := hinv
  obtain ⟨hlaLo, hlaHi, hopen, hprev⟩ := hok' hok
  obtain ⟨_, c2, _⟩ := li_cell hg (by linarith) hlaLo hlaHi
  have hfin' : ((st.laHi + liCellHi st.a ((N + 1 : ℕ) : ℚ) - st.k : ℚ) : ℝ) < st.fa := by
    have : ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by push_cast; rfl
    rw [this]; exact_mod_cast hfin
  push_cast at hfin' c2
  intro x hx1 hx2
  rcases lt_or_ge x st.a with hxa | hxa
  · exact hprev x hx1 hxa
  · rw [hconst x hxa (by linarith), ← hk]
    exact cellB_bound ha hfa hlaLo c2 hopen (by push_cast; linarith) hxa (by push_cast; linarith)

/-- The `π − li` check on `[2657, 4·10⁵]`. -/
theorem checkB_pi : checkB 400000 = true := by native_decide

/-- **`PiSmallRange`**: `|π(x) − li(x)| < √x log x/(8π)` on `[2657, 4·10⁵]`. -/
theorem piSmallRange : PiSmallRange := fun x hx1 hx2 =>
  checkB_sound checkB_pi x hx1 (by push_cast; exact hx2)

end Schoenfeld.Check
