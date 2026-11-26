import Mathlib

/-!
# Oppermann ⇒ Andrica ⇒ Legendre, and Oppermann ⇒ Brocard

The four prime-gap conjectures below are copied word for word from google-deepmind/formal-conjectures
at commit `9097e2f`, each as a `def … : Prop` (the binders of the source theorem become `∀`).

* `andrica_of_oppermann`: Oppermann's conjecture implies Andrica's conjecture (stated on Wikipedia,
  "Oppermann's conjecture", section Consequences). If `x² ≤ p < (x+1)²`, Oppermann at `x + 1` puts a
  prime in `((x+1)x, (x+1)²)` or in `((x+1)², (x+1)(x+2))`, and the next prime `q` then satisfies
  `(q - p - 1)² < 4p`, which is Andrica's inequality `√q - √p < 1` squared out.
* `legendre_of_andrica`: Andrica's conjecture implies Legendre's conjecture. If `p ≤ n² < q` are
  consecutive primes, `√q < √p + 1 ≤ n + 1`.
* `legendre_of_oppermann`, `brocard_of_oppermann`: formal-conjectures' own `textbook` proofs
  `Oppermann.oppermann_implies_legendre` and `Oppermann.oppermann_implies_brocard`, ported.

Everything here is elementary; no computation is involved.
-/

set_option linter.dupNamespace false

namespace Implications.PrimeGaps

open Finset

namespace Oppermann

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/Oppermann.lean`,
`Oppermann.oppermann_conjecture` (commit `9097e2f`, `research open`), copied verbatim as a `Prop`
(its binders `(x : ℕ) (hx : 2 ≤ x)` become `∀`).

**Oppermann's Conjecture**:
For every integer $x \ge 2$, the following hold:
- There exists a prime between $x(x-1)$ and $x^2$.
- There exists a prime between $x^2$ and $x(x+1)$. -/
def OppermannConjecture : Prop :=
    ∀ (x : ℕ) (_hx : 2 ≤ x),
    (∃ p ∈ Ioo (x * (x - 1)) (x^2), p.Prime) ∧
    (∃ p ∈ Ioo (x^2) (x * (x + 1)), p.Prime)

end Oppermann

namespace Andrica

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/Andrica.lean`,
`Andrica.andrica_conjecture` (commit `9097e2f`, `research open`), copied verbatim as a `Prop`
(its binder `(n : ℕ)` becomes `∀`).

**Andrica's conjecture**
The inequality $\sqrt{p_{n+1}}-\sqrt{p_n} < 1$ holds for all $n$, where $p_n$ is the $n$-th prime
number. -/
def AndricaConjecture : Prop :=
    ∀ (n : ℕ),
    Real.sqrt ((n+1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1

end Andrica

namespace LegendreConjecture

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/LegendreConjecture.lean`,
`LegendreConjecture.legendre_conjecture` (commit `9097e2f`, `research open`), copied verbatim as a
`Prop`.

Does there always exist at least one prime between consecutive perfect squares? -/
def LegendreConjecture : Prop :=
    ∀ n ≥ 1, ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p

end LegendreConjecture

namespace Brocard

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/BrocardConjecture.lean`,
`Brocard.brocard_conjecture` (commit `9097e2f`, `research open`), copied verbatim as a `Prop`
(its binders `(n : ℕ) (hn : 1 ≤ n)` become `∀`).

**Brocard's Conjecture**
For every `n ≥ 2`, between the squares of the `n`-th and `(n+1)`-th primes,
there are at least four prime numbers. -/
def BrocardConjecture : Prop :=
    ∀ (n : ℕ) (_hn : 1 ≤ n),
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card

end Brocard

/-! ## Consecutive primes around a number -/

/-- Every `m ≥ 2` lies in `[p_k, p_{k+1})` for some `k`. -/
lemma exists_nth_le_lt {m : ℕ} (hm : 2 ≤ m) :
    ∃ k, Nat.nth Nat.Prime k ≤ m ∧ m < Nat.nth Nat.Prime (k + 1) := by
  have hinf := Nat.infinite_setOfPred_prime
  have hc : 0 < Nat.count Nat.Prime (m + 1) := by
    rw [Nat.lt_nth_iff_count_lt hinf]
    rw [Nat.nth_prime_zero_eq_two]; omega
  refine ⟨Nat.count Nat.Prime (m + 1) - 1, ?_, ?_⟩
  · have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := m + 1)
      (k := Nat.count Nat.Prime (m + 1) - 1) (by omega)
    omega
  · have := Nat.le_nth_count (p := Nat.Prime) hinf (m + 1)
    rw [Nat.sub_add_cancel hc]
    omega

/-- A prime `q > p_k` is at least `p_{k+1}`. -/
lemma nth_succ_le_of_prime {k q : ℕ} (hq : q.Prime) (h : Nat.nth Nat.Prime k < q) :
    Nat.nth Nat.Prime (k + 1) ≤ q := by
  by_contra! hlt
  exact absurd (Nat.le_nth_of_lt_nth_succ hlt hq) (not_le.2 h)

/-- `p_k < p_{k+1}`. -/
lemma nth_lt_nth_succ (k : ℕ) : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)

/-! ## Andrica's inequality squared out -/

/-- If `a < b` and `(b - a - 1)² < 4a` then `√b - √a < 1`. -/
lemma sqrt_sub_sqrt_lt_one {a b : ℕ} (hab : a < b) (h : (b - a - 1) ^ 2 < 4 * a) :
    Real.sqrt b - Real.sqrt a < 1 := by
  have hd : ((b - a - 1 : ℕ) : ℝ) = (b : ℝ) - a - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hab.le]; push_cast; ring
  have h' : ((b : ℝ) - a - 1) ^ 2 < 4 * a := by
    rw [← hd]; exact_mod_cast h
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hsa := Real.sq_sqrt ha0
  have hsa0 := Real.sqrt_nonneg (a : ℝ)
  -- `b - a - 1 < 2 √a`
  have hlt : (b : ℝ) - a - 1 < 2 * Real.sqrt a := by
    by_contra hc
    push Not at hc
    have h2 : (2 * Real.sqrt a) ^ 2 ≤ ((b : ℝ) - a - 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc 2
    rw [mul_pow, hsa] at h2
    linarith
  have hb : (b : ℝ) < (Real.sqrt a + 1) ^ 2 := by nlinarith
  have := Real.sqrt_lt_sqrt (by positivity) hb
  rw [Real.sqrt_sq (by positivity)] at this
  linarith

/-! ## Oppermann ⇒ Andrica -/

/-- **Oppermann's conjecture implies Andrica's conjecture.** -/
theorem andrica_of_oppermann (h : Oppermann.OppermannConjecture) : Andrica.AndricaConjecture := by
  intro k
  set p := Nat.nth Nat.Prime k with hp
  set q := Nat.nth Nat.Prime (k + 1) with hq
  have hpq : p < q := nth_lt_nth_succ k
  have hpP : p.Prime := Nat.prime_nth_prime k
  have hp2 : 2 ≤ p := hpP.two_le
  suffices hs : (q - p - 1) ^ 2 < 4 * p by
    exact_mod_cast sqrt_sub_sqrt_lt_one hpq hs
  obtain ⟨x, hx⟩ : ∃ x, x = Nat.sqrt p := ⟨_, rfl⟩
  have hx1 : x * x ≤ p := hx ▸ Nat.sqrt_le p
  have hx2 : p < (x + 1) * (x + 1) := hx ▸ Nat.lt_succ_sqrt p
  have hx0 : 1 ≤ x := by
    rw [hx, Nat.le_sqrt]; omega
  have e1 : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by ring
  have e2 : (x + 1) * (x + 1 - 1) = x * x + x := by rw [Nat.add_sub_cancel]; ring
  have e3 : (x + 1) ^ 2 = x * x + 2 * x + 1 := by ring
  have e4 : (x + 1) * (x + 1 + 1) = x * x + 3 * x + 2 := by ring
  rcases lt_or_ge p (x * x + x) with hcase | hcase
  · -- `p < x² + x = (x+1)x`: Oppermann (i) at `x + 1` gives a prime in `((x+1)x, (x+1)²)`.
    obtain ⟨r, hr, hrP⟩ := (h (x + 1) (by omega)).1
    rw [Finset.mem_Ioo] at hr
    have hr1 : p < r := by omega
    have hqr : q ≤ r := nth_succ_le_of_prime hrP hr1
    have hr2 : r < (x + 1) ^ 2 := hr.2
    have : q - p - 1 ≤ 2 * x - 1 := by omega
    calc (q - p - 1) ^ 2 ≤ (2 * x - 1) ^ 2 := Nat.pow_le_pow_left this 2
      _ < 4 * p := by
        have : 2 * x - 1 < 2 * x := by omega
        have h' : (2 * x - 1) ^ 2 < (2 * x) ^ 2 := Nat.pow_lt_pow_left this (by norm_num)
        nlinarith
  · -- `p ≥ x² + x`, and `p = x² + x` only for `p = 2`.
    rcases eq_or_lt_of_le hcase with heq | hgt
    · -- `p = x(x+1)` is prime only when `x = 1`, `p = 2`, `q = 3`.
      have hx1' : x = 1 := by
        by_contra hne
        have hdvd : x ∣ p := ⟨x + 1, by rw [← heq]; ring⟩
        rcases (Nat.dvd_prime hpP).1 hdvd with h1 | h1
        · exact hne h1
        · nlinarith
      have hp2' : p = 2 := by rw [← heq, hx1']
      have hk : k = 0 := by
        have : Nat.nth Nat.Prime k = Nat.nth Nat.Prime 0 := by
          rw [← hp, hp2', Nat.nth_prime_zero_eq_two]
        exact Nat.nth_injective Nat.infinite_setOfPred_prime this
      have hq3 : q = 3 := by rw [hq, hk]; exact Nat.nth_prime_one_eq_three
      rw [hq3, hp2']; norm_num
    · -- Oppermann (ii) at `x + 1` gives a prime in `((x+1)², (x+1)(x+2))`.
      obtain ⟨r, hr, hrP⟩ := (h (x + 1) (by omega)).2
      rw [Finset.mem_Ioo] at hr
      have hr1 : p < r := by omega
      have hqr : q ≤ r := nth_succ_le_of_prime hrP hr1
      have hr2 : r < (x + 1) * (x + 1 + 1) := hr.2
      have hr3 : r ≤ x * x + 3 * x + 1 := by omega
      have : q - p - 1 ≤ 2 * x - 1 := by omega
      calc (q - p - 1) ^ 2 ≤ (2 * x - 1) ^ 2 := Nat.pow_le_pow_left this 2
        _ < 4 * p := by
          have : 2 * x - 1 < 2 * x := by omega
          have h' : (2 * x - 1) ^ 2 < (2 * x) ^ 2 := Nat.pow_lt_pow_left this (by norm_num)
          nlinarith

/-! ## Andrica ⇒ Legendre -/

/-- **Andrica's conjecture implies Legendre's conjecture.** -/
theorem legendre_of_andrica (h : Andrica.AndricaConjecture) :
    LegendreConjecture.LegendreConjecture := by
  intro n hn
  rcases eq_or_lt_of_le hn with rfl | hn2
  · exact ⟨2, by norm_num, Nat.prime_two⟩
  obtain ⟨k, hk1, hk2⟩ := exists_nth_le_lt (m := n ^ 2) (by nlinarith)
  refine ⟨Nat.nth Nat.Prime (k + 1), ⟨hk2, ?_⟩, Nat.prime_nth_prime _⟩
  have hA := h k
  have hsp : Real.sqrt (Nat.nth Nat.Prime k) ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast hk1
  have hlt : Real.sqrt (Nat.nth Nat.Prime (k + 1)) < (n : ℝ) + 1 := by linarith
  have h0 : (0 : ℝ) ≤ Nat.nth Nat.Prime (k + 1) := by positivity
  have := (Real.sqrt_lt' (by positivity)).1 hlt
  exact_mod_cast this

/-! ## formal-conjectures' Oppermann ⇒ Legendre and Oppermann ⇒ Brocard, ported -/

/-- formal-conjectures `Oppermann.oppermann_implies_legendre` (`textbook`), ported (the proof is
the source's), stated as `OppermannConjecture → LegendreConjecture`. -/
theorem legendre_of_oppermann (P : Oppermann.OppermannConjecture) :
    LegendreConjecture.LegendreConjecture := by
  intro n hn
  obtain ⟨⟨p, ph⟩, _⟩ := P (n + 1) (by simpa)
  refine ⟨p, ?_, ph.2⟩
  rw [Set.mem_Ioo]
  have h := Finset.mem_Ioo.1 ph.1
  refine ⟨lt_of_le_of_lt ?_ h.1, h.2⟩
  push_cast [sq, add_one_mul, le_self_add]

/-- formal-conjectures `Oppermann.oppermann_implies_brocard` (`textbook`), ported (the proof is
the source's), stated as `OppermannConjecture → BrocardConjecture`. -/
theorem brocard_of_oppermann (P : Oppermann.OppermannConjecture) :
    Brocard.BrocardConjecture := by
  intro n hn
  set prev := n.nth Nat.Prime with hprev_def
  set next := (n+1).nth Nat.Prime with hnext_def
  have hprev_prime : prev.Prime := Nat.prime_nth_prime n
  have hnext_prime : next.Prime := Nat.prime_nth_prime (n+1)
  have hprev_ge : 3 ≤ prev := Nat.nth_prime_one_eq_three ▸
    (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr hn
  have hlt : prev < next :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
  have hgap : prev + 2 ≤ next := by
    rcases hprev_prime.odd_of_ne_two (by omega) with ⟨k, hk⟩
    rcases hnext_prime.odd_of_ne_two (by omega) with ⟨m, hm⟩
    omega
  obtain ⟨_, p1, hp1mem, hp1p⟩ := P prev (by omega)
  obtain ⟨⟨p2, hp2mem, hp2p⟩, p3, hp3mem, hp3p⟩ := P (prev+1) (by omega)
  obtain ⟨p4, hp4mem, hp4p⟩ := (P (prev+2) (by omega)).1
  simp only [Finset.mem_Ioo, show prev + 1 - 1 = prev from rfl,
    show prev + 2 - 1 = prev + 1 from rfl, show prev + 1 + 1 = prev + 2 from rfl]
    at hp1mem hp2mem hp3mem hp4mem
  have hsq : (prev + 2)^2 ≤ next^2 := Nat.pow_le_pow_left hgap 2
  have hsq1 : (prev + 1)^2 ≤ next^2 := Nat.pow_le_pow_left (by omega) 2
  have hb0 : prev * (prev + 1) < (prev + 1)^2 := by nlinarith
  have hb1 : (prev + 1) * (prev + 2) < (prev + 2)^2 := by nlinarith
  have h12 : p1 < p2 := by linarith [hp1mem.2, hp2mem.1]
  have h23 : p2 < p3 := by linarith [hp2mem.2, hp3mem.1]
  have h34 : p3 < p4 := by linarith [hp3mem.2, hp4mem.1]
  refine ((show ({p1, p2, p3, p4} : Finset ℕ).card = 4 from ?_) ▸
    Finset.card_le_card (s := {p1, p2, p3, p4}) ?_)
  · simp [Finset.card_insert_of_notMem, h12.ne, (h12.trans h23).ne,
      (h12.trans (h23.trans h34)).ne, h23.ne, (h23.trans h34).ne, h34.ne]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨?_, ?_⟩, by assumption⟩ <;>
      linarith [hp1mem.1, hp1mem.2, hp2mem.1, hp2mem.2, hp3mem.1, hp3mem.2,
        hp4mem.1, hp4mem.2, hb0, hb1, hsq, hsq1]

end Implications.PrimeGaps
