import Mathlib
import Mills.Greedy

/-!
# The fifth and sixth Mills primes, certified in the kernel

`g 4 = b₅ = 16022236204009818131831320183 = 2521008887³ + 80` and
`g 5 = b₆ = b₅³ + 12` (85 digits).

* **Primality**: a Lucas (Pratt) certificate, checked by Mathlib's `primality` tactic. The
  tactic builds a proof term `prime_of_lucasCheck … (Eq.refl true)`, so the kernel evaluates the
  modular powers itself (GMP-backed `Nat` arithmetic); no `native_decide`.
* **Minimality**: every `n` with `b₄³ ≤ n < b₅` (or `b₅³ ≤ n < b₆`) is composite. Each one fails Fermat's test to
  base `2` (`2^(n-1) mod n ≠ 1`, `fermatComposite`), which is proved to imply compositeness
  (`not_prime_of_fermatComposite`). The range check is a kernel `decide`.
-/

namespace Mills

open Mathlib.Tactic.Primality

/-- `n > 2` fails Fermat's test to base `2`. -/
def fermatComposite (n : ℕ) : Bool :=
  2 < n && powMod 2 (n - 1) n != 1

/-- **Soundness of the Fermat checker**: an `n` that fails Fermat's test is not prime. -/
theorem not_prime_of_fermatComposite {n : ℕ} (h : fermatComposite n = true) : ¬ n.Prime := by
  intro hp
  simp only [fermatComposite, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hpow⟩ := h
  have := Fact.mk hp
  apply hpow
  have h2ne : (2 : ZMod n) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  have hf := ZMod.pow_card_sub_one_eq_one h2ne
  rw [powMod_def, ← ZMod.val_natCast, Nat.cast_pow]
  push_cast
  rw [hf, ZMod.val_one'' (by omega)]

/-- Every `n` in `[b, b + k)` fails Fermat's test. -/
def allFermatComposite (b k : ℕ) : Bool :=
  (List.range k).all fun i => fermatComposite (b + i)

theorem not_prime_of_allFermatComposite {b k : ℕ} (h : allFermatComposite b k = true) {n : ℕ}
    (h1 : b ≤ n) (h2 : n < b + k) : ¬ n.Prime := by
  apply not_prime_of_fermatComposite
  simp only [allFermatComposite, List.all_eq_true, List.mem_range] at h
  have := h (n - b) (by omega)
  rwa [Nat.add_sub_cancel' h1] at this

/-- Pin `nextPrime x = p` from a certified prime and a Fermat range check below it. -/
theorem nextPrime_eq_of_check {x p : ℕ} (hp : p.Prime) (hle : x ^ 3 ≤ p)
    (h : allFermatComposite (x ^ 3) (p - x ^ 3) = true) : nextPrime x = p :=
  nextPrime_eq hp hle fun q h1 h2 => not_prime_of_allFermatComposite h h1 (by omega)

/-- **`b₅` is prime** (Lucas certificate, 9 links, kernel-checked). -/
theorem prime_b5 : Nat.Prime 16022236204009818131831320183 := by
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 3, 149, 487, 122833, 299599849588197443] },
    .lucas { root := 10, primeFactors := [2, 3, 853] },
    .lucas { root := 2, primeFactors := [2, 19, 7884206568110459] },
    .lucas { root := 2, primeFactors := [2, 17, 23, 10082105585819] },
    .lucas { root := 2, primeFactors := [2, 7, 1987, 362431001] },
    .lucas { root := 2, primeFactors := [2, 3, 331] },
    .lucas { root := 3, primeFactors := [2, 5, 362431] },
    .lucas { root := 3, primeFactors := [2, 3, 5, 4027] },
    .lucas { root := 3, primeFactors := [2, 3, 11, 61] }])

/-- The 80 numbers `b₄³, …, b₄³ + 79` are composite. -/
theorem check_b5 : allFermatComposite (2521008887 ^ 3) (16022236204009818131831320183 - 2521008887 ^ 3) = true := by
  decide +kernel

/-- **`g 4 = b₅`**: `16022236204009818131831320183` is the least prime `≥ 2521008887³`. -/
theorem g_four : g 4 = 16022236204009818131831320183 := by
  rw [g_succ, g_three]
  exact nextPrime_eq_of_check prime_b5 (by norm_num) check_b5

/-- **`b₆` is prime** (85 digits; Lucas certificate with 26 links, kernel-checked).
`b₆ - 1 = 2 · 3 · 29 · 6311 · 4946911994449 · 4767859693324212149320551641267 ·
158805050530653056698774265519084179`; the last two factors were found with GMP-ECM. -/
theorem prime_b6 : Nat.Prime 4113101149215104800030529537915953170486139623539759933135949994882770404074832568499 := by
  primality (cert := .witnesses [
    .lucas { root := 2, primeFactors := [2, 3, 29, 6311, 4946911994449, 4767859693324212149320551641267, 158805050530653056698774265519084179] },
    .lucas { root := 7, primeFactors := [2, 5, 631] },
    .lucas { root := 19, primeFactors := [2, 3, 2753, 12478589] },
    .lucas { root := 3, primeFactors := [2, 43] },
    .lucas { root := 2, primeFactors := [2, 3119647] },
    .lucas { root := 3, primeFactors := [2, 3, 29, 17929] },
    .lucas { root := 11, primeFactors := [2, 3, 83] },
    .lucas { root := 2, primeFactors := [2, 1499, 1027759, 1547392721093657541013] },
    .lucas { root := 2, primeFactors := [2, 7, 107] },
    .lucas { root := 3, primeFactors := [2, 3, 171293] },
    .lucas { root := 5, primeFactors := [2, 11, 17, 229] },
    .lucas { root := 2, primeFactors := [2, 3, 7, 13, 43, 17327, 76943, 24718207] },
    .lucas { root := 5, primeFactors := [2, 8663] },
    .lucas { root := 5, primeFactors := [2, 61, 71] },
    .lucas { root := 10, primeFactors := [2, 17, 31, 73] },
    .lucas { root := 3, primeFactors := [2, 3, 43, 149, 643] },
    .lucas { root := 3, primeFactors := [2, 3, 61, 103, 31051, 102773782927, 440014321269031] },
    .lucas { root := 11, primeFactors := [2, 3, 5, 23] },
    .lucas { root := 3, primeFactors := [2, 3, 137, 41676311] },
    .lucas { root := 17, primeFactors := [2, 5, 13, 19, 47, 359] },
    .lucas { root := 3, primeFactors := [2, 3, 5, 14667144042301] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 61, 801483281] },
    .lucas { root := 3, primeFactors := [2, 5, 13, 770657] },
    .lucas { root := 3, primeFactors := [2, 24083] },
    .lucas { root := 2, primeFactors := [2, 12041] },
    .lucas { root := 3, primeFactors := [2, 5, 7, 43] }])

/-- The 12 numbers `b₅³, …, b₅³ + 11` are composite. -/
theorem check_b6 : allFermatComposite (16022236204009818131831320183 ^ 3) (4113101149215104800030529537915953170486139623539759933135949994882770404074832568499 - 16022236204009818131831320183 ^ 3) = true := by
  decide +kernel

/-- **`g 5 = b₆`**: the 85-digit `b₆` is the least prime `≥ b₅³`. -/
theorem g_five : g 5 = 4113101149215104800030529537915953170486139623539759933135949994882770404074832568499 := by
  rw [g_succ, g_four]
  exact nextPrime_eq_of_check prime_b6 (by norm_num) check_b6

end Mills
