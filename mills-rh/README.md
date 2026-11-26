# Mills' constant to 87 decimals under RH in Lean

This repository proves that Mills' constant begins
`1.30637788386308069046861449260260571291678458515671364436805375996643405376682659882150…`,
87 correct decimals, and that a prime lies between `x³` and `(x+1)³` for every real
`x ≥ 2^{1/3} − 1 ≈ 0.26` (Caldwell–Cheng's Lemma 5, with their threshold). Both are proved
unconditionally in Lean, with RH supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
and Schoenfeld's θ bound with his constant `1/(8π)` taken from
[`schoenfeld-rh`](https://github.com/senamakel/schoenfeld-rh). The main library holds complete
Lean proofs that RH implies each statement and the enclosure `(1.3063778838, 1.3063778839)` of
the formal-conjectures statement, and proves the lower bound `A > 1.3063778838` with no
hypothesis. The fifth and sixth Mills primes (29 and 85 digits) are certified prime in the
kernel.

Mills (Bull. AMS 53, 1947) showed that there is a real `A > 1` with `⌊A^(3^n)⌋` prime for every
`n ≥ 1`; the least such `A` is *Mills' constant*. Caldwell and Cheng (*Determining Mills'
constant and a note on Honaker's problem*, J. Integer Seq. 8 (2005), Art. 05.4.1) showed that
under the Riemann hypothesis there is a prime between `x³` and `(x+1)³` for every
`x ≥ 2^{1/3} − 1` (their Lemma 5). So the greedy sequence `2, 11, 1361, 2521008887, …` never gets
stuck and its limit is the least Mills number. Computing its terms, they gave 600 decimals of the
constant (their Theorem 1, from ten certified primes, the last with 6854 digits).

**Literature status.** Lemma 5, the enclosure and the digits are *RH-consequences*
(Caldwell–Cheng 2005; formal-conjectures lists the enclosure as open). The lower bound
`A > 1.3063778838` is *known* unconditionally (Caldwell–Cheng). The proof follows Caldwell–Cheng,
with Schoenfeld's θ bound in place of his `π(x)` bound and Lucas certificates for the Mills
primes. The proof of RH is L. Alpöge's (2026), certified by the Lean FRO and the Mathlib
Initiative on 2026-11-21. Before it, only existence (Mills) and irrationality (Saito,
Mathematika 71, 2025) were known.

```lean
-- Unconditional/MillsUnconditional.lean
theorem mills_digits87_unconditional {A : ℝ} (hA : Mills.IsMinMills A) :
    ((1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501 : ℕ) : ℝ) / 10 ^ 87 ≤ A ∧
      A < (((1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501 : ℕ) : ℝ) + 1) / 10 ^ 87

theorem mills_digits30_unconditional {A : ℝ} (hA : Mills.IsMinMills A) :
    ((1306377883863080690468614492602 : ℕ) : ℝ) / 10 ^ 30 ≤ A ∧
      A < (((1306377883863080690468614492602 : ℕ) : ℝ) + 1) / 10 ^ 30

theorem prime_between_cubes_unconditional (x : ℝ) (hx : (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) ≤ (x + 1) ^ 3

theorem prime_strictly_between_cubes_unconditional (x : ℝ)
    (hx : (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 < x) :
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) < (x + 1) ^ 3

theorem mills_constant_bounds_unconditional {A : ℝ} (hA : Mills.IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839

-- Mills/CubesSharp.lean, Mills/Digits.lean (targets in Mills/Statement2.lean)
theorem Mills.caldwellChengLemma5_of_RH : CaldwellChengLemma5
theorem Mills.primeStrictlyBetweenCubes_of_RH : PrimeStrictlyBetweenCubesOfRH
theorem Mills.millsDigits30_of_RH : MillsDigits 30 1306377883863080690468614492602
theorem Mills.millsDigits87_of_RH : MillsDigits 87 1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501

def CaldwellChengLemma5 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) ≤ (x + 1) ^ 3
def PrimeStrictlyBetweenCubesOfRH : Prop :=
  RiemannHypothesis → ∀ x : ℝ, (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 < x →
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) < (x + 1) ^ 3
def MillsDigits (N D : ℕ) : Prop :=
  RiemannHypothesis → ∀ {A : ℝ}, IsMinMills A →
    (D : ℝ) / 10 ^ N ≤ A ∧ A < ((D : ℝ) + 1) / 10 ^ N

-- Mills/Certificates.lean (no hypothesis)
theorem Mills.g_four : g 4 = 16022236204009818131831320183
theorem Mills.g_five : g 5 = 4113101149215104800030529537915953170486139623539759933135949994882770404074832568499

-- Mills/Final.lean (LowerBoundOfRH in Mills/Statement.lean)
theorem Mills.lower_bound_of_RH : LowerBoundOfRH
theorem Mills.mills_bounds_of_RH (hRH : RiemannHypothesis) {A : ℝ} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839

def LowerBoundOfRH : Prop :=
  RiemannHypothesis → ∀ {A}, IsMinMills A → A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839

-- Mills/Cubes.lean (PrimeBetweenCubes in Mills/Upper.lean)
theorem Mills.primeBetweenCubes_of_RH (hRH : RiemannHypothesis) : PrimeBetweenCubes (10 ^ 9)

def PrimeBetweenCubes (x₀ : ℕ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3

-- Mills/Main.lean (no hypothesis)
theorem Mills.mills_lower_bound {A : ℝ} (hA : IsMinMills A) : (1.3063778838 : ℝ) < A
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `mills_digits30_unconditional`, `mills_digits87_unconditional`, `prime_between_cubes_unconditional`, `prime_strictly_between_cubes_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `mills_constant_bounds_unconditional` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `Mills.millsDigits30_of_RH`, `Mills.millsDigits87_of_RH` | C | `RiemannHypothesis` |
| `Mills.caldwellChengLemma5_of_RH`, `Mills.primeStrictlyBetweenCubes_of_RH` | C | `RiemannHypothesis` |
| `Mills.lower_bound_of_RH`, `Mills.mills_bounds_of_RH` | C | `RiemannHypothesis` |
| `Mills.primeBetweenCubes_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `Mills.mills_bounds_of_primeBetweenCubes` (the reduction) | C + H | `PrimeBetweenCubes x₀`, `x₀ ≤ 2521008887` |
| `Mills.mills_lower_bound` | D | none |
| `Mills.prime_b5`, `Mills.prime_b6`, `Mills.g_four`, `Mills.g_five` | D | none |
| `Mills.primeStrictlyBetweenCubes_small` (`1 ≤ x < 9`) | D | none |

`Mills.CaldwellChengLemma5`, `Mills.PrimeStrictlyBetweenCubesOfRH`, `Mills.MillsDigits` and
`Mills.CaldwellChengTheorem1` (`Mills/Statement2.lean`) transcribe Caldwell–Cheng's Lemma 5 and
Theorem 1; formal-conjectures has neither. Lemma 5 reads "there is at least one prime between
`x³` and `(x+1)³` for every `x ≥ x₀ = 2^{1/3} − 1`" with `x` real. At `x = x₀` the only candidate
is `2 = (x₀+1)³`, so "between" includes the upper end there. `CaldwellChengLemma5` says
`x³ < p ≤ (x+1)³`, and `PrimeStrictlyBetweenCubesOfRH` is the open-interval form for `x > x₀`.
Both are proved.

`IsMills` and `IsMinMills` are copied verbatim from
[formal-conjectures `Wikipedia/Mills.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mills.lean)
(commit `86a2f58a`), and `Mills.LowerBoundOfRH` in `Mills/Statement.lean` is its
`lower_bound_of_RH` as a proposition, with Mathlib's `RiemannHypothesis`. The main library does
not import riemann-hypothesis.

## Axioms

`lake env lean scripts/axioms.lean` (2026-11-24, branch `round9`):

```
'Mills.prime_2521008887' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.g_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.exists_mills_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_bounds_of_primeBetweenCubes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.lowerBoundOfRH_of_primeBetweenCubes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.primeBetweenCubes_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.lower_bound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_bounds_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.prime_b5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.prime_b6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.g_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.g_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.primeStrictlyBetweenCubes_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.caldwellChengLemma5_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Mills.primeStrictlyBetweenCubes_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Mills.primeBetweenCubes_one_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Mills.millsDigits30_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Mills.millsDigits87_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'Mills.millsDigits87_prefix' depends on axioms: [propext]
```

There is no `sorry` and no `axiom` declaration, and nothing in this repository uses
`native_decide`. The theorems of the `1/4` route (`Mills/Cubes.lean`), the
certificates, the finite range of Lemma 5 and `millsDigits87_prefix` use the standard three
axioms only. Everything built on Schoenfeld's `1/(8π)` bound (`caldwellChengLemma5_of_RH`, the
strict form, `primeBetweenCubes_one_of_RH`, `millsDigits30_of_RH`, `millsDigits87_of_RH`) adds the
22 `native_decide` axioms of `Schoenfeld.schoenfeldTheta_of_RH` in schoenfeld-rh: 21 for
`PsiCert` (20 chunks of a segmented sieve checking `ψ` up to `10^10`, plus `checkA_psiCert`;
13.9 CPU-minutes) and `checkA_theta` (θ on the small range). Each checker has a soundness proof
in schoenfeld-rh.

Primality is checked in the kernel, not by `native_decide`: `2521008887` by a Lucas certificate
evaluated with `reduce_mod_char`, and `b₅` (29 digits, 9 links) and `b₆` (85 digits, 26 links)
by Mathlib's `primality` tactic, whose proof term is `prime_of_lucasCheck … (Eq.refl true)`, so
the kernel computes the modular powers with its GMP-backed `Nat` arithmetic. The two factors
`4767859693324212149320551641267` and `158805050530653056698774265519084179` of `b₆ − 1` were
found with GMP-ECM; the certificate only needs them, not how they were found. Minimality
(`g 4 = b₅`, `g 5 = b₆`) checks the 80 and 12 integers below each prime with a Fermat test to
base 2 (`fermatComposite`, proved sound by `not_prime_of_fermatComposite`), by kernel `decide`.

## Proof outline

1. `Mills/Greedy.lean`: `g 0 = 2`, and `g (n+1)` is the least prime `≥ (g n)³` (it exists
   unconditionally). `g_one`, `g_two`, `g_three` compute `11, 1361, 2521008887`: the least prime
   above `2³ = 8` is `11`, above `11³ = 1331` is `1361`, and above `1361³ = 2521008881` is
   `2521008887`, by checking `3`, `30` and `6` integers.
2. Minimality, no RH (`g_le_floor`): if `⌊A^(3^n)⌋` is prime for all `n`, then
   `⌊A^(3^(n+1))⌋ ≥ ⌊A^(3^n)⌋³`, so by induction `⌊A^(3^(n+1))⌋ ≥ g n`. At `n = 3`,
   `A^81 ≥ 2521008887 > 1.3063778838^81` (`lower_bound`, a rational comparison by `norm_num`).
3. `Mills/Upper.lean`: from `PrimeBetweenCubes`, `g (n+1) < (g n + 1)³`, and strictly
   `g (n+1) + 1 < (g n + 1)³` since `(g n+1)³ − 1 = g n·(g n² + 3 g n + 3)` is composite.
   Hence `lo n = (g n)^{1/3^{n+1}}` increases, `hi n = (g n + 1)^{1/3^{n+1}}` decreases, and
   `lo n ≤ hi m` for all `n, m`. `PrimeBetweenCubes` is used only at the points `x = g n` with
   `n ≥ 3`, that is `x ≥ 2521008887`, so any `x₀ ≤ 2521008887` suffices and the cubes between
   `x₀³` and `2521008887³` are never needed.
4. The limit `A = sup lo n` satisfies `⌊A^(3^(n+1))⌋ = g n` (`floor_greedyLimit`), so it is a
   Mills number (`isMills_greedyLimit`), and `A^81 ≤ 2521008888 < 1.3063778839^81`.
5. `Mills/Main.lean`: the least Mills number `A` is at most this one and exceeds the lower bound.
6. `Mills/Cubes.lean`: `PrimeBetweenCubes (10^9)` from RH, with
   `Schoenfeld.thetaBound_of_RH : ThetaBound (1/4) 599` from schoenfeld-rh (rev `b2c3137`), that
   is `|θ(y) − y| < √y log² y / 4` for `y ≥ 599`. A prime lies in `(a, b]` when `θ(b) > θ(a)`.
   With `a = x³` and `b = x³ + 3x² + 3x = (x+1)³ − 1` the bound gives `θ(b) − θ(a) > 0` as soon
   as `3x² + 3x > ½ √b log² b`. Putting `t = (x+1)^{1/8}` (so `√b ≤ t¹²`, `log b ≤ 24 t`), this
   reduces to `3(t⁸ − 1)² > 288 t¹⁴`, true for `t ≥ 13`, that is `x ≥ 10^9`. This route gives
   the enclosure `(1.3063778838, 1.3063778839)`.
7. `Mills/CubesSharp.lean`: Lemma 5 from `Schoenfeld.schoenfeldTheta_of_RH : RiemannHypothesis →
   SchoenfeldTheta`, Schoenfeld's 1976 bound `|θ(y) − y| < √y log² y / (8π)` for `y ≥ 599`.
   * Real `x ≥ 9`: with `a = x³ ≥ 599`, `b = (x+1)³ − 1`, `u = x + 1` and `t = u^{1/4}`,
     `√b ≤ t⁶` and `log b ≤ 12 log t ≤ 12t/e`, so `2·√b log² b/(8π) ≤ 288 t⁸/(8π e²) < 1.56 u²`,
     which is below `b − a = 3u² − 3u` for `u ≥ 10`. So `θ(b) > θ(a)` and a prime lies in
     `(x³, (x+1)³)` (`primeStrictlyBetweenCubes_large`).
   * `1 ≤ x < 9`: with `k = ⌊2x⌋ ∈ [2, 17]`, one of 16 primes `5, 11, 17, …, 739` satisfies
     `(k+1)³ < 8p < (k+2)³`, so `x³ < p < (x+1)³` (`primeStrictlyBetweenCubes_small`, no RH).
   * `2^{1/3} − 1 ≤ x < 1`: `p = 2`.

   The integer form `PrimeBetweenCubes 1` follows.
8. `Mills/Certificates.lean`: `g 4 = b₅` and `g 5 = b₆` (certified primes, Fermat-tested gaps).
9. `Mills/Digits.lean`: `g k ≤ A^{3^{k+1}} < g k + 1` for the least Mills number
   (`minMills_pow_bounds`), so `A ∈ [b^{1/m}, (b+1)^{1/m})` with `m = 3^{k+1}`. At `k = 4`
   (`m = 243`) this fixes 30 decimals, and at `k = 5` (`m = 729`) 87. The digit comparisons
   `D^m ≤ b·10^{Nm}` and `(b+1)·10^{Nm} ≤ (D+1)^m` are kernel `decide`s on numbers of up to
   64,000 digits. `millsDigits87_prefix` checks that the 87 digits are the first 87 of
   Caldwell–Cheng's table.

## Layout

| File | Content |
|---|---|
| `Mills/Statement.lean` | `IsMills`, `IsMinMills` (verbatim), `LowerBoundOfRH` |
| `Mills/Statement2.lean` | Caldwell–Cheng Lemma 5 (two forms), `MillsDigits`, Theorem 1 (600 digits) |
| `Mills/Greedy.lean` | greedy sequence, the four values, primality certificate, lower bound |
| `Mills/Upper.lean` | `PrimeBetweenCubes`, monotone enclosure, greedy limit is Mills |
| `Mills/Main.lean` | reduction to `PrimeBetweenCubes`, lower bound |
| `Mills/Cubes.lean` | `PrimeBetweenCubes (10^9)` from RH via Schoenfeld's θ bound |
| `Mills/Final.lean` | `lower_bound_of_RH`, `mills_bounds_of_RH` |
| `Mills/CubesSharp.lean` | Lemma 5 for real `x ≥ 2^{1/3} − 1` from Schoenfeld's `1/(8π)` |
| `Mills/Certificates.lean` | Fermat composite checker, Lucas certificates for `b₅`, `b₆`, `g 4`, `g 5` |
| `Mills/Digits.lean` | 30 and 87 decimals of Mills' constant |
| `Unconditional/MillsUnconditional.lean` | one-line discharge of RH from riemann-hypothesis |
| `scripts/check-unconditional.sh` | builds and checks the unconditional file |
| `scripts/axioms.lean` | `#print axioms` for the headline theorems |

## Deviations from the literature

Digits: Caldwell–Cheng's Theorem 1 states 600 decimals under RH; this repository proves 87
(`millsDigits87_of_RH`). Their digits come from the Mills primes `b₁, …, b₁₀` (`b₁₀` has 6854
digits; `b₇`, `b₈`, `b₉` were proved prime with Titanix, an ECPP program, and `b₁₀` with Morain's
fastECPP in about 68 CPU-days). The 600-digit target `CaldwellChengTheorem1` is stated in
`Mills/Statement2.lean`. Each further Mills prime roughly triples the digits: `b₇` (254 digits)
would give 256 decimals and `b₈` (762 digits) would reach 600. Neither has a Lucas or
Pocklington certificate within reach. After trial division to `10^7` and GMP-ECM at
`B1 = 10^6` (15 CPU-minutes per number), `b₇ − 1 = 2²·3³·7·C251` and
`b₇ + 1 = 2·5²·61·601·291539·500536237·184968672986919581·P217` (`C251` an unfactored
composite, `P217` a 217-digit probable prime). So `b₇ + 1` is fully factored, and Morrison's
`N + 1` test (Lucas sequences, not in Mathlib) would reduce `b₇` to `P217`. But `P217 − 1` has a
192-digit composite cofactor and `P217 + 1 = 2·2267·55320204473·P202`, so the descent goes on
one probable prime at a time, a few digits per step. An `N − 1` (Pocklington) proof of `b₇`
needs about 127 factored digits of `b₇ − 1`, which are not available. The next step is an
elliptic-curve (Goldwasser–Kilian, Atkin–Morain) certificate checker in Lean, with an ECPP
certificate for `b₇` produced elsewhere. It does not need the Hasse bound if each step asks
`q > 2√N + 1` (the trivial bound `#E(𝔽_p) ≤ 2p + 1`), but it does need the group law of a
Weierstrass curve reduced from `ℤ/N` to `𝔽_p`, which is not in Mathlib.

Lemma 5 has Caldwell–Cheng's statement and threshold. They prove it from Schoenfeld's bound
`|π(x) − li(x)| < √x log x/(8π)` (`x ≥ 2657`) for `x > 2657^{1/3}`, and "using a computer
program" below that. Here the analytic step uses Schoenfeld's θ bound (from `y = 599`, so from
`x = 9`) instead of the π bound, and the range below is 16 explicit primes and `p = 2`.

The enclosure `mills_bounds_of_RH` (the formal-conjectures statement) goes through
`Mills/Cubes.lean`, with θ constant `1/4` and threshold `10^9` in place of Caldwell–Cheng's
`2657`. Any threshold up to `2521008887` gives the same enclosure, since primes between cubes
are only used from `x = g 3 = 2521008887`.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`).

```
lake exe cache get
lake build            # target `Mills`
```

The repository's own modules take under a minute once their dependencies are built
(`Mills.Certificates` about 10 s, `Mills.Digits` about 10 s, both mostly kernel arithmetic).

`Schoenfeld` is a lake dependency (`schoenfeld-rh` rev `b2c3137`). Its closure includes the
vendored Rosser zero count (`Vendor/Rosser/`, about 95,000 lines), about 3 CPU-hours from cold;
set `LEAN_NUM_THREADS` to the number of cores.

(Building erdos-985 from its Mathlib cache takes about 2 minutes on 16 cores.)

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `mills_constant_bounds_unconditional` | the least Mills number lies in `(1.3063778838, 1.3063778839)` | standard three |
| `prime_between_cubes_unconditional` | Caldwell–Cheng Lemma 5: a prime `p` with `x³ < p ≤ (x+1)³` for every real `x ≥ 2^{1/3} − 1` | standard three + schoenfeld-rh's 22 `native_decide` |
| `prime_strictly_between_cubes_unconditional` | a prime in `(x³, (x+1)³)` for every real `x > 2^{1/3} − 1` | standard three + the same 22 |
| `mills_digits30_unconditional` | Mills' constant to 30 decimals | standard three + the same 22 |
| `mills_digits87_unconditional` | Mills' constant to 87 decimals | standard three + the same 22 |

`#print axioms` output (2026-11-24, from `scripts/check-unconditional.sh`, 15 min wall on a loaded
box, no `sorryAx`):

```
'mills_constant_bounds_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'prime_between_cubes_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'prime_strictly_between_cubes_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'mills_digits30_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
'mills_digits87_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1]
```

Checked against riemann-hypothesis commit `507a75d91d` with
`scripts/check-unconditional.sh /path/to/riemann-hypothesis` (needs about 93 GB of cache, about
19 GB of RAM and a limit of roughly 900k open files; on Linux run
`sudo prlimit --pid $$ --nofile=2000000:2000000` first).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. The Schoenfeld bounds come from the `schoenfeld-rh` lake dependency.
`IsMills`, `IsMinMills` and the `lower_bound_of_RH` statement are copied from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Apache-2.0, commit
`86a2f58a`).
The 600 digits in `Mills/Statement2.lean` are copied from the table of Caldwell–Cheng's
Theorem 1. The factors of `b₆ − 1` were found with GMP-ECM 7.0.6; only the resulting
certificate is in the repository.
