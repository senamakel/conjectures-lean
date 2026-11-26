import Mathlib
import Mills.Statement

/-!
Second set of target statements (round 9). Fixed once written (see the conjectures tracker,
rule 3); `Mills/Statement.lean` is unchanged.

Source: C. K. Caldwell and Y. Cheng, *Determining Mills' Constant and a Note on Honaker's
Problem*, J. Integer Sequences 8 (2005), Article 05.4.1.

* **Lemma 5**: "Assume the Riemann Hypothesis. There is at least one prime between `x³` and
  `(x+1)³` for every `x ≥ x₀ = 2^{1/3} − 1`." Here `x` is real. At `x = x₀` itself
  `(x₀+1)³ = 2` and `x₀³ < 1`, so the only candidate is `p = 2 = (x₀+1)³`: "between" includes
  the upper end. `CaldwellChengLemma5` is that reading; `PrimeStrictlyBetweenCubesOfRH` is the
  strict form, which holds for every `x > x₀`.
* **Theorem 1**: "Assume the Riemann Hypothesis. The minimum Mills' constant (for the exponent
  c=3) begins with the following 600 digits: 1.3063778838 6308069046 …". `MillsDigits N D` says
  that the least Mills number begins with the `N + 1` digits of `D` (one before the point, `N`
  after it), i.e. `D / 10^N ≤ A < (D + 1) / 10^N`. The paper's table prints `1.3063778838`
  followed by 59 blocks of ten digits: 600 digits after the point. `CaldwellChengTheorem1` is
  `MillsDigits 600` with those digits, copied from the table.
-/

namespace Mills

/-- **Caldwell–Cheng 2005, Lemma 5**: under RH there is a prime between `x³` and `(x+1)³` for
every real `x ≥ 2^{1/3} − 1`. -/
def CaldwellChengLemma5 : Prop :=
  RiemannHypothesis → ∀ x : ℝ, (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) ≤ (x + 1) ^ 3

/-- The strict form of Lemma 5: under RH, for every real `x > 2^{1/3} − 1` some prime lies in
the open interval `(x³, (x+1)³)`. -/
def PrimeStrictlyBetweenCubesOfRH : Prop :=
  RiemannHypothesis → ∀ x : ℝ, (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 < x →
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) < (x + 1) ^ 3

/-- Under RH, the least Mills number begins with the decimal digits of `D`, `N` of them after
the point: `D / 10^N ≤ A < (D + 1) / 10^N`. -/
def MillsDigits (N D : ℕ) : Prop :=
  RiemannHypothesis → ∀ {A : ℝ}, IsMinMills A →
    (D : ℝ) / 10 ^ N ≤ A ∧ A < ((D : ℝ) + 1) / 10 ^ N

/-- The digits of Caldwell–Cheng's Theorem 1, as one natural number (`1.3063…` times
`10^600`), copied row by row from the paper's table. -/
def caldwellChengDigits600 : ℕ :=
  1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501403701197395707296960938103086882238861447816353486887133922146194353457871100331881405093575355831932648017213832361522359062218601610856679057215197976095161992952797079925631721527841237130765849112456317518426331056521535131866841550790793723859233522084218420405320517689026025793443008695290636205698968726212274997876664385157661914387728449820775905648255609150041237885247936260880466881540643744253401310736114409413765036437930126767211713103026522838661546668804874760951441079075406984172603473107746

/-- **Caldwell–Cheng 2005, Theorem 1**: under RH, Mills' constant begins with these 600 digits. -/
def CaldwellChengTheorem1 : Prop := MillsDigits 600 caldwellChengDigits600

end Mills
