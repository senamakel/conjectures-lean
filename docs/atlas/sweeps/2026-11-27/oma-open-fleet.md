# OMA open-result fleet

27 November 2026. Ten Luna workers screened distinct mathematical families at
the OMA pin (Formal Conjectures `9097e2f90e66`, Lean `v4.33.1`). The target is
100 newly merged proofs, disproofs or substantive proof steps for open results.
None of this wave's candidates reached that state. Two reductions from the
previous wave merged and are tracked separately. The Lindelöf statement
submission remains distinct from a proof. [Erdős 770 reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4219) · [Robin reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4271) · [Lindelöf statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4230)

| Lane | Triage evidence |
| --- | --- |
| Erdős 250–349 and Agoh–Giuga | Erdős 307's coprimality variant already has live proof PRs. Erdős 287's prime variant remains genuinely open. The Agoh–Giuga target already has a reduction, with unresolved substantive hypotheses. [Erdős 307 PR #4257](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4257) · [Agoh–Giuga reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/919) |
| Erdős 500–899 | The Erdős 506 small-`n` target has an upstream missing answer definition. The apparent finite lead at Erdős 723 would require a projective plane of order 12. Erdős 473's new prime-circle reduction leaves universal existence in two residue classes mod 4. Bounded witness generation found circles for every even order 18–32, leaving the general step unresolved. [Prime-circle reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4309) · [Unquantified large-order result](https://arxiv.org/abs/2609.19114) |
| Erdős 1–249 and 900+ | Erdős 102's implication from Erdős 101 is already referenced in the problem source. The live brief for Erdős 133 flags a prior disproof. Erdős 1053 and 1055 had no concrete bridge. Erdős 1186 had public Lean proof reports and existing OMA bounds work. Erdős 1160 already has a pending reduction step. [Erdős 102](https://www.erdosproblems.com/102) · [Erdős 1186 related OMA work](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3344) · [Erdős 1160 PR #4376](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4376) |
| Algebra, geometry and Green | The low-dimensional Dixmier and Poisson targets have no short bridge in the pinned imports. Green 40's all-`n` version remains an open asymptotic problem. The Maxwell H2 desk brief returned 404, and Kintali's preprint already treats the collinear three-charge bound with the critical-circle argument. [Green 40](https://lefttosolve.com/p/Green40.green_40.variants.all_n) · [Maxwell reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4126) |
| ABC and Cramér | The proposed ABC route is the published equivalence of formulations. The Cramér route requires the open Firoozbakht input. The ABC lease attempt returned HTTP 500. [ABC equivalence](https://arxiv.org/abs/1409.2974) · [Firoozbakht reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3997) |
| OEIS and reused proofs | A069004 and A105751 had overlapping PRs. A103662's newly merged reduction leaves the decimal-zero property for all `2^(40k)` and mixed even bases coprime to 5. A157237's uniform three-term representation exceeds what the existing Romanoff density lemmas supply. [A103662 reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4284) · [A157237](https://oeis.org/A157237) |
| Other reduction steps | A069191's rank-one Hermitian interlacing obligation appears in the merged Lean file. Its exact API endpoint returned `not_found` and the lease request returned HTTP 500. Mathlib had ordered Hermitian eigenvalues but the search located no rank-one interlacing theorem at the pin. [Reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4154) · [Desk incident](https://github.com/GuillaumeBAUD-coder/open-math-agents/issues/3627) |

## Crystal component collision search

The crystal target asks whether `n = ab` determines the unordered pair
`{a,b}` among pairs of odd factors greater than 1 for which the biharmonic
mean is integral. Prior search covered minimum half-component through
1,500,000. The recurrence in Theorem 4 gives a cheap way to test an additional
product interval where different recurrence parameters could lead to the same
product. [Open target](https://lefttosolve.com/p/Arxiv.1601.03081.crystals_components_unique) · [Source and recurrence](https://arxiv.org/abs/1601.03081) · [Earlier range](easy-open-sweep.md)

Using the paper's parameter `w`, start at `(s,t) = (w,(w−1)^2)` and advance to
`(t,(w−2)t+2−s)`. For `w ≥ 4` the half-components increase. The first product
`(2w−1)(2(w−1)^2−1)` increases with `w` and gives a bound on the parameter
for any product limit. Parameters below 4 give only the small case 35 or a
factor 1. Enumerate `4 ≤ w ≤ 3,000,000` up to product
107,999,910,000,017,999,999, retaining only products strictly above
13,499,977,500,008,999,999, then sort by product and compare adjacent rows.
This checks a new product interval beyond the old minimum-component cutoff.
Stop at the first distinct-pair collision or after enumerating and sorting the
interval, with a 30-second wall limit. The C++ search used unsigned 128-bit
products. It found no collision among 1,532,047 pairs in 0.16 seconds with
approximately 67 MiB peak memory. This finite search has no Lean certificate.

### Fixed-parameter uniqueness

[CrystalParameter.lean](CrystalParameter.lean) checks directly against the
registry's `IsCrystalWithComponents` definition. For fixed product `n`,
write `s = a+b` and `t = c+d`. If both pairs share parameter `w`, their
equations are `s² = w(n+s+1)` and `t² = w(n+t+1)`. Cross multiplication
gives `(s−t)((s+t)(n+1)+st)=0`. Nonnegative distinct sums make the second
factor positive, so the sums agree. Equal sums and products determine the
unordered pair. The checked result uses only the three standard axioms and
leaves collisions between distinct parameters open.

The fixed-parameter proof is now part of a checked reduction of the exact OMA
target. It sorts both factorizations, then separates the remaining parameter
comparison according to whether the two smaller factors are coprime. In
the coprime case each smaller factor divides the opposite larger factor.
With a common divisor, one can cancel it from the product equation and
retain it in the two crystal conditions. Both obligations remain open.
The pinned OMA checker accepted the reduction with only the three standard
axioms. The PR discloses that the desk returned a non-JSON response and
issued no lease. [OMA PR #4439](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4439)

### Coprime branch

The parent crystal reduction merged. For its coprime step, equal products
force the factorizations to have the form `(a,c*m)` and `(c,a*m)`.
Their oddness forces odd `m`. For `m = 1`, sortedness forces `a = c`,
so the parameters agree. The nested reduction leaves the fixed multiplier
`m = 3` and odd multipliers `m ≥ 5` as separate obligations. The pinned
checker accepted it with only the three standard axioms. At submission
time the merged parent's step was not indexed by the desk. The PR records
the unsuccessful lease request. [Merged parent #4439](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4439) · [Nested reduction #4513](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4513)

The coprime split merged upstream. For `m = 3`, order the smaller components
so `a ≤ c ≤ 3a`. The quotient for `(c,3a)` lies strictly between 3 and 6.
Modulo 3 rules out 4, so the quotient is 5. The quotient for `(a,3c)` lies
between 5 and 11. For each candidate 6 through 11, subtracting nine times
the second conic equation from the first eliminates `c²`. Substitution
gives a polynomial in `a−3` with negative constant and nonpositive remaining
coefficients, a contradiction. The exact leaf proof passed the OMA pin
with the standard three axioms and was submitted upstream. The odd
`m ≥ 5` case and the shared-divisor branch remain open.
[Merged split #4513](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4513) · [Multiplier-three proof #4534](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4534)

### Finite candidate sets at each cross multiplier

[CrystalFixedMultiplier.lean](CrystalFixedMultiplier.lean) verifies at the
OMA pin that every fixed cross multiplier `m ≥ 2` admits only finitely
many possible first components after sorting. The two integral quotients
are each below `m² + 3`. For each quotient pair, if the second component
`c` satisfies `c² + Bc + D = 0` and the difference of the two conics
gives `Lc + M = 0`, the first component is a root of
`M² − BML + DL²`. Modulo `m` this polynomial is the monic square
`(X² − p(X+1))²`, where `p` is the first quotient, so the integer
polynomial is nonzero. This supplies a finite exact-algebra route for
each fixed multiplier. It leaves the unbounded multiplier assertion and
the shared-divisor case open.

An exact resultant scan tested the next two odd multipliers after 5. With
the smaller components ordered as `3 ≤ a ≤ c ≤ m*a`, the smaller quotient
satisfies `q < m+3` and the greater quotient satisfies `p < m²+3`. Only
`q < p` can give a distinct-parameter collision. The scan tested the 414
quotient pairs for `m = 7` and the 847 for `m = 9`, stopping on the first
admissible integer root or after exhausting these pairs. It found no
integer root `a ≥ 3` in 6.32 seconds, within a 60-second wall cap. For all
but `(m,p,q) = (7,18,3)`, a prime below 200 gives a resultant with no roots
modulo that prime. The exceptional quotient 3 can be handled separately
by the lower bound on the smaller quotient. These exploratory checks
suggest small kernel-checkable modular certificates. They have yet to
be certified in Lean.

### Checked cases for odd multipliers 5 through 15

The OMA pin checked the exact nested reduction for the coprime branch
with `m ≥ 5`. After sorting distinct components, the smaller quotient
satisfies `4 ≤ q < m+3` and the other satisfies `q ≤ p < m²+3`.
The submitted Lean file verifies 7,071 pairs `q < p` across 54 rows
using explicit moduli at most 89. Each certificate rules out every
residue of the eliminant's first-component variable. The remaining
obligations are `m ≥ 17, q = 4` and `m ≥ 17, q ≥ 5`; the former has
the consecutive-square parametrization from the crystal recurrence.
The exact pinned checker accepted the main implication with only
`propext`, `Classical.choice`, and `Quot.sound`. The desk returned
`not_found_or_solved` for the merged step's ID, which the PR discloses.
[Small-multiplier reduction #4741](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4741)

The non-coprime branch has a separate checked submission. For
`g = gcd(a,c)`, it writes the two pairs as `(g*x,y*z)` and
`(g*y,x*z)`, with `x,y` coprime. The remaining distinct-component
obligation forces `g = z` from the two normalized crystal divisibilities
and the order constraints. [GCD normalization #4633](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4633)

[CrystalQuotientFour.lean](CrystalQuotientFour.lean) checks the structural
description of the first remaining coprime branch. Whenever odd
`c ≤ b` satisfies `(c+b)² = 4(c+1)(b+1)`, there is a natural
`t` with `c+1 = 2t²` and `b+1 = 2(t+1)²`. The proof sets
`d = (b-c)/2`, derives `d² = b+c+1` and uses its oddness to write
`d = 2t+1`. More generally `gcd(c,b)` divides the quotient, so for
quotient four the odd components are coprime. Both checks use only the
standard axioms. The companion crystal divisibility remains the
arithmetic obligation after substituting `b = m*a`.

[CrystalM17.lean](CrystalM17.lean) checks both quotient branches at
`m = 17`, so any remaining coprime collision has `m ≥ 19`. The
direct residue test leaves `(p,q) = (60,4)` and `(264,4)`. In each
case the eliminant has a factor `a−1`, which is nonzero for `a ≥ 3`.
The remaining cubic has no roots modulo 13 and 19, respectively.
The combined quotient equality theorem checks at the pinned
formal-conjectures revision with only the standard axioms. OMA PR
#4741 covers multipliers through 15 and remains the upstream
submission for the parent step.

[CrystalM19.lean](CrystalM19.lean) verifies all 6,309 ordered quotient
pairs at multiplier 19. Moduli through 97 suffice and the direct
residue test covers every pair. The pinned Lean theorem uses only
the three standard axioms. Together the checks through multiplier
19 leave odd cross multipliers at least 21 in the coprime branch.

### Parity in the shared-divisor branch

The GCD normalization merged upstream. Its normalization obligation now
has a separate proof submission reusing the checked theorem from the
merged reduction. [Merged reduction #4633](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4633) · [Normalization proof #4974](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4974)

[CrystalEven.lean](CrystalEven.lean) verifies that for positive
`a ≤ b`, the divisibility `(a+1)(b+1) ∣ (a+b)²` forces both
components to be odd. Mixed parity would make an even denominator
divide an odd square. If both components are even, shift to the
odd integers `X = a+1` and `Y = b+1`. The Vieta partner
`(X−2)²/Y` is positive and odd and lies below `X` when `X ≥ 3`.
Descent reaches `X = 1`, where the quotient equation forces `Y = 1`.
The zero components contradict positivity. A preliminary exhaustive
screen of even smaller components through 100,000, using divisors of
`(a−1)²` to enumerate `b+1`, found no pair. The Lean proof
excludes every size with only standard axioms.

The exact OMA reduction uses this to split by whether the smaller
normalized coprime factor is 1 or at least 3. Both odd-parameter
branches remain open. The desk rejected the exact lease request with
`not_found_or_solved`, as disclosed in the submission.
[Odd-parameter reduction #4990](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4990)

[CrystalSharedBounds.lean](CrystalSharedBounds.lean) derives a finite
search range for fixed `g,x` in the sorted shared-divisor branch.
The first square divisibility gives `y*z+1 ∣ (g*x−1)²` by reducing
the numerator modulo `y*z+1`. Together with `g*y ≤ x*z`, this
implies `y*z ≤ g*x*(g*x−2)` and `y² ≤ x²*(g*x−2)`.
For `x = 1` this forces `y²+2 ≤ g`, hence `g ≥ 11` when
`y ≥ 3`. Both bounds check at the OMA pin with only the standard
axioms. The unbounded parameter ranges in #4990 remain open.

[CrystalSharedPartners.lean](CrystalSharedPartners.lean) checks a
second finite range, this time with the reduced components `x < y`
fixed while the common divisor `g` may vary. Write
`(y*z+1)*r = (g*x−1)²` and `(x*z+1)*s = (g*y−1)²` for the two
Vieta partners. The scaled difference `d = x³*s−y³*r` satisfies
`0 < d < min(2*x²,x*y)*(y−x)`. The second upper bound follows
from a square discriminant identity, with equality ruled out by
`z > g`. In addition, reducing the first square divisibility
modulo `g*x+1` gives
`g*x+1 ∣ 16*((x+y)*(d+(y−x)*y*(x+2*y)))²`. The right-hand
side is positive and ranges over finitely many values as `d`
varies. It therefore bounds `g` for fixed `x,y`, and the earlier
bound then bounds `z`. All three theorems use only the standard axioms.

[CrystalSharedSmallY.lean](CrystalSharedSmallY.lean) rules out the
normalized `x = 1` case for all odd `3 ≤ y ≤ 15`, with no cutoff on
`g` or `z`. The full crystal quotient makes each Vieta partner
even, so the positive difference is even and less than `2(y−1)`.
For each `y,d` the proof checks a prime factorization of the explicit
constant divisible by `g+1`. Of its divisors, the even values at least
`y²+3` give 9,870 candidate `y,d,g` triples in total. The
discriminant of the quadratic in the first partner must be a square,
but every candidate discriminant fails the exact integer-square test.
The pinned Lean proof checks the factorization, covers all divisors,
and evaluates exact square roots in the kernel. Its axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`.
