import Mathlib

/-!
# Target statements for the `k`-free generalisation (fixed once written; tracker rule 3)

`Powerfree` is copied verbatim (definition body) from google-deepmind/formal-conjectures,
`FormalConjecturesForMathlib/Algebra/Powerfree.lean` (commit `9097e2f9`, checked 2026-11-24,
Apache License 2.0). It is placed in the `Erdos969` namespace so that it cannot clash with a later
Mathlib definition. formal-conjectures has no statement about the count of `k`-free integers, so
`kFreeCounting`, `kFreeCountingError`, `AxerKFreeBound` and `MontgomeryVaughanBound` are this
repository's own; `kFreeCounting` follows the shape of `squarefreeCounting` in
`Erdos969/Statement.lean`.

Let `Q_k(x)` count the `k`-free integers in `[1, x]`, and `E_k(x) = Q_k(x) - x / ζ(k)`.

* `AxerKFreeBound k`: `E_k(x) = O(x^{2/(2k+1)+ε})` for every `ε > 0`. Under RH this is
  Axer's theorem (1911), as reported by Pappalardi, *A survey on k-freeness* (2003), §2. For
  `k = 2` it is `AxerBound` (see `Erdos969.KFree.axerKFreeBound_two_iff`).
* `MontgomeryVaughanBound k`: `E_k(x) = O(x^{1/(k+1)+ε})` for every `ε > 0`. Under RH this is
  Montgomery and Vaughan, *The distribution of squarefree numbers*, Recent Progress in Analytic
  Number Theory, Vol. 1 (Durham, 1979), Academic Press, 1981, pp. 247–256. The paper itself was
  not available; the statement is as quoted by Pappalardi (2003) and by Meng, arXiv:1408.0429,
  §1. **This target is not proved in this repository.**

`ζ(k)` is written `(riemannZeta k).re`: for an integer `k ≥ 2`, `riemannZeta k` is the real number
`∑ n⁻ᵏ`.
-/

namespace Erdos969

open Filter Asymptotics

section Powerfree
variable {M : Type*} [Monoid M]

/-- `m` is `k`-th-power-free: every `x` with `x ^ k ∣ m` is a unit (formal-conjectures). -/
def Powerfree (k : ℕ) (m : M) : Prop :=
  ∀ ⦃x : M⦄, x ^ k ∣ m → IsUnit x

end Powerfree

open Classical in
/-- The `k`-free counting function `Q_k(x)`. -/
noncomputable def kFreeCounting (k x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (Powerfree k)).card

/-- The error term in `Q_k(x) = x / ζ(k) + E_k(x)`. -/
noncomputable def kFreeCountingError (k x : ℕ) : ℝ :=
  (kFreeCounting k x : ℝ) - x / (riemannZeta k).re

/-- **Axer's bound for `k`-free numbers**: `E_k(x) = O(x^{2/(2k+1)+ε})` for every `ε > 0`. -/
def AxerKFreeBound (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℕ => |kFreeCountingError k x|) =O[atTop]
      fun x : ℕ => (x : ℝ) ^ (2 / (2 * (k : ℝ) + 1) + ε)

/-- **Montgomery–Vaughan's bound**: `E_k(x) = O(x^{1/(k+1)+ε})` for every `ε > 0`. -/
def MontgomeryVaughanBound (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℕ => |kFreeCountingError k x|) =O[atTop]
      fun x : ℕ => (x : ℝ) ^ (1 / ((k : ℝ) + 1) + ε)

end Erdos969
