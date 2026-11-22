import Artin.SieveHalf
import Artin.Analytic.Counting
import Artin.Analytic.Continuation
import Artin.Analytic.Core.Unsmoothing

/-!
# Artin's conjecture under Hooley's hypothesis and Hecke's continuation

`conditional_artin_primitive_roots.parts.i` (`Artin/Main.lean`) assumes only
`HooleyHypothesis a`. That hypothesis says something about every function `Z` that continues
`ζ_{K_k}` to `ℂ ∖ {1}`, but to use it one needs such a `Z`, with the functional equation, and
neither our Mathlib pin nor upstream Mathlib has it. So the theorem here takes Hecke's
continuation as an explicit extra hypothesis, `DedekindContinuation` (`Artin/Analytic/Continuation.lean`),
for each Kummer field `K_k`, `k` squarefree. With Hecke's theorem formalised, a separate
`Unconditional/` module can discharge it and recover the statement of `Artin/Main.lean`.

The proof is the chain

* `kummerPsiBounds_of_hooley_of_continuation`: RH and Hecke's continuation for every `ζ_{K_k}`
  give `KummerPsiBounds a`, by the per-field analytic core `psiKBound_of_continuation`
  (blueprint steps A1–A4, `Artin/Analytic/Core/`), whose constant is absolute;
* `effectiveKummerChebotarev_of_kummerPsiBounds` (`Artin/Analytic/Counting.lean`, sorry-free);
* `artin_of_effectiveKummerChebotarev` (`Artin/SieveHalf.lean`, sorry-free).
-/

namespace Artin.Analytic

open ArtinPrimitiveRootsConjecture

/-- **The analytic core** (blueprint A1–A4): Hooley's hypothesis plus Hecke's continuation
for every Kummer field `K_k` gives the Lagarias–Odlyzko bound
`|ψ_{K_k}(x) - x| ≤ C √x (log |d_{K_k}| + n_k log x) log x`, with one `C` for all squarefree `k`. -/
theorem kummerPsiBounds_of_hooley_of_continuation (a : ℤ) (h : HooleyHypothesis a)
    (hc : ∀ k : ℕ, Squarefree k → DedekindContinuation (Kummer.KField a k)) :
    KummerPsiBounds a := by
  obtain ⟨C, hC⟩ := psiKBound_of_continuation
  exact ⟨C, fun k hk => hC (Kummer.KField a k) (h k hk) (hc k hk)⟩

/-- The analytic half, with Hecke's continuation as a hypothesis. -/
theorem effectiveKummerChebotarev_of_hooley_of_continuation (a : ℤ) (ha : a ≠ 0)
    (h : HooleyHypothesis a)
    (hc : ∀ k : ℕ, Squarefree k → DedekindContinuation (Kummer.KField a k)) :
    EffectiveKummerChebotarev a :=
  effectiveKummerChebotarev_of_kummerPsiBounds ha (kummerPsiBounds_of_hooley_of_continuation a h hc)

end Artin.Analytic

namespace ArtinPrimitiveRootsConjecture

open Artin.Analytic

/-- **Artin's Conjecture on Primitive Roots**, first half, conditional on the Riemann hypothesis
for the Dedekind zeta functions of the fields $\mathbb{Q}(\zeta_k, a^{1/k})$, $k$ squarefree
[Ho67], and on Hecke's analytic continuation of those zeta functions (a theorem, not yet in
Mathlib). Same conclusion as `conditional_artin_primitive_roots.parts.i`. -/
theorem conditional_artin_primitive_roots.parts.i_of_continuation (a : ℤ) (ha : ¬IsSquare a)
    (ha' : a ≠ -1) (h : HooleyHypothesis a)
    (hc : ∀ k : ℕ, Squarefree k → DedekindContinuation (Artin.Kummer.KField a k)) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime} := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  exact Artin.artin_of_effectiveKummerChebotarev a ha ha'
    (effectiveKummerChebotarev_of_hooley_of_continuation a ha0 h hc)

end ArtinPrimitiveRootsConjecture
