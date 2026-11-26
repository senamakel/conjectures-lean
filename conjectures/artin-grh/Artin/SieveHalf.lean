import Artin.Sieve.Assembly
import Artin.Kummer.Degree
import Artin.Kummer.Density

/-!
# The sieve half, proved

`artin_of_effectiveKummerChebotarev` is the sieve half of the split in `Artin/Interfaces.lean`:
effective Chebotarev for the Kummer fields of `a` gives a positive density of primes with `a` as a
primitive root. It is `artin_of_effectiveKummerChebotarev_of_kummer` (`Artin/Sieve/Assembly.lean`)
with its two Kummer-theory hypotheses discharged by `Artin/Kummer/`:

* `KummerDegreeLowerBound a` (B5) from `Artin.Kummer.exists_mul_totient_le_kummerDegree`;
* `KummerDensityPos a` (B6) from `Artin.Kummer.kummerDensity_pos_of_not_isSquare`.

The statement lives here rather than in `Artin/Interfaces.lean` because both the sieve and the
Kummer files import `Artin/Interfaces.lean` for `kummerDegree`, `kummerCount` and
`EffectiveKummerChebotarev`; proving it there would be an import cycle.
-/

namespace Artin

open ArtinPrimitiveRootsConjecture

/-- Blueprint B5, discharged: `k φ(k) ≪ [K_k : ℚ]` for `a ∉ {0, 1, -1}`. -/
theorem kummerDegreeLowerBound_of_ne {a : ℤ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ -1) :
    KummerDegreeLowerBound a := by
  obtain ⟨c, hc, h⟩ := Kummer.exists_mul_totient_le_kummerDegree ha0 ha1 ha2
  exact ⟨c, hc, fun k hk hk0 => h k hk hk0⟩

/-- Blueprint B6, discharged: `δ(a) > 0` for `a` not a square and `a ≠ -1`. -/
theorem kummerDensityPos_of_not_isSquare {a : ℤ} (ha : ¬IsSquare a) (ha' : a ≠ -1) :
    KummerDensityPos a :=
  Kummer.kummerDensity_pos_of_not_isSquare ha ha'

/-- **Sieve half** (statement as in the split of `Artin/Interfaces.lean`): Hooley's sieve plus
Kummer theory. Effective Chebotarev for the Kummer fields of `a` gives a positive density of
primes `p` for which `a` is a primitive root. -/
theorem artin_of_effectiveKummerChebotarev (a : ℤ) (ha : ¬IsSquare a) (ha' : a ≠ -1)
    (h : EffectiveKummerChebotarev a) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime} := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact ha ⟨1, by simp⟩
  exact artin_of_effectiveKummerChebotarev_of_kummer a ha ha'
    (kummerDegreeLowerBound_of_ne ha0 ha1 ha') (kummerDensityPos_of_not_isSquare ha ha') h

end Artin
