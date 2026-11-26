import SunA243164.Compute.Checker
import SunA243164.Compute.Chunk00
import SunA243164.Compute.Chunk01
import SunA243164.Compute.Chunk02
import SunA243164.Compute.Chunk03
import SunA243164.Compute.Chunk04
import SunA243164.Compute.Chunk05
import SunA243164.Compute.Chunk06
import SunA243164.Compute.Chunk07
import SunA243164.Compute.Chunk08
import SunA243164.Compute.Chunk09
import SunA243164.Compute.Chunk10
import SunA243164.Compute.Chunk11
import SunA243164.Compute.Chunk12
import SunA243164.Compute.Chunk13
import SunA243164.Compute.Chunk14
import SunA243164.Compute.Chunk15
import SunA243164.Compute.Chunk16
import SunA243164.Compute.Chunk17
import SunA243164.Compute.Chunk18
import SunA243164.Compute.Chunk19

/-!
# The finite range: every prime `P < 10^8` of index `π(P) > 6`

Twenty chunks of `5·10^6`, each a `native_decide` evaluation of `countFrom` (`Chunk00` …
`Chunk19`), chained through the prime counts at the chunk boundaries. Soundness:
`SunA243164.Compute.countFrom_sound`.
-/

namespace SunA243164.Compute

/-- Extend a verified prefix `[0, lo)` by one chunk. -/
lemma extend {lo k c c' : ℕ} (h : countFrom lo k c = some c') (hc : c = Nat.count Nat.Prime lo)
    (hprev : ∀ P, P < lo → P.Prime → 6 < Nat.primeCounting P → GoodPrime P) :
    c' = Nat.count Nat.Prime (lo + k) ∧
      ∀ P, P < lo + k → P.Prime → 6 < Nat.primeCounting P → GoodPrime P := by
  obtain ⟨h1, h2⟩ := countFrom_sound k lo c c' h hc
  refine ⟨h1, fun P hP hp h6 => ?_⟩
  by_cases hlo : P < lo
  · exact hprev P hlo hp h6
  · exact h2 P (by omega) hP hp h6

theorem verifiedBelow_10_8 : VerifiedBelow 100000000 := by
  have s0 : 0 = Nat.count Nat.Prime (0 * 5000000) ∧
      ∀ P, P < 0 * 5000000 → P.Prime → 6 < Nat.primeCounting P → GoodPrime P :=
    ⟨by simp, fun P h => by omega⟩
  have s1 := extend chunk_ok_0 s0.1 s0.2
  have s2 := extend chunk_ok_1 s1.1 s1.2
  have s3 := extend chunk_ok_2 s2.1 s2.2
  have s4 := extend chunk_ok_3 s3.1 s3.2
  have s5 := extend chunk_ok_4 s4.1 s4.2
  have s6 := extend chunk_ok_5 s5.1 s5.2
  have s7 := extend chunk_ok_6 s6.1 s6.2
  have s8 := extend chunk_ok_7 s7.1 s7.2
  have s9 := extend chunk_ok_8 s8.1 s8.2
  have s10 := extend chunk_ok_9 s9.1 s9.2
  have s11 := extend chunk_ok_10 s10.1 s10.2
  have s12 := extend chunk_ok_11 s11.1 s11.2
  have s13 := extend chunk_ok_12 s12.1 s12.2
  have s14 := extend chunk_ok_13 s13.1 s13.2
  have s15 := extend chunk_ok_14 s14.1 s14.2
  have s16 := extend chunk_ok_15 s15.1 s15.2
  have s17 := extend chunk_ok_16 s16.1 s16.2
  have s18 := extend chunk_ok_17 s17.1 s17.2
  have s19 := extend chunk_ok_18 s18.1 s18.2
  have s20 := extend chunk_ok_19 s19.1 s19.2
  intro P hP h6 hlt
  exact s20.2 P (by omega) hP h6

end SunA243164.Compute
