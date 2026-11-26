import Schoenfeld.PsiCert.Run
import Schoenfeld.PsiCert.Chunks.C00
import Schoenfeld.PsiCert.Chunks.C01
import Schoenfeld.PsiCert.Chunks.C02
import Schoenfeld.PsiCert.Chunks.C03
import Schoenfeld.PsiCert.Chunks.C04
import Schoenfeld.PsiCert.Chunks.C05
import Schoenfeld.PsiCert.Chunks.C06
import Schoenfeld.PsiCert.Chunks.C07
import Schoenfeld.PsiCert.Chunks.C08
import Schoenfeld.PsiCert.Chunks.C09
import Schoenfeld.PsiCert.Chunks.C10
import Schoenfeld.PsiCert.Chunks.C11
import Schoenfeld.PsiCert.Chunks.C12
import Schoenfeld.PsiCert.Chunks.C13
import Schoenfeld.PsiCert.Chunks.C14
import Schoenfeld.PsiCert.Chunks.C15
import Schoenfeld.PsiCert.Chunks.C16
import Schoenfeld.PsiCert.Chunks.C17
import Schoenfeld.PsiCert.Chunks.C18
import Schoenfeld.PsiCert.Chunks.C19

/-!
# The PsiCert chain

`Inv st0` (`inv_init`) and the 20 chunk transitions give `Inv st20`.
-/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

/-- The final state. -/
def st_final : PS := st20

theorem inv_final : Inv st_final := by
  have h0 : Inv st0 := inv_init
  have h1 := runSegs_sound _ _ _ h0 chunk00
  have h2 := runSegs_sound _ _ _ h1 chunk01
  have h3 := runSegs_sound _ _ _ h2 chunk02
  have h4 := runSegs_sound _ _ _ h3 chunk03
  have h5 := runSegs_sound _ _ _ h4 chunk04
  have h6 := runSegs_sound _ _ _ h5 chunk05
  have h7 := runSegs_sound _ _ _ h6 chunk06
  have h8 := runSegs_sound _ _ _ h7 chunk07
  have h9 := runSegs_sound _ _ _ h8 chunk08
  have h10 := runSegs_sound _ _ _ h9 chunk09
  have h11 := runSegs_sound _ _ _ h10 chunk10
  have h12 := runSegs_sound _ _ _ h11 chunk11
  have h13 := runSegs_sound _ _ _ h12 chunk12
  have h14 := runSegs_sound _ _ _ h13 chunk13
  have h15 := runSegs_sound _ _ _ h14 chunk14
  have h16 := runSegs_sound _ _ _ h15 chunk15
  have h17 := runSegs_sound _ _ _ h16 chunk16
  have h18 := runSegs_sound _ _ _ h17 chunk17
  have h19 := runSegs_sound _ _ _ h18 chunk18
  have h20 := runSegs_sound _ _ _ h19 chunk19
  exact h20

theorem final_a : 10 ^ 10 ≤ st_final.a := by decide

end Schoenfeld.PsiCert
