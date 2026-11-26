import Implications.Dickson.Statement

/-!
# Schinzel's hypothesis H implies Dickson's conjecture and Bunyakovsky's conjecture

Both are specialisations: Dickson's conjecture is hypothesis H for linear forms, and
Bunyakovsky's conjecture is hypothesis H for one polynomial. The statements are the
formal-conjectures ones (`Implications.Dickson.Statement`).
-/

open Polynomial

namespace Implications.Dickson

/-- Schinzel's hypothesis H implies Dickson's conjecture. -/
theorem dickson_of_schinzel (h : SchinzelConjecture) : DicksonConjecture :=
  fun fs hfs hfs' => h fs (fun f hf => (hfs f hf).2) hfs'

/-- Schinzel's hypothesis H implies Bunyakovsky's conjecture. -/
theorem bunyakovsky_of_schinzel (h : SchinzelConjecture) : BunyakovskyConjecture := by
  rintro f ⟨hf, hS⟩
  have H := h {f} (by simpa using hf) hS
  simpa using H

end Implications.Dickson
