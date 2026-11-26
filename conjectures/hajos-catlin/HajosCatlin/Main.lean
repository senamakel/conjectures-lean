import HajosCatlin.Statement
import HajosCatlin.Graph
import HajosCatlin.NoSubdivision

/-!
# Hajós' conjecture is false (Catlin 1979)

Catlin's graph `C₅[K₃]` has chromatic number at least `8` (`eight_le_chromaticNumber`) and no
subdivision of `K₈` (`not_containsSubdivision`). The headline theorem is formal-conjectures'
`HajosConjecture.hajos_conjecture`, statement unchanged.
-/

open SimpleGraph

namespace HajosConjecture

/-- **Hajós' conjecture is false** (Catlin 1979). The statement of formal-conjectures'
`HajosConjecture.hajos_conjecture`, word for word; the witness is `C₅[K₃]` with `k = 8`. -/
theorem hajos_conjecture : ¬
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      (k : ℕ∞) ≤ G.chromaticNumber → ContainsSubdivision (completeGraph (Fin k)) G := by
  intro h
  exact HajosCatlin.not_containsSubdivision
    (h HajosCatlin.catlin 8 HajosCatlin.eight_le_chromaticNumber)

/-- The same theorem against the copied statement `HajosConjectureFalse`. -/
theorem hajosConjectureFalse : HajosConjectureFalse := hajos_conjecture

/-- formal-conjectures' `hajos_conjecture.variants.catlin` at `k = 8`. -/
theorem hajos_conjecture.variants.catlin_eight : CatlinVariant 8 :=
  ⟨Fin 5 × Fin 3, inferInstance, HajosCatlin.catlin, HajosCatlin.eight_le_chromaticNumber,
    HajosCatlin.not_containsSubdivision⟩

end HajosConjecture
