import Mills.Upper

/-!
# Mills' constant lies in `(1.3063778838, 1.3063778839)` given primes between cubes

* `mills_lower_bound` needs no hypothesis (tier D).
* `mills_bounds_of_primeBetweenCubes` is the full enclosure of the least Mills number, with the
  analytic input `PrimeBetweenCubes x₀` as an explicit argument (tier C/H).
* `lowerBoundOfRH_of_primeBetweenCubes` is the formal-conjectures statement
  `Mills.lower_bound_of_RH`, reduced to "RH implies `PrimeBetweenCubes x₀`".
-/

set_option linter.constructorNameAsVariable false

namespace Mills

/-- **No hypotheses**: the least Mills number exceeds `1.3063778838`; more generally so does every
Mills number `A > 1`. -/
theorem mills_lower_bound {A : ℝ} (hA : IsMinMills A) : (1.3063778838 : ℝ) < A :=
  lower_bound hA.1.1 hA.1.2

/-- **Existence**: given primes between cubes above `x₀ ≤ 2521008887`, a Mills number exists,
and it is `< 1.3063778839`. -/
theorem exists_mills_lt {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) :
    ∃ A : ℝ, A > 1 ∧ IsMills A ∧ A < 1.3063778839 := by
  refine ⟨greedyLimit, one_lt_greedyLimit h hx, isMills_greedyLimit h hx, ?_⟩
  by_contra hle
  push Not at hle
  have h1 : (1.3063778839 : ℝ) ^ 81 ≤ greedyLimit ^ 81 := pow_le_pow_left₀ (by norm_num) hle 81
  have h2 := greedyLimit_pow_le h hx
  have h3 : (2521008888 : ℝ) < (1.3063778839 : ℝ) ^ 81 := by norm_num
  linarith

/-- **Mills' constant lies in `(1.3063778838, 1.3063778839)`**, given primes between cubes above
some `x₀ ≤ 2521008887` (Caldwell–Cheng 2005). -/
theorem mills_bounds_of_primeBetweenCubes {x₀ : ℕ} (h : PrimeBetweenCubes x₀)
    (hx : x₀ ≤ 2521008887) {A : ℝ} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  refine ⟨mills_lower_bound hA, ?_⟩
  obtain ⟨B, hB1, hBM, hBlt⟩ := exists_mills_lt h hx
  exact lt_of_le_of_lt (hA.2 ⟨hB1, hBM⟩) hBlt

/-- The formal-conjectures statement `Mills.lower_bound_of_RH`, given that RH yields primes between
cubes above some `x₀ ≤ 2521008887`. -/
theorem lowerBoundOfRH_of_primeBetweenCubes {x₀ : ℕ} (hx : x₀ ≤ 2521008887)
    (hRH : RiemannHypothesis → PrimeBetweenCubes x₀) : LowerBoundOfRH :=
  fun hRH' _ hA => mills_bounds_of_primeBetweenCubes (hRH hRH') hx hA

end Mills
