import Miller.GRH

/-! Axiom audit for the main results. -/

-- Standard three only.
#print axioms Miller.miller_of_bach
#print axioms Miller.prime_iff_of_bach
#print axioms Miller.exists_proper_subgroup_liars
-- Conditional on `BachSubgroupBound 2`, which no repository proves.
#print axioms Miller.millerTest_iff_prime
-- Standard three + the 8 `native_decide` axioms of ankeny-grh's finite check.
#print axioms Miller.miller_of_GRH
#print axioms Miller.prime_iff_of_GRH
#print axioms Miller.millerTestGRH_iff_prime
