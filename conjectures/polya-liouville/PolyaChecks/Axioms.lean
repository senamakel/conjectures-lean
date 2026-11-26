import Polya

/-!
# Axiom allow-list for the headline theorems

`lake build PolyaChecks` fails if a headline theorem picks up an axiom outside the allowed set
(`propext`, `Classical.choice`, `Quot.sound` and its documented `native_decide`), in particular
`sorryAx`.
-/
