# Round 2 tasks

GRH_ELAB = cd ~/work/personal/conjectures-lean/worktrees/grh-compact-port/conjectures/grh && export PATH=$HOME/.elan/bin:$PATH && nice -n 10 lake env lean --tstack=400000 -DmaxHeartbeats=4000000 -DmaxSynthPendingDepth=3 -DautoImplicit=false -DrelaxedAutoImplicit=false <your file>
MATHLIB_ELAB = cd ~/work/personal/conjectures-lean/conjectures/erdos-985 && export PATH=$HOME/.elan/bin:$PATH && nice -n 10 lake env lean <your file>

Port context (grh tasks): these files are from lsernau/grh-lean `grh-compact/` (Lean v4.35 / Mathlib 56a00585),
being ported to our pin in PR #31. Known drift patterns: ~/work/personal/conjectures-lean/worktrees/grh-compact-port/conjectures/grh/STATUS.md
("Recurring fix patterns"). Upstream sibling files under that worktree's src/ are readable for context.

## torsion  (bach-sharp-gap, PR #29, STATUS.md step 2; file Torsion.lean; MATHLIB_ELAB)
Prove the three theorems in Torsion.lean (all `sorry` now). Hints: (ZMod (p^e))ˣ is cyclic for odd p;
a finite cyclic group has at most n solutions of x^n = 1; (ZMod (2^e))ˣ has order 2^(e-1) (e ≥ 1), so odd ℓ
gives only 1; for ℓ = 2, x^2 = 1 mod 2^e forces 2^(e-1) | x-1 or x+1 for e ≥ 3 (or use the structure
(ZMod (2^e))ˣ ≃ C2 × C(2^(e-2)) if Mathlib has it). Handle e = 0, 1, 2 separately.

## mellin  (grh port; file MellinTheta.lean = src/Lib/Analytic/DirichletTheta/MellinTheta.lean; GRH_ELAB)
Known errors at lines 37, 163, 172: set-membership vs predicate (`x ∈ {z | 0 < z.re}`), and a `rw` under an
image of `fun i ↦ (q*i)⁻¹`. Goal: elaborates with no errors, no sorry.

## discreteunits  (grh port; file DiscreteUnits.lean = src/Lib/ClassField/GaloisCohomology/DiscreteUnits.lean; GRH_ELAB)
Known error at line 171: `fun_prop` cannot prove continuity of `Prod.map (fun x ↦ ⇑u ∘ x) …`. There may be more
after it. Goal: elaborates with no errors, no sorry.

## measplace  (grh port; file Place.lean = src/Lib/General/Measure/Place.lean; GRH_ELAB)
Known errors: line 231 unknown constant `Membership.mem.intro` / `Set.Mem.intro`; simp max recursion at 232.
There may be more. Goal: elaborates with no errors, no sorry.
