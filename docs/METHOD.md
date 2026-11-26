# Method

Every repo was built the same way, and most of what went wrong went wrong in the same few places.

**Targets come from connecting results that exist.** Since 2026-11-26 a target can be an open
conjecture in any area, and it is chosen because the pieces of its proof are already somewhere:
a lemma inside a large Lean proof, a theorem of one of our own projects, a conjecture solved last
month, a published implication between two conjectures. Scouts record every such link as an
edge in the [implication atlas](atlas/README.md), and we prove the easiest edges first. Four
earlier projects were found this way before it was the rule (artin-grh, abelian-erh, mertens-rh,
hironaka-fc): each needed one input, and riemann-hypothesis happened to prove it on the way to
its headline. An implication whose premise is still open is proved as `Y_of_X`, with the premise
as an argument.

**The statement comes first.** Before any proof, the target goes into `<Pkg>/Statement.lean` and
is not edited again. Where formal-conjectures has the statement, we copy it word for word. Where
it doesn't, we transcribe it from the paper and say so. This rule exists because the easiest way
to finish a hard proof is to weaken what it claims, and with a fixed file that shows up in a diff.

**RH is an argument of the theorem.** The main library of each repo never imports the RH proof.
A theorem reads `RiemannHypothesis → X` or `DirichletLNonvanishingRightOfHalf → X`, and a
separate `Unconditional/` file supplies the hypothesis from riemann-hypothesis in one line. So
each repo holds two results: the implication, which stands on Mathlib alone, and the
unconditional theorem.

**Agents did the proving, one per repo.** [OpenHuman](https://github.com/tinyhumansai/openhuman)
subagents each took one target on its own branch and opened a pull request. A lead session
then rebuilt the branch, read the `#print axioms` output itself, ran the unconditional check and
merged. An agent's report was never accepted without that rebuild. On 2026-11-22 a stale checkout
printed `sorryAx` under a headline theorem, and the rule dates from then.

**Large `x` by analysis, small `x` by computation.** Most of these theorems hold "for all `x`
above some point", and an explicit proof only works above a threshold. Below it we check every
case with a program whose correctness is proved in Lean and which runs through `native_decide`.
The work is in making the two ranges meet: sharpen the analytic constants until the threshold
drops to something a machine can reach. Three examples:

- erdos-985 checks every prime below `10^8`.
- grosswald-grh checks every prime below `10^13` in 2,502 chunks, about 3.3 million CPU-seconds.
- robin-rh sieves every integer below `1.07·10^13` in 624 chunks, about 54 core-hours.
- speiser-rh covers the band `5/2 ≤ |Im s| < 7` with 142,446 small discs in three minutes.

Agents write and size these checkers but do not run the large ones. The big runs go last, one at
a time, after an early attempt to run several at once overloaded the build machine.

**The published constant is the target.** A first proof often lands with a weaker constant than
the paper's, and the README then states the constant actually proved and why. Each of those
gaps was later closed. Bach's bound for the least non-residue went from `21/5` to `11/4` to
Bach's own `2` (lls-grh). Bach and Sorenson's bound went from `7/2` to their `2`. Schoenfeld's
bounds went from `1/8` to his `1/(8π)`, and Cramér's prime-gap constant from `2` to
Carneiro, Milinovich and Soundararajan's `22/25`. In every case the first estimate of what the
paper's constant would cost was too high: the barrier came from one loose step, and keeping
that step exact removed it.

**Missing background theory becomes a named hypothesis.** Some proofs need a classical theorem
that Mathlib doesn't have at our pin, such as the Kronecker-Weber theorem or Dirichlet's class
number formula. Those enter as explicit `Prop` arguments, never as `sorry`, and the
`Unconditional/` file discharges them from lemmas inside riemann-hypothesis where it has them.

**What did not work.**

- Erdős 233 asks for more than RH is known to give. We proved the classical RH bounds
  (Selberg's); the problem as posed stays open.
- A search for open Erdős problems that RH would settle by a new argument found nothing we kept.
- Several first guesses about attribution were wrong and were corrected against the papers.

The reasoning behind each dead end, and the constants that were sized up and rejected, are in
LivingBrain. The status of every box is in [`AGENTS.md`](../AGENTS.md).

**Public Lean code.** When a repo stalls we search for existing formalisations before writing
more. The search has turned up kernel-checked zeta enclosures
([smmercuri/zeta](https://github.com/smmercuri/zeta),
[teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab)), explicit zero counting
([anthropics/zeta-23-lean](https://github.com/anthropics/zeta-23-lean)) and a Weil explicit
formula inside calr3/ternary-goldbach. These are permissively licensed, so files can be vendored
with credit. riemann-hypothesis has no licence, so we import it and copy nothing from it.

