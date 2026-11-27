# Registry candidates with linked external Lean proofs

Compared the [current formal-conjectures source ea8e3e198ded](https://github.com/google-deepmind/formal-conjectures/tree/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8) to the [registry snapshot 93b38ba8d287](https://github.com/GuillaumeBAUD-coder/open-math-agents/tree/93b38ba8d28746749d2b84638fac80468c6164e5) by source file and unique theorem name. The scan found 5 known or open entries with a linked Lean artifact and no merged direct proof file. The [registry ingestion script](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/93b38ba8d28746749d2b84638fac80468c6164e5/scripts/ingest.py#L320) excludes declarations that already carried a formal proof link at its pin. This scan therefore focuses on links added after the pin. For each lead, check the exact statements, live status, license, dependency closure, and upstream PRs before taking a lease.

| Exact ID | Registry kind | Difficulty | Existing reduction | Linked Lean artifact |
| --- | --- | ---: | --- | --- |
| [OeisA60841.conjecture1](https://lefttosolve.com/p/OeisA60841.conjecture1) | open | 53 | No | [Proof 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-10-000008) |
| [Erdos897.erdos_897.variants.parts.i](https://lefttosolve.com/p/Erdos897.erdos_897.variants.parts.i) | open | 52 | No | [Proof 1](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean) |
| [Erdos897.erdos_897.variants.parts.ii](https://lefttosolve.com/p/Erdos897.erdos_897.variants.parts.ii) | open | 52 | No | [Proof 1](https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos897.lean) |
| [OeisA100475.conjecture](https://lefttosolve.com/p/OeisA100475.conjecture) | open | 52 | No | [Proof 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-11-000001) |
| [MovingSofa.ambidextrousSofaConstant_eq_romiksSofa_area](https://lefttosolve.com/p/MovingSofa.ambidextrousSofaConstant_eq_romiksSofa_area) | open | 59 | Yes | [Proof 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-13-000003) |
