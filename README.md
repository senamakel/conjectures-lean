# Bach's explicit Ankeny theorem under GRH in Lean

Work in progress. `Ankeny/Statement.lean` fixes the target statements; its definitions must not
change. The analytic toolkit (explicit formula for Dirichlet L-functions with weight
`(1 − n/x)`, Hadamard factorization, Perron formula, zero-sum bounds under GRH) comes from
[erdos-985](https://github.com/senamakel/erdos-985), required as a lake dependency.

GRH/RH is a hypothesis here. It is supplied by
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
whose statements are copied verbatim.
