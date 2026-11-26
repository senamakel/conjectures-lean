"""Cheng-Liu style matroids PG(r-1,2) minus D, D = P(W) u S (S line-separated from W),
built explicitly: flats = flat spans; flag f-vector by DP; then P,Q,Z,Y via the composition algebra.
Bounded exploration: r in {5,6,7}, q = 2, D drawn as in Cheng-Liu Cor. 1.2 (S inside an affine chart of a
complement X, so automatically line-separated), plus random caps for k = 0."""
import sys, random
from itertools import combinations
from invs import build, evaluate
from flags import all_subsets

def subspaces(r):
    """all subspaces of F_2^r as frozensets of nonzero vectors (ints), grouped by dim."""
    by = {0: {frozenset()}}
    for d in range(1, r + 1):
        nxt = set()
        for U in by[d - 1]:
            span = set(U) | {0}
            for v in range(1, 1 << r):
                if v not in span:
                    nxt.add(frozenset((span | {v ^ u for u in span}) - {0}))
        by[d] = nxt
    return by

def flags_of(r, D, by):
    E = set(range(1, 1 << r)) - D
    flats = {d: [] for d in range(r + 1)}
    for d, Us in by.items():
        for U in Us:
            F = frozenset(U & E)
            # flat span: E cap U spans U  <=>  rank(F) = d
            if rank(F) == d:
                flats[d].append(F)
    # alpha by DP over rank sets
    al = {}
    idx = {d: list(flats[d]) for d in flats}
    for S in all_subsets(r - 1):
        if not S:
            al[S] = 1; continue
        cnt = {F: 1 for F in idx[S[0]]}
        for a, b in zip(S, S[1:]):
            new = {}
            for G in idx[b]:
                new[G] = sum(c for F, c in cnt.items() if F <= G)
            cnt = new
        al[S] = sum(cnt.values())
    return al, len(E)

def rank(F):
    basis = []
    for v in F:
        for bv in basis:
            v = min(v, v ^ bv)
        if v:
            basis.append(v)
    return len(basis)

def cl_D(r, k, s, rng):
    # V = W + X, W = first k coords; X hyperplane H = {x_last = 0}; chart = X-vectors with last coord 1
    W = [v for v in range(1, 1 << k)]
    chart = [v for v in range(1, 1 << r) if (v & ((1 << k) - 1)) == 0 and (v >> (r - 1)) & 1]
    S = rng.sample(chart, s)
    return set(W) | set(S)

if __name__ == "__main__":
    I = build(8)
    rng = random.Random(20261126)
    for r in [5, 6]:
        by = subspaces(r)
        for k in range(0, (r + 1) // 2):
            chartsize = 2 ** (r - k - 1)
            for s in sorted(set([0, 1, 2, 3, 5, 8, min(chartsize, 2 ** (r - 2) - 2 ** k), chartsize // 2])):
                if s > chartsize or (2 ** k - 1) + s >= 2 ** (r - 2):
                    continue
                for trial in range(3 if s else 1):
                    D = cl_D(r, k, s, rng)
                    al, n = flags_of(r, D, by)
                    res = {}
                    bad = []
                    for nm in "PQZY":
                        c = [int(x) for x in evaluate(I[nm], al, r).coeffs()]
                        res[nm] = c
                        if any(c[i] ** 2 < c[i - 1] * c[i + 1] for i in range(1, len(c) - 1)):
                            bad.append(nm + "-notLC")
                        if any(c[i - 1] > c[i] < c[i + 1] for i in range(1, len(c) - 1)):
                            bad.append(nm + "-notUnimodal")
                    print(r, k, s, n, "P=", res["P"], "Y=", res["Y"], bad if bad else "ok")
                    sys.stdout.flush()
