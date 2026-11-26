"""Flag f-vectors (alpha dicts) of geometric lattices built from simple pieces.
A lattice is (n, alpha) with alpha keyed by sorted tuples of ranks in 1..n-1."""
from itertools import product as iprod
from flags import make_A, all_subsets, coalescence_alpha, gauss
from math import comb


def pg(d, q):
    A = make_A(q)
    return d, {S: A(d, 0, S) for S in all_subsets(d - 1)}


def boolean(n):
    A = make_A(2)
    return n, {S: A(0, n, S) for S in all_subsets(n - 1)}


def Dlat(d, t, q):
    A = make_A(q)
    n = d + t
    return n, {S: A(d, t, S) for S in all_subsets(n - 1)}


def line(s):
    """rank-2 lattice with s atoms (U_{2,s})."""
    al = {(): 1, (1,): s}
    return 2, al


def truncate(L, r):
    n, al = L
    assert r <= n
    return r, {S: al[S] for S in all_subsets(r - 1)}


def prod(L1, L2):
    n1, a1 = L1
    n2, a2 = L2
    n = n1 + n2
    out = {}
    for S in all_subsets(n - 1):
        tot = 0
        k = len(S)
        # choose weakly increasing a_i in [0,n1], b_i = s_i - a_i weakly increasing in [0,n2]
        def rec(i, aprev, bprev, avals, bvals):
            nonlocal tot
            if i == k:
                A1 = tuple(sorted(set(x for x in avals if 0 < x < n1)))
                B1 = tuple(sorted(set(x for x in bvals if 0 < x < n2)))
                tot += a1[A1] * a2[B1]
                return
            s = S[i]
            for a in range(aprev, min(n1, s) + 1):
                b = s - a
                if b < bprev or b > n2:
                    continue
                if i > 0 and a == aprev and b == bprev:
                    continue
                rec(i + 1, a, b, avals + [a], bvals + [b])
        rec(0, 0, 0, [], [])
        out[S] = tot
    return n, out


def coalescence(k, q):
    return k + 1, coalescence_alpha(k, q)


def pg_minus_point(n, q):
    A = make_A(q)
    al = {}
    for S in all_subsets(n - 1):
        v = A(n, 0, S)
        if S and S[0] == 1:
            v -= A(n - 1, 0, tuple(s - 1 for s in S[1:]))
        al[S] = v
    return n, al


def bose_burton(r, k, q):
    """PG(r-1,q) minus PG(k-1,q): flats = subspaces not inside W (dim k), plus 0."""
    A = make_A(q)
    al = {}
    for S in all_subsets(r - 1):
        v = A(r, 0, S)
        if S:
            s1 = S[0]
            v -= gauss(k, s1, q) * A(r - s1, 0, tuple(x - s1 for x in S[1:]))
        al[S] = v
    return r, al
