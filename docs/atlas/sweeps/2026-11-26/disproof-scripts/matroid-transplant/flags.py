"""Flag f-vectors of the BCEL hyperplane-coalescence matroids (own reimplementation).

M_{k,q}: rank r = k+1. K = F_{q^k}, V = K + K (dim 2k over F_q), m = q^k free points,
b = q^{k^2} blocks P(W_c) + {p_{c_top}} indexed by linearised polynomials of q-degree < k.
alpha[S] for S subset of {1..k} (proper ranks), as a dict keyed by sorted tuples.
"""
from functools import lru_cache
from itertools import combinations
from math import comb


def gauss(d, i, q):
    if i < 0 or i > d:
        return 0
    num = 1
    den = 1
    for j in range(i):
        num *= q ** (d - j) - 1
        den *= q ** (j + 1) - 1
    return num // den


def make_A(q):
    @lru_cache(maxsize=None)
    def A(d, t, S):
        """flag count of D_{d,t} = L(F_q^d) x B_t with selected rank set S (tuple, increasing)."""
        if not S:
            return 1
        s = S[-1]
        Sp = S[:-1]
        tot = 0
        for i in range(max(0, s - t), min(d, s) + 1):
            tot += gauss(d, i, q) * comb(t, s - i) * A(i, s - i, Sp)
        return tot
    return A


def hyperplane_types(k, q):
    """list of ((d,t), multiplicity) for the hyperplanes of M_{k,q}, lower lattice D_{d,t}
    (the (k,1) type is the coalesced block; only its ranks < k are ever used)."""
    m = q ** k
    b = q ** (k * k)
    N = lambda i: gauss(2 * k, i, q)
    L = gauss(k, k - 1, q)
    types = [((k, 0), N(k) - b), ((k, 1), b), ((k - 1, 1), m * N(k - 1) - b * L)]
    for d in range(k - 2, -1, -1):
        types.append(((d, k - d), N(d) * comb(m, k - d)))
    return types


def all_subsets(n):
    out = []
    for j in range(n + 1):
        out += list(combinations(range(1, n + 1), j))
    return out


def coalescence_alpha(k, q):
    A = make_A(q)
    m = q ** k
    types = hyperplane_types(k, q)
    alpha = {}
    for S in all_subsets(k):
        if k not in S:
            alpha[S] = A(2 * k, m, S)
        else:
            Sp = S[:-1]
            alpha[S] = sum(mult * A(d, t, Sp) for (d, t), mult in types)
    return alpha


def product_alpha(d, t, q, r=None):
    """flag f-vector of D_{d,t}, optionally truncated to rank r (top added)."""
    A = make_A(q)
    n = d + t
    if r is None:
        r = n
    alpha = {}
    for S in all_subsets(r - 1):
        alpha[S] = A(d, t, S)
    return alpha, r


def beta_from_alpha(alpha):
    beta = {}
    for S in alpha:
        tot = 0
        for j in range(len(S) + 1):
            for T in combinations(S, j):
                tot += (-1) ** (len(S) - j) * alpha[T]
        beta[S] = tot
    return beta
