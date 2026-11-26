"""Lattice of flats of a matroid given by a rank oracle on bitmasks, and the inverse Z-polynomial
computed directly from the definitions (no flag algebra, no layer formula).

Definitions used (Gao-Ruan-Xie arXiv:2507.01332, eqs. (2)-(3); Elias-Proudfoot-Wakefield KL):
  chi_{[F,G]}(t) = sum_{F<=H<=G} mu(F,H) t^{rk G - rk H}
  t^d P_{[F,G]}(1/t) - P_{[F,G]}(t) = sum_{F<H<=G} chi_{[F,H]}(t) P_{[H,G]}(t),  deg P < d/2
  Qhat = P^{-1} in the incidence algebra,  Q_{[F,G]} = (-1)^{rk G - rk F} Qhat_{[F,G]}
  Yhat_M = sum_F (-1)^{rk F} Q_{[0,F]}(t) t^{rk M - rk F} mu(F,1),   Y_M = (-1)^{rk M} Yhat_M
Polynomials are lists of Python ints (exact).
"""
from itertools import combinations


def padd(a, b, s=1):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + s * (b[i] if i < len(b) else 0) for i in range(n)]


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


class Lattice:
    """flats: list of bitmasks; rk: list of ranks; le[i]: set of j with flats[i] <= flats[j]."""

    def __init__(self, n, rank):
        self.n = n
        full = (1 << n) - 1
        def cl(S):
            r = rank(S)
            for e in range(n):
                if not (S >> e) & 1 and rank(S | (1 << e)) == r:
                    S |= 1 << e
            return S
        bot = cl(0)
        seen = {bot}
        frontier = [bot]
        while frontier:
            nxt = []
            for F in frontier:
                for e in range(n):
                    if not (F >> e) & 1:
                        G = cl(F | (1 << e))
                        if G not in seen:
                            seen.add(G); nxt.append(G)
            frontier = nxt
        fl = sorted(seen, key=lambda F: (rank(F), F))
        self.flats = fl
        self.rk = [rank(F) for F in fl]
        self.r = rank(full)
        m = len(fl)
        self.up = [[j for j in range(m) if fl[j] & fl[i] == fl[i]] for i in range(m)]
        self.top = m - 1
        assert fl[-1] == cl(full) and self.rk[-1] == self.r

    def rank_counts(self):
        W = [0] * (self.r + 1)
        for x in self.rk:
            W[x] += 1
        return W

    def mobius(self):
        m = len(self.flats)
        mu = {}
        for i in range(m):
            mu[(i, i)] = 1
            # order up-set by rank
            ups = sorted(self.up[i], key=lambda j: self.rk[j])
            for j in ups:
                if j == i:
                    continue
                s = 0
                for k in ups:
                    if k != j and self.flats[j] & self.flats[k] == self.flats[k] and (i, k) in mu:
                        s += mu[(i, k)]
                mu[(i, j)] = -s
        return mu

    def invZ(self):
        """returns (Y, P_top, Q_top) for the whole lattice, computed from the definitions."""
        m = len(self.flats); rk = self.rk; fl = self.flats
        mu = self.mobius()
        below = lambda a, b: fl[b] & fl[a] == fl[a]
        # chi on all intervals
        chi = {}
        for (i, j), v in mu.items():
            pass
        for i in range(m):
            for j in self.up[i]:
                d = rk[j] - rk[i]
                c = [0] * (d + 1)
                for k in self.up[i]:
                    if below(k, j):
                        c[rk[j] - rk[k]] += mu[(i, k)]
                chi[(i, j)] = c
        # P on intervals, by increasing length
        P = {}
        pairs = sorted(((i, j) for i in range(m) for j in self.up[i]), key=lambda p: rk[p[1]] - rk[p[0]])
        for (i, j) in pairs:
            d = rk[j] - rk[i]
            if d == 0:
                P[(i, j)] = [1]; continue
            R = []
            for k in self.up[i]:
                if k != i and below(k, j):
                    R = padd(R, pmul(chi[(i, k)], P[(k, j)]))
            R = R + [0] * (d + 1 - len(R))
            for a in range(d + 1):
                assert R[a] == -R[d - a], "KL antisymmetry failed"
            P[(i, j)] = trim([-R[a] for a in range(d + 1) if 2 * a < d])
        # Qhat = P^{-1}: sum_{i<=k<=j} Qhat(i,k) P(k,j) = delta
        Qh = {}
        for (i, j) in pairs:
            if i == j:
                Qh[(i, j)] = [1]; continue
            s = []
            for k in self.up[i]:
                if k != j and below(k, j):
                    s = padd(s, pmul(Qh[(i, k)], P[(k, j)]))
            Qh[(i, j)] = trim([-x for x in s])
        def Q(i, j):
            sg = -1 if (rk[j] - rk[i]) % 2 else 1
            return [sg * x for x in Qh[(i, j)]]
        b, t = 0, self.top
        r = self.r
        Yh = []
        for F in range(m):
            sg = -1 if rk[F] % 2 else 1
            term = pmul([sg * x for x in Q(b, F)], [0] * (r - rk[F]) + [mu[(F, t)]])
            Yh = padd(Yh, term)
        Y = trim([(-1 if r % 2 else 1) * x for x in Yh])
        return Y, P[(b, t)], Q(b, t)


def rank_table_from_bases(n, bases):
    """rank of every subset (bitmask) from a list of bases (bitmasks)."""
    N = 1 << n
    indep = bytearray(N)
    for B in bases:
        indep[B] = 1
    # downward closure
    for S in range(N - 1, -1, -1):
        if indep[S]:
            x = S
            while x:
                e = x & -x
                indep[S ^ e] = 1
                x ^= e
    rk = [0] * N
    for S in range(1, N):
        if indep[S]:
            rk[S] = bin(S).count('1')
        else:
            best = 0; x = S
            while x:
                e = x & -x
                v = rk[S ^ e]
                if v > best: best = v
                x ^= e
            rk[S] = best
    return rk


def revlex_bases(n, r, s):
    subs = sorted(combinations(range(n), r), key=lambda c: tuple(reversed(c)))
    return [sum(1 << e for e in c) for c, ch in zip(subs, s) if ch == '*']


def dual_bases(n, bases):
    full = (1 << n) - 1
    return [full ^ B for B in bases]
