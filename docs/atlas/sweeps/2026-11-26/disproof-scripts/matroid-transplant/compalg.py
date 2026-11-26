"""Composition (flag) algebra: universal incidence-algebra functions of graded posets whose
value on an interval depends only on chains through it and their rank jumps.

An element is a dict composition(tuple of positive ints) -> fmpz_poly in t.
Value on a graded poset of rank n with flag f-vector alpha:  sum_{c |= n} w(c) alpha(S(c)).
"""
from functools import lru_cache
from flint import fmpz_poly, fmpq_poly

T = fmpz_poly([0, 1])
ONE = fmpz_poly([1])
ZERO = fmpz_poly([])


def compositions(n):
    if n == 0:
        return [()]
    out = []
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            out.append((first,) + rest)
    return out


class Alg:
    def __init__(self, nmax):
        self.nmax = nmax
        self.comps = {n: compositions(n) for n in range(nmax + 1)}

    def conv(self, f, g):
        h = {}
        for n in range(self.nmax + 1):
            for c in self.comps[n]:
                s = ZERO
                for j in range(len(c) + 1):
                    a = f.get(c[:j]); b = g.get(c[j:])
                    if a is not None and b is not None and a != 0 and b != 0:
                        s += a * b
                if s != 0:
                    h[c] = s
        return h

    def inverse(self, f):
        """two-sided inverse, assuming f(()) = 1."""
        assert f[()] == ONE
        g = {(): ONE}
        for n in range(1, self.nmax + 1):
            for c in self.comps[n]:
                s = ZERO
                for j in range(1, len(c) + 1):
                    a = f.get(c[:j]); b = g.get(c[j:])
                    if a is not None and b is not None:
                        s += a * b
                if s != 0:
                    g[c] = -s
        return g

    def tpow(self):
        """T(x,y) = t^{rk(x,y)} (zeta weighted by t^rank)."""
        f = {(): ONE}
        for n in range(1, self.nmax + 1):
            f[(n,)] = T ** n
        return f

    def zeta(self):
        f = {(): ONE}
        for n in range(1, self.nmax + 1):
            f[(n,)] = ONE
        return f

    def mobius(self):
        return self.inverse(self.zeta())

    def chi(self):
        return self.conv(self.mobius(), self.tpow())

    def sgn(self, f):
        return {c: (f[c] if sum(c) % 2 == 0 else -f[c]) for c in f}

    def rev(self, f):
        out = {}
        for c, p in f.items():
            n = sum(c)
            coeffs = [int(x) for x in p.coeffs()]
            coeffs += [0] * (n + 1 - len(coeffs))
            assert len(coeffs) == n + 1, (c, p)
            out[c] = fmpz_poly(coeffs[::-1])
        return out

    def right_kls(self, kappa):
        """right KLS function f: f(x,x)=1, deg f(x,y) < rk/2 for x<y, f^rev = kappa * f."""
        f = {(): ONE}
        for n in range(1, self.nmax + 1):
            for c in self.comps[n]:
                R = ZERO
                for j in range(1, len(c) + 1):
                    a = kappa.get(c[:j]); b = f.get(c[j:])
                    if a is not None and b is not None:
                        R += a * b
                # t^n P(1/t) - P(t) = R
                co = [int(x) for x in R.coeffs()] + [0] * (n + 2)
                for i in range(n + 1):
                    assert co[i] == -co[n - i], ("not antisymmetric", c, R)
                low = [-co[i] for i in range(n + 1) if 2 * i < n]
                p = fmpz_poly(low)
                if p != 0:
                    f[c] = p
        return f

    def left_kls(self, kappa):
        """left KLS g: g^rev = g * kappa."""
        g = {(): ONE}
        for n in range(1, self.nmax + 1):
            for c in self.comps[n]:
                R = ZERO
                for j in range(0, len(c)):
                    a = g.get(c[:j]); b = kappa.get(c[j:])
                    if a is not None and b is not None:
                        R += a * b
                co = [int(x) for x in R.coeffs()] + [0] * (n + 2)
                for i in range(n + 1):
                    assert co[i] == -co[n - i], ("not antisymmetric", c, R)
                low = [-co[i] for i in range(n + 1) if 2 * i < n]
                p = fmpz_poly(low)
                if p != 0:
                    g[c] = p
        return g


def evaluate(f, alpha, n):
    """value of f on a rank-n poset with flag f-vector alpha (keys: sorted tuples of ranks in 1..n-1)."""
    s = ZERO
    for c in compositions(n):
        w = f.get(c)
        if w is None:
            continue
        S = []
        acc = 0
        for x in c[:-1]:
            acc += x
            S.append(acc)
        s += w * alpha[tuple(S)]
    return s
