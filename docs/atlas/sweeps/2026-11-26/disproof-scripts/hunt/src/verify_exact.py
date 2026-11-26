"""Exact, floating-point-free check of a counterexample to Cazenave's Conjecture 2 (#20829),
lambda_2(A) <= mu_1(L) - 2 for connected graphs.

The graph is rebuilt from its description, not from the search output:
  G(k, p): two copies of K_k minus an edge {x_i, y_i}; join x_1 to x_2 by a path with p internal vertices.
Certificate: rational a, b with b - 2 < a and
  #roots of charpoly(A) in (a, oo) >= 2   (so lambda_2 > a)
  #roots of charpoly(L) in [b, oo) == 0   (so mu_1 < b)
Root counts use Sturm sequences over Fractions; charpolys by Faddeev-LeVerrier over Fractions.
"""
from fractions import Fraction as F
import sys, itertools

def graph(k, p):
    V = 2 * k + p
    E = set()
    for c in range(2):
        vs = list(range(c * k, (c + 1) * k))
        for a, b in itertools.combinations(vs, 2):
            E.add((a, b))
        E.discard((vs[0], vs[1]))           # missing edge x=vs[0], y=vs[1]
    path = [0] + list(range(2 * k, 2 * k + p)) + [k]
    for a, b in zip(path, path[1:]):
        E.add((min(a, b), max(a, b)))
    return V, sorted(E)

def connected(V, E):
    nb = {v: set() for v in range(V)}
    for a, b in E: nb[a].add(b); nb[b].add(a)
    seen = {0}; st = [0]
    while st:
        u = st.pop()
        for w in nb[u]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == V

def matmul(X, Y):
    n = len(X)
    return [[sum(X[i][t] * Y[t][j] for t in range(n)) for j in range(n)] for i in range(n)]

def charpoly(M):
    """Faddeev-LeVerrier: returns c with det(xI - M) = sum c[i] x^(n-i), c[0] = 1."""
    n = len(M); c = [F(1)]
    Mk = [[F(0)] * n for _ in range(n)]
    I = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    for k in range(1, n + 1):
        Mk = matmul(M, [[Mk[i][j] + c[-1] * I[i][j] for j in range(n)] for i in range(n)])
        ck = -sum(Mk[i][i] for i in range(n)) / k
        c.append(ck)
    return c

def peval(p, x):
    r = F(0)
    for a in p: r = r * x + a
    return r

def pdiv_rem(a, b):
    a = a[:]
    while len(a) >= len(b):
        q = a[0] / b[0]
        for i in range(len(b)): a[i] -= q * b[i]
        a.pop(0)
    while a and a[0] == 0: a.pop(0)
    return a

def sturm(p):
    d = [p[i] * (len(p) - 1 - i) for i in range(len(p) - 1)]
    seq = [p, d]
    while True:
        r = pdiv_rem(seq[-2], seq[-1])
        if not r: break
        seq.append([-x for x in r])
    return seq

def sign_changes(seq, x):
    vals = [peval(s, x) for s in seq]
    vals = [v for v in vals if v != 0]
    return sum(1 for u, v in zip(vals, vals[1:]) if (u > 0) != (v > 0))

def sign_changes_inf(seq):
    vals = [s[0] for s in seq]   # leading coeffs decide sign at +oo
    return sum(1 for u, v in zip(vals, vals[1:]) if (u > 0) != (v > 0))

def roots_above(p, a, strict=True):
    """number of distinct real roots in (a, oo); if not strict, in [a, oo)."""
    seq = sturm(p)
    n = sign_changes(seq, a) - sign_changes_inf(seq)
    if not strict and peval(p, a) == 0: n += 1
    return n

if __name__ == '__main__':
    k, p = int(sys.argv[1]), int(sys.argv[2])
    a, b = F(sys.argv[3]), F(sys.argv[4])
    V, E = graph(k, p)
    assert connected(V, E)
    A = [[F(0)] * V for _ in range(V)]
    for u, v in E: A[u][v] = A[v][u] = F(1)
    deg = [sum(r) for r in A]
    L = [[(deg[i] if i == j else 0) - A[i][j] for j in range(V)] for i in range(V)]
    pA, pL = charpoly(A), charpoly(L)
    # multiplicity-aware count of roots of pA above a: use squarefree part count plus check
    # via signs: count with multiplicity = sum over distinct roots; we need >= 2 roots counted
    # with multiplicity, so count distinct roots of pA in (a, oo) and, if 1, check its multiplicity.
    nA = roots_above(pA, a)
    nL = roots_above(pL, b, strict=False)
    print('n =', V, ' m =', len(E), ' degrees =', deg)
    print('distinct roots of det(xI-A) above', a, ':', nA)
    print('distinct roots of det(xI-L) at or above', b, ':', nL)
    ok = nA >= 2 and nL == 0 and b - 2 < a
    print('certificate: lambda2 >', a, '> ', b - 2, '> mu1 - 2  ->', 'COUNTEREXAMPLE' if ok else 'not certified')
