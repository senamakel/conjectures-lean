"""Independent evaluator for the Duhamel-Cazenave spectral conjecture corpus (prefix syntax),
with a graph pool and a hill-climbing search on the slack LHS - RHS.

Semantics follow the corpus README / lang.py grammar:
  rank Adj = rank(A); rank laplac Adj = rank(L) = n-1; large/large-2 eigen M = 1st/2nd largest
  eigenvalue; sum eigen Adj = 0, sum eigen laplac Adj = 2m; IndRand Adj = Randic index;
  rad/dia Adj; max-v Adj f(v) = max over vertices; max-v-u Adj f(u,v) = max over edges uv
  (both orientations); degree x, temp x = d/(n-d), weight u v = 1/sqrt(d_u d_v).
"""
import math, sys, random
import numpy as np
from scipy.sparse.csgraph import shortest_path as _sp

BIN = {'+', '-', '*', '/', '^'}


def parse(s):
    toks = s.split(); pos = 0
    def nxt():
        nonlocal pos
        t = toks[pos]; pos += 1; return t
    def matrix():
        t = nxt()
        if t == 'Adj': return 'A'
        if t == 'laplac':
            assert nxt() == 'Adj'; return 'L'
        raise ValueError(s)
    def ex():
        t = nxt()
        if t in BIN: return (t, ex(), ex())
        if t in ('log', 'sqrt'): return (t, ex())
        if t in ('1', '2'): return ('c', float(t))
        if t == 'rank': return ('a', 'rA' if matrix() == 'A' else 'rL')
        if t in ('large', 'large-2', 'sum'):
            assert nxt() == 'eigen'; M = matrix()
            return ('a', {('large', 'A'): 'l1', ('large-2', 'A'): 'l2', ('large', 'L'): 'mu1',
                          ('large-2', 'L'): 'mu2', ('sum', 'A'): 'sA', ('sum', 'L'): 'sL'}[(t, M)])
        if t in ('IndRand', 'rad', 'dia'):
            assert nxt() == 'Adj'; return ('a', {'IndRand': 'R', 'rad': 'rad', 'dia': 'dia'}[t])
        if t == 'max-v':
            assert nxt() == 'Adj'; return ('maxv', ex())
        if t == 'max-v-u':
            assert nxt() == 'Adj'; return ('maxe', ex())
        if t in ('degree', 'temp'):
            x = nxt(); assert x in 'uv'; return ('loc', t, x)
        if t == 'weight':
            a = nxt(); b = nxt(); return ('w', a, b)
        raise ValueError((t, s))
    assert nxt() == '<='
    a = ex(); b = ex(); assert pos == len(toks)
    return a, b


def invariants(A):
    """A: (n,n) 0/1 numpy array of a connected graph."""
    n = A.shape[0]
    deg = A.sum(1).astype(float)
    L = np.diag(deg) - A
    ea = np.linalg.eigvalsh(A.astype(float)); el = np.linalg.eigvalsh(L.astype(float))
    rA = int((np.abs(ea) > 1e-8).sum())
    m = deg.sum() / 2
    # distances (scipy, C speed); disconnected -> None
    D = _sp(A, unweighted=True, directed=False)
    if not np.isfinite(D).all(): return None
    ecc = D.max(axis=1)
    s_, t_ = np.nonzero(A)
    du = deg[t_]; dv = deg[s_]
    R = float((1 / np.sqrt(du * dv)).sum() / 2)
    return dict(n=float(n), m=m, rA=float(rA), rL=float(n - 1), l1=ea[-1], l2=ea[-2], mu1=el[-1],
                mu2=el[-2], sA=0.0, sL=2 * m, R=R, rad=ecc.min(), dia=ecc.max(), deg=deg, du=du, dv=dv)


def ev(e, I, ctx=None):
    t = e[0]
    if t == 'c': return e[1]
    if t == 'a': return I[e[1]]
    if t == 'loc':
        kind, x = e[1], e[2]
        if ctx == 'v': d = I['deg']
        elif ctx == 'e': d = I['dv'] if x == 'v' else I['du']
        else: raise ValueError('local atom outside binder')
        return d if kind == 'degree' else d / (I['n'] - d)
    if t == 'w':
        if ctx != 'e': raise ValueError('weight outside edge binder')
        if {e[1], e[2]} == {'u', 'v'}: return 1 / np.sqrt(I['du'] * I['dv'])
        d = I['dv'] if e[1] == 'v' else I['du']; return 1 / d   # w_vv style (unused in corpus)
    if t == 'maxv':
        return float(np.max(np.broadcast_to(ev(e[1], I, 'v'), I['deg'].shape)))
    if t == 'maxe':
        return float(np.max(np.broadcast_to(ev(e[1], I, 'e'), I['du'].shape)))
    if t == 'log': return np.log(ev(e[1], I, ctx))
    if t == 'sqrt': return np.sqrt(ev(e[1], I, ctx))
    x = ev(e[1], I, ctx); y = ev(e[2], I, ctx)
    if t == '+': return x + y
    if t == '-': return x - y
    if t == '*': return x * y
    if t == '/': return x / y
    if t == '^': return np.power(x, y)
    raise ValueError(t)


def slack(f, I):
    """(LHS - RHS) / (1 + |LHS| + |RHS|); nan if undefined."""
    with np.errstate(all='ignore'):
        try:
            a = float(ev(f[0], I)); b = float(ev(f[1], I))
        except (ZeroDivisionError, OverflowError, ValueError):
            return float('nan')
    if not (math.isfinite(a) and math.isfinite(b)): return float('nan')
    return (a - b) / (1 + abs(a) + abs(b))


# ------------------------------------------------------------------ graph pool
def adj_from_edges(n, E):
    A = np.zeros((n, n), dtype=np.int8)
    for a, b in E: A[a, b] = A[b, a] = 1
    return A

def clique_edges(vs): return [(vs[i], vs[j]) for i in range(len(vs)) for j in range(i + 1, len(vs))]

def pool(rng, nmax=40):
    G = []
    for n in range(4, nmax + 1):
        # two cliques joined by an edge / by a path / sharing a vertex, unequal sizes
        for a in range(2, n - 1):
            b = n - a
            if b < 2: continue
            E = clique_edges(list(range(a))) + clique_edges(list(range(a, n))) + [(0, a)]
            G.append(adj_from_edges(n, E))
            E2 = clique_edges(list(range(a))) + clique_edges(list(range(a, n))) + [(0, a), (1, a + 1)]
            G.append(adj_from_edges(n, E2))
        for a in range(2, n - 2):     # clique + pendant path (kite) and clique + pendants (crown-ish)
            E = clique_edges(list(range(a))) + [(a - 1, a)] + [(i, i + 1) for i in range(a, n - 1)]
            G.append(adj_from_edges(n, E))
            E = clique_edges(list(range(a))) + [(i % a, i) for i in range(a, n)]
            G.append(adj_from_edges(n, E))
            E = clique_edges(list(range(a))) + [(0, i) for i in range(a, n)]
            G.append(adj_from_edges(n, E))
        for k in range(2, n // 2 + 1):   # chain of cliques of size k
            if n % k == 0:
                c = n // k
                E = []
                for i in range(c):
                    E += clique_edges(list(range(i * k, (i + 1) * k)))
                    if i: E.append(((i - 1) * k + k - 1, i * k))
                G.append(adj_from_edges(n, E))
    for _ in range(4000):           # random G(n,p), random trees, random cliques glued
        n = int(rng.integers(8, nmax + 1)); p = float(rng.choice([0.08, 0.15, 0.3, 0.5, 0.7, 0.85, 0.95]))
        A = (rng.random((n, n)) < p).astype(np.int8); A = np.triu(A, 1); A = A + A.T
        G.append(A)
        par = [int(rng.integers(0, i)) for i in range(1, n)]
        G.append(adj_from_edges(n, [(i + 1, par[i]) for i in range(n - 1)]))
    return G


def mutate(A, rng):
    n = A.shape[0]; B = A.copy(); r = rng.random()
    if r < 0.75 or n <= 4:
        i, j = rng.choice(n, 2, replace=False); B[i, j] = B[j, i] = 1 - B[i, j]
    elif r < 0.88 and n < 60:         # add a vertex attached to a random subset
        B = np.zeros((n + 1, n + 1), dtype=np.int8); B[:n, :n] = A
        k = int(rng.integers(1, max(2, n // 3)))
        for j in rng.choice(n, k, replace=False): B[n, j] = B[j, n] = 1
    else:                              # delete a vertex
        v = int(rng.integers(n)); keep = [i for i in range(n) if i != v]; B = A[np.ix_(keep, keep)]
    return B


def climb(f, A0, rng, iters=3000, temp=0.02):
    """Simulated annealing maximising slack(f) over connected graphs."""
    I = invariants(A0); cur = slack(f, I) if I else float('nan')
    if not math.isfinite(cur): cur = -1e9
    best, bestA, A = cur, A0, A0
    for it in range(iters):
        B = mutate(A, rng); I = invariants(B)
        if I is None: continue
        s = slack(f, I)
        if not math.isfinite(s): continue
        T = temp * (1 - it / iters) + 1e-6
        if s >= cur or rng.random() < math.exp((s - cur) / T):
            A, cur = B, s
            if s > best:
                best, bestA = s, B
                if best > 1e-6: break
    return best, bestA
