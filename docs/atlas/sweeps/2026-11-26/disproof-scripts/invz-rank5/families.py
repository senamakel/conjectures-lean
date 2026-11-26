"""Rank-5 families beyond 9 elements: projective/affine geometries over GF(2), GF(3), truncations,
direct sums with long lines.  For each: (A) h(L) >= 3, (B) W2(H) >= 2W1(H) - 2 on hyperplanes,
(C) c2 = alpha24 - alpha14 - W2 + W1 >= W1, and where the lattice is small, (D) c2 = y2 - y1 from
the direct inverse-Z computation and Y log-concave."""
from itertools import product
from lattice import Lattice
from functools import lru_cache


def vec_rank_fn(vecs, p, cap=None):
    def rank(S):
        rows = [list(vecs[i]) for i in range(len(vecs)) if (S >> i) & 1]
        r = 0; m = len(vecs[0])
        for c in range(m):
            piv = next((i for i in range(r, len(rows)) if rows[i][c] % p), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], p - 2, p)
            rows[r] = [x * inv % p for x in rows[r]]
            for i in range(len(rows)):
                if i != r and rows[i][c] % p:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
            r += 1
        return r if cap is None else min(r, cap)
    return lru_cache(maxsize=None)(rank)


def proj_points(d, p):
    pts = []
    for v in product(range(p), repeat=d):
        if any(v):
            lead = next(x for x in v if x)
            if lead == 1: pts.append(v)
    return pts


def aff_points(d, p):
    return [(1,) + v for v in product(range(p), repeat=d)]


def dsum(parts):
    """parts: list of (size, rank) uniform matroids; direct sum rank function."""
    offs = []; o = 0
    for sz, _ in parts:
        offs.append(o); o += sz
    def rank(S):
        return sum(min(bin((S >> off) & ((1 << sz) - 1)).count('1'), rk) for off, (sz, rk) in zip(offs, parts))
    return o, rank


def check(name, n, rank, direct):
    L = Lattice(n, rank)
    assert L.r == 5
    fl, rk = L.flats, L.rk
    pts = [i for i in range(len(fl)) if rk[i] == 1]
    lns = [i for i in range(len(fl)) if rk[i] == 2]
    hyp = [i for i in range(len(fl)) if rk[i] == 4]
    sub = lambda a, b: fl[a] & fl[b] == fl[a]
    A = min(sum(1 for H in hyp if sub(l, H)) for l in lns) >= 3
    a14 = a24 = 0; Bok = True
    for H in hyp:
        w1 = sum(1 for x in pts if sub(x, H)); w2 = sum(1 for l in lns if sub(l, H))
        a14 += w1; a24 += w2; Bok &= w2 >= 2 * w1 - 2
    W1, W2 = len(pts), len(lns)
    c2 = a24 - a14 - W2 + W1
    line = f'{name:28s} n={n:3d} flats={len(fl):5d} W1={W1} W2={W2} W4={len(hyp)} c2={c2} c2-W1={c2-W1} A={A} B={Bok} C={c2>=W1}'
    if direct:
        Y, P, Q = L.invZ()
        D = (Y[2] - Y[1] == c2)
        LC = all(Y[i] ** 2 >= Y[i - 1] * Y[i + 1] for i in range(1, 5))
        line += f' D={D} LC={LC} Y={Y}'
    print(line, flush=True)


if __name__ == '__main__':
    g = proj_points(5, 2); check('PG(4,2)', len(g), vec_rank_fn(g, 2), True)
    g = aff_points(4, 2); check('AG(4,2)', len(g), vec_rank_fn(g, 2), True)
    g = proj_points(6, 2); check('T5 PG(5,2)', len(g), vec_rank_fn(g, 2, 5), False)
    g = aff_points(4, 3); check('AG(4,3)', len(g), vec_rank_fn(g, 3), False)
    g = proj_points(5, 3); check('PG(4,3)', len(g), vec_rank_fn(g, 3), False)
    g = aff_points(5, 2); check('T5 AG(5,2)', len(g), vec_rank_fn(g, 2, 5), False)
    for parts in [[(12, 2), (3, 3)], [(12, 2), (2, 2), (1, 1)], [(8, 2), (8, 2), (1, 1)],
                  [(6, 2), (6, 2), (6, 2)][:2] + [(1, 1)], [(10, 4), (1, 1)], [(7, 3), (5, 2)],
                  [(15, 2), (1, 1), (1, 1), (1, 1)], [(5, 2), (5, 2), (1, 1)], [(9, 3), (1, 1), (1, 1)]]:
        n, rk = dsum(parts)
        if rk((1 << n) - 1) != 5: continue
        check('+'.join(f'U{r},{s}' for s, r in parts), n, rk, n <= 18)
    # truncations of direct sums of lines to rank 5
    for parts in [[(6, 2)] * 3, [(5, 2)] * 4, [(4, 2), (4, 2), (4, 2), (1, 1)], [(10, 3), (10, 3)]]:
        n, rk0 = dsum(parts)
        check('T5(' + '+'.join(f'U{r},{s}' for s, r in parts) + ')', n, lambda S, f=rk0: min(f(S), 5), n <= 16)
