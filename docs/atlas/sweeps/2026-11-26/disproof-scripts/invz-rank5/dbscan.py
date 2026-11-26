"""Exhaustive check over every matroid of rank 5 on <= 9 elements (duals of the Matsumoto-Moriyama-
Imai-Bremner rank <= 4 lists shipped in the matroid_database wheel) and every rank-4 matroid on
<= 9 elements.

For rank 5 it checks, from the lattice of flats:
  (A) h(L) >= 3 for every line L;
  (B) W2(H) >= 2 W1(H) - 2 for every hyperplane H (the rank-4 lemma);
  (C) c2 := alpha24 - alpha14 - W2 + W1 >= W1   (the inequality proved in the report);
and, for the matroids selected by --direct (all with n <= 8, and every k-th one with n = 9), it
computes Y directly from the definitions (lattice.invZ) and checks
  (D) Y = c0[6] + c1 t[4] + c2 t^2[2] with c2 equal to the flag value in (C);
  (E) Y log-concave.
For rank 4: lemma W2 >= 2 W1 - 2, and Y unimodal and log-concave via the direct code.

usage: python3 dbscan.py <path to matroid_database/_all> [direct_stride] [workers]
"""
import sys, lzma, os
from multiprocessing import Pool
from lattice import rank_table_from_bases, revlex_bases, dual_bases, Lattice

DB = sys.argv[1]
STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 50
WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 16


def flats_by_rank(n, rk):
    N = 1 << n
    out = {}
    for S in range(N):
        r = rk[S]
        if all(rk[S | (1 << e)] > r for e in range(n) if not (S >> e) & 1):
            out.setdefault(r, []).append(S)
    return out


def sub(a, b):
    return a & b == a


def flagdata(n, rk, r):
    fb = flats_by_rank(n, rk)
    pts, lns, hyp = fb.get(1, []), fb.get(2, []), fb.get(r - 1, [])
    return fb, pts, lns, hyp


def check5(args):
    n, s, dual, idx, direct = args
    rr = 4 if dual else 5
    B = revlex_bases(n, rr if not dual else n - 5, s) if False else None
    # database stores rank (n-5) matroids for dual==True
    r0 = n - 5 if dual else 5
    B = revlex_bases(n, r0, s)
    if dual:
        B = dual_bases(n, B)
    rk = rank_table_from_bases(n, B)
    assert rk[(1 << n) - 1] == 5
    fb, pts, lns, hyp = flagdata(n, rk, 5)
    W1, W2, W4 = len(pts), len(lns), len(hyp)
    res = {'n': n, 'idx': idx, 'bad': []}
    hL = [sum(1 for H in hyp if sub(L, H)) for L in lns]
    if min(hL) < 3:
        res['bad'].append('A')
    a14 = a24 = 0
    for H in hyp:
        w1 = sum(1 for x in pts if sub(x, H)); w2 = sum(1 for L in lns if sub(L, H))
        a14 += w1; a24 += w2
        if w2 < 2 * w1 - 2:
            res['bad'].append('B')
    c2 = a24 - a14 - W2 + W1
    res['c2'] = c2; res['W1'] = W1; res['slack'] = c2 - W1
    if c2 < W1:
        res['bad'].append('C')
    if direct:
        Y, P, Q = Lattice(n, lambda S: rk[S]).invZ()
        Y = Y + [0] * (6 - len(Y))
        c0 = Y[0]; c1 = Y[1] - Y[0]; c2d = Y[2] - Y[1]
        expect = [c0, c0 + c1, c0 + c1 + c2d, c0 + c1 + c2d, c0 + c1, c0]
        if Y != expect or c2d != c2:
            res['bad'].append('D')
        if not all(Y[i] ** 2 >= Y[i - 1] * Y[i + 1] for i in range(1, 5)):
            res['bad'].append('E')
        res['Y'] = Y; res['c1'] = c1
    return res


def check4(args):
    n, s, idx, direct = args
    B = revlex_bases(n, 4, s)
    rk = rank_table_from_bases(n, B)
    fb = flats_by_rank(n, rk)
    W1, W2 = len(fb[1]), len(fb[2])
    res = {'n': n, 'idx': idx, 'bad': [], 'slack': W2 - (2 * W1 - 2)}
    if W2 < 2 * W1 - 2:
        res['bad'].append('lemma')
    if direct:
        Y, P, Q = Lattice(n, lambda S: rk[S]).invZ()
        Y = Y + [0] * (5 - len(Y))
        if not all(Y[i] ** 2 >= Y[i - 1] * Y[i + 1] for i in range(1, 4)):
            res['bad'].append('LC4')
        if not (Y[0] <= Y[1] <= Y[2] >= Y[3] >= Y[4]):
            res['bad'].append('UM4')
    return res


def lines(r, n):
    with lzma.open(os.path.join(DB, f'allr{r}n{n:02d}.txt.xz'), 'rt') as f:
        for line in f:
            yield line.strip()


if __name__ == '__main__':
    jobs5 = []
    for n in range(5, 10):
        r0 = n - 5
        if r0 == 0:
            jobs5.append((5, '*', True, 0, True)); continue
        for i, s in enumerate(lines(r0, n)):
            jobs5.append((n, s, True, i, n <= 8 or i % STRIDE == 0))
    jobs4 = []
    for n in range(4, 10):
        for i, s in enumerate(lines(4, n)):
            jobs4.append((n, s, i, n <= 8 or i % STRIDE == 0))
    with Pool(WORKERS) as pool:
        bad = []; cnt = {}; ndir = 0; minslack = None; tight = 0
        for res in pool.imap_unordered(check5, jobs5, chunksize=64):
            cnt[res['n']] = cnt.get(res['n'], 0) + 1
            if res['bad']: bad.append(res)
            if 'Y' in res: ndir += 1
            if minslack is None or res['slack'] < minslack: minslack = res['slack']
            if res['slack'] == 0: tight += 1
        print('rank 5: matroids per n', dict(sorted(cnt.items())), 'direct Y computed for', ndir)
        print('rank 5: failures', len(bad), bad[:5])
        print('rank 5: min (c2 - W1) =', minslack, ' #with c2 == W1:', tight)
        bad4 = []; cnt4 = {}; ms4 = None; t4 = 0
        for res in pool.imap_unordered(check4, jobs4, chunksize=64):
            cnt4[res['n']] = cnt4.get(res['n'], 0) + 1
            if res['bad']: bad4.append(res)
            if ms4 is None or res['slack'] < ms4: ms4 = res['slack']
            if res['slack'] == 0: t4 += 1
        print('rank 4: matroids per n', dict(sorted(cnt4.items())))
        print('rank 4: failures', len(bad4), bad4[:5])
        print('rank 4: min (W2 - 2W1 + 2) =', ms4, ' #tight:', t4)
