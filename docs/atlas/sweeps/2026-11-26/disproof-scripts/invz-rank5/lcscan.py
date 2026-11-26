"""Direct inverse Z (lattice.invZ, from the definitions) on EVERY matroid of rank 4 and rank 5 on
<= 9 elements (rank 5 as duals of the rank <= 4 lists).  Checks log-concavity (GRX Conj 1.5),
records the smallest ratio y_i^2 / (y_{i-1} y_{i+1}), and on every STRIDE-th matroid checks the
Rethlas truncation identity  y_i - y_{i-1} = q_i(M) + q_{i-1}(T(M))  for 0 <= i <= r/2, with
Q(T(M)) computed directly on the truncated lattice.

usage: python3 lcscan.py <path to matroid_database/_all> [stride] [workers]
"""
import sys, lzma, os
from fractions import Fraction
from multiprocessing import Pool
from lattice import rank_table_from_bases, revlex_bases, dual_bases, Lattice

DB = sys.argv[1]
STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 20
WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 16


def job(args):
    r, n, s, idx = args
    r0 = r if r == 4 else n - 5
    B = revlex_bases(n, r0, s) if r0 > 0 else [0]
    if r == 5:
        B = dual_bases(n, B)
    rk = rank_table_from_bases(n, B)
    assert rk[(1 << n) - 1] == r
    Y, P, Q = Lattice(n, lambda S: rk[S]).invZ()
    Y = Y + [0] * (r + 1 - len(Y))
    out = {'r': r, 'n': n, 'idx': idx, 'Y': Y, 'bad': []}
    ratios = [Fraction(Y[i] ** 2, Y[i - 1] * Y[i + 1]) for i in range(1, r)]
    out['minratio'] = min(ratios)
    if out['minratio'] < 1:
        out['bad'].append('LC')
    if idx % STRIDE == 0:
        _, _, QT = Lattice(n, lambda S: min(rk[S], r - 1)).invZ()
        q = lambda p, i: p[i] if 0 <= i < len(p) else 0
        for i in range(0, r // 2 + 1):
            if Y[i] - (Y[i - 1] if i else 0) != q(Q, i) + q(QT, i - 1):
                out['bad'].append(('identity', i))
        out['idchecked'] = True
    return out


def lines(r, n):
    with lzma.open(os.path.join(DB, f'allr{r}n{n:02d}.txt.xz'), 'rt') as f:
        for line in f:
            yield line.strip()


if __name__ == '__main__':
    jobs = []
    for n in range(4, 10):
        jobs += [(4, n, s, i) for i, s in enumerate(lines(4, n))]
    jobs.append((5, 5, '*', 0))
    for n in range(6, 10):
        jobs += [(5, n, s, i) for i, s in enumerate(lines(n - 5, n))]
    best = {}; bad = []; nid = 0; cnt = {}
    with Pool(WORKERS) as pool:
        for o in pool.imap_unordered(job, jobs, chunksize=32):
            cnt[o['r']] = cnt.get(o['r'], 0) + 1
            nid += 'idchecked' in o
            if o['bad']: bad.append(o)
            k = o['r']
            if k not in best or o['minratio'] < best[k]['minratio']:
                best[k] = o
    print('counts', cnt, 'identity checked on', nid)
    print('failures', len(bad), bad[:5])
    for k, o in best.items():
        print('rank', k, 'min LC ratio', float(o['minratio']), o['minratio'], 'at n', o['n'], 'idx', o['idx'], 'Y', o['Y'])
