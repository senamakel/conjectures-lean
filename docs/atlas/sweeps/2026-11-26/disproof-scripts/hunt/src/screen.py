"""Screen corpus formulas against a graph pool.  usage: screen.py CSV OUT STATUSES [limit] [nproc]"""
import sys, csv, json, math, random, pickle, os
import multiprocessing as mp
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec

POOL = None

def work(item):
    cid, s = item
    try: f = spec.parse(s)
    except Exception as e: return cid, None, None, 'parse'
    best, arg, undef = -math.inf, None, 0
    for k, I in enumerate(POOL):
        v = spec.slack(f, I)
        if not math.isfinite(v): undef += 1; continue
        if v > best: best, arg = v, k
    return cid, best, arg, undef

if __name__ == '__main__':
    path, out, statuses = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    nproc = int(sys.argv[5]) if len(sys.argv) > 5 else 16
    rows = [r for r in csv.DictReader(open(path, encoding='utf8')) if r['statut'] in statuses]
    if limit:
        random.Random(7).shuffle(rows); rows = rows[:limit]
    rng = np.random.default_rng(12345)
    G = spec.pool(rng)
    POOL_A = []; POOL = []
    for A in G:
        I = spec.invariants(A)
        if I is not None: POOL.append(I); POOL_A.append(A)
    print('pool', len(POOL), 'formulas', len(rows), file=sys.stderr, flush=True)
    items = [(r['id'], r['formule_prefixe']) for r in rows]
    with mp.get_context('fork').Pool(nproc) as p:
        res = list(p.imap_unordered(work, items, chunksize=20))
    meta = {r['id']: (r['statut'], r['enonce']) for r in rows}
    with open(out, 'w') as fh:
        for cid, best, arg, undef in sorted(res, key=lambda x: -(x[1] if x[1] is not None else -9)):
            edges = None
            if arg is not None and best is not None and best > 1e-9:
                A = POOL_A[arg]; edges = [(int(i), int(j)) for i, j in zip(*np.nonzero(np.triu(A)))]
            fh.write(json.dumps(dict(id=cid, status=meta[cid][0], stmt=meta[cid][1], slack=best,
                                     n=int(POOL_A[arg].shape[0]) if arg is not None else None,
                                     undef=undef, edges=edges), ensure_ascii=False) + '\n')
    nhit = sum(1 for _, b, _, _ in res if b is not None and b > 1e-6)
    print('positive slack >1e-6:', nhit, file=sys.stderr)
