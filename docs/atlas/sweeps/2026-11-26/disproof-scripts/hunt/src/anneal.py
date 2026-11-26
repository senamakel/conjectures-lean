"""Anneal each formula.  usage: anneal.py CSV OUT STATUSES RESTARTS ITERS NPROC [IDFILE]"""
import sys, csv, json, math, os, time
import multiprocessing as mp
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec

POOL = POOL_A = None
RESTARTS = ITERS = 0

def work(item):
    cid, s = item
    rng = np.random.default_rng(int(cid) * 7919 + 1)
    try: f = spec.parse(s)
    except Exception: return cid, None, None
    sl = []
    idx = rng.choice(len(POOL), min(1500, len(POOL)), replace=False)
    for k in idx:
        v = spec.slack(f, POOL[k])
        if math.isfinite(v): sl.append((v, k))
    sl.sort(reverse=True)
    starts = [POOL_A[k] for _, k in sl[:RESTARTS]]
    while len(starts) < RESTARTS:
        starts.append(POOL_A[int(rng.integers(len(POOL_A)))])
    best, bestA = -math.inf, None
    for A0 in starts:
        b, A = spec.climb(f, A0, rng, iters=ITERS)
        if b > best: best, bestA = b, A
        if best > 1e-6: break
    edges = [(int(i), int(j)) for i, j in zip(*np.nonzero(np.triu(bestA)))] if bestA is not None else None
    return cid, best, (int(bestA.shape[0]) if bestA is not None else None, edges)

if __name__ == '__main__':
    path, out, statuses = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
    RESTARTS, ITERS, nproc = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    ids = set(open(sys.argv[7]).read().split()) if len(sys.argv) > 7 else None
    rows = [r for r in csv.DictReader(open(path, encoding='utf8')) if r['statut'] in statuses and (ids is None or r['id'] in ids)]
    G = spec.pool(np.random.default_rng(999))
    POOL, POOL_A = [], []
    for A in G:
        I = spec.invariants(A)
        if I is not None: POOL.append(I); POOL_A.append(A)
    meta = {r['id']: r['enonce'] for r in rows}
    t0 = time.time(); nh = 0
    with open(out, 'w') as fh, mp.get_context('fork').Pool(nproc) as p:
        for k, (cid, best, g) in enumerate(p.imap_unordered(work, [(r['id'], r['formule_prefixe']) for r in rows], chunksize=4)):
            hit = best is not None and best > 1e-6
            nh += hit
            fh.write(json.dumps(dict(id=cid, stmt=meta[cid], slack=best, n=g[0] if g else None,
                                     edges=g[1] if (g and hit) else None), ensure_ascii=False) + '\n'); fh.flush()
            if k % 500 == 0: print(k, nh, round(time.time() - t0), file=sys.stderr, flush=True)
    print('done hits', nh, file=sys.stderr)
