"""Deep annealing on the curated conjectures.  usage: deep_curated.py OUT SEEDS ITERS NPROC"""
import sys, os, json, math, time
import multiprocessing as mp
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec, curated

POOL_A = None

def cslack(k, I):
    _, L, R = curated.C[k]
    try: a, b = float(L(I)), float(R(I))
    except (ValueError, ZeroDivisionError, OverflowError): return float('nan')
    if not (math.isfinite(a) and math.isfinite(b)): return float('nan')
    return (a - b) / (1 + abs(a) + abs(b))

def work(job):
    k, seed, iters = job
    rng = np.random.default_rng(seed * 1000 + k)
    spec.slack = lambda f, I: cslack(k, I)     # climb() calls spec.slack(f, I)
    # start: best of 400 random pool graphs for this conjecture, or a random one for odd seeds
    idx = rng.choice(len(POOL_A), 400, replace=False)
    cands = []
    for i in idx:
        I = spec.invariants(POOL_A[i])
        if I is not None:
            v = cslack(k, I)
            if math.isfinite(v): cands.append((v, i))
    cands.sort(reverse=True)
    A0 = POOL_A[cands[seed % 5][1]] if seed % 2 == 0 else POOL_A[cands[int(rng.integers(len(cands)))][1]]
    best, A = spec.climb(None, A0, rng, iters=iters, temp=0.01 if seed % 3 else 0.05)
    edges = [(int(i), int(j)) for i, j in zip(*np.nonzero(np.triu(A)))]
    return k, seed, best, int(A.shape[0]), edges

if __name__ == '__main__':
    out, seeds, iters, nproc = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    POOL_A = spec.pool(np.random.default_rng(4242), nmax=30)
    jobs = [(k, s, iters) for s in range(seeds) for k in range(len(curated.C))]
    t0 = time.time()
    with open(out, 'w') as fh, mp.get_context('fork').Pool(nproc) as p:
        for k, seed, best, n, edges in p.imap_unordered(work, jobs):
            fh.write(json.dumps(dict(conj=curated.C[k][0], seed=seed, slack=best, n=n,
                                     edges=edges if best > -1e-3 else None)) + '\n'); fh.flush()
    print('elapsed', time.time() - t0, file=sys.stderr)
