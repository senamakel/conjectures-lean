import numpy as np, sys
from math import log, sqrt
N = int(sys.argv[1])
s = np.ones(N+1, dtype=bool); s[:2]=False; s[4::2]=False
for i in range(3, int(N**0.5)+1, 2):
    if s[i]: s[i*i::2*i]=False
P = np.nonzero(s)[0]
small = [int(q) for q in P[:2000] if q > 2]
exc = []; worst = {1/3:[], 0.3:[], 0.27:[], 0.25:[]}
maxratio = (0,0)
for p in P[1:]:
    p = int(p); e = (p-1)//2
    for q in small:
        if q == p: continue
        if pow(q, e, p) == 1: r = q; break
    if r*r >= p: exc.append((p,r))
    lp = log(p)
    if p > 1000 and r/lp**2 > maxratio[0]: maxratio = (r/lp**2, p, r)
    for c in worst:
        if r >= p**c: worst[c].append((p,r))
print("exceptions rho_p >= sqrt p:", exc)
print("max rho/log^2 p for p>1000:", maxratio)
for c,v in worst.items(): print("c=%.3f count %d last %s" % (c, len(v), v[-3:]))
