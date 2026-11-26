import math,sys
exec(open('fq.py').read().split("from decimal")[0].split("import mpmath")[0])
def bounds(q,nmax):
    A=0.0; B=0.0; out=[None]
    # work in log scale relative to q^n to avoid overflow: store (logA, B/A)
    res=[None]
    for n in range(1,nmax+1):
        # A_n/q^n = sum_{d<=n} q^{d-n}/d ; B_n/q^n = sum_{d=2..n} q^{d/2+1-n}/((q-1)d)
        a=sum(q**(d-n)/d for d in range(max(1,n-60),n+1))
        b=sum(q**(d/2+1-n)/((q-1)*d) for d in range(2,n+1))
        lo=a-b; hi=a+b
        res.append((n*math.log(q)+math.log(lo) if lo>0 else None, n*math.log(q)+math.log(hi)))
    return res
QM=int(sys.argv[1]); NM=int(sys.argv[2])
need={'i':[], 'ii':[], 'iii':[]}
for q in ppowers(QM):
    R=bounds(q,NM+2)
    for n in range(1,NM+1):
        lo=[R[k][0] for k in (n,n+1,n+2)]; hi=[R[k][1] for k in (n,n+1,n+2)]
        if None in lo: need['i'].append((q,n)); need['ii'].append((q,n)); need['iii'].append((q,n)); continue
        # (i) 2 log M(n+1) < log M(n) + log M(n+2)
        if not (2*hi[1] < lo[0]+lo[2]): need['i'].append((q,n))
        if n>2 and not (hi[0]/n < lo[1]/(n+1)): need['ii'].append((q,n))
        if n>3 and not (2*lo[1]/(n+1) > hi[0]/n + hi[2]/(n+2)): need['iii'].append((q,n))
for k,v in need.items():
    qs=sorted(set(a for a,b in v)); print(k, "bound fails at", len(v), "pairs; max q", max(qs) if qs else None, "max n", max(b for a,b in v) if v else None)
    big=[(a,b) for a,b in v if a>50]; print("   pairs with q>50:", big[:20])
