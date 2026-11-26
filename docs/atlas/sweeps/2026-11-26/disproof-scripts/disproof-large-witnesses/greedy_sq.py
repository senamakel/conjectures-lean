# Budgeted greedy set cover: find n with n - G_k non-squarefree for all admissible k with G_k < n.
# mode F: k>=2 (A304331); mode Fodd: k>=0, n odd, only k%3==0 matter (A304522); mode L: Lucas k>=1 (A304333)
import sys, math, numpy as np
from sympy import primerange
mode=sys.argv[1]; D=int(sys.argv[2]); QMAX=int(sys.argv[3])
def terms(limit):
    if mode=='L': a,b,k=2,1,0
    else: a,b,k=0,1,0
    out=[]
    while a < limit:
        out.append((k,a)); a,b,k=b,a+b,k+1
    return out
LIM=10**D
T=terms(LIM)
if mode=='F': idx=[(k,v) for k,v in T if k>=2]
elif mode=='Fodd': idx=[(k,v) for k,v in T if k%3==0]
elif mode=='L': idx=[(k,v) for k,v in T if k>=1]
ks=[k for k,v in idx]; vals=[v for k,v in idx]
N=len(idx); unc=np.ones(N,bool)
budget=D*math.log(10)  # natural log budget for prod q^2
chosen=[]; used=0.0
primes=[q for q in primerange(2,QMAX) if not (mode=='Fodd' and q==2)]
res={q: np.array([v%(q*q) for v in vals],dtype=np.int64) for q in primes}
if mode=='Fodd': chosen.append((2,1)); used+=math.log(2)  # n odd: n == 1 mod 2 (cost log 2)
avail=set(primes)
while unc.any():
    best=None
    for q in avail:
        r=res[q][unc]
        if len(r)==0: break
        u,c=np.unique(r,return_counts=True)
        i=c.argmax(); sc=c[i]/(2*math.log(q))
        if best is None or sc>best[0]: best=(sc,q,int(u[i]),int(c[i]))
    sc,q,r,c=best
    if used+2*math.log(q)>budget: break
    used+=2*math.log(q); avail.discard(q); chosen.append((q,r))
    unc &= ~(res[q]==r)
print(mode,'D',D,'terms',N,'uncovered',int(unc.sum()),'primes used',len(chosen),'log10 used',round(used/math.log(10),1))
print('uncovered k:',[ks[i] for i in np.nonzero(unc)[0]][:60])
