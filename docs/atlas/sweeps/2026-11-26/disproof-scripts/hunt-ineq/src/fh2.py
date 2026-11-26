import sys, mpmath as mp
from math import comb, factorial
mp.mp.dps=int(sys.argv[2])
def run(k,m,N):
    q=[mp.mpf((-1)**j*comb(m,j)*factorial(k+m-j))/factorial(k+m) for j in range(m+1)]
    c=[mp.mpf(1)]
    for n in range(1,N+1):
        c.append(-mp.fsum(q[j]*c[n-j] for j in range(1,min(n,m)+1)))
    r=[c[n]/c[n-1] for n in range(1,N+1)]
    i=min(range(len(r)),key=lambda t:r[t])
    neg=[n for n in range(N+1) if c[n]<=0]
    return neg[:3], i+1, r[i], r[-1]
for m in map(int,sys.argv[1].split(',')):
    neg,i,rmin,rlast=run(m,m,8*m)
    print(m,"neg",neg,"argmin n",i,"m*rmin",mp.nstr(m*rmin,8),"m*r_last",mp.nstr(m*rlast,8),flush=True)
