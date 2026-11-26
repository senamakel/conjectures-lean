# greedy 2D covering of (a mod L2, b mod L3) by fibers {(a,b): 2^a 3^b == c mod q}
import sys, math, numpy as np
sys.path.insert(0,'py')
from sympy import n_order, primitive_root, discrete_log, factorint
import cypari2; pari=cypari2.Pari(); pari.allocatemem(2*10**9)
L2=int(sys.argv[1]); L3=int(sys.argv[2])
from sympy import divisors
cand=set()
for L in (L2,L3):
  base = 2 if L==L2 else 3
  for d in divisors(L):
    f=pari.factor(pari.polcyclo(d,base), 10**7)
    for p in f[0]:
        p=int(p)
        if pari.isprime(p) and p<10**15: cand.add(p)
pool=[]
for q in sorted(cand):
    if q<5: continue
    o2=n_order(2,q); o3=n_order(3,q)
    if L2%o2 or L3%o3: continue
    g=o2*o3//math.gcd(o2,o3)
    gen=pow(primitive_root(q),(q-1)//g,q)
    A=discrete_log(q,2,gen); B=discrete_log(q,3,gen)
    pool.append((q,g,A,B))
print('pool',len(pool),'sum1/g',sum(1/t[1] for t in pool))
a=np.arange(L2,dtype=np.int64)[:,None]; b=np.arange(L3,dtype=np.int64)[None,:]
unc=np.ones((L2,L3),bool)
avail=list(pool); chosen=[]
while avail and unc.any():
    best=None
    for t in avail:
        q,g,A,B=t
        lab=((a*A+b*B)%g)[unc]
        c=np.bincount(lab,minlength=g); i=int(c.argmax())
        if best is None or c[i]>best[0]: best=(int(c[i]),t,i)
    cnt,t,i=best
    q,g,A,B=t
    unc &= ((a*A+b*B)%g)!=i
    avail.remove(t); chosen.append((q,g,i))
    print('q',q,'g',g,'newly',cnt,'left frac',unc.mean())
