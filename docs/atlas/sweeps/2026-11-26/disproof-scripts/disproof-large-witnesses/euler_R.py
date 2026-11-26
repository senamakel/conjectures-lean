import numpy as np, sys, pickle, itertools
from sympy import primerange
P=int(sys.argv[1])
R={}
for p in primerange(3,P):
    a=np.arange(p,dtype=np.int64); base=(2*a+1)%p; sign=np.where(a%2==0,1,-1)
    pw=np.ones(p,dtype=np.int64)
    S=set()
    for r in range(1,p):       # r = 1..p-1
        pw=(pw*base)%p
        if r%2==0 and int((sign*pw).sum())%p==0: S.add(r)
    R[p]=S
pickle.dump(R,open(f'eulerR_{P}.pkl','wb'))
print('primes',len(R),'with nonzero-index irregular pairs',sum(1 for p,S in R.items() if S-{p-1}))
# check: p-1 in R_p iff p%4==1
assert all(((p-1) in S)==(p%4==1) for p,S in R.items())
def ok(m,ps):
    for p in ps:
        r=(m-1)%(p-1)
        if r==0: r=p-1
        if r not in R[p]: return False
    return True
pl=sorted(R)
hits=[]
for i,p in enumerate(pl):
    for q in pl[i+1:]:
        m=p*q
        if ok(m,(p,q)): hits.append((m,p,q))
print('2-prime hits (both <P):',sorted(hits)[:20], len(hits))
h3=[]
for p,q in itertools.combinations(pl[:200],2):
    for r in pl:
        if r<=q: continue
        m=p*q*r
        if ok(m,(p,q,r)): h3.append((m,p,q,r))
print('3-prime hits:',sorted(h3)[:30],len(h3))
