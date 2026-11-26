import sys
from decimal import Decimal, getcontext
getcontext().prec=150
exec(open('fq.py').read().split("import mpmath")[0].split("from decimal")[0])
QMAX=int(sys.argv[1]); NMAX=int(sys.argv[2])
n0={2:14,3:8,4:6,5:6}
bad1=[];bad2=[]
for q in ppowers(QMAX):
    N=[None]+[I(q,d) for d in range(1,NMAX+4)]
    L=[None]+[(Decimal(N[n]).ln()/n if N[n]>0 else None) for n in range(1,NMAX+4)]
    for n in range(2,NMAX+1):
        if not (L[n]<L[n+1]): bad1.append((q,n))
    m=n0.get(q,4)
    fails=[n for n in range(2,NMAX+1) if not (L[n+1]-L[n] > L[n+2]-L[n+1])]
    if any(n>=m for n in fails): bad2.append((q,[n for n in fails if n>=m]))
    if q<=13: print(q,"ratio-decreasing fails at",fails)
print("R1 increasing fails:",bad1); print("R1 ratio fails >= n0:",bad2)
