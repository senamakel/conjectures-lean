# Sun 1208.2683 Conj 2.17: M_q(n) = # monic irreducible polys of degree <= n over F_q
import sys
from fractions import Fraction
from math import log
def mobius(n):
    r=1; m=n; p=2
    while p*p<=m:
        if m%p==0:
            m//=p
            if m%p==0: return 0
            r=-r
        p+=1
    if m>1: r=-r
    return r
def I(q,d):
    return sum(mobius(d//e)*q**e for e in range(1,d+1) if d%e==0)//d
def ppowers(N):
    out=[]
    for q in range(2,N+1):
        m=q;p=2
        while m%p: p+=1
        while m%p==0: m//=p
        if m==1: out.append(q)
    return out
from decimal import Decimal, getcontext
getcontext().prec=120
QMAX=int(sys.argv[1]); NMAX=int(sys.argv[2])
ex1=[];ex2=[];ex3=[]
for q in ppowers(QMAX):
    M=[0]
    for d in range(1,NMAX+4): M.append(M[-1]+I(q,d))
    # (i) M(n+1)^2 < M(n) M(n+2), exact integers
    for n in range(1,NMAX+1):
        if not (M[n+1]**2 < M[n]*M[n+2]): ex1.append((q,n))
    L=[None]+[Decimal(M[n]).ln()/n for n in range(1,NMAX+4)]
    for n in range(1,NMAX+1):
        if n>2 and not (L[n] < L[n+1]): ex2.append((q,n))
        if n>3 and not (L[n+1]-L[n] > L[n+2]-L[n+1]): ex3.append((q,n))
print("ex(i)",ex1[:50]); print("ex(ii)",ex2[:50]); print("ex(iii)",ex3[:50])
