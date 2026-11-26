# Fasi-Higham diagonal: c_n(m,m) for 1/q_{m,m}, m odd. exact rationals via integer scaling.
import sys
from fractions import Fraction
from math import factorial, comb
def qcoef(k,m):
    return [Fraction((-1)**j*comb(m,j)*factorial(k+m-j),factorial(k+m)) for j in range(m+1)]
def recip(q,N):
    c=[Fraction(1)]
    for n in range(1,N+1):
        s=0
        for j in range(1,min(n,len(q)-1)+1): s+=q[j]*c[n-j]
        c.append(-s)
    return c
if __name__=="__main__":
    k_off=int(sys.argv[3]) if len(sys.argv)>3 else 0
    for m in range(3,int(sys.argv[1])+1,2):
        k=m+k_off
        q=qcoef(k,m); c=recip(q,int(sys.argv[2]))
        neg=[n for n,x in enumerate(c) if x<=0]
        mn=min(range(len(c)),key=lambda n: float(c[n]/c[n-1]) if n>0 else 9e9)
        print(m,k,"neg:",neg[:5], "min ratio c_n/c_{n-1} at",mn, float(c[mn]/c[mn-1]),flush=True)
