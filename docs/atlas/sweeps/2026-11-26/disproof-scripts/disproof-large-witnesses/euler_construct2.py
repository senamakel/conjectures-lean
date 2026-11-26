# m = p0 * prod(S): p0 has irregular Euler pair (p0, r0); S = primes p == 1 mod 4 with p-1 | L.
# Conditions: m == 1 mod L ; m == 1 + r0 mod (p0-1).  Then every p | m divides E_{m-1}.
import sys, random
from sympy import divisors, isprime
from math import gcd
from sympy.ntheory.modular import crt
p0=int(sys.argv[1]); r0=int(sys.argv[2]); L=int(sys.argv[3]); PMAX=int(sys.argv[4]); seed=int(sys.argv[5])
assert r0 % gcd(L,p0-1)==0 and L%p0
pool=[d+1 for d in divisors(L) if d%4==0 and isprime(d+1) and d+1<=PMAX and d+1!=p0 and L%(d+1) and (p0-1)%(d+1)]
M=L*(p0-1)//gcd(L,p0-1)
res=crt([L,p0-1],[pow(p0,-1,L),(1+r0)%(p0-1)])
assert res is not None
T=int(res[0])%M
print('pool',len(pool),'max',max(pool),'modulus',M)
random.seed(seed); random.shuffle(pool)
h=len(pool)//2; A,B=pool[:h],pool[h:]
def prods(P):
    d={1:()}
    for p in P:
        nd=dict(d)
        for v,s in d.items():
            w=v*p%M
            if w not in nd: nd[w]=s+(p,)
        d=nd
    return d
dA=prods(A); dB=prods(B)
print('halves',len(dA),len(dB))
sols=[]
for v,s in dA.items():
    w=T*pow(v,-1,M)%M
    if w in dB: sols.append(tuple(sorted(s+dB[w])))
if not sols: print('no solution'); sys.exit()
def val(S):
    m=p0
    for p in S: m*=p
    return m
sols.sort(key=val)
print('solutions',len(sols))
S=sols[0]; m=val(S)
print('S',S); print('m =',m); print('digits',len(str(m)))
