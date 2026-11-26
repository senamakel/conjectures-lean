from decimal import Decimal as D, getcontext
getcontext().prec=50
EG=D('1.781072417990197985236504103107179549169645214303430205357665')
def f(n): L=D(n).ln().ln(); return EG*L+D('2.5')/L
from math import prod
def primes(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
P=primes(2000)
print("primorial checks: k, N_k, phi, m/phi(m) - f(phi)")
N=1;ph=1
for k,p in enumerate(P[:60],1):
    N*=p; ph*=p-1
    if ph>2:
        diff=D(N)/D(ph)-f(ph)
        if k<=14 or diff>0: print(k,p,N if k<12 else '', ph if k<12 else '', float(diff))
# exact: a(n) for n=phi(N9)
