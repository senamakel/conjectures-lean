from fractions import Fraction as F
import math
def primes_upto(N):
    s=bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
PR=primes_upto(2000)
# float version of crit: K*[(2/3) g (log p + 5/3) + (log x + 2)/y] < y/2 - 1/20 - 3/y, y=sqrt x, log p<=2log(x+3)
def ok(K,y):
    x=y*y; g=1+2/y+3/y**3; lp=2*math.log(x+3)
    return K*((2/3)*g*(lp+5/3)+(math.log(x)+2)/y) < y/2-1/20-3/y
def ythresh(K):
    lo,hi=1.0,1e30
    for _ in range(200):
        m=math.sqrt(lo*hi)
        if ok(K,m): hi=m
        else: lo=m
    return hi
def Kval(n,s,d): return 2**(n-s)*(2+(s-1)/d)-1
def upper(n,L):
    best=None
    for s in range(0,n):
        M=L[n-s:] if s>0 else []
        d=1-sum(1/q for q in M)
        if d<=0: continue
        y=ythresh(Kval(n,s,d)); p=(y*y+2)**2
        if best is None or p<best[0]: best=(p,s,d)
    return best
if __name__ == '__main__':
  for n in range(1,36):
    L=PR[:n]; lower=max(math.prod(L)+1,2.5e15)
    u=upper(n,L)
    print(n, "%.3e"%lower, "%.3e"%u[0], u[1], "OK" if u[0]<=lower else "NEED")
