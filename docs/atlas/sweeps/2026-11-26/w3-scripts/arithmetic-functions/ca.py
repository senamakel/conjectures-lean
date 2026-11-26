# Generate colossally abundant numbers (generic: one prime power step at a time, sorted by critical epsilon)
import heapq, math, sys
from decimal import Decimal as D, getcontext
getcontext().prec=45
G=D('0.577215664901532860606512090082402431042159335939923598805767')
EG=D('1.781072417990197985236504103107179549169645214303430205357665')
PI2=D('9.869604401089358618834490999876151135313699407240790626413349')
def primes(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
def crit(p,k):  # epsilon at which exponent of p goes from k-1 to k
    s=sum(p**j for j in range(1,k+1))
    return math.log1p(1.0/s)/math.log(p)
def ca_stream(pmax):
    P=primes(pmax); exp={}
    h=[(-crit(p,1),p,1) for p in P]; heapq.heapify(h)
    logN=D(0); logS=D(0)  # log(sigma(N)/N)
    lnp={}
    while h:
        e,p,k=heapq.heappop(h)
        if p not in lnp: lnp[p]=D(p).ln()
        logN+=lnp[p]
        # sigma(p^k)/p^k over sigma(p^{k-1})/p^{k-1}
        num=D(p)**(k+1)-1; den=(D(p)**k-1)*p
        logS+= (num/den).ln()
        exp[p]=k
        if p**(k+1) < 10**30 or k<3: heapq.heappush(h,(-crit(p,k+1),p,k+1))
        yield p,k,-e,logN,logS
        if p==P[-1]: return
