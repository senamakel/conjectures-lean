# Python prototype of MTT Algorithm 1 with the constants of Grosswald/Crit.lean (floats; for sizing only).
import math, sys
from crit import primes_upto, ythresh, Kval
PR=primes_upto(5000)
LOW=2500000000000001
stats={'leaves':0,'cand':0,'nodes':0,'empty':0}
def upper(n,L):
    best=None
    for s in range(0,n):
        M=L[n-s:] if s>0 else []
        d=1-sum(1/q for q in M)
        if d<=0: continue
        y=math.ceil(ythresh(Kval(n,s,d))); p=(y*y+2)**2
        if best is None or p<best: best=p
    return best
LIM=10**6
def node(n,X,Y,depth=0):
    stats['nodes']+=1
    L=[q for q in PR if q not in Y][:n]
    lower=max(math.prod(L)+1,LOW)
    up=upper(n,L)
    prodX=math.prod(X)
    if up<=lower: stats['empty']+=1; return
    enum=(up-lower)//prodX
    if enum>LIM:
        used=set(X)|set(Y)
        q=next(r for r in PR if r not in used)
        node(n,X+[q],Y,depth+1); node(n,X,Y+[q],depth+1)
    else:
        stats['leaves']+=1; stats['cand']+=enum+1
if __name__ == '__main__':
 for n in [12,13,14]:
    for k in stats: stats[k]=0
    node(n,[2],[])
    print(n,stats)
