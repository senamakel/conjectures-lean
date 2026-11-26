import math
from crit import primes_upto, ok
for B in [16,64,256,1024]:
    k=round(math.log2(B))
    P=[q for q in primes_upto(B-1)]
    logCk = len(P)*math.log(B) - sum(math.log(q) for q in P)   # log(C^k)
    C=math.exp(logCk/k)
    # need for y: K=C*p^(1/k) with p~y^4
    lo,hi=10.0,1e60
    for _ in range(300):
        m=math.sqrt(lo*hi)
        if ok(C*(m**4)**(1/k)*1.0001, m): hi=m
        else: lo=m
    print(B,k,"C=%.4g"%C,"p_tail=%.3e"%(hi**4))
