import math,sys
primes=[p for p in range(2,5000) if all(p%d for d in range(2,int(p**.5)+1))]
g=0.5772156649
def loss_log(p,x):
    s=0; pk=p
    while pk<=x: s+=math.log(p)*math.log(x/pk); pk*=p
    return s
def loss_ces(p,x):
    s=0; pk=p
    while pk<x: s+=math.log(p)/pk*(1-pk/x); pk*=p
    return s
def margin(c,L,P,crude=False):
    # P: primes dividing q (all assumed | f: worst case once-loss); f=q
    x=math.floor(c*L*L); sx=math.sqrt(x); lx=math.log(x)
    PL = x-0.15*sx-3*lx-3
    low = PL - sum(loss_log(p,x) for p in P)
    Pc = lx-2-lx/x
    Sp = Pc - sum(loss_ces(p,x) for p in P)
    G2 = -0.5*math.log(math.pi)*(1-1/x) + (-g/2*(1-1/x)+(lx+1)/x)
    Z2 = max(0,(L*(1-1/x) - 2*Sp + 2*G2)/(1+1/x-2/sx))
    Et = math.pi**2/6 - g/2*lx
    up = (sx+1)*Z2 + (L+Z2)/2*lx - 0.5*math.log(math.pi)*lx + Et
    return low-up
def worst(c,L):
    # q multiple of first k primes, k max with primorial<=e^L; check all k' <= k
    best=1e9; lp=0; P=[]
    best=margin(c,L,[])
    for p in primes:
        if lp+math.log(p)>L: break
        lp+=math.log(p); P.append(p)
        best=min(best,margin(c,L,P))
    return best
for c in [1.5,2,2.25,2.5,3]:
    bad=[L for L in [i/20 for i in range(int(20*math.log(3000)),20*150)] if worst(c,L)<=0]
    pb=[L for L in [i/20 for i in range(int(20*math.log(5)),20*150)] if margin(c,L,[])<=0]
    print(c,"last bad worst-case L",max(bad) if bad else None, "2^%.1f"%(max(bad)/math.log(2)) if bad else "", "| prime-q bad up to L", max(pb) if pb else None)
