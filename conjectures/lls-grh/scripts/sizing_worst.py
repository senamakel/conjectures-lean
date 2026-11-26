import math,itertools
exec(open(__file__.replace('sizing_worst.py','sizing_base.py')).read().split('def margin')[0])
def margin2(c,L,Pf,PR,PLc=(0.15,3,3)):
    x=math.floor(c*L*L); sx=math.sqrt(x); lx=math.log(x)
    a,b,d=PLc
    PL = x-a*sx-b*lx-d
    low = PL - sum(loss_log(p,x) for p in Pf) - 2*sum(loss_log(p,x) for p in PR)
    Pc = lx-2-lx/x
    Sp = Pc - sum(loss_ces(p,x) for p in Pf) - 2*sum(loss_ces(p,x) for p in PR)
    lf = L - sum(math.log(p) for p in PR)
    G2 = -0.5*math.log(math.pi)*(1-1/x) + (-g/2*(1-1/x)+(lx+1)/x)
    Z2 = max(0,(lf*(1-1/x) - 2*Sp + 2*G2)/(1+1/x-2/sx))
    Et = math.pi**2/6 - g/2*lx
    up = (sx+1)*Z2 + (lf+Z2)/2*lx - 0.5*math.log(math.pi)*lx + Et
    return low-up
def worst(c,L):
    lp=0; P=[]
    best=margin2(c,L,[],[])
    for p in primes:
        if lp+math.log(p)>L: break
        lp+=math.log(p); P.append(p)
        # choose for each of 2,3 (and 5,7) whether in R
        small=[q for q in P if q<=7]; rest=[q for q in P if q>7]
        for r in range(len(small)+1):
            for R in itertools.combinations(small,r):
                Pf=[q for q in small if q not in R]+rest
                best=min(best,margin2(c,L,Pf,list(R)))
    return best
import sys
for c in [2,2.25,2.5,3,3.5]:
    bad=[L for L in [i/20 for i in range(int(20*math.log(3000)),20*120)] if worst(c,L)<=0]
    print(c,"last bad",max(bad) if bad else None,"2^%.1f"%(max(bad)/math.log(2)) if bad else "")
