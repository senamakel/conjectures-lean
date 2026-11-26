import math, sys
from fractions import Fraction as F
L2LO=F(6931471803,10**10); L2HI=F(6931471808,10**10)
LPI=F(11364,10000); G=F(57688,100000); PI=F(31416,10000)
lp={2:(64,64),3:(101,102),5:(148,149),7:(179,180),11:(221,222),13:(236,237),17:(261,262)}
def lplo(p): return F(lp[p][0],64)*L2LO
def lphi(p): return F(lp[p][1],64)*L2HI
def klo(n):  # largest k with 2^k <= n^64
    v=n**64; return v.bit_length()-1
def khi(n):
    v=n**64; k=v.bit_length()-1
    return k if 2**k==v else k+1
def mx(a,b): return a if a>=b else b
def philo(x,s1,s2,l1,l2,L2):
    x=F(x)
    K1=(s1+1+l1/2)/(1+1/x-2/s2); K2=(s2+1+l2/2)/(1+1/x-2/s1)
    k1=K1*(1-1/x)+l1/2; k2=K2*(1-1/x)+l2/2
    Es=-F(1,2)*(1-1/x)*LPI-G/2*(1-1/x)+(l2+2)/x
    b1=l1**2/(2*lphi(17))+2*K1/16; b2=l2**2/(2*lplo(17))+2*K2/16
    tot=0
    for p in [2,3,5,7,11,13]:
        A=(l2-lplo(p)/2)**2/2+2*K2*(lphi(p)/(p-1))
        W=A+mx(0,A-k1*lplo(p))
        tot+=mx(0,W-b1*lplo(p))
    v=x-F(3,20)*s2-3*l2-3+2*K1*(l1-2)-k2*L2-2*K1*Es+F(1,2)*LPI*l1-(PI**2/6-G/2*l1)-b2*L2-tot
    side = x>=64 and s1>0 and 1+1/x-2/s1>0 and l1>=2 and L2>=0 and Es<=0 and b2<=k1 and all(lphi(p)/2<=l1 for p in [2,3,5,7,11,13])
    return v, side
def sqrt_bounds(x):
    r=math.isqrt(x)
    # s1 = r + d/1000 with s1^2<=x
    s1=F(r); 
    for d in range(999,-1,-1):
        c=F(r)+F(d,1000)
        if c*c<=x: s1=c;break
    s2=F(r+1)
    for d in range(0,1000):
        c=F(r)+F(d,1000)
        if c*c>=x: s2=c;break
    return s1,s2
def data(Qa,Qb,c):
    ka=klo(Qa); la=F(ka,64)*L2LO
    kb=khi(Qb); Lb=F(kb,64)*L2HI
    x=math.floor(c*la*la)
    s1,s2=sqrt_bounds(x)
    k1=klo(x); k2=khi(x)
    l1=F(k1,64)*L2LO; l2=F(k2,64)*L2HI
    v,side=philo(x,s1,s2,l1,l2,Lb)
    return dict(Qa=Qa,Qb=Qb,ka=ka,kb=kb,x=x,s1=s1,s2=s2,k1=k1,k2=k2,v=v,side=side)
def plan(c, Qstart, Qend):
    ivs=[]; Q=Qstart
    while Q<Qend:
        best=None
        for r in [2.0,1.6,1.4,1.3,1.2,1.15,1.1,1.07,1.05,1.03,1.02]:
            Qb=min(Qend, int(Q**r)) if r>1 else Q+1
            if Qb<=Q: continue
            d=data(Q,Qb,c)
            if d['v']>0 and d['side']: best=d;break
        if best is None: print("FAIL at",Q, math.log(Q)); return None
        ivs.append(best); Q=best['Qb']
    return ivs
if __name__=="__main__":
    c=F(sys.argv[1]); Tbits=int(sys.argv[2])
    ivs=plan(c,2**17,2**Tbits)
    if ivs:
        print(len(ivs)); 
        for d in ivs: print(d['Qa'].bit_length(), d['Qb'].bit_length(), d['x'], float(d['v']))
