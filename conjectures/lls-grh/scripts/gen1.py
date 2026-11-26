import math
from gen import *
def phi1lo(x,s1,s2,l1,l2,L2):
    x=F(x)
    K1=(s1+1+l1/2)/(1+1/x-2/s2); K2=(s2+1+l2/2)/(1+1/x-2/s1)
    k1=K1*(1-1/x)+l1/2; k2=K2*(1-1/x)+l2/2
    Es=-F(1,2)*(1-1/x)*LPI-G/2*(1-1/x)+(l2+2)/x
    v=x-F(3,20)*s2-3*l2-3+2*K1*(l1-2)-k2*L2-2*K1*Es+F(1,2)*LPI*l1-(PI**2/6-G/2*l1)
    side = x>=64 and s1>0 and 1+1/x-2/s1>0 and l1>=2 and L2>=0 and Es<=0
    return v,side
def data1(Qa,Qb,c=F(1)):
    ka=klo(Qa); la=F(ka,64)*L2LO; kb=khi(Qb); Lb=F(kb,64)*L2HI
    x=math.floor(c*la*la); s1,s2=sqrt_bounds(x); k1=klo(x); k2=khi(x)
    v,side=phi1lo(x,s1,s2,F(k1,64)*L2LO,F(k2,64)*L2HI,Lb)
    return dict(Qa=Qa,Qb=Qb,ka=ka,kb=kb,x=x,s1=s1,s2=s2,k1=k1,k2=k2,v=v,side=side)
def plan1(Qs,Qe):
    ivs=[];Q=Qs
    while Q<Qe:
        best=None
        for m in [2**64,2**32,2**16,2**8,16,4,2,F(3,2),F(5,4),F(9,8),F(17,16),F(33,32),F(65,64)]:
            Qb=min(Qe,int(Q*m))
            d=data1(Q,Qb)
            if d['v']>0 and d['side']: best=d;break
        if best is None: return ivs,Q
        ivs.append(best);Q=best['Qb']
    return ivs,None
if __name__=='__main__':
  for s in [12,13,14]:
    iv,fail=plan1(2**s,2**700)
    print(s,len(iv),fail and fail.bit_length())
