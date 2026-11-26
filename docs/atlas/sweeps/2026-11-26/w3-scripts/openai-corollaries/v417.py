import numpy as np, sys, math
N=int(float(sys.argv[1])); M=7*N
phi=np.arange(M+1,dtype=np.int64)
isc=np.zeros(M+1,dtype=bool)
for p in range(2,M+1):
    if not isc[p]:
        isc[2*p::p]=True if p*2<=M else isc[2*p::p]
        phi[p::p]-=phi[p::p]//p
# check bound: min over n in (M/2..M] of phi(n) must exceed N so all preimages of v<=N lie <= M
L=math.log(math.log(M)); assert 7>math.exp(0.5772156649)*L+2.50637/L
# least preimage ell(v) for v<=N
ell=np.full(N+1,-1,dtype=np.int64)
vals=phi[1:]; idx=np.arange(1,M+1)
mask=vals<=N
v=vals[mask]; n=idx[mask]
order=np.argsort(v,kind='stable')  # n increasing within equal v since stable and idx increasing
v=v[order]; n=n[order]
first=np.ones(len(v),dtype=bool); first[1:]=v[1:]!=v[:-1]
ell[v[first]]=n[first]
for e in range(3,int(math.log10(N))+1):
  for c in (1,2,5):
    x=c*10**e
    if x>N: break
    tot=ell[1:x+1]>0
    V=tot.sum(); Vp=(tot & (ell[1:x+1]<=x)).sum()
    l=ell[1:x+1][tot]; vv=np.arange(1,x+1)[tot]
    N1=((l>x)&(l<=2*x)).sum(); N2=((l>2*x)&(l<=3*x)).sum()
    r=l/vv
    print(x,V,Vp,round(V/Vp,5),'N1/V',round(N1/V,4),'N2/V',round(N2/V,4),'frac ell/v<=2',round((r<=2).mean(),4),'max ell/v',round(r.max(),3))
