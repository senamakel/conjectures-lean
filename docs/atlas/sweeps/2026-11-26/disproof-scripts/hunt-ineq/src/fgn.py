import sys, mpmath as mp
mp.mp.dps=int(sys.argv[3])
N=int(sys.argv[2])
def rho(H,k):
    if k==0: return mp.mpf(1)
    return (mp.mpf(k+1)**(2*H)-2*mp.mpf(k)**(2*H)+mp.mpf(k-1)**(2*H))/2
for Hs in sys.argv[1].split(','):
    H=mp.mpf(Hs); r=[rho(H,k) for k in range(N+1)]
    phi=[r[1]]; v=1-r[1]**2; worst=(mp.inf,None)
    for m in range(2,N+1):
        k=(r[m]-mp.fsum(phi[j]*r[m-1-j] for j in range(m-1)))/v
        phi=[phi[j]-k*phi[m-2-j] for j in range(m-1)]+[k]
        v=v*(1-k*k)
        mn=min(range(m),key=lambda j:phi[j])
        if phi[mn]<worst[0]: worst=(phi[mn],(m,mn+1))
        if phi[mn]<=0: print("NEG H",Hs,"order",m,"j",mn+1,mp.nstr(phi[mn],10),flush=True); break
    print("H",Hs,"N",N,"min coef",mp.nstr(worst[0],8),"at (order,j)",worst[1],"pacf last",mp.nstr(k,6),flush=True)
