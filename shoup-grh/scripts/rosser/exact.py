# Exact integer checker mirroring the planned Lean checker.
import pickle, sys, math
D=2**48; R=100; TN=1200; M=6
def cdiv(a,b): return -(-a//b)
def mulU(x,y): return cdiv(x*y,D)
def omU(a,b):   # t=a/b>=1 ; (1001/1000) t (1+(t-1)/1000) - 1
    assert a>=b
    num=1001*a*(1000*b+a-b) - 10**6*b*b
    return cdiv(D*num, 10**6*b*b)
def crudeU(a,b): # v=a/b: 12^-6 (om(2v) + kap*4 v^2/15), kap=(1001/1000)^2
    num1=omU(2*a,b)
    t2=cdiv(D*1001*1001*4*a*a, 10**6*15*b*b)
    return cdiv(num1+t2, 12**6)
def momega(entries, tend):
    # entries: list of (ta,tb,H) thresholds t_k=ta/tb (first is 1), H decreasing; tend=(a,b)
    tot=0
    for k in range(len(entries)):
        H=entries[k][2]
        if k+1<len(entries):
            H1=entries[k+1][2]; a,b=entries[k+1][0],entries[k+1][1]
            assert H>=H1
            tot+=mulU(H-H1, omU(a,b))
        else:
            tot+=mulU(H, omU(*tend))
    return tot
def lrow(g,beta,i):
    S=g[i]; N=len(g)-1
    k0=max(k for k in range(N) if g[k]+R<=S)
    ent=[(1,1,beta[k0])]+[(g[k]+R,S,beta[k]) for k in range(k0+1,N)]
    return momega(ent,(TN+R,S))+crudeU(TN+R,S)
def urow(g,alpha,j,idl):
    S=g[j]; N=len(g)-1
    if g[idl]+R>S:
        ent=[(1,1,D)]+[(g[i]+R,S,alpha[i]) for i in range(idl,N)]
    else:
        st=max(i for i in range(idl,N) if g[i]+R<=S)
        ent=[(1,1,alpha[st])]+[(g[i]+R,S,alpha[i]) for i in range(st+1,N)]
    return momega(ent,(TN+R,S))+crudeU(TN+R,S)
def psiU(a,b):  # (a/b - 1/12)^-6 upper
    return cdiv(D*(12*b)**6, (12*a-b)**6)
def tailrow(X):
    us=[(120+q,120) for q in range(11)]+[(780+35*j,720) for j in range(1,61)]
    ent=[]
    for q,(a,b) in enumerate(us[:-1]):
        H=psiU(a,b)
        if q<10: H=max(H,X)
        ent.append((a,b,H))
    ent[0]=(1,1,ent[0][2])
    assert us[-1]==(2880,720)
    tot=momega(ent,(4,1))
    tot+=mulU(psiU(4,1), omU(8,1)+cdiv(D*1001*1001*64, 10**6*15))
    return tot
def check(g,beta,alpha,idl,s0i,amin):
    N=len(g)-1; ok=True; worst=1e9
    for k in range(N-1): assert beta[k]>=beta[k+1]
    for i in range(N):
        if g[i]>=200 and i+1<N: assert alpha[i]>=alpha[i+1], i
    assert alpha[idl]<=D
    for i in range(N):
        if g[i]>=200:
            v=lrow(g,beta,i)
            worst=min(worst,(alpha[i]-v)/D)
            if v>alpha[i]: ok=False; print("L fail",g[i],v/D,alpha[i]/D)
    for j in range(N):
        v=urow(g,alpha,j,idl)
        worst=min(worst,(beta[j]-v)/D)
        if v>beta[j]: ok=False; print("U fail",g[j],v/D,beta[j]/D)
    kT1=g.index(TN-R)
    for X in (beta[kT1]*13**6, alpha[kT1]*13**6):
        v=tailrow(X)
        if v>D: ok=False; print("tail fail",v/D)
        else: print("tail",v/D)
    print("ok",ok,"worst margin",worst, "a(s0)=",1-alpha[s0i]/D)
    return ok
if __name__=="__main__":
    g,x,(N,I,i0,idl)=pickle.load(open(sys.argv[1],'rb'))
    N=len(g)-1
    beta=[math.ceil(x[k]*D)+0 for k in range(N)]
    alpha=[D]*N
    for i in I[:-1]: alpha[i]=math.ceil(x[N+i-i0]*D)
    # enforce monotone after rounding
    for k in range(N-2,-1,-1): beta[k]=max(beta[k],beta[k+1])
    for i in range(N-2,i0-1,-1): alpha[i]=max(alpha[i],alpha[i+1])
    s0i=g.index(205)
    ok=check(g,beta,alpha,idl,s0i,0.03)
    pickle.dump((g,beta,alpha,idl),open('table.pkl','wb'))
