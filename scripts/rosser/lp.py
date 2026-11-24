# Regenerate the Rosser table: MM=6 TT=1200 python3 lp.py 205 0.03 && python3 exact.py sol_205.pkl && python3 gen.py
# (run inside scripts/rosser; needs numpy and scipy). The kernel re-checks the result (Shoup/Rosser/Table.lean).
# LP for Rosser tables, mirroring the planned Lean checker structure exactly (floats).
import math, sys, numpy as np, pickle
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
R=100
import os
ETA=1e-3; DL=1e-3; M=int(os.environ.get('MM','6')); K=1.0
DELU=10   # U includes p iff s_p > 2 + DELU/R
def om(v): return (1+DL)*v*(1+ETA*(v-1)) - 1
KAP=(1+DL)*(1+ETA)
def crude(vn, T):  # tail over u>vn of (sig u-1)^-m with sig vn - 1 = T
    return T**-M * (om(2*vn) + KAP*4*vn*vn*2.0**(2-M)/(1-2.0**(2-M)))
def grid(segs, T):
    g=[]
    for (lo,hi,st) in segs:
        x=lo
        while x<hi: g.append(x); x+=st
    g.append(T); return g   # integers in units 1/R
TT=int(os.environ.get('TT','1200'))
SEGS=[(100,200,2),(200,300,1),(300,400,2),(400,600,10),(600,TT,50)]
def rows_build(g):
    T=g[-1]/R; N=len(g)-1
    I=[i for i in range(N+1) if g[i]>=200]; i0=I[0]
    idl=min(i for i in I if g[i]>=200+DELU)
    nb=N; na=N-i0
    vb=lambda k:k; va=lambda i:nb+i-i0
    nv=nb+na
    betaN=K*T**-M; alphaN=betaN
    rows=[]  # (coefs dict, const, rhs, kind, idx)
    for i in I[:-1]:
        S=g[i]; k0=max(k for k in range(N+1) if g[k]+R<=S)
        co={}; const=0
        for k in range(k0,N):
            w=om((g[k+1]+R)/S)
            co[vb(k)]=co.get(vb(k),0)+w
            if k+1<N: co[vb(k+1)]=co.get(vb(k+1),0)-w
        const+=K*crude((g[N]+R)/S,T)
        co[va(i)]=co.get(va(i),0)-1
        rows.append((co,const,0,'L',i))
    for j in range(N):
        S=g[j]; co={}; const=0
        if g[idl]+R > S:
            pts=[(None,0)]+[(i,(g[i]+R)/S) for i in I if i>=idl]
        else:
            st=max(i for i in I if g[i]+R<=S)
            pts=[(st,0)]+[(i,(g[i]+R)/S) for i in I if i>st]
        for t in range(len(pts)-1):
            i=pts[t][0]; i1,u1=pts[t+1]; w=om(u1)
            if i is None: const+=w
            else: co[va(i)]=co.get(va(i),0)+w
            if i1!=N: co[va(i1)]=co.get(va(i1),0)-w
        const+=K*crude((g[N]+R)/S,T)
        co[vb(j)]=co.get(vb(j),0)-1
        rows.append((co,const,0,'U',j))
    # tail cells
    kT1=max(k for k in range(N+1) if g[k]<=g[N]-R)
    us=[1+(1/T)*j/10 for j in range(11)]+[(1+1/T)+(3-1/T)*j/60 for j in range(1,61)]
    ps=[(u-1/T)**-M for u in us]
    # layers from q=10 on: H_q=ps_q ; region (1,us10]: H=X (assumed X>=ps0)
    rest=sum((ps[q]-ps[q+1])*om(us[q+1]) for q in range(10,len(us)-2))+ps[-2]*om(us[-1])
    rest+=ps[-1]*KAP*64/(1-2.0**-4)
    w1=om(us[10])
    for var,kind in [(vb(kT1),'TL'),(va(kT1),'TU')]:
        rows.append(({var:(T+1)**M/K*w1}, rest-ps[10]*w1, 1, kind, kT1))
        rows.append(({var:-(T+1)**M/K}, ps[0], 0, kind+'x', kT1))  # X>=ps0
    tn=rest; 
    # monotone
    for k in range(N-1): rows.append(({vb(k+1):1,vb(k):-1},0,0,'mb',k))
    rows.append(({vb(N-1):-1},betaN,0,'mb',N-1))
    for i in range(i0,N-1): rows.append(({va(i+1):1,va(i):-1},0,0,'ma',i))
    rows.append(({va(N-1):-1},alphaN,0,'ma',N-1))
    rows.append(({va(idl):1},0,1,'pos',idl))
    return rows,nv,(N,I,i0,idl,vb,va,tn,ps[0],w1)
def solve(g, s0, amin):
    rows,nv,info=rows_build(g); N,I,i0,idl,vb,va,_,_,_=info
    # maximize margin t: each L/U row gets + t*(1) ; require a(s0)>=amin
    A=lil_matrix((len(rows)+1,nv+1)); b=[]
    for r,(co,const,rhs,kind,idx) in enumerate(rows):
        for c,v in co.items(): A[r,c]=v
        if kind in ('L','U'): A[r,nv]=1.0
        b.append(rhs-const)
    is0=I.index(min(i for i in I if g[i]>=s0))
    A[len(rows),va(I[is0])]=1; b.append(1-amin)
    c=np.zeros(nv+1); c[nv]=-1
    res=linprog(c,A_ub=A.tocsr(),b_ub=np.array(b),bounds=[(0,None)]*nv+[(0,1)],method='highs')
    return res,info
if __name__=="__main__":
    s0=int(sys.argv[1]); amin=float(sys.argv[2])
    g=grid(SEGS,TT)
    res,info=solve(g,s0,amin)
    print(len(g),res.status,res.message, "margin", -res.fun if res.status==0 else None)
    if res.status==0:
        N,I,i0,idl,vb,va,tn,p0,w1=info; x=res.x
        for i in I[:-1]:
            if g[i] in (200,202,204,206,208,210,215,220,250,300): print(g[i], 1-x[va(i)])
        pickle.dump((g,x[:-1],info[:4]),open(f'sol_{s0}.pkl','wb'))
