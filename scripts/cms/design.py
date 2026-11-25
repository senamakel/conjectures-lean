import numpy as np, json, sys
from lpfold import solve
from scipy.integrate import quad
def leftout_solve(M,K,B,nt=8000,jsub=1):
    # LP variant: BT term uses left-Riemann sums over knot segments split into jsub pieces
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, vstack, identity
    t=(np.arange(nt)+0.5)*np.pi/nt; dt=np.pi/nt
    C=np.ones((nt,K+1)); C[:,1:]=2*np.cos(np.outer(t,np.arange(1,K+1)))
    nv=K+1; ns=nt; npv=K+1
    c=np.concatenate([np.zeros(nv),dt*np.ones(ns),np.zeros(npv)])
    Cs=csr_matrix(C); I=identity(nt,format='csr'); Z=csr_matrix((nt,npv))
    A=vstack([hstack([Cs,-I,Z]),hstack([-Cs,-I,Z])]); b=np.zeros(2*nt)
    rows=[]
    for k in range(M,K+1):
        r=np.zeros(nv+ns+npv); r[k]=1; r[nv+ns+k]=-1; rows.append(r)
    r=np.zeros(nv+ns+npv); r[0]=-1/M; r[1:nv]=-2/M
    # left sums with jsub pieces per segment [k,k+1]: sum_{i<jsub} ((jsub-i)p_k + i p_{k+1})/jsub /(M jsub), x2 sides
    for k in range(M,K):
        for i in range(jsub):
            r[nv+ns+k]+=2*B*(jsub-i)/jsub/(M*jsub)
            r[nv+ns+k+1]+=2*B*i/jsub/(M*jsub)
    rows.append(r)
    A=vstack([A,csr_matrix(np.array(rows))]); b=np.concatenate([b,np.zeros(len(rows)-1),[-1]])
    bounds=[(None,None)]*nv+[(0,None)]*ns+[(0,None)]*npv
    bounds[K]=(0,0)
    res=linprog(c,A_ub=A,b_ub=b,bounds=bounds,method='highs')
    return np.pi/res.fun, res.x[:nv]
if __name__=='__main__':
    M=int(sys.argv[1]); B=float(sys.argv[2]); jsub=int(sys.argv[3])
    best=None
    for K in range(M+2,2*M+2):
        J,Phi=leftout_solve(M,K,B,jsub=jsub)
        if best is None or J>best[0]: best=(J,K,Phi)
    J,K,Phi=best; Phi=Phi/Phi[0]
    print(M,K,jsub,J,1/J); print(np.round(Phi,5).tolist())
    json.dump(dict(M=M,K=K,Phi=Phi.tolist(),J=J),open(f'design_M{M}_j{jsub}.json','w'))
