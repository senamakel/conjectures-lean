# LP over piecewise-linear even weights with integer knots k/M, folded L1: A1 = int_0^pi |P(t)| dt,
# P(t)=Phi0+2 sum Phi_k cos(kt).  J = pi*(S/M - B*out)/A1.
import numpy as np, sys, json
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack, identity
def solve(M,K,B,nt=20000,nonneg_in=False):
    t=(np.arange(nt)+0.5)*np.pi/nt; dt=np.pi/nt
    C=np.ones((nt,K+1)); C[:,1:]=2*np.cos(np.outer(t,np.arange(1,K+1)))
    nv=K+1; ns=nt; npv=K+1
    c=np.concatenate([np.zeros(nv),dt*np.ones(ns),np.zeros(npv)])
    Cs=csr_matrix(C); I=identity(nt,format='csr'); Z=csr_matrix((nt,npv))
    A=vstack([hstack([Cs,-I,Z]),hstack([-Cs,-I,Z])]); b=np.zeros(2*nt)
    # p_k >= Phi_k (k>=M)
    rows=[]
    for k in range(M,K+1):
        r=np.zeros(nv+ns+npv); r[k]=1; r[nv+ns+k]=-1; rows.append(r)
    # S/M - B*out >= 1 : -(S/M) + B*out <= -1 ; S=Phi0+2sum Phi_k ; out=(2/M)(p_M/2+sum_{k>M}p_k)
    r=np.zeros(nv+ns+npv); r[0]=-1/M; r[1:nv]=-2/M
    r[nv+ns+M]+=B*(1/M)
    r[nv+ns+M+1:nv+ns+K+1]+=B*(2/M)
    rows.append(r)
    A=vstack([A,csr_matrix(np.array(rows))]); b=np.concatenate([b,np.zeros(len(rows)-1),[-1]])
    bounds=[(None,None)]*nv+[(0,None)]*ns+[(0,None)]*npv
    bounds[K]=(0,0)
    if nonneg_in:
        for k in range(M): bounds[k]=(0,None)
    res=linprog(c,A_ub=A,b_ub=b,bounds=bounds,method='highs')
    Phi=res.x[:nv]
    return np.pi/res.fun, Phi
if __name__=='__main__':
    B=float(sys.argv[1])
    for M in [2,3,4,5,6,8,10,16]:
        best=None
        for K in range(M+1,2*M+2):
            J,Phi=solve(M,K,B,nt=6000)
            if best is None or J>best[0]: best=(J,K,Phi)
        J,K,Phi=best
        print(M,K,round(J,5),round(1/J,5),np.round(Phi/Phi[0],4).tolist())
