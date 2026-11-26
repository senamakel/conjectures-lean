# Habib-Hildebrand: u''u-(u')^2 = e^{-x}P(u)-1, u = sum p_k(x) e^{-kx}, p_0=x. Exact recursion with flint fmpq_poly.
import sys
from flint import fmpq_poly, fmpq
X=fmpq_poly([0,1])
def Lop(p,s):
    d1=p.derivative(); d2=d1.derivative()
    return X*(d2-2*s*d1+s*s*p)-2*(d1-s*p)
def solveL(r,s):
    # find polynomial p with L_s p = r ; return p or None
    if r==0: return fmpq_poly([0])
    D=r.degree(); N=D-1
    if N<0: return None
    a=[fmpq(0)]*(N+3)
    rc=lambda m: r[m] if m<=D else fmpq(0)
    for m in range(N+1,0,-1):
        a[m-1]=(rc(m)-2*s*(1-m)*a[m]-(m+1)*(m-2)*a[m+1])/(s*s)
    p=fmpq_poly(a[:N+1])
    return p if Lop(p,s)==r else None
def run(Pcoef,S,verbose=False):
    d=len(Pcoef)-1
    P=fmpq_poly(Pcoef)
    Pder=[P]; 
    fact=[1]
    for l in range(1,d+1): Pder.append(Pder[-1].derivative()); fact.append(fact[-1]*l)
    p=[X]
    A={}  # A[(l,n)] = [U^l]_n, U = sum_{k>=1} p_k z^k
    out=[]
    for s in range(0,S):
        # need [U^l]_s for l=1..min(s,d)
        for l in range(1,min(s,d)+1):
            if l==1: A[(1,s)]=p[s]
            else:
                acc=fmpq_poly([0])
                for k in range(1,s-l+2):
                    if (l-1,s-k) in A: acc+=p[k]*A[(l-1,s-k)]
                A[(l,s)]=acc
        # [P(x+U)]_s
        if s==0: rhs=P
        else:
            rhs=fmpq_poly([0])
            for l in range(1,min(s,d)+1):
                rhs+=Pder[l]*A[(l,s)]/fact[l]
        k1=s+1
        for k in range(1,k1):
            l=k1-k
            pk,pl=p[k],p[l]; dk=pk.derivative(); dl=pl.derivative()
            rhs-= dk.derivative()*pl - dk*dl - 2*(k-l)*dk*pl + k*(k-l)*pk*pl
        q=solveL(rhs,k1)
        if q is None:
            return out,('NOPOLY',k1)
        p.append(q)
        cs=[q[j] for j in range(q.degree()+1)]
        neg=[j for j,c in enumerate(cs) if c<0]
        out.append((k1,q.degree(),neg))
        if verbose: print(k1,q.degree(),'neg',neg[:6],flush=True)
    return out,p
if __name__=="__main__":
    Pc=[fmpq(*map(int,t.split('/'))) if '/' in t else fmpq(int(t)) for t in sys.argv[1].split(',')]
    o,p=run(Pc,int(sys.argv[2]),True)
    if isinstance(p,tuple): print(p)
