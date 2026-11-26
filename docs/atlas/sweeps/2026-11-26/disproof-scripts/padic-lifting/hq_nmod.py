# third route: flint nmod_poly product tree mod p^E (word-size modulus), truncated at degree K
import sys, flint, time
p, N, E, K = map(int, sys.argv[1:5]); ks=[int(x) for x in sys.argv[5:]]
M=p**E; assert M < 2**63
t=time.time()
def tree(lo,hi):
    if hi-lo<=64:
        P=flint.nmod_poly([1],M)
        for i in range(lo,hi): P=P*flint.nmod_poly([1,i%M],M)
        return P
    mid=(lo+hi)//2
    A=tree(lo,mid); B=tree(mid,hi)
    if A.degree()+B.degree()>K:
        C=A.mul_low(B,K+1) if hasattr(A,'mul_low') else (A*B)
        if C.degree()>K: C=flint.nmod_poly(C.coeffs()[:K+1],M)
    else: C=A*B
    return C
P=tree(1,N)
print("tree %.1fs"%(time.time()-t),flush=True)
for k in ks:
    x=int(P[k]); v=0
    if x==0: v=">=%d"%E
    else:
        while x%p==0: x//=p; v+=1
    print("p=%d N=%d k=%d v=%s (mod p^%d)"%(p,N,k,v,E),flush=True)
