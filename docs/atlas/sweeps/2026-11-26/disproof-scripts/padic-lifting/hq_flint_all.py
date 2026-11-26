import sys, flint, time
p, n, a, E = map(int, sys.argv[1:5])
N=a*p**n; K=a*(p-1)*p**(n-1)+1
M=p**E; ctx=flint.fmpz_mod_poly_ctx(M)
sys.setrecursionlimit(10000)
def tree(lo,hi):
    if hi-lo<=64:
        P=ctx([1])
        for i in range(lo,hi): P=P*ctx([1,i%M])
        return P
    mid=(lo+hi)//2
    C=tree(lo,mid)*tree(mid,hi)
    if C.degree()>K: C=C.truncate(K+1) if hasattr(C,'truncate') else ctx([C[j] for j in range(K+1)])
    return C
t=time.time(); P=tree(1,N); print("tree %.1fs"%(time.time()-t),file=sys.stderr)
for k in range(2,K+1):
    x=int(P[k]); v=0
    if x==0: v=E
    else:
        while x%p==0: x//=p; v+=1
    print(p,a,n,k,v)
