import sys, flint
p,a,n,m,E=map(int,sys.argv[1:6])
N=a*p**n; J=a*p**m; M=p**E
# coefficients x^0..x^J of x(x+1)...(x+N-1) mod p^E  (s(N,j))
ctx=flint.fmpz_mod_poly_ctx(M)
def tree(lo,hi):
    if hi-lo<=64:
        P=ctx([1])
        for i in range(lo,hi): P=P*ctx([i%M,1])
        return P
    mid=(lo+hi)//2
    C=tree(lo,mid)*tree(mid,hi)
    if C.degree()>J: C=ctx([C[j] for j in range(J+1)])
    return C
low=tree(0,N)   # s(N,j) for j<=J
# s(N,N-k) for k<=K via reversed product prod (1+i y)
K=a*(p-1)*p**(m-1)+1
def tree2(lo,hi):
    if hi-lo<=64:
        P=ctx([1])
        for i in range(lo,hi): P=P*ctx([1,i%M])
        return P
    mid=(lo+hi)//2
    C=tree2(lo,mid)*tree2(mid,hi)
    if C.degree()>K: C=ctx([C[j] for j in range(K+1)])
    return C
high=tree2(1,N)
def vp(x):
    x=int(x)
    if x==0: return None
    v=0
    while x%p==0: x//=p; v+=1
    return v
vJ=vp(low[J]); print("v(s(N,ap^m))=",vJ)
bad=0
for k in range(2,K+1):
    l=vp(low[J-k]); r1=vp(high[k])
    if l is None or r1 is None or vJ is None: continue
    rhs=vJ+r1+(2*(k//2)-1)*(n-m)
    if l!=rhs:
        bad+=1
        if bad<8: print("5.3 FAIL k=%d lhs=%d rhs=%d"%(k,l,rhs))
print("checked",K-1,"fails",bad)
