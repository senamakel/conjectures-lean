# Conj 5.1(i) with m<n: v_p(s(a p^n, a p^m - k)), unsigned s; column j = a p^m - k of row N = a p^n.
# compute coefficients of x^0..x^J of x(x+1)...(x+N-1) mod p^E
import sys
p,a,n,m,E=map(int,sys.argv[1:6]); ks=[int(x) for x in sys.argv[6:]]
M=p**E; N=a*p**n; J=a*p**m
c=[0]*(J+1); c[0]=1
for i in range(N):  # multiply by (x+i)
    for j in range(J,0,-1):
        c[j]=(c[j-1]+i*c[j])%M
    c[0]=(i*c[0])%M
def vp(x):
    if x==0: return None
    v=0
    while x%p==0: x//=p; v+=1
    return v
for k in ks:
    print("p=%d a=%d n=%d m=%d k=%d v=%s (precision %d)"%(p,a,n,m,k,vp(c[J-k]),E))
