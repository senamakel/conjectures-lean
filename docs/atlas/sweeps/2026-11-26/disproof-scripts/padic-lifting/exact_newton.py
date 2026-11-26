# independent exact check: e_k(1..N-1) via Newton identities from exact power sums
import sys
N=int(sys.argv[1]); K=int(sys.argv[2]); p=int(sys.argv[3])
P=[0]*(K+1)
for j in range(1,N):
    t=1
    for i in range(1,K+1):
        t*=j; P[i]+=t
e=[1]+[0]*K
for k in range(1,K+1):
    s=0
    for i in range(1,k+1):
        s+= (-1)**(i-1)*e[k-i]*P[i]
    assert s%k==0
    e[k]=s//k
def vp(x):
    v=0
    while x%p==0: x//=p; v+=1
    return v
for k in [int(x) for x in sys.argv[4:]]:
    print("N=%d k=%d s(N,N-k)=e_k has %d digits, v_%d = %d"%(N,k,len(str(e[k])),p,vp(e[k])))
