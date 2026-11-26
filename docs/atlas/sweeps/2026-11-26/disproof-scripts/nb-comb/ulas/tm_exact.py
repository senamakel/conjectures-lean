# exact t_m(n)=[x^n] prod (1-x^{2^j})^m and b_m(n)=[x^n] prod (1-x^{2^j})^{-m}
# checks GMU Conj 3.15 (t_m(n)!=0, m>=4), 5.9 (no 3 consecutive same sign; t^2>t(n-1)t(n+1)), 5.10 (b^2>b(n-1)b(n+1), m>=4)
import sys
from itertools import accumulate
def upsample(a, N):
    u=[0]*(N+1)
    for i,v in enumerate(a):
        if 2*i>N: break
        u[2*i]=v
    return u
def tseq(m,N):
    t=[1,-m]
    M=2
    while M<=N:
        u=upsample(t,2*M-1)
        for _ in range(m):
            u=[u[0]]+[u[i]-u[i-1] for i in range(1,len(u))]
        t=u; M=len(t)
        if M>N: break
    return t[:N+1]
def bseq(m,N):
    b=[1,m]; M=2
    while True:
        u=upsample(b,2*M-1)
        for _ in range(m): u=list(accumulate(u))
        b=u; M=len(b)
        if M>N: break
    return b[:N+1]
if __name__=="__main__":
    N=int(sys.argv[1]); ms=list(map(int,sys.argv[2].split(',')))
    for m in ms:
        t=tseq(m,N)
        zeros=[n for n in range(1,N+1) if t[n]==0]
        three=[n for n in range(1,N) if (t[n-1]>0)==(t[n]>0)==(t[n+1]>0) and t[n-1]!=0 and t[n]!=0 and t[n+1]!=0]
        lc=[n for n in range(1,N) if not t[n]*t[n]>t[n-1]*t[n+1]]
        print(f"t m={m} N={N} zeros={zeros[:10]}({len(zeros)}) samesign3={three[:10]}({len(three)}) notLC={lc[:10]}({len(lc)})",flush=True)
        b=bseq(m,N)
        blc=[n for n in range(1,N) if not b[n]*b[n]>b[n-1]*b[n+1]]
        print(f"b m={m} notLC={blc[:10]}({len(blc)}) last={blc[-3:] if blc else None}",flush=True)
