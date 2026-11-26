# independent check: brute-force domination and independence polynomials over all subsets
import sys, itertools
def polys(n, edges):
    nb=[1<<v for v in range(n)]; adj=[0]*n
    for a,b in edges: nb[a]|=1<<b; nb[b]|=1<<a; adj[a]|=1<<b; adj[b]|=1<<a
    D=[0]*(n+1); I=[0]*(n+1); full=(1<<n)-1
    for S in range(1<<n):
        cov=0; ind=True; k=bin(S).count('1')
        for v in range(n):
            if S>>v&1:
                cov|=nb[v]
                if adj[v]&S: ind=False
        if cov==full: D[k]+=1
        if ind: I[k]+=1
    return D,I
# read parent arrays from gentreeg -p output (1-based)
out=[]
for line in sys.stdin:
    p=list(map(int,line.split()))
    if not p: continue
    n=len(p); edges=[(j-1,p[j-1]-1) for j in range(2,n+1)]
    D,I=polys(n,edges)
    while D and D[-1]==0: D.pop()
    while I and I[-1]==0: I.pop()
    print(' '.join(map(str,D)),'|',' '.join(map(str,I)))
