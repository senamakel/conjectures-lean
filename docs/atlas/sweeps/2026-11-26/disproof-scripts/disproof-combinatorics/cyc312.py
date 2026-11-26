# count cyclic 312-avoiding perms of [n] via stack-realization DP with path-matching state
import sys
from itertools import permutations
def brute(n, pat):
    k=len(pat); c=0
    from itertools import combinations
    for p in permutations(range(1,n+1)):
        # cyclic?
        seen=1; x=p[0]
        while x!=1: x=p[x-1]; seen+=1
        if seen!=n: continue
        ok=True
        for idx in combinations(range(n),k):
            vals=[p[i] for i in idx]
            if all((vals[a]<vals[b])==(pat[a]<pat[b]) for a in range(k) for b in range(a+1,k)):
                ok=False;break
        if ok: c+=1
    return c
def dp312(n):
    # state: g tuple, g[i] = end-rank (0-based) of path starting at stack pos i (0=bottom)
    # layer by step; v pushes, p pops
    cur={(0,0,()):1}
    total=0; maxstates=0
    for step in range(2*n):
        nxt={}
        for (v,p,g),c in cur.items():
            h=len(g)
            if v<n:
                key=(v+1,p,g+(h,))
                nxt[key]=nxt.get(key,0)+c
            if h>0:
                a=g.index(0)
                if a==h-1:
                    if v==n and p==n-1: total+=c
                    continue
                gt=g[h-1]
                ng=list(g[:h-1]); ng[a]=gt
                ng=tuple(x-1 for x in ng)
                key=(v,p+1,ng)
                nxt[key]=nxt.get(key,0)+c
        cur=nxt; maxstates=max(maxstates,len(cur))
    return total,maxstates
if __name__=="__main__":
    for n in range(2,8): print(n, brute(n,(3,1,2)), dp312(n)[0])
    import time
    for n in range(8,int(sys.argv[1])+1):
        t=time.time(); r=dp312(n); print(n,r,round(time.time()-t,2),flush=True)
