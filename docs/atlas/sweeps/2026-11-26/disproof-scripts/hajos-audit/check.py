import itertools, sys
V=[(i,a) for i in range(5) for a in range(3)]
idx={v:k for k,v in enumerate(V)}
def adj(x,y):
    return x!=y and ((x[0]==y[0]) or (y[0]-x[0])%5 in (1,4))
N=[[adj(x,y) for y in V] for x in V]
n=15
# chromatic number: exact via search for proper k-colouring
def colorable(k):
    col=[-1]*n
    order=list(range(n))
    def rec(i,used):
        if i==n: return True
        v=order[i]
        for c in range(min(used+1,k)):
            if all(not(N[v][u] and col[u]==c) for u in range(n)):
                col[v]=c
                if rec(i+1,max(used,c+1)): return True
                col[v]=-1
        return False
    return rec(0,0)
print("7-colourable:",colorable(7),"8-colourable:",colorable(8))
alpha=max(len(s) for r in range(1,5) for s in itertools.combinations(range(n),r) if all(not N[a][b] for a,b in itertools.combinations(s,2)))
print("alpha:",alpha)
# exact K8 topological-minor search: branch set B (8 vertices), every pair of B joined by
# internally disjoint paths whose interiors avoid B. Adjacent pairs: use direct edge (WLOG: a
# path with empty interior uses no resources). Non-adjacent pairs need paths through free vertices.
def paths_through(s,t,free):
    # all simple paths s -> t with interior a nonempty subset of free (as frozenset of interior)
    res=[]
    def dfs(v,seen,inter):
        for u in free:
            if u not in seen and N[v][u]:
                if N[u][t]:
                    res.append(frozenset(inter+[u]))
                dfs(u,seen|{u},inter+[u])
    dfs(s,{s},[])
    return list(set(res))
count=0; found=None
for B in itertools.combinations(range(n),8):
    Bs=set(B); free=[v for v in range(n) if v not in Bs]
    pairs=[(a,b) for a,b in itertools.combinations(B,2) if not N[a][b]]
    if len(pairs)>len(free): continue
    opts=[paths_through(a,b,free) for a,b in pairs]
    opts.sort(key=len)
    def rec(i,used):
        if i==len(opts): return True
        for p in opts[i]:
            if not (p & used):
                if rec(i+1,used|p): return True
        return False
    count+=1
    if rec(0,frozenset()):
        found=B; break
print("branch sets needing search:",count,"subdivision found:",found)
# also sanity: the search finds K7 subdivision (positive control) and K8 in K15-type graph
# positive control: K7 in C5[K3]
def has_Kk(k):
    for B in itertools.combinations(range(n),k):
        Bs=set(B); free=[v for v in range(n) if v not in Bs]
        pairs=[(a,b) for a,b in itertools.combinations(B,2) if not N[a][b]]
        if len(pairs)>len(free): continue
        opts=sorted([paths_through(a,b,free) for a,b in pairs],key=len)
        def rec(i,used):
            if i==len(opts): return True
            return any(not(p&used) and rec(i+1,used|p) for p in opts[i])
        if rec(0,frozenset()): return B
    return None
print("K7 subdivision (positive control):",has_Kk(7))
# arithmetic lemma check over all vectors
bad=[a for a in itertools.product(range(4),repeat=5) if sum(a)==8 and not
     7+sum(min(a[(c-1)%5]*a[(c+1)%5],3-a[c]) for c in range(5)) < 2*sum(a[(c-1)%5]*a[(c+1)%5] for c in range(5))]
print("arith counterexamples:",bad, "vectors:",sum(1 for a in itertools.product(range(4),repeat=5) if sum(a)==8))
