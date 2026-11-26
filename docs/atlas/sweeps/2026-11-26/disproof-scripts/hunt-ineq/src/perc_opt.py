import sys, random, numpy as np
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from perc import g6, configs
def margins(n,E,ps):
    w,C=configs(n,E,ps)
    size=np.zeros_like(C)
    for v in range(n): size[:,v]=[bin(x).count('1') for x in C[:,v]]
    best=(9,None)
    conn=np.zeros((n,n,len(w)),bool)
    for a in range(n):
        for b in range(n): conn[a,b]=(C[:,a]>>b)&1==1
    for o in range(n):
        C0=C[:,o]
        for A in range(1,1<<n):
            if (A>>o)&1 or bin(A).count('1')<3: continue
            hit=(C0&A)!=0; wA=w*hit
            al=[a for a in range(n) if A>>a&1]
            lhs=(wA*size[:,o]).sum(); rhs=min((wA*size[:,a]).sum() for a in al)
            m=(lhs-rhs)/max(lhs,1e-300)
            if m<best[0]: best=(m,('mcp',o,A))
            for b in range(n):
                if b==o or (A>>b)&1: continue
                P0b=(w*conn[o,b]).sum()
                pre=min((wA*conn[a,b]).sum() for a in al)
                post=wA.sum()*min((w*conn[a,b]).sum() for a in al)
                m1=(P0b-pre)/max(P0b,1e-300); m2=(P0b-post)/max(P0b,1e-300)
                if m1<best[0]: best=(m1,('pre',o,b,A))
                if m2<best[0]: best=(m2,('post',o,b,A))
    return best
lines=open(sys.argv[1]).read().split(); random.seed(int(sys.argv[2])); steps=int(sys.argv[3]); G=int(sys.argv[4])
for gi in random.sample(range(len(lines)),min(G,len(lines))):
    n,E=g6(lines[gi])
    ps=[random.random() for _ in E]; cur=margins(n,E,ps)
    for s in range(steps):
        q=[min(0.999,max(0.001,p+random.gauss(0,0.15))) if random.random()<0.5 else p for p in ps]
        m=margins(n,E,q)
        if m[0]<cur[0]: ps,cur=q,m
    print(lines[gi],"best margin",cur,[round(p,3) for p in ps],flush=True)
    if cur[0]<0: print("VIOLATION",lines[gi],cur,ps,flush=True)
