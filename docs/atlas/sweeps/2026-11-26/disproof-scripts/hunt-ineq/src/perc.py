# Kozma-Nitzan conjectures: exhaustive small graphs, float search
import sys, itertools, numpy as np, random
def g6(s):
    s=s.strip(); n=ord(s[0])-63; bits=[]
    for ch in s[1:]:
        v=ord(ch)-63; bits+= [(v>>(5-i))&1 for i in range(6)]
    E=[]; k=0
    for j in range(1,n):
        for i in range(j):
            if bits[k]: E.append((i,j))
            k+=1
    return n,E
def configs(n,E,ps):
    m=len(E); N=1<<m
    out_w=np.empty(N); comps=np.empty((N,n),dtype=np.int64)
    for c in range(N):
        w=1.0; adj=[1<<v for v in range(n)]
        for e,(i,j) in enumerate(E):
            if c>>e&1: w*=ps[e]; adj[i]|=1<<j; adj[j]|=1<<i
            else: w*=1-ps[e]
        # components
        comp=[0]*n
        for v in range(n):
            if comp[v]: continue
            S=1<<v; F=S
            while F:
                NF=0; x=F
                while x:
                    lb=x&-x; NF|=adj[lb.bit_length()-1]; x^=lb
                F=NF&~S; S|=NF
            x=S
            while x:
                lb=x&-x; comp[lb.bit_length()-1]=S; x^=lb
        out_w[c]=w; comps[c]=comp
    return out_w,comps
def check(n,E,ps,tag,res):
    w,C=configs(n,E,ps)
    size=np.zeros_like(C)
    for v in range(n): size[:,v]=[bin(x).count('1') for x in C[:,v]]
    for o in range(n):
        C0=C[:,o]
        subsets=[A for A in range(1,1<<n) if not (A>>o)&1 and bin(A).count('1')>=3]
        for A in subsets:
            hit=(C0&A)!=0; wA=w*hit; PA=wA.sum()
            al=[a for a in range(n) if A>>a&1]
            # mcp f=|Cl|
            lhs=(wA*size[:,o]).sum(); rhs=min((wA*size[:,a]).sum() for a in al)
            if lhs<rhs-1e-12: res.append(('mcp|Cl|',tag,o,A,lhs-rhs))
            for k in range(5,n+1):
                lhs=(wA*(size[:,o]>=k)).sum(); rhs=min((wA*(size[:,a]>=k)).sum() for a in al)
                if lhs<rhs-1e-12: res.append(('mcp>=%d'%k,tag,o,A,lhs-rhs))
            for b in range(n):
                if b==o: continue
                bmask=1<<b
                P0b=(w*((C0&bmask)!=0)).sum()
                pre=[(wA*((C[:,a]&bmask)!=0)).sum() for a in al]
                pab=[(w*((C[:,a]&bmask)!=0)).sum() for a in al]
                if P0b<min(pre)-1e-12: res.append(('pre',tag,o,b,A,P0b-min(pre)))
                if P0b<PA*min(pab)-1e-12: res.append(('post',tag,o,b,A,P0b-PA*min(pab)))
                # Question 1: minimiser of P(a<->b) satisfies P(0<->b,0<->A) >= P(0<->A,a<->b)
                i=int(np.argmin(pab)); lhs=(wA*((C0&bmask)!=0)).sum()
                ties=[j for j in range(len(al)) if pab[j]<=pab[i]+1e-12]
                if all(lhs<pre[j]-1e-12 for j in ties): res.append(('Q1',tag,o,b,A,lhs-max(pre[j] for j in ties)))
if __name__=="__main__":
    f=sys.argv[1]; mode=sys.argv[2]; seed=int(sys.argv[3]); random.seed(seed)
    lines=open(f).read().split()
    lo,hi=map(int,sys.argv[4].split(':')) if len(sys.argv)>4 else (0,len(lines))
    res=[]
    for li in range(lo,min(hi,len(lines))):
        n,E=g6(lines[li])
        if mode=='half': plist=[[0.5]*len(E)]
        elif mode=='grid': plist=[[p]*len(E) for p in (0.1,0.3,0.7,0.9)]
        else: plist=[[random.choice([0.05,0.2,0.5,0.8,0.95,1.0]) for _ in E] for _ in range(int(mode))]
        for ps in plist:
            check(n,E,ps,(lines[li],tuple(ps)),res)
    seen=set()
    for r in res:
        k=(r[0],r[1][0])
        if k in seen: continue
        seen.add(k); print(r,flush=True)
    print("done",f,mode,len(res),flush=True)
