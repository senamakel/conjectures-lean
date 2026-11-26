# cyclic 231-avoiders (= cyclic 312-avoiders by inversion) via position sweep:
# pi(i) must lie in the lowest run of consecutive unused values.
import sys,time
from cyc312 import brute
def dp231(n):
    # state: (sep, gend, mask, f)
    # sep: tuple of bools len h-1: used value between A[i],A[i+1]; gend: used value in (A[last], p]
    # mask: bit j => value p+1+j used ; f: A-rank -> B-rank
    cur={((),False,0,()):1}; total=0; mx=0
    for p in range(n):
        q=p+1; nxt={}
        for (sep,gend,mask,f),c in cur.items():
            h=len(f)
            def add(k):
                nxt[k]=nxt.get(k,0)+c
            qinB = mask&1
            # lowest run candidates
            cands=[]  # ('A',i) or ('V',off)
            if h>0:
                j=0
                cands.append(('A',0))
                while j<h-1 and not sep[j]:
                    j+=1; cands.append(('A',j))
                cont = (j==h-1 and not gend)
            else:
                cont=True
            if cont:
                off=1
                # skip? the run continues into values > p only through unused values starting at p+1
                if h==0:
                    # u = smallest unused > p: skip used bits first
                    while mask>>(off-1)&1: off+=1
                while off<=n-p and not (mask>>(off-1)&1):
                    cands.append(('V',off)); off+=1
            for typ,x in cands:
                if typ=='V' and x==1: continue  # y==q fixed point
                if qinB:
                    s=f.index(0)
                    if typ=='A':
                        i=x
                        if s==i:
                            if q==n and h==1: total+=c
                            continue
                        nf=list(f); nf[s]=f[i]; del nf[i]; nf=tuple(v-1 for v in nf)
                        # remove A[i]: merges gaps: sep between A[i-1],A[i+1] becomes True
                        ns=list(sep)
                        if h==1: ns=[]; ng=True
                        elif i==h-1: ng=True; ns=ns[:-1]
                        else:
                            if i==0: ns=ns[1:]
                            else: ns[i-1]=True; del ns[i]
                            ng=gend
                        ng=True  # q (used) now <= p'
                        add((tuple(ns),ng,mask>>1,nf))
                    else:
                        y=x
                        nm=(mask|(1<<(y-1)))>>1
                        # B ranks: remove q (rank0), add y with rank = number of B elems below y
                        rank=bin(mask & ((1<<(y-1))-1)).count('1')  # includes q
                        nf=list(f); nf[s]=None
                        nf=[(v-1 if v<rank else v) if v is not None else None for v in nf]
                        nf=[v if v is None or v<rank-1 else v for v in nf]
                        # simpler recompute below
                        nf2=[]
                        for a,v in enumerate(f):
                            if a==s: nf2.append(rank-1)
                            else:
                                nv=v-1
                                if nv>=rank-1: nv+=1
                                nf2.append(nv)
                        add((sep,True,nm,tuple(nf2)))
                else:
                    if typ=='A':
                        i=x
                        nf=list(f); fi=f[i]; del nf[i]; nf.append(fi)
                        ns=list(sep)
                        # remove A[i]
                        if h==1: ns=[]; g2=True
                        elif i==h-1: ns=ns[:-1]; g2=True
                        else:
                            if i==0: ns=ns[1:]
                            else: ns[i-1]=True; del ns[i]
                            g2=gend
                        # add q as new max A: sep to previous last = g2 (used values in (A_last, p]) 
                        if len(nf)>1: ns.append(g2)
                        add((tuple(ns),False,mask>>1,tuple(nf)))
                    else:
                        y=x
                        rank=bin(mask & ((1<<(y-1))-1)).count('1')
                        nf2=[]
                        for v in f:
                            nf2.append(v+1 if v>=rank else v)
                        nf2.append(rank)
                        nm=(mask|(1<<(y-1)))>>1
                        ns=list(sep)
                        if h>0: ns.append(gend)
                        add((tuple(ns),False,nm,tuple(nf2)))
        cur=nxt; mx=max(mx,len(cur))
    return total,mx
if __name__=="__main__":
    for n in range(2,8): print(n, brute(n,(2,3,1)), dp231(n)[0])
    for n in range(8,int(sys.argv[1])+1):
        t=time.time(); r=dp231(n); print(n,r,round(time.time()-t,2),flush=True)
