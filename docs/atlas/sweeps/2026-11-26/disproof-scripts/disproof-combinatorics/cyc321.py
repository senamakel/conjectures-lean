import sys,time
from cyc312 import brute
def dp321(n):
    # state: (mask, f) ; mask bit j (j>=0) means value p+1+j is used (in B); f: tuple, f[a]=b-rank for A-rank a
    cur={(0,()):1}; total=0; mx=0
    for p in range(n):
        q=p+1; nxt={}
        for (mask,f),c in cur.items():
            h=len(f)
            m_off = mask.bit_length()  # m = p + m_off if mask else <=p
            inB = mask & 1
            Bpos=[j for j in range(m_off) if mask>>j&1]  # offsets sorted
            def add(nm,nf):
                k=(nm,nf); nxt[k]=nxt.get(k,0)+c
            if inB:
                # q is B-rank 0
                s=f.index(0)
                # y = min A (rank 0)
                if s==0:
                    if q==n and h==1: total+=c
                else:
                    fy=f[0]
                    nf=list(f); nf[s]=fy; nf=nf[1:]  # remove A-rank0
                    nf=tuple(x-1 for x in nf)       # B-rank 0 removed
                    add(mask>>1, nf)
                # y = w > m
                for w_off in range(m_off+1, n-p+1):
                    newmask=(mask | (1<<(w_off-1)))>>1
                    # new B ranks: B without q, plus w at the end (largest)
                    nf=list(f); nf[s]=h  # w gets rank h before removing q -> after shift h-1
                    nf=tuple(x-1 for x in nf)
                    add(newmask, nf)
            else:
                if h>0:
                    fu=f[0]
                    nf=f[1:]+(fu,)   # remove rank0, add q as max A with end f(u)
                    add(mask>>1, nf)
                else:
                    pass # u==q fixed point: bad (n>1)
                for w_off in range(max(m_off,0)+1, n-p+1):
                    if w_off==1: continue  # w==q fixed point
                    newmask=(mask | (1<<(w_off-1)))>>1
                    # B ranks: w is the largest
                    nf=f+(h,)
                    add(newmask, nf)
        cur=nxt; mx=max(mx,len(cur))
    return total,mx
if __name__=="__main__":
    for n in range(2,8): print(n, brute(n,(3,2,1)), dp321(n)[0])
    for n in range(8,int(sys.argv[1])+1):
        t=time.time(); r=dp321(n); print(n,r,round(time.time()-t,2),flush=True)
