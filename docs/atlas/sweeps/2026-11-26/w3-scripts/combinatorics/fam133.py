# Build C4-free structured graphs and write edge lists; compute rad, l, C4-freeness
import itertools, sys, random
def polarity(q):  # ER_q, q prime: points of PG(2,q), x~y iff x.y=0, x!=y
    pts=[]
    for a in range(q):
        for b in range(q): pts.append((1,a,b))
    for b in range(q): pts.append((0,1,b))
    pts.append((0,0,1))
    idx={p:i for i,p in enumerate(pts)}
    E=[(i,j) for i in range(len(pts)) for j in range(i+1,len(pts)) if sum(x*y for x,y in zip(pts[i],pts[j]))%q==0]
    return len(pts),E
def incidence(q):  # Levi graph of PG(2,q), q prime
    pts=[]
    for a in range(q):
        for b in range(q): pts.append((1,a,b))
    for b in range(q): pts.append((0,1,b))
    pts.append((0,0,1)); N=len(pts)
    E=[(i,N+j) for i in range(N) for j in range(N) if sum(x*y for x,y in zip(pts[i],pts[j]))%q==0]
    return 2*N,E
def petersen():
    E=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(5+i,5+(i+2)%5) for i in range(5)]
    return 10,E
def hoffman_singleton():
    # Robertson construction: pentagons P_h, pentagrams Q_i, h,i in 0..4; P_h: j~j+1; Q_i: j~j+2; P_h j ~ Q_i (hi+j) mod 5
    V=lambda t,a,b: t*25+a*5+b
    E=[]
    for h in range(5):
        for j in range(5):
            E.append((V(0,h,j),V(0,h,(j+1)%5))); E.append((V(1,h,j),V(1,h,(j+2)%5)))
    for h in range(5):
        for j in range(5):
            for i in range(5): E.append((V(0,h,j),V(1,i,(h*i+j)%5)))
    E=list({tuple(sorted(e)) for e in E}); return 50,E
def stats(n,E):
    A=[set() for _ in range(n)]
    for a,b in E: A[a].add(b); A[b].add(a)
    c4=any(len(A[a]&A[c])>=2 for a in range(n) for c in range(a+1,n))
    ecc=[]
    for s in range(n):
        d={s:0}; fr=[s]
        while fr:
            nf=[]
            for x in fr:
                for y in A[x]:
                    if y not in d: d[y]=d[x]+1; nf.append(y)
            fr=nf
        assert len(d)==n
        ecc.append(max(d.values()))
    rad=min(ecc)
    from fractions import Fraction
    L=Fraction(sum(len(A[v])-sum(1 for x in A[v] for y in A[v] if x<y and y in A[x]) for v in range(n)),n)
    return c4,rad,L,max(ecc)
out=sys.argv[1]
fams=[('petersen',)+petersen(),('HS',)+hoffman_singleton()]
for q in [2,3,5,7,11,13]:
    fams.append(('ER%d'%q,)+polarity(q)); fams.append(('PG%dinc'%q,)+incidence(q))
for name,n,E in fams:
    c4,rad,L,diam=stats(n,E)
    import math
    target = rad+1 if c4 else rad+L
    print(name,n,len(E),'C4' if c4 else 'C4free','rad',rad,'diam',diam,'l',L,float(L),'need_path>=',math.ceil(target))
    with open(f'{out}/{name}.el','w') as f:
        f.write(f"{n} {len(E)} {math.ceil(target)}\n"+"\n".join(f"{a} {b}" for a,b in E)+"\n")
