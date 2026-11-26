import sys, itertools
def parse(s):
    n=ord(s[0])-63; bits=[]
    for ch in s[1:]:
        v=ord(ch)-63; bits+= [(v>>(5-i))&1 for i in range(6)]
    E=set(); k=0
    for j in range(1,n):
        for i in range(j):
            if bits[k]: E.add((i,j))
            k+=1
    return n,E
def adj(E,a,b): return (min(a,b),max(a,b)) in E
def comps(S,E):
    S=set(S); c=0
    while S:
        st=[S.pop()]; c+=1
        while st:
            x=st.pop()
            for y in list(S):
                if adj(E,x,y): S.remove(y); st.append(y)
    return c
def ne(S,E): return sum(1 for a,b in itertools.combinations(S,2) if adj(E,a,b))
def bip(S,E):
    S=list(S)
    for col in itertools.product([0,1],repeat=len(S)):
        if all(col[i]!=col[j] for i,j in itertools.combinations(range(len(S)),2) if adj(E,S[i],S[j])): return True
    return False
def ispath(seq,E): return all(adj(E,seq[i],seq[i+1]) for i in range(len(seq)-1))
for line in sys.stdin:
    s=line.strip(); n,E=parse(s); V=range(n)
    subs=[S for r in range(1,n+1) for S in itertools.combinations(V,r)]
    f=max(len(S) for S in subs if ne(S,E)==len(S)-comps(S,E))
    b=max(len(S) for S in subs if bip(S,E))
    tree=max(len(S) for S in subs if comps(S,E)==1 and ne(S,E)==len(S)-1)
    pth=max(len(S) for S in subs if comps(S,E)==1 and ne(S,E)==len(S)-1 and all(sum(adj(E,v,w) for w in S if w!=v)<=2 for v in S))
    kap=n-1
    for S in subs:
        if len(S)<kap:
            R=[v for v in V if v not in S]
            if comps(R,E)!=1: kap=len(S)
    for r in range(0,1):
        if comps(list(V),E)!=1: kap=0
    hp=int(any(ispath(p,E) for p in itertools.permutations(V)))
    pathable=lambda S: any(ispath(p,E) for p in itertools.permutations(S))
    # path cover by brute
    def pcov(rem):
        if not rem: return 0
        v=min(rem); best=99
        others=[x for x in rem if x!=v]
        for r in range(len(others)+1):
            for T in itertools.combinations(others,r):
                S=(v,)+T
                if pathable(S): best=min(best,1+pcov(tuple(x for x in rem if x not in S)))
        return best
    print("INV",f,b,tree,pth,kap,hp,pcov(tuple(V)))
