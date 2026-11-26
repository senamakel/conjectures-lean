import sys, math
L=int(sys.argv[1])  # check p_n <= L
M=2*L+1000 if True else L
M=int(2.3*L)+1000
spf=list(range(M+1))
for i in range(2,int(M**0.5)+1):
    if spf[i]==i:
        for j in range(i*i,M+1,i):
            if spf[j]==j: spf[j]=i
primes=[i for i in range(2,M+1) if spf[i]==i]
def pf(m):
    out=[]
    while m>1:
        q=spf[m]; out.append(q)
        while m%q==0: m//=q
    return out
cache={}
def isprim(g,p):
    if p==2: return g%2==1
    if g%p==0: return False
    fs=cache.get(p)
    if fs is None: fs=cache[p]=pf(p-1)
    return all(pow(g,(p-1)//q,p)!=1 for q in fs)
f291=[];f847=[];mx291=(0,0);mx847=(0,0)
for n in range(1,len(primes)):
    P=primes[n-1]
    if P>L: break
    P1=primes[n]; 
    # A291690 comment: prime q<P primitive root mod P and P1
    ok=None
    for q in primes:
        if q>=P: break
        if isprim(q,P) and isprim(q,P1): ok=q;break
    if ok is None: f291.append(n)
    else: mx291=max(mx291,(ok,P))
    # A243847(i): prime q<P primitive mod P and p_{2n}
    if 2*n-1<len(primes):
        P2=primes[2*n-1]; ok=None
        for q in primes:
            if q>=P: break
            if isprim(q,P) and isprim(q,P2): ok=q;break
        if ok is None: f847.append(n)
        else: mx847=max(mx847,(ok,P))
print('A291690-comment failures n:',f291,' max least q:',mx291)
print('A243847(i) failures n:',f847,' max least q:',mx847)
