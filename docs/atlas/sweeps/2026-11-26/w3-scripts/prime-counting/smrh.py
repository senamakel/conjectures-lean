import math
g=0.5772156649015329
def li(x):
    L=math.log(x); t=1.0; tot=0.0
    for n in range(1,2000):
        t*=L/n
        tot+=t/n
        if t/n<1e-17*tot and n>L: break
    return g+math.log(L)+tot
def eps(x,c=1.0): return c*math.sqrt(x)*math.log(x)/(8*math.pi)
def upper(m,c):
    # sup over x>=2657 of m li(x) - x + m eps(x); scan log-grid around e^m
    best=-1e300
    lo=max(math.log(2657),m-6); hi=m+6
    N=6000
    for i in range(N+1):
        t=lo+(hi-lo)*i/N; x=math.exp(t)
        v=m*li(x)-x+m*eps(x,c)
        best=max(best,v)
    return best
def lower(m,c):
    x=math.exp(m); return m*li(x)-x-m*eps(x,c)
for c in (1.0,1.1):
    bad=[]
    for m in range(8,120):
        U=upper(m,c); L=lower(m+1,c)
        if not(L>0 and U>0 and math.log(U)/m < math.log(L)/(m+1)): bad.append(m)
    print("slack",c,"RH bound fails to separate m =",bad[-5:] if bad else None, "last",bad[-1] if bad else None)
# sanity: compare G* with true S
S={10:2743,15:254053,20:27130829}
for m in S: x=math.exp(m); print(m,S[m], m*li(x)-x)
