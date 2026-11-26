import numpy as np, sys, itertools
rng=np.random.default_rng(int(sys.argv[1])); T=int(sys.argv[2])
X0=[np.sqrt(2),np.sqrt(3),2.0]; B=[1/8,1/16,9/256]
signs={}
def S(n):
    if n not in signs: signs[n]=np.array(list(itertools.product([-1,1],repeat=n)),dtype=float)
    return signs[n]
def score(a):
    a=a/np.linalg.norm(a); s=S(len(a))@a
    return [np.mean(s>x+1e-9)-b for x,b in zip(X0,B)]
best=[-1,-1,-1]; 
for t in range(T):
    n=rng.integers(3,15)
    a=np.abs(rng.normal(size=n))**rng.uniform(0.2,3)
    for which in range(3):
        cur=score(a)[which]; aa=a.copy()
        for it in range(300):
            q=np.abs(aa*np.exp(rng.normal(0,0.1,n)) if rng.random()<0.7 else aa+rng.normal(0,0.05,n)*(rng.random(n)<0.3))
            v=score(q)[which]
            if v>=cur: aa,cur=q,v
        if cur>best[which]:
            best[which]=cur; print("which",which,"n",n,"excess",cur,"w",np.round(aa/np.linalg.norm(aa),4).tolist(),flush=True)
        if cur>1e-12: print("VIOL",which,(aa/np.linalg.norm(aa)).tolist(),flush=True)
print("done best",best)
