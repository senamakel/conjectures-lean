import numpy as np, itertools, sys
rng=np.random.default_rng(int(sys.argv[2]))
n=int(sys.argv[1]); trials=int(sys.argv[3])
def conj_order(n):  # positions: a1,a3,a5,...,a6,a4,a2  (indices 0-based of sorted)
    odd=list(range(0,n,2)); even=list(range(1,n,2))
    return odd+even[::-1]
perms=[(0,)+p for p in itertools.permutations(range(1,n))]
perms=[p for p in perms if p[1]<p[-1]]  # mod reflection
P=np.array(perms)
thetas=np.linspace(0,np.pi/n,7)
def lmax_batch(W,th):  # W: (m,n) weights in cyclic order
    m=W.shape[0]; H=np.zeros((m,n,n),complex)
    idx=np.arange(n); nxt=(idx+1)%n
    H[:,idx,nxt]=W*np.exp(-1j*th)/2; H[:,nxt,idx]=W*np.exp(1j*th)/2
    return np.linalg.eigvalsh(H)[:,-1]
worst=-1
for t in range(trials):
    mode=t%3
    a=np.sort(rng.random(n)**(1+3*rng.random()) if mode==0 else (rng.integers(1,6,n).astype(float) if mode==1 else np.exp(rng.normal(0,1.5,n))))
    co=conj_order(n); Wc=a[co][None,:]
    W=a[P]
    for th in thetas:
        lc=lmax_batch(Wc,th)[0]; ls=lmax_batch(W,th)
        gap=(ls.max()-lc)/lc
        if gap>worst: worst=gap; best=(a.tolist(),th,P[ls.argmax()].tolist(),gap)
        if gap>1e-9: print("VIOL",a.tolist(),th,P[ls.argmax()].tolist(),gap,flush=True)
print("n",n,"trials",trials,"worst rel gap",worst,best,flush=True)
