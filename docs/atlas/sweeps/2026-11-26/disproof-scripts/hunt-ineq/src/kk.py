import mpmath as mp, random, sys
mp.mp.dps=30; random.seed(int(sys.argv[1]))
def g(a,c,mu,k): return mp.rf(a+mu,k)/mp.rf(c+mu,k)
def coef(f,a,c,mu,nu,m,G):
    return mp.fsum(f[k]*f[m-k]/(mp.factorial(k)*mp.factorial(m-k))*(G(mu,k)*G(nu,m-k)-G(0,k)*G(mu+nu,m-k)) for k in range(m+1))
worst=(1,None); M=25
for t in range(int(sys.argv[2])):
    a=mp.mpf(random.choice([random.uniform(0.01,1),random.uniform(0.01,10)])); c=a+mp.mpf(random.choice([random.uniform(0,0.2),random.uniform(0,5),random.uniform(0,50)]))
    mu=mp.mpf(random.uniform(0,3)); nu=mp.mpf(random.choice([random.uniform(0,1),random.uniform(0,3)]))
    typ=random.randrange(4); q=mp.mpf(random.uniform(0.05,20))
    if typ==0: f=[mp.mpf(1)]*(M+1)
    elif typ==1: f=[q**k for k in range(M+1)]
    elif typ==2: L=random.randint(1,M); f=[mp.binomial(L,k) if k<=L else mp.mpf(0) for k in range(M+1)]
    else: f=[q**k/mp.factorial(k) for k in range(M+1)]
    G=lambda mu_,k: g(a,c,mu_,k)
    for m in range(1,M+1):
        v=coef(f,a,c,mu,nu,m,G)
        scale=mp.fsum(abs(f[k]*f[m-k]/(mp.factorial(k)*mp.factorial(m-k)))*G(mu,k)*G(nu,m-k) for k in range(m+1))
        r=v/scale if scale else 0
        if r<worst[0]: worst=(r,(float(a),float(c),float(mu),float(nu),typ,float(q),m))
        if v< -mp.mpf(10)**-25*scale: print("NEG",float(a),float(c),float(mu),float(nu),typ,float(q),m,mp.nstr(r,8),flush=True); break
print("worst",worst)
