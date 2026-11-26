# d^5/dt^5 of int g_t^alpha, g_t = p_t * mu, heat e^{t d^2} (variance 2t), mu = Gu-Sellke atomic measure.
import sys, mpmath as mp
mp.mp.dps=40
w0=mp.mpf('0.002'); c=[mp.mpf(s) for s in '0.034 0.093 0.134 0.123 0.075 0.031 0.008 0.001'.split()]
atoms=[(mp.mpf(0),w0)]+[(s*(mp.mpf('1.8')+j),c[j]) for j in range(8) for s in (1,-1)]
NMAX=int(sys.argv[3]) if len(sys.argv)>3 else 5
def herm(n,z):
    return mp.hermite(n,z)
def derivs(x,t):
    rho=[w*(4*mp.pi*t)**-0.5*mp.exp(-(x-a)**2/(4*t)) for a,w in atoms]
    g=mp.fsum(rho)
    K=[mp.mpf(1)]+[mp.fsum(r*herm(2*n,(x-a)/(2*mp.sqrt(t))) for r,(a,w) in zip(rho,atoms))/g/(4*t)**n for n in range(1,NMAX+1)]
    L=[mp.log(g)]
    for n in range(1,NMAX+1):
        L.append(K[n]-mp.fsum(mp.binomial(n-1,r-1)*L[r]*K[n-r] for r in range(1,n)))
    return g,K,L
def bell(n,xs):  # complete Bell Y_n(x1..xn)
    Y=[mp.mpf(1)]
    for k in range(1,n+1):
        Y.append(mp.fsum(mp.binomial(k-1,j-1)*xs[j]*Y[k-j] for j in range(1,k+1)))
    return Y[n]
def integrand(x,t,al,n):
    g,K,L=derivs(x,t)
    return g**al*bell(n,[None]+[al*L[j] for j in range(1,n+1)])
def T(al,t,n=5):
    pts=[mp.mpf(i)/2 for i in range(0,51)]
    return 2*mp.quad(lambda x: integrand(x,t,al,n),pts)
if __name__=="__main__":
    t=mp.mpf(sys.argv[2])
    for al in sys.argv[1].split(','):
        al=mp.mpf(al); v=T(al,t,NMAX)
        print("alpha",al,"t",t,"d^%d int g^a ="%NMAX,mp.nstr(v,15),"  /(a-1) =",mp.nstr(v/(al-1),10),flush=True)
