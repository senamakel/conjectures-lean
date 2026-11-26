import numpy as np, json, sys, math
from numpy.polynomial import chebyshev as Ch, polynomial as Pl
d=json.load(open(sys.argv[1])); K=d['K']; phi=np.array(d['Phi']); phi[np.abs(phi)<1e-12]=0
tol=float(sys.argv[2]); Theta=float(sys.argv[3]); ABS=float(sys.argv[4])
# Q(c) = phi0 + 2 sum phi_k T_k(c)
cc=np.zeros(K+1); cc[0]=phi[0]; cc[1:]=2*phi[1:]
Qp=Ch.cheb2poly(cc)  # power basis coefficients
def supQ(cl,ch):
    c0=(cl+ch)/2; r=(ch-cl)/2
    # Taylor coefficients at c0
    q=np.array([Pl.polyval(c0,Pl.polyder(Qp,j))/math.factorial(j) if j>0 else Pl.polyval(c0,Qp) for j in range(K+1)])
    return np.sum(np.abs(q)*r**np.arange(K+1))
def g0(th): return 2*(1-np.cos(th))*abs(Pl.polyval(np.cos(th),Qp))/th**2 if th>0 else Pl.polyval(1.0,Qp)
def cellsup(a,b):
    ca,cb=np.cos(a),np.cos(b); cl,ch=min(ca,cb),max(ca,cb)
    k0=np.ceil(a/np.pi); 
    if k0*np.pi<=b:  # straddles k pi
        if int(k0)%2==0: ch=1.0
        else: cl=-1.0
    sQ=supQ(cl,ch)
    if b*b<=15:
        f=1-a*a/12+a**4/360
    else:
        f=2*(1-cl)/a**2
    return f*sQ
# adaptive: grow cells so that (sup - integral avg)*width <= tol*width-ish
cells=[]; a=0.0; total=0.0; exact=0.0
from scipy.integrate import quad
dmin=1e-5
while a<Theta:
    dlt=0.05
    while True:
        b=min(a+dlt,Theta)
        G=cellsup(a,b)
        ex=quad(g0,a,b,limit=50)[0]
        loss=G*(b-a)-ex
        if loss<=tol*ex+ABS*(b-a) or dlt<dmin: break
        dlt/=1.6
    cells.append((a,b,G)); total+=G*(b-a); exact+=ex; a=b
print('cells',len(cells),'certified',total,'exact',exact,'ratio',total/exact)
json.dump(cells,open(sys.argv[5] if len(sys.argv)>5 else 'cells_tmp.json','w'))
