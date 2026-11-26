# LP design of the shifted-Lorentzian majorant (Cramer/Shift). Usage:
#   python3 scripts/shift_lp.py 0.15,0.3,1,4,14,30 12 0.125 1.012 B   -> sol_B.json
# Majorises the per-zero envelope at eps = 1/800 (times 1.004) by sum c (lor(s, x-t) + lor(s, x+t)),
# minimising R = sum 2 s c; the centred terms with s >= 3 must carry tail mass >= argv[4].
import numpy as np, sys, json
from scipy.optimize import linprog
eps=1/800; ep=eps/(1-eps)
x=np.concatenate([np.linspace(1e-4,40,16001),np.geomspace(40,20000,600)])
def sinc2(y): return np.sinc(y/np.pi)**2
def Tp(y): return 1-y/6+y*y/120
S=np.where(x<=1,(1+eps)*(Tp(x*x)**2+ep*(1+4*x*(1+ep))),np.inf)
wb=1.5*eps/(1-eps)+x*eps*(1+2*eps/(1-eps))
L=np.where((wb<=1)&(x>=0.5),sinc2(x)+(wb+wb**2)/(2*x**2),np.inf)
T=(1+2*eps)/x**2
f=np.minimum(np.minimum(S,L),T)
sigs=[float(s) for s in sys.argv[1].split(',')]
taus=np.arange(0,float(sys.argv[2])+1e-9,float(sys.argv[3]))
cols=[];cost=[];lab=[]
for s in sigs:
  for t in taus:
    k=s*s/(s*s+(x-t)**2)+s*s/(s*s+(x+t)**2)
    cols.append(k);cost.append(2*s);lab.append((s,t))
A=np.array(cols).T
tail=np.array([[-2*l[0]**2 if (l[1]==0 and l[0]>=3) else 0 for l in lab]])
r=linprog(cost,A_ub=np.vstack([-A,tail]),b_ub=np.concatenate([-f*1.004,[-float(sys.argv[4])]]),bounds=[(0,None)]*len(cost),method='highs-ds')
print("R(1.004 f) =",r.fun)
sol=[(l,v) for l,v in zip(lab,r.x) if v>1e-7]
json.dump([(l[0],l[1],v) for l,v in sol],open("sol_"+sys.argv[5]+".json","w"))
print(len(sol))
