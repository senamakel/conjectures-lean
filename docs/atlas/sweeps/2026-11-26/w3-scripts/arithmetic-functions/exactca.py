import sys; sys.path.insert(0,'.')
from ca import *
from fractions import Fraction
from decimal import getcontext
getcontext().prec=300
G=D('0.5772156649015328606065120900824024310421593359399235988057672348848677267776646709369470632917467495')
def sigma_from(exps):
    s=1
    for p,a in exps.items(): s*=(p**(a+1)-1)//(p-1)
    return s
def H(n):  # harmonic number, exact for small n, asymptotic for large n
    nn=D(n); return nn.ln()+G+1/(2*nn)-1/(12*nn*nn)+1/(120*nn**4)-1/(252*nn**6)
def Hsmall(n):
    from math import fsum
    s=Fraction(0)
    for k in range(1,n+1): s+=Fraction(1,k)
    return D(s.numerator)/D(s.denominator)
def L(n):
    h=Hsmall(n) if n<3000 else H(n)
    v=h+h.exp()*h.ln()
    return int(v.to_integral_value(rounding='ROUND_FLOOR'))
# exact CA list by the epsilon heap (generic), starting N=1
exps={}; N=1; out=[]
for p,k,eps,logN,logS in ca_stream(2000):
    exps[p]=k; N*=p
    out.append((N,dict(exps),p,eps))
    if N>10**200: break
# note: A004490 starts 2,6,12,60,120,360,2520,5040,...
print([o[0] for o in out[:12]])
F=[]
for i,(N,e,p,eps) in enumerate(out,1):
    s=sigma_from(e); f=L(N)-s; F.append(f)
for i in range(1,len(F)):
    r=Fraction(F[i],F[i-1]) if F[i-1]>0 else None
    flag = (r is not None and r<2)
    if i<25 or flag: print(i+1, out[i][2], "N=%.4e"%out[i][0], "F=",F[i] if F[i]<10**25 else "%.6e"%F[i], "ratio=%.6f"%float(r) if r else '', "RATIO<2" if flag else "")
