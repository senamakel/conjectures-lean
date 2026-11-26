from invs import *
from fractions import Fraction as Fr
import sys
I=build(9)
def lc(co):
    # min ratio a_i^2/(a_{i-1}a_{i+1}) over interior
    out=[]
    for i in range(1,len(co)-1):
        if co[i-1]*co[i+1]>0: out.append(Fr(co[i]**2,co[i-1]*co[i+1]))
    return out
def nreal(p):
    # count distinct real roots exactly via flint
    from flint import fmpz_poly
    return sum(1 for r,m in p.complex_roots() if r.imag==0 or (abs(r.imag)<1e-300 and False))
for k in range(3,9):
  for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32]:
    al=coalescence_alpha(k,q); n=k+1
    row=[]
    for name in 'PQZY':
        p=evaluate(I[name],al,n); co=[int(x) for x in p.coeffs()]
        r=lc(co)
        m=min(r) if r else None
        row.append('%s:%s'%(name, ('%.4g'%float(m)) if m is not None else '-'))
    print(k,q,' '.join(row)); sys.stdout.flush()
