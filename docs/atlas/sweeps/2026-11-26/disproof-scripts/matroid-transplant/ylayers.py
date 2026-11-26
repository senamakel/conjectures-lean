from betaw import beta_weights
from invs import build
from flint import fmpz_poly
I=build(10)
def coef(p,i):
    c=[int(x) for x in p.coeffs()]
    return c[i] if i<len(c) else 0
def layer_weights(n):
    W=beta_weights(I['Y'],n)
    out={}
    for j in range(0,n//2+1):
        d={}
        for T,p in W.items():
            v=coef(p,j)-(coef(p,j-1) if j>0 else 0)
            if v: d[T]=v
        out[j]=d
    return out
for n in range(3,10):
    Lw=layer_weights(n)
    print('rank',n)
    for j,d in Lw.items(): print('  c_%d ='%j, ' '.join(f'{v:+d}*b{"".join(map(str,T)) or "0"}' for T,v in sorted(d.items())))
    if n%2==0:
        j=n//2
        Pw=beta_weights(I['P'],n-1)
        pd={T:coef(p,j-1) for T,p in Pw.items() if coef(p,j-1)}
        print('  check c_%d == P_%d(trunc to rank %d):'%(j,j-1,n-1), pd==Lw[j])
