from flags import coalescence_alpha, beta_from_alpha
from itertools import combinations
import sympy as sp
x=sp.symbols('x')
def stable(m):
    out=[]
    for j in range(0,m+1):
        for S in combinations(range(1,m+1),j):
            if all(S[i+1]-S[i]>=2 for i in range(len(S)-1)): out.append(S)
    return out
def dual_polys(beta,r):
    R=tuple(range(1,r))
    H=sum(beta[tuple(a for a in R if a not in S)]*x**len(S)*(1+x)**(r-1-2*len(S)) for S in stable(r-2))
    F=sum(beta[tuple(a for a in R if a not in S)]*x**len(S)*(1+x)**(r-2*len(S)) for S in stable(r-1))
    return sp.Poly(sp.expand(H),x), sp.Poly(sp.expand(F),x)
def nreal(p): return sp.count_roots(p)   # exact (Sturm) count of distinct real roots
pp=[2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37]
for k in [4,5,6,7]:
    r=k+1; first=None
    for q in pp:
        b=beta_from_alpha(coalescence_alpha(k,q)); H,F=dual_polys(b,r)
        okH = nreal(H)==len(set(sp.roots(H,multiple=True))) if False else (sp.count_roots(H)==H.degree() and sp.sqf_part(H).degree()==H.degree())
        hr=sp.count_roots(sp.Poly(sp.sqf_part(H.as_expr()),x)); fr=sp.count_roots(sp.Poly(sp.sqf_part(F.as_expr()),x))
        hd=sp.Poly(sp.sqf_part(H.as_expr()),x).degree(); fd=sp.Poly(sp.sqf_part(F.as_expr()),x).degree()
        failH = hr<hd; failF= fr<fd
        if failH and failF and first is None: first=q
    print('rank',r,'first prime power with both failing:',first)
