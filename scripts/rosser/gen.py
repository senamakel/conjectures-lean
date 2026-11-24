import pickle, os
from exact import cdiv, mulU, omU, psiU, D
g,beta,alpha,idl=pickle.load(open('table.pkl','rb'))
N=len(g)-1
cells=[(g[k],beta[k],alpha[k]) for k in range(N)]
def crudeU(a,b): return cdiv(omU(2*a,b)+cdiv(D*(1001*1001*4*a*a),1000000*15*b*b),12**6)
def momU(l,ea,eb):
    if not l: return 0
    if len(l)==1: return mulU(l[0][2],omU(ea,eb))
    x,y=l[0],l[1]
    return mulU(x[2]-y[2],omU(y[0],y[1]))+momU(l[1:],ea,eb)
def chainOK(l):
    return all(x[0]*y[1]<=y[0]*x[1] and y[2]<=x[2] for x,y in zip(l,l[1:]))
def boundsOK(l,ea,eb): return all(0<x[1]<=x[0] and x[0]*eb<=ea*x[1] for x in l)
def lrowOK(c):
    S=c[0]; h=[d for d in cells if d[0]+100<=S]
    if not h: return False
    l=[(1,1,h[-1][1])]+[(d[0]+100,S,d[1]) for d in cells if S<d[0]+100]
    return chainOK(l) and boundsOK(l,1300,S) and 0<S<=1300 and momU(l,1300,S)+crudeU(1300,S)<=c[2]
def urowOK(c):
    S=c[0]; h=[d for d in cells if 210<=d[0] and d[0]+100<=S]
    hd=D if not h else h[-1][2]
    l=[(1,1,hd)]+[(d[0]+100,S,d[2]) for d in cells if 210<=d[0] and S<d[0]+100]
    return chainOK(l) and boundsOK(l,1300,S) and 0<S<=1300 and momU(l,1300,S)+crudeU(1300,S)<=c[1]
tpts=[(120+q,120) for q in range(11)]+[(815+35*j,720) for j in range(59)]
def tH(X,x): return max(X,psiU(*x)) if 12*x[0]<13*x[1] else psiU(*x)
tailCrude=mulU(psiU(4,1), omU(8,1)+cdiv(D*(1001*1001*64),1000000*15))
def tailOK(X):
    l=[(a,b,tH(X,(a,b))) for (a,b) in tpts]
    return chainOK(l) and boundsOK(l,4,1) and momU(l,4,1)+tailCrude<=D
import sys
sys.setrecursionlimit(10000)
ok=all(((c[0]<200) or lrowOK(c)) and urowOK(c) for c in cells)
c11=[c for c in cells if c[0]==1100][0]
ok=ok and tailOK(13**6*c11[1]) and tailOK(13**6*c11[2])
ok=ok and any(c[0]==210 and c[2]<=D for c in cells) and any(c[0]==205 and 100*c[2]<=98*D for c in cells)
print("allOK",ok, "tail", (momU([(a,b,tH(13**6*c11[1],(a,b))) for (a,b) in tpts],4,1)+tailCrude)/D)
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','Shoup','Rosser','Table.lean'),'w') as f:
    f.write('''import Shoup.Rosser.Rows

/-!
# The Rosser table (generated)

`cells` lists `(g, β, α)` for the grid `s = g/100`: `U ≤ V (1 + β/D)` for `s ≥ g/100`, and
`L ≥ V (1 - α/D)` for `s ≥ g/100 ≥ 2` (`D = 2^48`). The rows were found by a linear program
and are checked here by the kernel (`allOK_cells`).
-/

namespace Shoup.Rosser

def cells : List Ent := [
''')
    f.write(",\n".join(f"  ({a}, {b}, {c})" for a,b,c in cells))
    f.write('''
]

set_option maxRecDepth 100000 in
theorem allOK_cells : allOK cells = true := by decide +kernel

end Shoup.Rosser
''')
