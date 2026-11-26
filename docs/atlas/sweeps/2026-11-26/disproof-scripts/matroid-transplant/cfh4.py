import sys, io
_o=sys.stdout; sys.stdout=io.StringIO()
from yscan import fams
sys.stdout=_o
from lattices import *
from flags import beta_from_alpha
L4=[(n,L) for n,L in fams if L[0]==4]+[(f'coal3_{q}',coalescence(3,q)) for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,64,101,1009]]
worst=[]
for name,(n,al) in L4:
    b=beta_from_alpha(al)
    lhs=b[(1,2,3)]*b[(2,)]; rhs=b[(1,2)]*(b[(1,3)]+b[(2,3)])
    worst.append((rhs/lhs,name))
worst.sort()
for w in worst[:8]: print('%.4f'%w[0],w[1])
for w in worst:
    if w[1].startswith('coal'): print('%.4f'%w[0],w[1])
